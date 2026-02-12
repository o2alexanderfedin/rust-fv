//! VC caching with SHA-256 hash-based invalidation.
//!
//! Provides per-function caching of verification results to skip re-verification
//! when source code hasn't changed. Cache keys are SHA-256 hashes of:
//! - Function name
//! - All contracts (requires/ensures/invariants)
//! - MIR debug representation (conservative: any MIR change invalidates)
//!
//! Cache is stored in `target/rust-fv-cache/` as JSON files, one per function.
//! Cleaned by `cargo clean`.

use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::fs;
use std::path::PathBuf;

/// In-memory cache of verification results.
pub struct VcCache {
    /// Cached entries, keyed by SHA-256 hash
    entries: FxHashMap<[u8; 32], CacheEntry>,
    /// Directory for cache files (target/rust-fv-cache/)
    cache_dir: PathBuf,
}

/// Cached verification result for a single function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheEntry {
    /// Overall verification result (true = all VCs verified)
    pub verified: bool,
    /// Total number of VCs generated
    pub vc_count: usize,
    /// Number of VCs that verified successfully
    pub verified_count: usize,
    /// Failure message if any VC failed
    pub message: Option<String>,
}

impl VcCache {
    /// Create a new cache with the specified directory.
    ///
    /// If the directory doesn't exist, it will be created.
    pub fn new(cache_dir: PathBuf) -> Self {
        if !cache_dir.exists() {
            let _ = fs::create_dir_all(&cache_dir);
        }
        Self {
            entries: FxHashMap::default(),
            cache_dir,
        }
    }

    /// Load all cache entries from disk into memory.
    ///
    /// Reads all `.json` files from the cache directory and deserializes them.
    /// Malformed files are silently skipped.
    pub fn load(&mut self) {
        if !self.cache_dir.exists() {
            return;
        }

        let read_dir = match fs::read_dir(&self.cache_dir) {
            Ok(rd) => rd,
            Err(_) => return,
        };

        for entry in read_dir.flatten() {
            let path = entry.path();
            if path.extension().and_then(|s| s.to_str()) != Some("json") {
                continue;
            }

            // Extract hash from filename (64 hex chars)
            let filename = match path.file_stem().and_then(|s| s.to_str()) {
                Some(f) => f,
                None => continue,
            };

            if filename.len() != 64 {
                continue;
            }

            let hash = match hex_to_bytes(filename) {
                Some(h) => h,
                None => continue,
            };

            // Read and deserialize the entry
            let content = match fs::read_to_string(&path) {
                Ok(c) => c,
                Err(_) => continue,
            };

            let entry: CacheEntry = match serde_json::from_str(&content) {
                Ok(e) => e,
                Err(_) => continue,
            };

            self.entries.insert(hash, entry);
        }

        tracing::info!("Loaded {} cache entries", self.entries.len());
    }

    /// Compute cache key for a function.
    ///
    /// The key is a SHA-256 hash of:
    /// - Function name
    /// - All requires specs
    /// - All ensures specs
    /// - All invariants
    /// - MIR debug representation (via Debug formatting)
    ///
    /// This is conservative: any change to the function body or contracts invalidates the cache.
    pub fn compute_key(
        func_name: &str,
        contracts: &rust_fv_analysis::ir::Contracts,
        ir_debug: &str,
    ) -> [u8; 32] {
        let mut hasher = Sha256::new();

        // Hash function name
        hasher.update(func_name.as_bytes());

        // Hash contracts
        for req in &contracts.requires {
            hasher.update(b"requires:");
            hasher.update(req.raw.as_bytes());
        }
        for ens in &contracts.ensures {
            hasher.update(b"ensures:");
            hasher.update(ens.raw.as_bytes());
        }
        for inv in &contracts.invariants {
            hasher.update(b"invariant:");
            hasher.update(inv.raw.as_bytes());
        }
        if contracts.is_pure {
            hasher.update(b"pure");
        }

        // Hash IR representation (conservative)
        hasher.update(ir_debug.as_bytes());

        let result = hasher.finalize();
        let mut key = [0u8; 32];
        key.copy_from_slice(&result);
        key
    }

    /// Look up a cache entry by key.
    pub fn get(&self, key: &[u8; 32]) -> Option<&CacheEntry> {
        self.entries.get(key)
    }

    /// Insert a cache entry both in memory and on disk.
    ///
    /// Persists the entry to `{cache_dir}/{hex_hash}.json`.
    pub fn insert(&mut self, key: [u8; 32], entry: CacheEntry) {
        // Write to disk
        let filename = bytes_to_hex(&key);
        let path = self.cache_dir.join(format!("{}.json", filename));

        if let Ok(json) = serde_json::to_string_pretty(&entry) {
            let _ = fs::write(&path, json);
        }

        // Insert in memory
        self.entries.insert(key, entry);
    }

    /// Clear all cache entries (for --fresh flag).
    ///
    /// Removes all in-memory entries and deletes all cache files.
    pub fn clear(&mut self) {
        self.entries.clear();

        if !self.cache_dir.exists() {
            return;
        }

        let read_dir = match fs::read_dir(&self.cache_dir) {
            Ok(rd) => rd,
            Err(_) => return,
        };

        for entry in read_dir.flatten() {
            let path = entry.path();
            if path.extension().and_then(|s| s.to_str()) == Some("json") {
                let _ = fs::remove_file(path);
            }
        }

        tracing::info!("Cache cleared");
    }
}

/// Convert bytes to hex string.
fn bytes_to_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{:02x}", b)).collect()
}

/// Convert hex string to bytes.
fn hex_to_bytes(hex: &str) -> Option<[u8; 32]> {
    if hex.len() != 64 {
        return None;
    }

    let mut bytes = [0u8; 32];
    for i in 0..32 {
        let byte = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16).ok()?;
        bytes[i] = byte;
    }
    Some(bytes)
}
