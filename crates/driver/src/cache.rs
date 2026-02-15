//! VC caching with SHA-256 hash-based invalidation.
//!
//! Provides per-function caching of verification results to skip re-verification
//! when source code hasn't changed. Cache keys are SHA-256 hashes of:
//! - Function name
//! - All contracts (requires/ensures/invariants)
//! - MIR debug representation (conservative: any MIR change invalidates)
//!
//! Cache is stored in `target/verify-cache/` as JSON files, one per function.
//! Cleaned by `cargo clean` or `cargo verify clean`.

use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::fs;
use std::path::PathBuf;

/// In-memory cache of verification results.
pub struct VcCache {
    /// Cached entries, keyed by SHA-256 hash
    entries: FxHashMap<[u8; 32], CacheEntry>,
    /// Directory for cache files (target/verify-cache/)
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
    /// Hash of function body only (MIR representation)
    #[serde(default)]
    pub mir_hash: [u8; 32],
    /// Hash of contracts only (requires/ensures/invariants/pure/decreases)
    #[serde(default)]
    pub contract_hash: [u8; 32],
    /// Unix timestamp (UTC) when entry was created
    #[serde(default)]
    pub timestamp: i64,
    /// Function names this function calls (direct dependencies)
    #[serde(default)]
    pub dependencies: Vec<String>,
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
    /// Entries older than 30 days are evicted (deleted from disk).
    pub fn load(&mut self) {
        if !self.cache_dir.exists() {
            return;
        }

        let read_dir = match fs::read_dir(&self.cache_dir) {
            Ok(rd) => rd,
            Err(_) => return,
        };

        let now = chrono::Utc::now().timestamp();
        let max_age_seconds = 30 * 24 * 60 * 60; // 30 days
        let mut evicted_count = 0;

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

            // Check age and evict if expired
            // Note: timestamp == 0 means old cache format (before timestamps were added)
            // or explicitly set to 0. Treat as "unknown age" and keep it.
            if entry.timestamp != 0 && now - entry.timestamp > max_age_seconds {
                let _ = fs::remove_file(&path);
                evicted_count += 1;
                continue;
            }

            self.entries.insert(hash, entry);
        }

        if evicted_count > 0 {
            tracing::info!("Evicted {} expired cache entries", evicted_count);
        }
        tracing::info!("Loaded {} cache entries", self.entries.len());
    }

    /// Compute hash of function body only (MIR representation).
    ///
    /// Hash includes:
    /// - Function name
    /// - MIR debug representation (via Debug formatting)
    #[allow(dead_code)] // Used in future phases
    pub fn compute_mir_hash(func_name: &str, ir_debug: &str) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(func_name.as_bytes());
        hasher.update(ir_debug.as_bytes());
        let result = hasher.finalize();
        let mut hash = [0u8; 32];
        hash.copy_from_slice(&result);
        hash
    }

    /// Compute hash of contracts only.
    ///
    /// Hash includes:
    /// - Function name
    /// - All requires specs
    /// - All ensures specs
    /// - All invariants
    /// - Pure flag
    /// - Decreases clause
    #[allow(dead_code)] // Used in future phases
    pub fn compute_contract_hash(
        func_name: &str,
        contracts: &rust_fv_analysis::ir::Contracts,
    ) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(func_name.as_bytes());

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
        if let Some(ref dec) = contracts.decreases {
            hasher.update(b"decreases:");
            hasher.update(dec.raw.as_bytes());
        }

        let result = hasher.finalize();
        let mut hash = [0u8; 32];
        hash.copy_from_slice(&result);
        hash
    }

    /// Compute cache key for a function (deprecated).
    ///
    /// The key is a SHA-256 hash of:
    /// - Function name
    /// - All requires specs
    /// - All ensures specs
    /// - All invariants
    /// - MIR debug representation (via Debug formatting)
    ///
    /// This is conservative: any change to the function body or contracts invalidates the cache.
    #[deprecated(note = "Use compute_mir_hash + compute_contract_hash instead")]
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
    /// Automatically sets the timestamp to the current time if not already set.
    pub fn insert(&mut self, key: [u8; 32], mut entry: CacheEntry) {
        // Set timestamp if not already set (for new entries)
        if entry.timestamp == 0 {
            entry.timestamp = chrono::Utc::now().timestamp();
        }

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
    #[allow(dead_code)] // Deprecated: --fresh now bypasses cache without clearing
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

#[cfg(test)]
#[allow(deprecated)] // Tests use deprecated compute_key for backward compatibility testing
mod tests {
    use super::*;
    use std::path::PathBuf;

    /// Create a unique temporary directory for cache tests.
    fn temp_cache_dir(test_name: &str) -> PathBuf {
        let mut dir = std::env::temp_dir();
        dir.push(format!(
            "rust-fv-cache-test-{}-{}",
            test_name,
            std::process::id()
        ));
        // Clean up from any previous run
        let _ = fs::remove_dir_all(&dir);
        dir
    }

    // --- bytes_to_hex tests ---

    #[test]
    fn test_bytes_to_hex_empty() {
        assert_eq!(bytes_to_hex(&[]), "");
    }

    #[test]
    fn test_bytes_to_hex_single_byte() {
        assert_eq!(bytes_to_hex(&[0x00]), "00");
        assert_eq!(bytes_to_hex(&[0xff]), "ff");
        assert_eq!(bytes_to_hex(&[0x0a]), "0a");
        assert_eq!(bytes_to_hex(&[0xa0]), "a0");
    }

    #[test]
    fn test_bytes_to_hex_multiple_bytes() {
        assert_eq!(bytes_to_hex(&[0xde, 0xad, 0xbe, 0xef]), "deadbeef");
    }

    #[test]
    fn test_bytes_to_hex_32_bytes() {
        let bytes = [0u8; 32];
        let hex = bytes_to_hex(&bytes);
        assert_eq!(hex.len(), 64);
        assert_eq!(hex, "0".repeat(64));
    }

    #[test]
    fn test_bytes_to_hex_all_values() {
        // Verify lower-case hex output
        let bytes = [0xab, 0xcd, 0xef, 0x01, 0x23, 0x45, 0x67, 0x89];
        assert_eq!(bytes_to_hex(&bytes), "abcdef0123456789");
    }

    // --- hex_to_bytes tests ---

    #[test]
    fn test_hex_to_bytes_valid() {
        let hex = "0".repeat(64);
        let result = hex_to_bytes(&hex);
        assert_eq!(result, Some([0u8; 32]));
    }

    #[test]
    fn test_hex_to_bytes_nonzero() {
        let mut hex = String::new();
        for i in 0u8..32 {
            hex.push_str(&format!("{:02x}", i));
        }
        let result = hex_to_bytes(&hex).unwrap();
        for i in 0u8..32 {
            assert_eq!(result[i as usize], i);
        }
    }

    #[test]
    fn test_hex_to_bytes_wrong_length_short() {
        assert_eq!(hex_to_bytes("abcdef"), None);
    }

    #[test]
    fn test_hex_to_bytes_wrong_length_long() {
        let hex = "0".repeat(66);
        assert_eq!(hex_to_bytes(&hex), None);
    }

    #[test]
    fn test_hex_to_bytes_empty() {
        assert_eq!(hex_to_bytes(""), None);
    }

    #[test]
    fn test_hex_to_bytes_invalid_chars() {
        // 64 chars but with invalid hex character 'g'
        let mut hex = "g".repeat(64);
        assert_eq!(hex_to_bytes(&hex), None);

        // Mix of valid and invalid
        hex = "0".repeat(62) + "zz";
        assert_eq!(hex_to_bytes(&hex), None);
    }

    #[test]
    fn test_hex_bytes_roundtrip() {
        let original = [
            0xde, 0xad, 0xbe, 0xef, 0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0x00, 0x11,
            0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff,
            0x10, 0x20, 0x30, 0x40,
        ];
        let hex = bytes_to_hex(&original);
        let roundtripped = hex_to_bytes(&hex).unwrap();
        assert_eq!(original, roundtripped);
    }

    // --- VcCache::new tests ---

    #[test]
    fn test_cache_new_creates_directory() {
        let dir = temp_cache_dir("new_creates_dir");
        assert!(!dir.exists());

        let _cache = VcCache::new(dir.clone());
        assert!(dir.exists());

        // Cleanup
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_cache_new_existing_directory() {
        let dir = temp_cache_dir("new_existing_dir");
        fs::create_dir_all(&dir).unwrap();

        let _cache = VcCache::new(dir.clone());
        assert!(dir.exists());

        // Cleanup
        let _ = fs::remove_dir_all(&dir);
    }

    // --- VcCache::get / insert tests ---

    #[test]
    fn test_cache_get_missing() {
        let dir = temp_cache_dir("get_missing");
        let cache = VcCache::new(dir.clone());

        let key = [0u8; 32];
        assert!(cache.get(&key).is_none());

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_cache_insert_and_get() {
        let dir = temp_cache_dir("insert_get");
        let mut cache = VcCache::new(dir.clone());

        let key = [42u8; 32];
        let entry = CacheEntry {
            verified: true,
            vc_count: 3,
            verified_count: 3,
            message: None,
            mir_hash: [1u8; 32],
            contract_hash: [2u8; 32],
            timestamp: 0,
            dependencies: vec![],
        };

        cache.insert(key, entry);

        let retrieved = cache.get(&key).unwrap();
        assert!(retrieved.verified);
        assert_eq!(retrieved.vc_count, 3);
        assert_eq!(retrieved.verified_count, 3);
        assert!(retrieved.message.is_none());

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_cache_insert_persists_to_disk() {
        let dir = temp_cache_dir("insert_persists");
        let mut cache = VcCache::new(dir.clone());

        let key = [0xab; 32];
        let entry = CacheEntry {
            verified: false,
            vc_count: 5,
            verified_count: 2,
            message: Some("postcondition failed".to_string()),
            mir_hash: [1u8; 32],
            contract_hash: [2u8; 32],
            timestamp: 0,
            dependencies: vec![],
        };

        cache.insert(key, entry);

        // Verify the file exists on disk
        let filename = bytes_to_hex(&key);
        let path = dir.join(format!("{}.json", filename));
        assert!(path.exists());

        // Verify it's valid JSON
        let content = fs::read_to_string(&path).unwrap();
        let deserialized: CacheEntry = serde_json::from_str(&content).unwrap();
        assert!(!deserialized.verified);
        assert_eq!(deserialized.vc_count, 5);
        assert_eq!(deserialized.verified_count, 2);
        assert_eq!(
            deserialized.message.as_deref(),
            Some("postcondition failed")
        );

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_cache_insert_overwrite() {
        let dir = temp_cache_dir("insert_overwrite");
        let mut cache = VcCache::new(dir.clone());

        let key = [1u8; 32];
        let entry1 = CacheEntry {
            verified: false,
            vc_count: 1,
            verified_count: 0,
            message: Some("failed".to_string()),
            mir_hash: [1u8; 32],
            contract_hash: [2u8; 32],
            timestamp: 0,
            dependencies: vec![],
        };
        cache.insert(key, entry1);

        let entry2 = CacheEntry {
            verified: true,
            vc_count: 1,
            verified_count: 1,
            message: None,
            mir_hash: [1u8; 32],
            contract_hash: [2u8; 32],
            timestamp: 0,
            dependencies: vec![],
        };
        cache.insert(key, entry2);

        let retrieved = cache.get(&key).unwrap();
        assert!(retrieved.verified);
        assert_eq!(retrieved.verified_count, 1);

        let _ = fs::remove_dir_all(&dir);
    }

    // --- VcCache::load tests ---

    #[test]
    fn test_cache_load_from_disk() {
        let dir = temp_cache_dir("load_from_disk");

        // Write some cache entries to disk manually, then load
        {
            let mut cache = VcCache::new(dir.clone());
            cache.insert(
                [1u8; 32],
                CacheEntry {
                    verified: true,
                    vc_count: 2,
                    verified_count: 2,
                    message: None,
                    mir_hash: [1u8; 32],
                    contract_hash: [2u8; 32],
                    timestamp: 0,
                    dependencies: vec![],
                },
            );
            cache.insert(
                [2u8; 32],
                CacheEntry {
                    verified: false,
                    vc_count: 3,
                    verified_count: 1,
                    message: Some("overflow".to_string()),
                    mir_hash: [3u8; 32],
                    contract_hash: [4u8; 32],
                    timestamp: 0,
                    dependencies: vec![],
                },
            );
        }

        // Create a fresh cache and load from disk
        let mut cache = VcCache::new(dir.clone());
        assert!(cache.get(&[1u8; 32]).is_none()); // Not yet loaded
        cache.load();
        assert!(cache.get(&[1u8; 32]).is_some());
        assert!(cache.get(&[2u8; 32]).is_some());

        let entry1 = cache.get(&[1u8; 32]).unwrap();
        assert!(entry1.verified);
        assert_eq!(entry1.vc_count, 2);

        let entry2 = cache.get(&[2u8; 32]).unwrap();
        assert!(!entry2.verified);
        assert_eq!(entry2.message.as_deref(), Some("overflow"));

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_cache_load_empty_directory() {
        let dir = temp_cache_dir("load_empty");
        let mut cache = VcCache::new(dir.clone());
        cache.load(); // Should not panic

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_cache_load_nonexistent_directory() {
        let dir = temp_cache_dir("load_nonexistent");
        let _ = fs::remove_dir_all(&dir); // Ensure it doesn't exist

        // Create cache without creating dir
        let mut cache = VcCache {
            entries: FxHashMap::default(),
            cache_dir: dir.clone(),
        };
        cache.load(); // Should not panic, just return early

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_cache_load_skips_malformed_json() {
        let dir = temp_cache_dir("load_malformed");
        fs::create_dir_all(&dir).unwrap();

        // Write a malformed JSON file with a valid 64-char hex filename
        let filename = "a".repeat(64);
        fs::write(dir.join(format!("{}.json", filename)), "not valid json").unwrap();

        // Write a valid entry with recent timestamp
        let valid_key = [0xbb; 32];
        let valid_filename = bytes_to_hex(&valid_key);
        let valid_entry = CacheEntry {
            verified: true,
            vc_count: 1,
            verified_count: 1,
            message: None,
            mir_hash: [1u8; 32],
            contract_hash: [2u8; 32],
            timestamp: chrono::Utc::now().timestamp(),
            dependencies: vec![],
        };
        fs::write(
            dir.join(format!("{}.json", valid_filename)),
            serde_json::to_string(&valid_entry).unwrap(),
        )
        .unwrap();

        let mut cache = VcCache::new(dir.clone());
        cache.load();

        // The valid entry should be loaded
        assert!(cache.get(&valid_key).is_some());

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_cache_load_skips_non_json_files() {
        let dir = temp_cache_dir("load_non_json");
        fs::create_dir_all(&dir).unwrap();

        // Write a non-JSON file
        fs::write(dir.join("readme.txt"), "hello").unwrap();

        let mut cache = VcCache::new(dir.clone());
        cache.load(); // Should not panic

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_cache_load_skips_wrong_filename_length() {
        let dir = temp_cache_dir("load_wrong_len");
        fs::create_dir_all(&dir).unwrap();

        // Write a JSON file with a filename that's not 64 hex chars
        let valid_entry = CacheEntry {
            verified: true,
            vc_count: 1,
            verified_count: 1,
            message: None,
            mir_hash: [1u8; 32],
            contract_hash: [2u8; 32],
            timestamp: 0,
            dependencies: vec![],
        };
        fs::write(
            dir.join("short.json"),
            serde_json::to_string(&valid_entry).unwrap(),
        )
        .unwrap();

        let mut cache = VcCache::new(dir.clone());
        cache.load();
        // No entries should be loaded (filename too short)
        assert_eq!(cache.entries.len(), 0);

        let _ = fs::remove_dir_all(&dir);
    }

    // --- VcCache::clear tests ---

    #[test]
    fn test_cache_clear_removes_entries() {
        let dir = temp_cache_dir("clear_removes");
        let mut cache = VcCache::new(dir.clone());

        cache.insert(
            [1u8; 32],
            CacheEntry {
                verified: true,
                vc_count: 1,
                verified_count: 1,
                message: None,
                mir_hash: [1u8; 32],
                contract_hash: [2u8; 32],
                timestamp: 0,
                dependencies: vec![],
            },
        );
        cache.insert(
            [2u8; 32],
            CacheEntry {
                verified: true,
                vc_count: 2,
                verified_count: 2,
                message: None,
                mir_hash: [3u8; 32],
                contract_hash: [4u8; 32],
                timestamp: 0,
                dependencies: vec![],
            },
        );

        assert!(cache.get(&[1u8; 32]).is_some());
        assert!(cache.get(&[2u8; 32]).is_some());

        cache.clear();

        assert!(cache.get(&[1u8; 32]).is_none());
        assert!(cache.get(&[2u8; 32]).is_none());

        // Verify files are deleted too
        let json_count = fs::read_dir(&dir)
            .unwrap()
            .filter_map(|e| e.ok())
            .filter(|e| e.path().extension().and_then(|s| s.to_str()) == Some("json"))
            .count();
        assert_eq!(json_count, 0);

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_cache_clear_nonexistent_dir() {
        let dir = temp_cache_dir("clear_nonexistent");
        let _ = fs::remove_dir_all(&dir);

        let mut cache = VcCache {
            entries: FxHashMap::default(),
            cache_dir: dir.clone(),
        };
        cache.clear(); // Should not panic
    }

    #[test]
    fn test_cache_clear_preserves_non_json_files() {
        let dir = temp_cache_dir("clear_preserves");
        let mut cache = VcCache::new(dir.clone());

        // Add a non-JSON file
        fs::write(dir.join("readme.txt"), "keep me").unwrap();

        cache.insert(
            [1u8; 32],
            CacheEntry {
                verified: true,
                vc_count: 1,
                verified_count: 1,
                message: None,
                mir_hash: [1u8; 32],
                contract_hash: [2u8; 32],
                timestamp: 0,
                dependencies: vec![],
            },
        );

        cache.clear();

        // Non-JSON file should still be there
        assert!(dir.join("readme.txt").exists());
        // But JSON files should be gone
        let json_count = fs::read_dir(&dir)
            .unwrap()
            .filter_map(|e| e.ok())
            .filter(|e| e.path().extension().and_then(|s| s.to_str()) == Some("json"))
            .count();
        assert_eq!(json_count, 0);

        let _ = fs::remove_dir_all(&dir);
    }

    // --- VcCache::compute_key tests ---

    #[test]
    fn test_compute_key_deterministic() {
        let contracts = rust_fv_analysis::ir::Contracts {
            requires: vec![rust_fv_analysis::ir::SpecExpr {
                raw: "x > 0".to_string(),
            }],
            ensures: vec![rust_fv_analysis::ir::SpecExpr {
                raw: "result > 0".to_string(),
            }],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        };

        let key1 = VcCache::compute_key("my_func", &contracts, "ir_debug_repr");
        let key2 = VcCache::compute_key("my_func", &contracts, "ir_debug_repr");
        assert_eq!(key1, key2);
    }

    #[test]
    fn test_compute_key_different_names() {
        let contracts = rust_fv_analysis::ir::Contracts {
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        };

        let key1 = VcCache::compute_key("func_a", &contracts, "same_ir");
        let key2 = VcCache::compute_key("func_b", &contracts, "same_ir");
        assert_ne!(key1, key2);
    }

    #[test]
    fn test_compute_key_different_contracts() {
        let contracts1 = rust_fv_analysis::ir::Contracts {
            requires: vec![rust_fv_analysis::ir::SpecExpr {
                raw: "x > 0".to_string(),
            }],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        };

        let contracts2 = rust_fv_analysis::ir::Contracts {
            requires: vec![rust_fv_analysis::ir::SpecExpr {
                raw: "x > 1".to_string(),
            }],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        };

        let key1 = VcCache::compute_key("func", &contracts1, "same_ir");
        let key2 = VcCache::compute_key("func", &contracts2, "same_ir");
        assert_ne!(key1, key2);
    }

    #[test]
    fn test_compute_key_different_ir() {
        let contracts = rust_fv_analysis::ir::Contracts {
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        };

        let key1 = VcCache::compute_key("func", &contracts, "ir_v1");
        let key2 = VcCache::compute_key("func", &contracts, "ir_v2");
        assert_ne!(key1, key2);
    }

    #[test]
    fn test_compute_key_pure_flag_matters() {
        let contracts_pure = rust_fv_analysis::ir::Contracts {
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            is_pure: true,
            decreases: None,
        };

        let contracts_not_pure = rust_fv_analysis::ir::Contracts {
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        };

        let key1 = VcCache::compute_key("func", &contracts_pure, "same_ir");
        let key2 = VcCache::compute_key("func", &contracts_not_pure, "same_ir");
        assert_ne!(key1, key2);
    }

    #[test]
    fn test_compute_key_ensures_and_invariants() {
        let contracts_with_ensures = rust_fv_analysis::ir::Contracts {
            requires: vec![],
            ensures: vec![rust_fv_analysis::ir::SpecExpr {
                raw: "result >= 0".to_string(),
            }],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        };

        let contracts_with_invariant = rust_fv_analysis::ir::Contracts {
            requires: vec![],
            ensures: vec![],
            invariants: vec![rust_fv_analysis::ir::SpecExpr {
                raw: "i < n".to_string(),
            }],
            is_pure: false,
            decreases: None,
        };

        let key1 = VcCache::compute_key("func", &contracts_with_ensures, "same_ir");
        let key2 = VcCache::compute_key("func", &contracts_with_invariant, "same_ir");
        assert_ne!(key1, key2);
    }

    #[test]
    fn test_compute_key_is_32_bytes() {
        let contracts = rust_fv_analysis::ir::Contracts {
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        };

        let key = VcCache::compute_key("func", &contracts, "ir");
        assert_eq!(key.len(), 32); // SHA-256 = 32 bytes
    }

    // ====== Dual-hash tests ======

    #[test]
    fn test_compute_mir_hash_deterministic() {
        let hash1 = VcCache::compute_mir_hash("my_func", "ir_debug_repr");
        let hash2 = VcCache::compute_mir_hash("my_func", "ir_debug_repr");
        assert_eq!(hash1, hash2);
    }

    #[test]
    fn test_compute_mir_hash_changes_with_body() {
        let hash1 = VcCache::compute_mir_hash("my_func", "ir_v1");
        let hash2 = VcCache::compute_mir_hash("my_func", "ir_v2");
        assert_ne!(hash1, hash2);
    }

    #[test]
    fn test_compute_mir_hash_changes_with_name() {
        let hash1 = VcCache::compute_mir_hash("func_a", "same_ir");
        let hash2 = VcCache::compute_mir_hash("func_b", "same_ir");
        assert_ne!(hash1, hash2);
    }

    #[test]
    fn test_compute_contract_hash_deterministic() {
        let contracts = rust_fv_analysis::ir::Contracts {
            requires: vec![rust_fv_analysis::ir::SpecExpr {
                raw: "x > 0".to_string(),
            }],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        };

        let hash1 = VcCache::compute_contract_hash("my_func", &contracts);
        let hash2 = VcCache::compute_contract_hash("my_func", &contracts);
        assert_eq!(hash1, hash2);
    }

    #[test]
    fn test_compute_contract_hash_changes_with_contracts() {
        let contracts1 = rust_fv_analysis::ir::Contracts {
            requires: vec![rust_fv_analysis::ir::SpecExpr {
                raw: "x > 0".to_string(),
            }],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        };

        let contracts2 = rust_fv_analysis::ir::Contracts {
            requires: vec![rust_fv_analysis::ir::SpecExpr {
                raw: "x > 1".to_string(),
            }],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        };

        let hash1 = VcCache::compute_contract_hash("func", &contracts1);
        let hash2 = VcCache::compute_contract_hash("func", &contracts2);
        assert_ne!(hash1, hash2);
    }

    #[test]
    fn test_compute_contract_hash_pure_flag() {
        let contracts_pure = rust_fv_analysis::ir::Contracts {
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            is_pure: true,
            decreases: None,
        };

        let contracts_not_pure = rust_fv_analysis::ir::Contracts {
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        };

        let hash1 = VcCache::compute_contract_hash("func", &contracts_pure);
        let hash2 = VcCache::compute_contract_hash("func", &contracts_not_pure);
        assert_ne!(hash1, hash2);
    }

    #[test]
    fn test_compute_contract_hash_includes_decreases() {
        let contracts_with_dec = rust_fv_analysis::ir::Contracts {
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: Some(rust_fv_analysis::ir::SpecExpr {
                raw: "n".to_string(),
            }),
        };

        let contracts_without_dec = rust_fv_analysis::ir::Contracts {
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        };

        let hash1 = VcCache::compute_contract_hash("func", &contracts_with_dec);
        let hash2 = VcCache::compute_contract_hash("func", &contracts_without_dec);
        assert_ne!(hash1, hash2);
    }

    #[test]
    fn test_mir_hash_unchanged_when_contracts_change() {
        let contracts1 = rust_fv_analysis::ir::Contracts {
            requires: vec![rust_fv_analysis::ir::SpecExpr {
                raw: "x > 0".to_string(),
            }],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        };

        let contracts2 = rust_fv_analysis::ir::Contracts {
            requires: vec![rust_fv_analysis::ir::SpecExpr {
                raw: "x > 1".to_string(),
            }],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        };

        // MIR hash should be the same regardless of contracts
        let mir_hash1 = VcCache::compute_mir_hash("func", "same_ir");
        let mir_hash2 = VcCache::compute_mir_hash("func", "same_ir");
        assert_eq!(mir_hash1, mir_hash2);

        // But contract hash should differ
        let contract_hash1 = VcCache::compute_contract_hash("func", &contracts1);
        let contract_hash2 = VcCache::compute_contract_hash("func", &contracts2);
        assert_ne!(contract_hash1, contract_hash2);
    }

    #[test]
    fn test_contract_hash_unchanged_when_body_changes() {
        let contracts = rust_fv_analysis::ir::Contracts {
            requires: vec![rust_fv_analysis::ir::SpecExpr {
                raw: "x > 0".to_string(),
            }],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        };

        // Contract hash should be the same regardless of IR
        let contract_hash1 = VcCache::compute_contract_hash("func", &contracts);
        let contract_hash2 = VcCache::compute_contract_hash("func", &contracts);
        assert_eq!(contract_hash1, contract_hash2);

        // But MIR hash should differ
        let mir_hash1 = VcCache::compute_mir_hash("func", "ir_v1");
        let mir_hash2 = VcCache::compute_mir_hash("func", "ir_v2");
        assert_ne!(mir_hash1, mir_hash2);
    }

    // ====== Age-based eviction tests ======

    #[test]
    fn test_age_based_eviction_removes_old_entries() {
        let dir = temp_cache_dir("eviction_old");
        let mut cache = VcCache::new(dir.clone());

        // Insert an entry with old timestamp (31 days ago)
        let old_timestamp = chrono::Utc::now().timestamp() - (31 * 24 * 60 * 60);
        let key = [0xaa; 32];
        cache.insert(
            key,
            CacheEntry {
                verified: true,
                vc_count: 1,
                verified_count: 1,
                message: None,
                mir_hash: [1u8; 32],
                contract_hash: [2u8; 32],
                timestamp: old_timestamp,
                dependencies: vec![],
            },
        );

        // Verify file exists
        let filename = bytes_to_hex(&key);
        let path = dir.join(format!("{}.json", filename));
        assert!(path.exists());

        // Load cache - should evict the old entry
        let mut fresh_cache = VcCache::new(dir.clone());
        fresh_cache.load();

        // Entry should not be loaded
        assert!(fresh_cache.get(&key).is_none());

        // File should be deleted
        assert!(!path.exists());

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_age_based_eviction_keeps_recent_entries() {
        let dir = temp_cache_dir("eviction_recent");
        let mut cache = VcCache::new(dir.clone());

        // Insert an entry with recent timestamp (1 day ago)
        let recent_timestamp = chrono::Utc::now().timestamp() - (24 * 60 * 60); // 1 day ago
        let key = [0xbb; 32];
        cache.insert(
            key,
            CacheEntry {
                verified: true,
                vc_count: 1,
                verified_count: 1,
                message: None,
                mir_hash: [1u8; 32],
                contract_hash: [2u8; 32],
                timestamp: recent_timestamp,
                dependencies: vec![],
            },
        );

        // Load cache - should keep the recent entry
        let mut fresh_cache = VcCache::new(dir.clone());
        fresh_cache.load();

        // Entry should be loaded
        assert!(fresh_cache.get(&key).is_some());

        let _ = fs::remove_dir_all(&dir);
    }

    // ====== Backward compatibility tests ======

    #[test]
    fn test_backward_compatibility_old_cache_format() {
        let dir = temp_cache_dir("backward_compat");
        fs::create_dir_all(&dir).unwrap();

        // Manually create an old-format cache entry (without new fields)
        let old_entry_json = r#"{
            "verified": true,
            "vc_count": 3,
            "verified_count": 3,
            "message": null
        }"#;

        let key = [0xcc; 32];
        let filename = bytes_to_hex(&key);
        let path = dir.join(format!("{}.json", filename));
        fs::write(&path, old_entry_json).unwrap();

        // Load cache
        let mut cache = VcCache::new(dir.clone());
        cache.load();

        // Entry should be loaded with default values for new fields
        let entry = cache.get(&key).unwrap();
        assert!(entry.verified);
        assert_eq!(entry.vc_count, 3);
        assert_eq!(entry.verified_count, 3);
        assert_eq!(entry.mir_hash, [0u8; 32]); // default
        assert_eq!(entry.contract_hash, [0u8; 32]); // default
        assert_eq!(entry.timestamp, 0); // default
        assert_eq!(entry.dependencies, Vec::<String>::new()); // default

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_insert_sets_timestamp_automatically() {
        let dir = temp_cache_dir("auto_timestamp");
        let mut cache = VcCache::new(dir.clone());

        let before = chrono::Utc::now().timestamp();

        let key = [0xdd; 32];
        cache.insert(
            key,
            CacheEntry {
                verified: true,
                vc_count: 1,
                verified_count: 1,
                message: None,
                mir_hash: [1u8; 32],
                contract_hash: [2u8; 32],
                timestamp: 0, // Will be set automatically
                dependencies: vec![],
            },
        );

        let after = chrono::Utc::now().timestamp();

        let entry = cache.get(&key).unwrap();
        assert!(entry.timestamp >= before);
        assert!(entry.timestamp <= after);

        let _ = fs::remove_dir_all(&dir);
    }
}
