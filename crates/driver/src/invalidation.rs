//! Cache invalidation decision logic for incremental verification.
//!
//! Determines whether a function needs re-verification based on:
//! - MIR hash changes (function body modifications)
//! - Contract hash changes (spec modifications)
//! - Transitive contract dependencies (callee contract changes)
//! - Cache age (30-day TTL)
//! - Fresh flag (force re-verification)

use std::collections::HashSet;

#[cfg(test)]
use crate::cache::CacheEntry;
use crate::cache::VcCache;

/// Reason why a function needs re-verification.
#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(dead_code)] // Used in future phases
pub enum InvalidationReason {
    /// Function body (MIR) changed
    MirChanged,
    /// Function's own contract changed
    ContractChanged { dependency: String },
    /// Forced re-verification via --fresh flag
    Fresh,
    /// No cache entry exists
    CacheMiss,
    /// Cache entry expired (older than 30 days)
    Expired,
}

/// Decision whether a function should be verified.
#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(dead_code)] // Used in future phases
pub struct InvalidationDecision {
    /// True if the function should be verified
    pub should_verify: bool,
    /// Reason for verification (None if cached)
    pub reason: Option<InvalidationReason>,
}

impl InvalidationDecision {
    /// Create a decision to verify with a reason.
    pub fn verify(reason: InvalidationReason) -> Self {
        Self {
            should_verify: true,
            reason: Some(reason),
        }
    }

    /// Create a decision to skip verification (cache hit).
    pub fn skip() -> Self {
        Self {
            should_verify: false,
            reason: None,
        }
    }
}

/// Decide whether a function needs verification based on cache state.
///
/// # Arguments
/// * `cache` - The verification cache
/// * `func_name` - Name of the function being checked
/// * `mir_hash` - Current MIR hash of the function
/// * `contract_hash` - Current contract hash of the function
/// * `fresh` - If true, force re-verification regardless of cache
/// * `changed_contracts` - Set of function names whose contracts have changed
/// * `dependencies` - Direct callees of this function
///
/// # Returns
/// A decision indicating whether to verify and why.
#[allow(dead_code)] // Used in future phases
pub fn decide_verification(
    cache: &VcCache,
    func_name: &str,
    mir_hash: [u8; 32],
    contract_hash: [u8; 32],
    fresh: bool,
    changed_contracts: &HashSet<String>,
    dependencies: &[String],
) -> InvalidationDecision {
    // Check fresh flag first
    if fresh {
        return InvalidationDecision::verify(InvalidationReason::Fresh);
    }

    // Compute cache key (using the deprecated combined hash for now)
    // TODO: Switch to separate mir_hash/contract_hash lookup once cache format is updated
    let contracts = rust_fv_analysis::ir::Contracts::default();
    #[allow(deprecated)]
    let key = VcCache::compute_key(func_name, &contracts, "");

    // Check if cache entry exists
    let entry = match cache.get(&key) {
        Some(e) => e,
        None => return InvalidationDecision::verify(InvalidationReason::CacheMiss),
    };

    // Check if expired (30 days)
    let now = chrono::Utc::now().timestamp();
    let max_age_seconds = 30 * 24 * 60 * 60;
    if now - entry.timestamp > max_age_seconds {
        return InvalidationDecision::verify(InvalidationReason::Expired);
    }

    // Check MIR hash
    if entry.mir_hash != mir_hash {
        return InvalidationDecision::verify(InvalidationReason::MirChanged);
    }

    // Check contract hash
    if entry.contract_hash != contract_hash {
        return InvalidationDecision::verify(InvalidationReason::ContractChanged {
            dependency: func_name.to_string(),
        });
    }

    // Check if any dependency has changed contract
    for dep in dependencies {
        if changed_contracts.contains(dep) {
            return InvalidationDecision::verify(InvalidationReason::ContractChanged {
                dependency: dep.clone(),
            });
        }
    }

    // Cache hit - no verification needed
    InvalidationDecision::skip()
}

#[cfg(test)]
#[allow(deprecated)] // Tests use deprecated compute_key temporarily
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn temp_cache_dir(test_name: &str) -> PathBuf {
        let mut dir = std::env::temp_dir();
        dir.push(format!(
            "rust-fv-invalidation-test-{}-{}",
            test_name,
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        dir
    }

    #[test]
    fn test_decision_verify() {
        let decision = InvalidationDecision::verify(InvalidationReason::Fresh);
        assert!(decision.should_verify);
        assert_eq!(decision.reason, Some(InvalidationReason::Fresh));
    }

    #[test]
    fn test_decision_skip() {
        let decision = InvalidationDecision::skip();
        assert!(!decision.should_verify);
        assert_eq!(decision.reason, None);
    }

    #[test]
    fn test_fresh_flag_forces_verification() {
        let dir = temp_cache_dir("fresh_flag");
        let cache = VcCache::new(dir.clone());

        let decision = decide_verification(
            &cache,
            "test_func",
            [1u8; 32],
            [2u8; 32],
            true, // fresh = true
            &HashSet::new(),
            &[],
        );

        assert!(decision.should_verify);
        assert_eq!(decision.reason, Some(InvalidationReason::Fresh));

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_cache_miss() {
        let dir = temp_cache_dir("cache_miss");
        let cache = VcCache::new(dir.clone());

        let decision = decide_verification(
            &cache,
            "test_func",
            [1u8; 32],
            [2u8; 32],
            false,
            &HashSet::new(),
            &[],
        );

        assert!(decision.should_verify);
        assert_eq!(decision.reason, Some(InvalidationReason::CacheMiss));

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_mir_changed() {
        let dir = temp_cache_dir("mir_changed");
        let mut cache = VcCache::new(dir.clone());

        let old_mir_hash = [1u8; 32];
        let new_mir_hash = [2u8; 32];
        let contract_hash = [3u8; 32];

        // Insert entry with old MIR hash
        let contracts = rust_fv_analysis::ir::Contracts::default();
        let key = VcCache::compute_key("test_func", &contracts, "");
        cache.insert(
            key,
            CacheEntry {
                verified: true,
                vc_count: 1,
                verified_count: 1,
                message: None,
                mir_hash: old_mir_hash,
                contract_hash,
                timestamp: chrono::Utc::now().timestamp(),
                dependencies: vec![],
            },
        );

        // Check with different MIR hash
        let decision = decide_verification(
            &cache,
            "test_func",
            new_mir_hash,
            contract_hash,
            false,
            &HashSet::new(),
            &[],
        );

        assert!(decision.should_verify);
        assert_eq!(decision.reason, Some(InvalidationReason::MirChanged));

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_contract_changed_self() {
        let dir = temp_cache_dir("contract_changed_self");
        let mut cache = VcCache::new(dir.clone());

        let mir_hash = [1u8; 32];
        let old_contract_hash = [2u8; 32];
        let new_contract_hash = [3u8; 32];

        // Insert entry with old contract hash
        let contracts = rust_fv_analysis::ir::Contracts::default();
        let key = VcCache::compute_key("test_func", &contracts, "");
        cache.insert(
            key,
            CacheEntry {
                verified: true,
                vc_count: 1,
                verified_count: 1,
                message: None,
                mir_hash,
                contract_hash: old_contract_hash,
                timestamp: chrono::Utc::now().timestamp(),
                dependencies: vec![],
            },
        );

        // Check with different contract hash
        let decision = decide_verification(
            &cache,
            "test_func",
            mir_hash,
            new_contract_hash,
            false,
            &HashSet::new(),
            &[],
        );

        assert!(decision.should_verify);
        assert_eq!(
            decision.reason,
            Some(InvalidationReason::ContractChanged {
                dependency: "test_func".to_string()
            })
        );

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_contract_changed_dependency() {
        let dir = temp_cache_dir("contract_changed_dep");
        let mut cache = VcCache::new(dir.clone());

        let mir_hash = [1u8; 32];
        let contract_hash = [2u8; 32];

        // Insert entry
        let contracts = rust_fv_analysis::ir::Contracts::default();
        let key = VcCache::compute_key("test_func", &contracts, "");
        cache.insert(
            key,
            CacheEntry {
                verified: true,
                vc_count: 1,
                verified_count: 1,
                message: None,
                mir_hash,
                contract_hash,
                timestamp: chrono::Utc::now().timestamp(),
                dependencies: vec!["helper".to_string()],
            },
        );

        // Mark dependency as having changed contract
        let mut changed_contracts = HashSet::new();
        changed_contracts.insert("helper".to_string());

        let decision = decide_verification(
            &cache,
            "test_func",
            mir_hash,
            contract_hash,
            false,
            &changed_contracts,
            &["helper".to_string()],
        );

        assert!(decision.should_verify);
        assert_eq!(
            decision.reason,
            Some(InvalidationReason::ContractChanged {
                dependency: "helper".to_string()
            })
        );

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_expired_entry() {
        let dir = temp_cache_dir("expired");
        let mut cache = VcCache::new(dir.clone());

        let mir_hash = [1u8; 32];
        let contract_hash = [2u8; 32];

        // Insert entry with old timestamp (31 days ago)
        let old_timestamp = chrono::Utc::now().timestamp() - (31 * 24 * 60 * 60);
        let contracts = rust_fv_analysis::ir::Contracts::default();
        let key = VcCache::compute_key("test_func", &contracts, "");
        cache.insert(
            key,
            CacheEntry {
                verified: true,
                vc_count: 1,
                verified_count: 1,
                message: None,
                mir_hash,
                contract_hash,
                timestamp: old_timestamp,
                dependencies: vec![],
            },
        );

        let decision = decide_verification(
            &cache,
            "test_func",
            mir_hash,
            contract_hash,
            false,
            &HashSet::new(),
            &[],
        );

        assert!(decision.should_verify);
        assert_eq!(decision.reason, Some(InvalidationReason::Expired));

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_cache_hit() {
        let dir = temp_cache_dir("cache_hit");
        let mut cache = VcCache::new(dir.clone());

        let mir_hash = [1u8; 32];
        let contract_hash = [2u8; 32];

        // Insert fresh entry
        let contracts = rust_fv_analysis::ir::Contracts::default();
        let key = VcCache::compute_key("test_func", &contracts, "");
        cache.insert(
            key,
            CacheEntry {
                verified: true,
                vc_count: 1,
                verified_count: 1,
                message: None,
                mir_hash,
                contract_hash,
                timestamp: chrono::Utc::now().timestamp(),
                dependencies: vec![],
            },
        );

        // Check with same hashes
        let decision = decide_verification(
            &cache,
            "test_func",
            mir_hash,
            contract_hash,
            false,
            &HashSet::new(),
            &[],
        );

        assert!(!decision.should_verify);
        assert_eq!(decision.reason, None);

        let _ = std::fs::remove_dir_all(&dir);
    }
}
