//! Parallel verification using Rayon.
//!
//! Implements per-function parallelism: multiple functions are verified simultaneously,
//! with each function's VCs processed sequentially. Uses subprocess-based solvers to
//! avoid Z3 global state conflicts.
//!
//! Verification follows topological order: leaf functions (callees) are verified
//! before their callers, ensuring function summaries are available when needed.

use rayon::prelude::*;
use std::sync::Arc;

use crate::cache::{CacheEntry, VcCache};
use crate::callbacks::VerificationResult;
use rust_fv_analysis::contract_db::ContractDatabase;
use rust_fv_analysis::ir::Function;
use rust_fv_analysis::vcgen::{VcKind, VcLocation};

/// A function verification task.
#[derive(Clone)]
pub struct VerificationTask {
    /// Function name
    pub name: String,
    /// IR function (owned, moved into thread)
    pub ir_func: Function,
    /// Shared contract database
    pub contract_db: Arc<ContractDatabase>,
    /// Cache key for this function (legacy combined hash)
    pub cache_key: [u8; 32],
    /// Hash of MIR body only
    pub mir_hash: [u8; 32],
    /// Hash of contracts only
    pub contract_hash: [u8; 32],
    /// Direct callees of this function
    pub dependencies: Vec<String>,
    /// Invalidation decision (whether to verify and why)
    pub invalidation_decision: crate::invalidation::InvalidationDecision,
}

/// Result of verifying a single function.
pub struct VerificationTaskResult {
    /// Function name
    #[allow(dead_code)] // Used for logging/debugging
    pub name: String,
    /// Per-VC verification results
    pub results: Vec<VerificationResult>,
    /// Cache key for this function
    pub cache_key: [u8; 32],
    /// Whether this result came from cache
    #[allow(dead_code)] // Used for logging/debugging
    pub from_cache: bool,
    /// Invalidation reason (Some if re-verified, None if cached)
    pub invalidation_reason: Option<crate::invalidation::InvalidationReason>,
    /// Verification duration in milliseconds (None if cached)
    pub duration_ms: Option<u64>,
}

/// Verify multiple functions in parallel using Rayon.
///
/// # Arguments
/// * `tasks` - Functions to verify
/// * `cache` - VC cache (will be updated with new results)
/// * `jobs` - Number of parallel threads (default: num_cpus/2)
/// * `fresh` - If true, bypass cache and re-verify everything
/// * `use_simplification` - If true, apply formula simplification before solver submission
///
/// # Returns
/// Verification results for all tasks
pub fn verify_functions_parallel(
    tasks: Vec<VerificationTask>,
    cache: &mut VcCache,
    jobs: usize,
    _fresh: bool, // Deprecated: now handled via InvalidationDecision
    use_simplification: bool,
) -> Vec<VerificationTaskResult> {
    // Build Rayon thread pool
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(jobs)
        .build()
        .unwrap();

    // Separate cached and uncached tasks based on InvalidationDecision
    let (cached_tasks, uncached_tasks): (Vec<_>, Vec<_>) = tasks
        .into_iter()
        .partition(|task| !task.invalidation_decision.should_verify);

    // Log cache statistics
    tracing::info!(
        "Cache: {} hits, {} misses",
        cached_tasks.len(),
        uncached_tasks.len()
    );

    // Build results from cache
    let mut all_results: Vec<VerificationTaskResult> = cached_tasks
        .into_iter()
        .map(|task| {
            let entry = cache.get(&task.cache_key).unwrap(); // Safe: we just checked
            tracing::debug!("Cache hit: {}", task.name);

            // Reconstruct VerificationResult from CacheEntry
            let results = if entry.verified {
                vec![VerificationResult {
                    function_name: task.name.clone(),
                    condition: format!("{} VCs verified", entry.vc_count),
                    verified: true,
                    counterexample: None,
                    vc_location: VcLocation {
                        function: task.name.clone(),
                        block: 0,
                        statement: 0,
                        source_file: None,
                        source_line: None,
                        contract_text: None,
                        vc_kind: VcKind::Postcondition,
                    },
                }]
            } else {
                vec![VerificationResult {
                    function_name: task.name.clone(),
                    condition: entry
                        .message
                        .clone()
                        .unwrap_or_else(|| "verification failed".to_string()),
                    verified: false,
                    counterexample: None,
                    vc_location: VcLocation {
                        function: task.name.clone(),
                        block: 0,
                        statement: 0,
                        source_file: None,
                        source_line: None,
                        contract_text: None,
                        vc_kind: VcKind::Postcondition,
                    },
                }]
            };

            VerificationTaskResult {
                name: task.name,
                results,
                cache_key: task.cache_key,
                from_cache: true,
                invalidation_reason: None,
                duration_ms: None,
            }
        })
        .collect();

    // Verify uncached tasks in parallel with timing
    let new_results: Vec<VerificationTaskResult> = pool.install(|| {
        uncached_tasks
            .par_iter()
            .map(|task| {
                let start = std::time::Instant::now();
                let mut result = verify_single(task, use_simplification);
                result.duration_ms = Some(start.elapsed().as_millis() as u64);
                result.invalidation_reason = task.invalidation_decision.reason.clone();
                result
            })
            .collect()
    });

    // Insert new results into cache with dual hashes and dependencies
    for (result, task) in new_results.iter().zip(uncached_tasks.iter()) {
        let all_verified = result.results.iter().all(|r| r.verified);
        let vc_count = result.results.len();
        let verified_count = result.results.iter().filter(|r| r.verified).count();
        let message = if !all_verified {
            result
                .results
                .iter()
                .find(|r| !r.verified)
                .map(|r| r.condition.clone())
        } else {
            None
        };

        cache.insert(
            result.cache_key,
            CacheEntry {
                verified: all_verified,
                vc_count,
                verified_count,
                message,
                mir_hash: task.mir_hash,
                contract_hash: task.contract_hash,
                timestamp: 0, // Will be set by insert()
                dependencies: task.dependencies.clone(),
            },
        );
    }

    all_results.extend(new_results);
    all_results
}

/// Verify a single function.
///
/// Creates a fresh Z3 solver instance for this thread (subprocess-based to avoid global state).
fn verify_single(task: &VerificationTask, use_simplification: bool) -> VerificationTaskResult {
    tracing::debug!("Verifying: {}", task.name);

    // Create a fresh solver instance for this thread
    let solver = match rust_fv_solver::Z3Solver::with_default_config() {
        Ok(s) => s,
        Err(e) => {
            // Solver creation failed -- return error result
            return VerificationTaskResult {
                name: task.name.clone(),
                results: vec![VerificationResult {
                    function_name: task.name.clone(),
                    condition: format!("solver error: {}", e),
                    verified: false,
                    counterexample: None,
                    vc_location: VcLocation {
                        function: task.name.clone(),
                        block: 0,
                        statement: 0,
                        source_file: None,
                        source_line: None,
                        contract_text: None,
                        vc_kind: VcKind::PanicFreedom,
                    },
                }],
                cache_key: task.cache_key,
                from_cache: false,
                invalidation_reason: None,
                duration_ms: None,
            };
        }
    };

    // Generate VCs with inter-procedural support
    let func_vcs = rust_fv_analysis::vcgen::generate_vcs(&task.ir_func, Some(&task.contract_db));

    let mut results = Vec::new();

    // Check each VC with Z3
    for vc in &func_vcs.conditions {
        // Apply simplification if enabled
        let script = if use_simplification {
            rust_fv_analysis::simplify::simplify_script(&vc.script)
        } else {
            vc.script.clone()
        };

        let script_text = script.to_string();

        match solver.check_sat_raw(&script_text) {
            Ok(rust_fv_solver::SolverResult::Unsat) => {
                results.push(VerificationResult {
                    function_name: task.name.clone(),
                    condition: vc.description.clone(),
                    verified: true,
                    counterexample: None,
                    vc_location: vc.location.clone(),
                });
            }
            Ok(rust_fv_solver::SolverResult::Sat(model)) => {
                let cx_str = model.as_ref().map(|m| {
                    m.assignments
                        .iter()
                        .map(|(k, v)| format!("{k} = {v}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                });

                results.push(VerificationResult {
                    function_name: task.name.clone(),
                    condition: vc.description.clone(),
                    verified: false,
                    counterexample: cx_str,
                    vc_location: vc.location.clone(),
                });
            }
            Ok(rust_fv_solver::SolverResult::Unknown(reason)) => {
                results.push(VerificationResult {
                    function_name: task.name.clone(),
                    condition: format!("{} (unknown: {reason})", vc.description),
                    verified: false,
                    counterexample: None,
                    vc_location: vc.location.clone(),
                });
            }
            Err(e) => {
                results.push(VerificationResult {
                    function_name: task.name.clone(),
                    condition: format!("{} (error: {e})", vc.description),
                    verified: false,
                    counterexample: None,
                    vc_location: vc.location.clone(),
                });
            }
        }
    }

    VerificationTaskResult {
        name: task.name.clone(),
        results,
        cache_key: task.cache_key,
        from_cache: false,
        invalidation_reason: None, // Will be set by caller
        duration_ms: None,          // Will be set by caller
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::invalidation::{InvalidationDecision, InvalidationReason};

    #[test]
    fn test_verification_task_result_with_timing() {
        let result = VerificationTaskResult {
            name: "test_func".to_string(),
            results: vec![],
            cache_key: [1u8; 32],
            from_cache: false,
            invalidation_reason: Some(InvalidationReason::MirChanged),
            duration_ms: Some(42),
        };

        assert_eq!(result.name, "test_func");
        assert!(!result.from_cache);
        assert_eq!(result.duration_ms, Some(42));
        assert_eq!(
            result.invalidation_reason,
            Some(InvalidationReason::MirChanged)
        );
    }

    #[test]
    fn test_cached_task_no_duration() {
        let result = VerificationTaskResult {
            name: "cached_func".to_string(),
            results: vec![],
            cache_key: [1u8; 32],
            from_cache: true,
            invalidation_reason: None,
            duration_ms: None,
        };

        assert!(result.from_cache);
        assert_eq!(result.duration_ms, None);
        assert_eq!(result.invalidation_reason, None);
    }

    #[test]
    fn test_invalidation_decision_partitioning() {
        // Test that tasks are correctly partitioned by InvalidationDecision
        let should_verify = InvalidationDecision::verify(InvalidationReason::Fresh);
        let should_skip = InvalidationDecision::skip();

        assert!(should_verify.should_verify);
        assert!(!should_skip.should_verify);
        assert_eq!(should_verify.reason, Some(InvalidationReason::Fresh));
        assert_eq!(should_skip.reason, None);
    }

    #[test]
    fn test_fresh_invalidation_reason() {
        let decision = InvalidationDecision::verify(InvalidationReason::Fresh);
        assert!(decision.should_verify);
        assert_eq!(decision.reason, Some(InvalidationReason::Fresh));
    }

    #[test]
    fn test_mir_changed_invalidation_reason() {
        let decision = InvalidationDecision::verify(InvalidationReason::MirChanged);
        assert!(decision.should_verify);
        assert_eq!(decision.reason, Some(InvalidationReason::MirChanged));
    }
}
