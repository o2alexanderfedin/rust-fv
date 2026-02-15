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
    /// Cache key for this function
    pub cache_key: [u8; 32],
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
    fresh: bool,
    use_simplification: bool,
) -> Vec<VerificationTaskResult> {
    // Build Rayon thread pool
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(jobs)
        .build()
        .unwrap();

    // Separate cached and uncached tasks
    let (cached_tasks, uncached_tasks): (Vec<_>, Vec<_>) = tasks
        .into_iter()
        .partition(|task| !fresh && cache.get(&task.cache_key).is_some());

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
            }
        })
        .collect();

    // Verify uncached tasks in parallel
    let new_results: Vec<VerificationTaskResult> = pool.install(|| {
        uncached_tasks
            .par_iter()
            .map(|task| verify_single(task, use_simplification))
            .collect()
    });

    // Insert new results into cache
    for result in &new_results {
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
                mir_hash: [0u8; 32],      // TODO: Pass from task
                contract_hash: [0u8; 32], // TODO: Pass from task
                timestamp: 0,             // Will be set by insert()
                dependencies: vec![],     // TODO: Pass from task
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
    }
}
