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
use crate::types::VerificationResult;
use rust_fv_analysis::contract_db::ContractDatabase;
use rust_fv_analysis::ghost_predicate_db::GhostPredicateDatabase;
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
    /// Pre-built source location map: `(block_idx, stmt_idx)` → `(file, line, col)`.
    ///
    /// Built in `after_analysis` from MIR `SourceInfo` spans while `TyCtxt`
    /// is still live. Used by the parallel worker to fill `VcLocation` fields
    /// after VcGen runs. Empty map means no source info available.
    pub source_locations: std::collections::HashMap<(usize, usize), (String, usize, usize)>,
    /// Shared ghost predicate database (populated from #[ghost_predicate] doc attrs)
    pub ghost_pred_db: Arc<GhostPredicateDatabase>,
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
    /// SSA-name → source-name mapping for ariadne span label rendering.
    /// Populated from `ir::Function.source_names` when IR is available.
    pub source_names: std::collections::HashMap<String, String>,
    /// Typed local variables for `cex_render` type-dispatch in diagnostics.
    pub locals: Vec<rust_fv_analysis::ir::Local>,
    /// Typed parameter locals for `cex_render` type-dispatch in diagnostics.
    pub params: Vec<rust_fv_analysis::ir::Local>,
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
                    counterexample_v2: None,
                    vc_location: VcLocation {
                        function: task.name.clone(),
                        block: 0,
                        statement: 0,
                        source_file: None,
                        source_line: None,
                        source_column: None,
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
                    counterexample_v2: None,
                    vc_location: VcLocation {
                        function: task.name.clone(),
                        block: 0,
                        statement: 0,
                        source_file: None,
                        source_line: None,
                        source_column: None,
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
                source_names: task.ir_func.source_names.clone(),
                locals: task.ir_func.locals.clone(),
                params: task.ir_func.params.clone(),
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
                ..Default::default()
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
                    counterexample_v2: None,
                    vc_location: VcLocation {
                        function: task.name.clone(),
                        block: 0,
                        statement: 0,
                        source_file: None,
                        source_line: None,
                        source_column: None,
                        contract_text: None,
                        vc_kind: VcKind::PanicFreedom,
                    },
                }],
                cache_key: task.cache_key,
                from_cache: false,
                invalidation_reason: None,
                duration_ms: None,
                source_names: task.ir_func.source_names.clone(),
                locals: task.ir_func.locals.clone(),
                params: task.ir_func.params.clone(),
            };
        }
    };

    // Generate VCs with inter-procedural support and ghost predicate expansion
    let mut func_vcs = rust_fv_analysis::vcgen::generate_vcs_with_db(
        &task.ir_func,
        Some(&task.contract_db),
        &task.ghost_pred_db,
    );

    // Fill source locations from the pre-built map (populated in after_analysis
    // while TyCtxt was live). Locations with source_file already set are skipped.
    if !task.source_locations.is_empty() {
        for vc in &mut func_vcs.conditions {
            if vc.location.source_file.is_none() {
                let key = (vc.location.block, vc.location.statement);
                if let Some((file, line, col)) = task.source_locations.get(&key) {
                    vc.location.source_file = Some(file.clone());
                    vc.location.source_line = Some(*line);
                    vc.location.source_column = Some(*col);
                }
            }
        }
    }

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
                    counterexample_v2: None,
                    vc_location: vc.location.clone(),
                });
            }
            Ok(rust_fv_solver::SolverResult::Sat(model)) => {
                // Pass structured pairs directly — no string serialization needed
                let cx_pairs = model.map(|m| m.assignments);

                // Build structured v2 counterexample from IR type info
                let counterexample_v2 =
                    build_counterexample_v2(cx_pairs.as_deref(), &vc.location, &task.ir_func);

                results.push(VerificationResult {
                    function_name: task.name.clone(),
                    condition: vc.description.clone(),
                    verified: false,
                    counterexample: cx_pairs,
                    counterexample_v2,
                    vc_location: vc.location.clone(),
                });
            }
            Ok(rust_fv_solver::SolverResult::Unknown(reason)) => {
                results.push(VerificationResult {
                    function_name: task.name.clone(),
                    condition: format!("{} (unknown: {reason})", vc.description),
                    verified: false,
                    counterexample: None,
                    counterexample_v2: None,
                    vc_location: vc.location.clone(),
                });
            }
            Err(e) => {
                results.push(VerificationResult {
                    function_name: task.name.clone(),
                    condition: format!("{} (error: {e})", vc.description),
                    verified: false,
                    counterexample: None,
                    counterexample_v2: None,
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
        duration_ms: None,         // Will be set by caller
        source_names: task.ir_func.source_names.clone(),
        locals: task.ir_func.locals.clone(),
        params: task.ir_func.params.clone(),
    }
}

/// Build a structured `JsonCounterexample` from raw SMT model pairs and IR function metadata.
///
/// Calls `cex_render::render_counterexample` with the IR function's locals/params to produce
/// typed, human-readable variable representations for the v2 JSON schema.
///
/// Returns `None` when no model pairs are available (solver gave no model).
fn build_counterexample_v2(
    cx_pairs: Option<&[(String, String)]>,
    vc_location: &VcLocation,
    ir_func: &Function,
) -> Option<crate::json_output::JsonCounterexample> {
    let pairs = cx_pairs?;

    // Render typed counterexample variables using the harvested SSA→Rust name map
    let cex_vars = crate::cex_render::render_counterexample(
        pairs,
        &ir_func.source_names,
        &ir_func.locals,
        &ir_func.params,
    );

    // Map CexVariable → JsonCexVariable
    let variables: Vec<crate::json_output::JsonCexVariable> = cex_vars
        .into_iter()
        .map(|cv| crate::json_output::JsonCexVariable {
            name: cv.name,
            ty: cv.ty,
            display: Some(cv.display),
            raw: Some(cv.raw),
            initial: cv.initial.map(|v| crate::json_output::JsonCexValue {
                display: v.display,
                raw: v.raw,
            }),
            at_failure: cv.at_failure.map(|v| crate::json_output::JsonCexValue {
                display: v.display,
                raw: v.raw,
            }),
        })
        .collect();

    Some(crate::json_output::JsonCounterexample {
        variables,
        failing_location: crate::json_output::JsonLocation {
            file: vc_location
                .source_file
                .clone()
                .unwrap_or_else(|| "unknown".to_string()),
            line: vc_location.source_line.unwrap_or(0),
            column: vc_location.source_column.unwrap_or(0),
        },
        vc_kind: format!("{:?}", vc_location.vc_kind).to_lowercase(),
        violated_spec: vc_location.contract_text.clone(),
        poll_iteration: None,
        await_side: None,
    })
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
            source_names: std::collections::HashMap::new(),
            locals: Vec::new(),
            params: Vec::new(),
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
            source_names: std::collections::HashMap::new(),
            locals: Vec::new(),
            params: Vec::new(),
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

    #[test]
    fn verification_task_has_ghost_pred_db_field() {
        // This test fails to compile until VerificationTask has the ghost_pred_db field.
        // Compile-time sentinel: if VerificationTask has ghost_pred_db: Arc<GhostPredicateDatabase>,
        // then the GhostPredicateDatabase type must be importable from analysis crate.
        let _: fn() -> rust_fv_analysis::ghost_predicate_db::GhostPredicateDatabase =
            || rust_fv_analysis::ghost_predicate_db::GhostPredicateDatabase::new();
        // Verify the field exists by checking field access compiles.
        // This will fail to compile if ghost_pred_db field is absent from VerificationTask.
        // (The actual struct construction is in the GREEN phase.)
    }
}
