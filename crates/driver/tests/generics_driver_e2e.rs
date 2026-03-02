//! End-to-end driver-level integration tests for generic function verification.
//!
//! These tests exercise the FULL pipeline: VerificationTask → verify_functions_parallel()
//! → verify_single() → generate_vcs_with_db() with generic_params populated.
//!
//! The key invariant being tested:
//!   A generic function IR (with generic_params non-empty) must produce non-empty
//!   VC results when run through the driver verification pipeline.
//!
//! Follows the same pattern as ghost_predicate_e2e.rs.

use rust_fv_analysis::ghost_predicate_db::GhostPredicateDatabase;
use rust_fv_analysis::ir::{
    BasicBlock, Contracts, Function, GenericParam, Local, Operand, Place, Rvalue, SpecExpr,
    Statement, Terminator, Ty,
};
use rust_fv_driver::cache::VcCache;
use rust_fv_driver::invalidation::{InvalidationDecision, InvalidationReason};
use rust_fv_driver::parallel::{VerificationTask, verify_functions_parallel};
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;

fn temp_cache_dir(name: &str) -> PathBuf {
    let mut dir = std::env::temp_dir();
    dir.push(format!(
        "rust-fv-generics-e2e-{}-{}",
        name,
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    dir
}

/// Build a max-like generic function body.
///
/// ```rust
/// fn max<T: Ord>(a: T, b: T) -> T {
///     _0 = _1  // body: assign return from first param
/// }
/// ```
/// with `ensures _0 == _1`
fn make_generic_test_func(generic_params: Vec<GenericParam>) -> Function {
    Function {
        name: "test_generic_max".to_string(),
        params: vec![
            Local::new("_1", Ty::Generic("T".to_string())),
            Local::new("_2", Ty::Generic("T".to_string())),
        ],
        return_local: Local::new("_0", Ty::Generic("T".to_string())),
        locals: vec![],
        basic_blocks: vec![BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::Use(Operand::Copy(Place::local("_1"))),
            )],
            terminator: Terminator::Return,
        }],
        contracts: Contracts {
            requires: vec![],
            ensures: vec![SpecExpr {
                raw: "_0 == _1".to_string(),
            }],
            invariants: vec![],
            is_pure: false,
            decreases: None,
            fn_specs: vec![],
            state_invariant: None,
            is_inferred: false,
        },
        loops: vec![],
        generic_params,
        prophecies: vec![],
        lifetime_params: vec![],
        outlives_constraints: vec![],
        borrow_info: vec![],
        reborrow_chains: vec![],
        unsafe_blocks: vec![],
        unsafe_operations: vec![],
        unsafe_contracts: None,
        is_unsafe_fn: false,
        thread_spawns: vec![],
        atomic_ops: vec![],
        sync_ops: vec![],
        lock_invariants: vec![],
        concurrency_config: None,
        source_names: HashMap::new(),
        coroutine_info: None,
    }
}

fn make_generic_task(func: Function) -> VerificationTask {
    VerificationTask {
        name: func.name.clone(),
        ir_func: func,
        contract_db: Arc::new(rust_fv_analysis::contract_db::ContractDatabase::new()),
        ghost_pred_db: Arc::new(GhostPredicateDatabase::new()),
        cache_key: [0u8; 32],
        mir_hash: [0u8; 32],
        contract_hash: [0u8; 32],
        dependencies: vec![],
        invalidation_decision: InvalidationDecision::verify(InvalidationReason::Fresh),
        source_locations: HashMap::new(),
    }
}

/// Test 3: generic_ir_function_routes_through_vcs_with_db_when_generic_params_populated
///
/// A VerificationTask with a Function where generic_params contains
/// GenericParam { name: "T", trait_bounds: ["Ord"] } must produce non-empty results.
///
/// This tests that the parametric axiom path fires correctly through the driver pipeline
/// and that generic functions are not silently dropped or produce empty VCs.
#[test]
fn generic_ir_function_produces_nonempty_results_when_generic_params_populated() {
    let func = make_generic_test_func(vec![GenericParam {
        name: "T".to_string(),
        trait_bounds: vec!["Ord".to_string()],
    }]);
    let task = make_generic_task(func);

    let cache_dir = temp_cache_dir("populated");
    let mut cache = VcCache::new(cache_dir);

    let results = verify_functions_parallel(vec![task], &mut cache, 1, false, false);

    assert_eq!(
        results.len(),
        1,
        "Must have one result for test_generic_max"
    );
    let task_results = &results[0].results;

    assert!(
        !task_results.is_empty(),
        "Generic function with populated generic_params must produce at least one VC result. \
        Got 0 — the driver pipeline may be dropping generic function VCs. Got: {:?}",
        task_results
            .iter()
            .map(|r| &r.condition)
            .collect::<Vec<_>>()
    );
}

/// Test 4: generic_function_with_empty_generic_params_still_verifies
///
/// A VerificationTask with generic_params: vec![] must also produce non-empty results.
/// This confirms no regression: plain (non-generic) functions continue to work.
#[test]
fn generic_function_with_empty_generic_params_still_verifies() {
    let func = make_generic_test_func(vec![]);
    let task = make_generic_task(func);

    let cache_dir = temp_cache_dir("empty");
    let mut cache = VcCache::new(cache_dir);

    let results = verify_functions_parallel(vec![task], &mut cache, 1, false, false);

    assert_eq!(
        results.len(),
        1,
        "Must have one result for test_generic_max"
    );
    let task_results = &results[0].results;

    assert!(
        !task_results.is_empty(),
        "Function with empty generic_params must still produce VC results (no regression). \
        Got 0 results. Got: {:?}",
        task_results
            .iter()
            .map(|r| &r.condition)
            .collect::<Vec<_>>()
    );
}
