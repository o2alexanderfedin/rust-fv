//! End-to-end driver-level integration test for async counterexample field population (ASY-02).
//!
//! Tests the FULL pipeline: IR async Function with falsifiable state_invariant
//! -> VerificationTask -> verify_functions_parallel() -> VerificationTaskResult
//! -> failing result has counterexample_v2 with non-None poll_iteration and await_side.
//!
//! Distinct from crates/analysis/tests/async_verification.rs which tests at the
//! analysis (VC generation + Z3) level. This test validates the driver pipeline
//! correctly populates async counterexample fields end-to-end.

use rust_fv_analysis::ghost_predicate_db::GhostPredicateDatabase;
use rust_fv_analysis::ir::{
    BasicBlock, Contracts, CoroutineExitKind, CoroutineInfo, CoroutineState, Function, IntTy,
    Local, SpecExpr, Terminator, Ty,
};
use rust_fv_analysis::vcgen::VcKind;
use rust_fv_driver::cache::VcCache;
use rust_fv_driver::invalidation::{InvalidationDecision, InvalidationReason};
use rust_fv_driver::parallel::{VerificationTask, verify_functions_parallel};
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;

fn temp_cache_dir(name: &str) -> PathBuf {
    let mut dir = std::env::temp_dir();
    dir.push(format!(
        "rust-fv-async-cex-e2e-{}-{}",
        name,
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    dir
}

/// Build a minimal async IR function with a falsifiable state_invariant.
///
/// The function has one persistent field `counter: i64` and the invariant `counter >= 1`.
/// Default Z3 model assigns counter = 0, which violates >= 1, producing a SAT counterexample.
///
/// Uses one Yield state (state_id=0) and one Return state (state_id=1),
/// matching the canonical async state machine shape from async_verification.rs.
fn make_async_state_invariant_func() -> Function {
    let states = vec![
        CoroutineState {
            state_id: 0,
            entry_block: 0,
            exit_kind: CoroutineExitKind::Yield,
            await_source_line: Some(10),
        },
        CoroutineState {
            state_id: 1,
            entry_block: 1,
            exit_kind: CoroutineExitKind::Return,
            await_source_line: None,
        },
    ];

    let contracts = Contracts {
        state_invariant: Some(SpecExpr {
            raw: "counter >= 1".to_string(),
        }),
        ..Default::default()
    };

    Function {
        name: "async_cex_e2e".to_string(),
        params: vec![Local::new("counter", Ty::Int(IntTy::I64))],
        return_local: Local::new("_0", Ty::Unit),
        locals: vec![],
        basic_blocks: vec![
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            },
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            },
        ],
        contracts,
        loops: vec![],
        generic_params: vec![],
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
        coroutine_info: Some(CoroutineInfo {
            states,
            persistent_fields: vec![("counter".to_string(), Ty::Int(IntTy::I64))],
        }),
    }
}

/// ASY-02 E2E: driver pipeline must populate poll_iteration and await_side
/// in counterexample_v2 for a falsifiable state_invariant failure.
#[test]
fn test_async_cex_e2e_async_fields_populated() {
    // Check Z3 is available — skip gracefully if not
    if std::process::Command::new("z3")
        .arg("--version")
        .output()
        .is_err()
    {
        eprintln!("Skipping: z3 not found in PATH");
        return;
    }

    let func = make_async_state_invariant_func();
    let cache_dir = temp_cache_dir("async-cex");
    let mut cache = VcCache::new(cache_dir.clone());

    let task = VerificationTask {
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
    };

    let task_results = verify_functions_parallel(vec![task], &mut cache, 1, false, false);

    assert_eq!(
        task_results.len(),
        1,
        "Must have one VerificationTaskResult for async_cex_e2e"
    );

    let results = &task_results[0].results;

    // 1. At least one result must be a failure (invariant falsified)
    let failures: Vec<_> = results.iter().filter(|r| !r.verified).collect();
    assert!(
        !failures.is_empty(),
        "Expected at least one state_invariant failure. \
         Got results: {:?}",
        results
            .iter()
            .map(|r| format!("verified={} kind={:?}", r.verified, r.vc_location.vc_kind))
            .collect::<Vec<_>>()
    );

    // 2. All failures must be AsyncStateInvariant* kind
    for failure in &failures {
        assert!(
            matches!(
                failure.vc_location.vc_kind,
                VcKind::AsyncStateInvariantSuspend | VcKind::AsyncStateInvariantResume
            ),
            "Expected AsyncStateInvariant* vc_kind, got: {:?}",
            failure.vc_location.vc_kind
        );
    }

    // Find one failure with a populated counterexample_v2
    let cex_failure = failures.iter().find(|r| r.counterexample_v2.is_some());
    assert!(
        cex_failure.is_some(),
        "Expected at least one failure to have counterexample_v2 populated. \
         Failures: {:?}",
        failures
            .iter()
            .map(|r| format!(
                "kind={:?} cex_v2={}",
                r.vc_location.vc_kind,
                r.counterexample_v2.is_some()
            ))
            .collect::<Vec<_>>()
    );

    let cex = cex_failure.unwrap().counterexample_v2.as_ref().unwrap();

    // 3. poll_iteration must be Some(_) — not None
    assert!(
        cex.poll_iteration.is_some(),
        "Expected counterexample_v2.poll_iteration to be Some(_), got None. \
         vc_kind={:?}",
        cex_failure.unwrap().vc_location.vc_kind
    );

    // 4. await_side must be Some("pre_await") or Some("post_await")
    let await_side = cex.await_side.as_deref();
    assert!(
        matches!(await_side, Some("pre_await") | Some("post_await")),
        "Expected await_side to be Some(\"pre_await\") or Some(\"post_await\"), got: {:?}",
        await_side
    );
}
