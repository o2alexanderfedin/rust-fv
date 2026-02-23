//! End-to-end driver-level integration test for WMM-03 weak memory race detection.
//!
//! Tests the FULL pipeline: IR Function with concurrent Relaxed atomics
//! -> VerificationTask -> verify_functions_parallel() -> VerificationTaskResult
//! -> results list contains WeakMemoryRace failure.
//!
//! Distinct from crates/analysis/tests/weak_memory_litmus.rs which tests at the
//! analysis (VC generation + Z3) level. This test validates the driver pipeline
//! correctly propagates race errors to users.

use rust_fv_analysis::ghost_predicate_db::GhostPredicateDatabase;
use rust_fv_analysis::ir::{
    AtomicOp, AtomicOpKind, AtomicOrdering, BasicBlock, ConcurrencyConfig, Constant, Contracts,
    Function, IntTy, Local, Operand, Place, Rvalue, Statement, Terminator, ThreadSpawn, Ty,
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
    dir.push(format!("rust-fv-wmm-e2e-{}-{}", name, std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    dir
}

/// Build a minimal IR function with two concurrent Relaxed atomic stores to the same location.
/// Thread 0 stores 1 to `x`, thread 1 stores 2 to `x` — a textbook Relaxed data race.
///
/// Uses the same make_litmus_function pattern as weak_memory_litmus.rs:
/// - atomic_ops on the Function (not as statements)
/// - ThreadSpawn entries for each spawned thread_id > 0
/// - ConcurrencyConfig with verify_concurrency: true
fn make_relaxed_race_func() -> Function {
    let atomic_ops = vec![
        AtomicOp {
            kind: AtomicOpKind::Store,
            ordering: AtomicOrdering::Relaxed,
            atomic_place: Place::local("x"),
            value: Some(Operand::Constant(Constant::Int(1, IntTy::I32))),
            thread_id: 0,
        },
        AtomicOp {
            kind: AtomicOpKind::Store,
            ordering: AtomicOrdering::Relaxed,
            atomic_place: Place::local("x"),
            value: Some(Operand::Constant(Constant::Int(2, IntTy::I32))),
            thread_id: 1,
        },
    ];

    // thread_id=1 means one spawned thread (id 0..max_thread exclusive, so max=1 gives h0)
    let max_thread = atomic_ops.iter().map(|op| op.thread_id).max().unwrap_or(0);
    let thread_spawns: Vec<ThreadSpawn> = (0..max_thread)
        .map(|t| ThreadSpawn {
            handle_local: format!("h{t}"),
            thread_fn: format!("worker_{t}"),
            args: vec![],
            is_scoped: false,
        })
        .collect();

    Function {
        name: "relaxed_race".to_string(),
        params: vec![],
        return_local: Local::new("_0", Ty::Unit),
        locals: vec![Local::new("x", Ty::Int(IntTy::I32))],
        basic_blocks: vec![BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::Use(Operand::Constant(Constant::Unit)),
            )],
            terminator: Terminator::Return,
        }],
        contracts: Contracts::default(),
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
        thread_spawns,
        atomic_ops,
        sync_ops: vec![],
        lock_invariants: vec![],
        concurrency_config: Some(ConcurrencyConfig {
            verify_concurrency: true,
            max_threads: 4,
            max_context_switches: 6,
        }),
        source_names: HashMap::new(),
        coroutine_info: None,
    }
}

/// WMM-03: A function with two concurrent Relaxed atomic stores to the same location
/// must be reported as NOT verified (race detected) by the driver pipeline.
#[test]
fn test_relaxed_race_surfaces_as_driver_failure() {
    // Check Z3 is available — skip gracefully if not
    if std::process::Command::new("z3")
        .arg("--version")
        .output()
        .is_err()
    {
        eprintln!("Skipping: z3 not found in PATH");
        return;
    }

    let func = make_relaxed_race_func();
    let cache_dir = temp_cache_dir("relaxed-race");
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
        "Must have one VerificationTaskResult for relaxed_race"
    );

    let results = &task_results[0].results;

    // At least one result must be verified:false with WeakMemoryRace vc_kind
    let race_failures: Vec<_> = results
        .iter()
        .filter(|r| !r.verified && r.vc_location.vc_kind == VcKind::WeakMemoryRace)
        .collect();

    assert!(
        !race_failures.is_empty(),
        "Expected WeakMemoryRace failure in driver results for two concurrent Relaxed stores. \
         Got results: {:?}",
        results
            .iter()
            .map(|r| format!("verified={} kind={:?}", r.verified, r.vc_location.vc_kind))
            .collect::<Vec<_>>()
    );

    // Cleanup
    let _ = std::fs::remove_dir_all(&cache_dir);
}
