//! End-to-end driver-level integration tests for ALIAS-01/02 gap closure.
//!
//! These tests exercise the FULL pipeline:
//!   VerificationTask → verify_functions_parallel() → verify_single()
//!   → generate_vcs_with_db() → generate_call_site_vcs() → alias VC emission.
//!
//! Distinct from Phase 34 unit tests in crates/analysis/tests/unsafe_verification.rs
//! which call vcgen::generate_vcs() directly (bypassing the driver path).
//!
//! Architecture: Manually construct IR (caller + callee summary in ContractDatabase)
//! and call verify_functions_parallel. The tests do NOT go through the HIR compiler
//! path (that would require full rustc compilation). Instead they validate that when
//! callbacks.rs correctly populates FunctionSummary.alias_preconditions, the downstream
//! vcgen path produces alias VCs — confirming both ends of the pipeline are wired.

use rust_fv_analysis::contract_db::{AliasPrecondition, ContractDatabase, FunctionSummary};
use rust_fv_analysis::ir::{
    BasicBlock, Contracts, Function, IntTy, Local, Mutability, Operand, Place, Statement,
    Terminator, Ty,
};
use rust_fv_analysis::monomorphize::MonomorphizationRegistry;
use rust_fv_analysis::vcgen::VcKind;
use rust_fv_driver::cache::VcCache;
use rust_fv_driver::invalidation::{InvalidationDecision, InvalidationReason};
use rust_fv_driver::parallel::{VerificationTask, verify_functions_parallel};
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;

fn temp_cache_dir(name: &str) -> PathBuf {
    let mut dir = std::env::temp_dir();
    dir.push(format!("rust-fv-alias-e2e-{}-{}", name, std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    dir
}

/// Build a callee FunctionSummary with one alias precondition: !alias(ptr_a, ptr_b).
///
/// param_idx_a=0, param_idx_b=1 correspond to the first and second pointer parameters.
fn make_callee_summary_with_alias() -> FunctionSummary {
    FunctionSummary {
        contracts: Contracts::default(),
        param_names: vec!["_1".to_string(), "_2".to_string()],
        param_types: vec![
            Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Mutable),
            Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Mutable),
        ],
        return_ty: Ty::Int(IntTy::I32),
        alias_preconditions: vec![AliasPrecondition {
            param_idx_a: 0,
            param_idx_b: 1,
            raw: "!alias(ptr_a, ptr_b)".to_string(),
        }],
        is_inferred: false,
    }
}

/// Build a caller Function that calls "swap_unsafe" with the given args.
///
/// The caller has params _1 and _2 (both *mut i32).
/// args controls which locals are passed to the callee.
fn make_caller_func(args: Vec<Operand>) -> Function {
    Function {
        name: "caller".to_string(),
        params: vec![
            Local::new(
                "_1",
                Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Mutable),
            ),
            Local::new(
                "_2",
                Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Mutable),
            ),
        ],
        return_local: Local::new("_0", Ty::Int(IntTy::I32)),
        locals: vec![],
        basic_blocks: vec![
            BasicBlock {
                statements: vec![Statement::Nop],
                terminator: Terminator::Call {
                    func: "swap_unsafe".to_string(),
                    args,
                    destination: Place::local("_0"),
                    target: 1,
                },
            },
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            },
        ],
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
        thread_spawns: vec![],
        atomic_ops: vec![],
        sync_ops: vec![],
        lock_invariants: vec![],
        concurrency_config: None,
        source_names: HashMap::new(),
        coroutine_info: None,
    }
}

/// Build a VerificationTask for the caller with a ContractDatabase containing the callee.
fn make_alias_task(func: Function, contract_db: ContractDatabase) -> VerificationTask {
    VerificationTask {
        name: func.name.clone(),
        ir_func: func,
        contract_db: Arc::new(contract_db),
        ghost_pred_db: Arc::new(
            rust_fv_analysis::ghost_predicate_db::GhostPredicateDatabase::new(),
        ),
        monomorphization_registry: Arc::new(MonomorphizationRegistry::new()),
        cache_key: [0u8; 32],
        mir_hash: [0u8; 32],
        contract_hash: [0u8; 32],
        dependencies: vec![],
        invalidation_decision: InvalidationDecision::verify(InvalidationReason::Fresh),
        source_locations: HashMap::new(),
    }
}

/// Test 1: Caller whose callee has alias_preconditions populated in ContractDatabase
/// produces at least one VcKind::PointerAliasing VC via verify_functions_parallel.
///
/// This validates the driver path from VerificationTask → vcgen → alias VC emission.
#[test]
fn alias_precondition_vc_generated_via_driver_path() {
    let mut db = ContractDatabase::new();
    db.insert("swap_unsafe".to_string(), make_callee_summary_with_alias());

    // Caller passes distinct args _1 and _2 — UNSAT (no violation), but VC is still generated.
    let caller = make_caller_func(vec![
        Operand::Move(Place::local("_1")),
        Operand::Move(Place::local("_2")),
    ]);
    let task = make_alias_task(caller, db);

    let cache_dir = temp_cache_dir("generated");
    let mut cache = VcCache::new(cache_dir);

    let results = verify_functions_parallel(vec![task], &mut cache, 1, false, false);
    assert_eq!(results.len(), 1, "Expected exactly one task result");

    let task_results = &results[0].results;

    let alias_vcs: Vec<_> = task_results
        .iter()
        .filter(|r| r.vc_location.vc_kind == VcKind::PointerAliasing)
        .collect();

    assert!(
        !alias_vcs.is_empty(),
        "Expected at least one VcKind::PointerAliasing VC via driver path; \
        got VC kinds: {:?}",
        task_results
            .iter()
            .map(|r| &r.vc_location.vc_kind)
            .collect::<Vec<_>>()
    );
}

/// Test 2: SAT case — caller passes the same local (_1) for both pointer arguments.
///
/// The alias VC asserts `_1 == _1` (pointers are aliased — SAT = violation detected).
/// The VC must be NOT verified (verified=false), indicating the precondition is violated.
#[test]
fn alias_precondition_vc_is_sat_for_aliased_args() {
    let mut db = ContractDatabase::new();
    db.insert("swap_unsafe".to_string(), make_callee_summary_with_alias());

    // Both args are _1 — same pointer, aliased — violates !alias precondition.
    let caller = make_caller_func(vec![
        Operand::Move(Place::local("_1")),
        Operand::Move(Place::local("_1")),
    ]);
    let task = make_alias_task(caller, db);

    let cache_dir = temp_cache_dir("sat");
    let mut cache = VcCache::new(cache_dir);

    let results = verify_functions_parallel(vec![task], &mut cache, 1, false, false);
    assert_eq!(results.len(), 1, "Expected exactly one task result");

    let task_results = &results[0].results;

    let alias_vcs: Vec<_> = task_results
        .iter()
        .filter(|r| r.vc_location.vc_kind == VcKind::PointerAliasing)
        .collect();

    assert!(
        !alias_vcs.is_empty(),
        "Expected at least one VcKind::PointerAliasing VC for aliased args; \
        got VC kinds: {:?}",
        task_results
            .iter()
            .map(|r| &r.vc_location.vc_kind)
            .collect::<Vec<_>>()
    );

    // When args are aliased (_1 == _1), the VC detects a violation (SAT = not verified).
    let alias_violation = alias_vcs.iter().any(|r| !r.verified);
    assert!(
        alias_violation,
        "Alias VC must be SAT (not verified) when same pointer passed twice; \
        got verified={:?}",
        alias_vcs.iter().map(|r| r.verified).collect::<Vec<_>>()
    );
}

/// Test 3: UNSAT case — caller passes distinct locals _1 and _2 AND has a precondition
/// `_1 != _2` that constrains the pointers to be non-aliasing.
///
/// The alias VC asserts `_1 == _2`, but the caller's `requires _1 != _2` precondition
/// is assumed in the VC script. With `_1 != _2` assumed, `_1 == _2` is UNSAT (verified).
#[test]
fn alias_precondition_vc_is_unsat_for_distinct_args() {
    use rust_fv_analysis::ir::SpecExpr;

    let mut db = ContractDatabase::new();
    db.insert("swap_unsafe".to_string(), make_callee_summary_with_alias());

    // Distinct args _1 and _2. The caller requires `_1 != _2` so Z3 knows they're distinct.
    let mut caller = make_caller_func(vec![
        Operand::Move(Place::local("_1")),
        Operand::Move(Place::local("_2")),
    ]);
    // Add caller precondition: _1 != _2 — makes alias VC UNSAT (verified).
    caller.contracts.requires.push(SpecExpr {
        raw: "_1 != _2".to_string(),
    });
    let task = make_alias_task(caller, db);

    let cache_dir = temp_cache_dir("unsat");
    let mut cache = VcCache::new(cache_dir);

    let results = verify_functions_parallel(vec![task], &mut cache, 1, false, false);
    assert_eq!(results.len(), 1, "Expected exactly one task result");

    let task_results = &results[0].results;

    let alias_vcs: Vec<_> = task_results
        .iter()
        .filter(|r| r.vc_location.vc_kind == VcKind::PointerAliasing)
        .collect();

    assert!(
        !alias_vcs.is_empty(),
        "Expected at least one VcKind::PointerAliasing VC for distinct args; \
        got VC kinds: {:?}",
        task_results
            .iter()
            .map(|r| &r.vc_location.vc_kind)
            .collect::<Vec<_>>()
    );

    // All alias VCs must be verified (UNSAT = no violation) for distinct pointers.
    let all_alias_verified = alias_vcs.iter().all(|r| r.verified);
    assert!(
        all_alias_verified,
        "Alias VC must be UNSAT (verified) when distinct pointers passed; \
        got verified={:?}",
        alias_vcs.iter().map(|r| r.verified).collect::<Vec<_>>()
    );
}

/// Test 4: Regression guard — callee with empty alias_preconditions produces ZERO
/// VcKind::PointerAliasing VCs.
///
/// Ensures that alias VC emission is only triggered when alias_preconditions is non-empty.
#[test]
fn alias_precondition_no_vc_for_empty_preconditions() {
    let mut db = ContractDatabase::new();
    // Callee with NO alias preconditions
    db.insert(
        "swap_unsafe".to_string(),
        FunctionSummary {
            contracts: Contracts::default(),
            param_names: vec!["_1".to_string(), "_2".to_string()],
            param_types: vec![
                Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Mutable),
                Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Mutable),
            ],
            return_ty: Ty::Int(IntTy::I32),
            alias_preconditions: vec![], // deliberately empty
            is_inferred: false,
        },
    );

    let caller = make_caller_func(vec![
        Operand::Move(Place::local("_1")),
        Operand::Move(Place::local("_2")),
    ]);
    let task = make_alias_task(caller, db);

    let cache_dir = temp_cache_dir("empty");
    let mut cache = VcCache::new(cache_dir);

    let results = verify_functions_parallel(vec![task], &mut cache, 1, false, false);
    assert_eq!(results.len(), 1, "Expected exactly one task result");

    let task_results = &results[0].results;

    let alias_vcs: Vec<_> = task_results
        .iter()
        .filter(|r| r.vc_location.vc_kind == VcKind::PointerAliasing)
        .collect();

    assert!(
        alias_vcs.is_empty(),
        "Expected ZERO VcKind::PointerAliasing VCs when alias_preconditions is empty; \
        got {} alias VCs",
        alias_vcs.len()
    );
}
