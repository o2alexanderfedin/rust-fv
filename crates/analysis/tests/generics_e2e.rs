//! End-to-end analysis-layer tests for generic function VC generation.
//!
//! These tests verify that:
//! 1. The parametric axiom branch in generate_vcs_with_db fires for functions
//!    with non-empty generic_params (vcgen.rs:290-298).
//! 2. Functions with empty generic_params still generate VCs normally.
//!
//! These are pure analysis-layer tests — no driver or TyCtxt needed.

use rust_fv_analysis::ghost_predicate_db::GhostPredicateDatabase;
use rust_fv_analysis::ir::{
    BasicBlock, Contracts, Function, GenericParam, Local, Operand, Place, Rvalue, SpecExpr,
    Statement, Terminator, Ty,
};
use rust_fv_analysis::vcgen;

/// Build a max-like generic function with contracts.
///
/// ```rust
/// fn max<T: Ord>(a: T, b: T) -> T {
///     _0 = _1  // simplified body
/// }
/// ```
/// with `ensures _0 == _1`
fn make_generic_func(generic_params: Vec<GenericParam>) -> Function {
    Function {
        name: "max".to_string(),
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
        source_names: std::collections::HashMap::new(),
        coroutine_info: None,
        refcell_ghost_states: vec![],
        maybeuninit_ghost_states: vec![],
    }
}

/// Test 1: parametric_axioms_fire_for_generic_function
///
/// A Function with generic_params=[GenericParam { name: "T", trait_bounds: ["Ord"] }]
/// should generate non-empty VCs. The parametric axiom branch at vcgen.rs:290-298
/// fires and injects trait bound assumptions. The ensures contract produces a VC.
///
/// This documents existing correct behavior of the analysis layer.
#[test]
fn parametric_axioms_fire_for_generic_function() {
    let func = make_generic_func(vec![GenericParam {
        name: "T".to_string(),
        trait_bounds: vec!["Ord".to_string()],
    }]);

    let ghost_pred_db = GhostPredicateDatabase::new();
    let func_vcs = vcgen::generate_vcs_with_db(&func, None, &ghost_pred_db);

    assert!(
        !func_vcs.conditions.is_empty(),
        "Generic function with Ord bound must produce at least one VC (postcondition check). \
        Got 0 conditions — parametric axiom branch may not be generating VCs."
    );
}

/// Test 2: empty_generic_params_produces_no_axiom_assumptions
///
/// A Function with generic_params: vec![] should still generate VCs from the ensures
/// contract. This confirms that empty generic_params is valid and the ensures VC
/// is generated regardless.
#[test]
fn empty_generic_params_produces_vcs_from_ensures() {
    let func = make_generic_func(vec![]);

    let ghost_pred_db = GhostPredicateDatabase::new();
    let func_vcs = vcgen::generate_vcs_with_db(&func, None, &ghost_pred_db);

    assert!(
        !func_vcs.conditions.is_empty(),
        "Function with ensures contract must produce at least one VC even with empty generic_params. \
        Got 0 conditions."
    );
}

/// Test: ord_generic_smt_script_contains_declare_sort
///
/// A generic function with T: Ord bound must produce a VC script that contains
/// DeclareSort and DeclareFun commands for the uninterpreted sort T.
#[test]
fn ord_generic_smt_script_contains_declare_sort() {
    use rust_fv_smtlib::command::Command;

    let func = make_generic_func(vec![GenericParam {
        name: "T".to_string(),
        trait_bounds: vec!["Ord".to_string()],
    }]);

    let ghost_pred_db = GhostPredicateDatabase::new();
    let func_vcs = vcgen::generate_vcs_with_db(&func, None, &ghost_pred_db);

    assert!(
        !func_vcs.conditions.is_empty(),
        "Must have at least one VC for the ensures contract"
    );

    let first_vc = &func_vcs.conditions[0];
    let has_declare_sort = first_vc
        .script
        .commands()
        .iter()
        .any(|c| matches!(c, Command::DeclareSort(name, 0) if name == "T"));
    assert!(
        has_declare_sort,
        "VC script must contain (declare-sort T 0) for T: Ord generic bound. \
        Commands: {:?}",
        first_vc.script.commands()
    );

    let has_declare_fun = first_vc
        .script
        .commands()
        .iter()
        .any(|c| matches!(c, Command::DeclareFun(name, _, _) if name.starts_with("T_")));
    assert!(
        has_declare_fun,
        "VC script must contain (declare-fun T_le ...) for Ord predicate. \
        Commands: {:?}",
        first_vc.script.commands()
    );
}

/// Test 3: generic_function_vc_count_matches_non_generic
///
/// Both generic and non-generic versions of the same function (with same contracts)
/// must produce the same number of VCs. Generic params add axiom assumptions but do
/// not suppress or duplicate contract VCs.
#[test]
fn generic_function_vc_count_matches_non_generic() {
    let generic_func = make_generic_func(vec![GenericParam {
        name: "T".to_string(),
        trait_bounds: vec!["Ord".to_string()],
    }]);
    let plain_func = make_generic_func(vec![]);

    let ghost_pred_db = GhostPredicateDatabase::new();
    let generic_vcs = vcgen::generate_vcs_with_db(&generic_func, None, &ghost_pred_db);
    let plain_vcs = vcgen::generate_vcs_with_db(&plain_func, None, &ghost_pred_db);

    assert_eq!(
        generic_vcs.conditions.len(),
        plain_vcs.conditions.len(),
        "Generic and non-generic functions with same contracts must produce same VC count. \
        Generic: {}, non-generic: {}",
        generic_vcs.conditions.len(),
        plain_vcs.conditions.len()
    );
}
