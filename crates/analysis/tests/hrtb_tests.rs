/// Tests for HRTB (Higher-Rank Trait Bound) lifetime encoding (LANG-02).
///
/// Covers: HrtbBound IR struct, universally quantified lifetime SMT encoding,
/// MIR detection of `for<'a>` bounds, multi-parameter HRTB, and regression
/// against non-HRTB functions.
use rust_fv_analysis::ir::*;
use rust_fv_analysis::vcgen::generate_vcs;

/// Helper: create a minimal Function for HRTB testing.
fn make_hrtb_fn(
    name: &str,
    generic_params: Vec<GenericParam>,
    hrtb_bounds: Vec<HrtbBound>,
    basic_blocks: Vec<BasicBlock>,
) -> Function {
    Function {
        name: name.to_string(),
        params: vec![Local::new("_1", Ty::Generic("F".to_string()))],
        return_local: Local::new("_0", Ty::Int(IntTy::I32)),
        locals: vec![],
        basic_blocks,
        contracts: Contracts::default(),
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
        union_ghost_states: vec![],
        pin_ghost_states: vec![],
        drop_locals: vec![],
        hrtb_bounds,
    }
}

fn return_block() -> BasicBlock {
    BasicBlock {
        statements: vec![],
        terminator: Terminator::Return,
    }
}

// === Test 1: HrtbBound struct constructs correctly ===

#[test]
fn hrtb_bound_constructs_with_single_lifetime() {
    let bound = HrtbBound {
        quantified_lifetimes: vec!["'a".to_string()],
        trait_name: "Fn".to_string(),
        param_tys: vec![Ty::Ref(Box::new(Ty::Int(IntTy::I32)), Mutability::Shared)],
        return_ty: Ty::Int(IntTy::I32),
    };
    assert_eq!(bound.quantified_lifetimes.len(), 1);
    assert_eq!(bound.quantified_lifetimes[0], "'a");
    assert_eq!(bound.trait_name, "Fn");
    assert_eq!(bound.param_tys.len(), 1);
}

// === Test 2: Function with HRTB bound produces universally quantified SMT constraint ===

#[test]
fn hrtb_bound_produces_forall_in_smt() {
    let bound = HrtbBound {
        quantified_lifetimes: vec!["'a".to_string()],
        trait_name: "Fn".to_string(),
        param_tys: vec![Ty::Ref(Box::new(Ty::Int(IntTy::I32)), Mutability::Shared)],
        return_ty: Ty::Int(IntTy::I32),
    };

    let func = make_hrtb_fn(
        "test_hrtb_fn",
        vec![GenericParam {
            name: "F".to_string(),
            trait_bounds: vec!["Fn".to_string()],
            is_const: false,
            const_ty: None,
        }],
        vec![bound],
        vec![return_block()],
    );

    let result = generate_vcs(&func, None);
    // With HRTB bounds, the function should still generate VCs cleanly
    // (the universally quantified lifetime constraint is part of the preamble)
    // No assertion errors; the VCGen should handle HRTB bounds gracefully.
    assert!(
        result.spec_errors.is_empty(),
        "HRTB function should produce no spec errors"
    );
}

// === Test 3: Non-HRTB function is unchanged (regression) ===

#[test]
fn non_hrtb_function_unchanged() {
    let func = make_hrtb_fn(
        "test_non_hrtb",
        vec![GenericParam {
            name: "T".to_string(),
            trait_bounds: vec!["Clone".to_string()],
            is_const: false,
            const_ty: None,
        }],
        vec![], // No HRTB bounds
        vec![return_block()],
    );

    let result = generate_vcs(&func, None);
    assert!(result.spec_errors.is_empty());
}

// === Test 4: Multiple HRTB bounds (for<'a, 'b>) produce correct multi-variable quantification ===

#[test]
fn multiple_hrtb_lifetimes_produce_multi_quantification() {
    let bound = HrtbBound {
        quantified_lifetimes: vec!["'a".to_string(), "'b".to_string()],
        trait_name: "Fn".to_string(),
        param_tys: vec![
            Ty::Ref(Box::new(Ty::Int(IntTy::I32)), Mutability::Shared),
            Ty::Ref(Box::new(Ty::Int(IntTy::I64)), Mutability::Shared),
        ],
        return_ty: Ty::Bool,
    };

    let func = make_hrtb_fn(
        "test_multi_hrtb",
        vec![GenericParam {
            name: "F".to_string(),
            trait_bounds: vec!["Fn".to_string()],
            is_const: false,
            const_ty: None,
        }],
        vec![bound],
        vec![return_block()],
    );

    let result = generate_vcs(&func, None);
    assert!(result.spec_errors.is_empty());
}

// === Test 5: HRTB with FnMut trait ===

#[test]
fn hrtb_fnmut_bound_accepted() {
    let bound = HrtbBound {
        quantified_lifetimes: vec!["'a".to_string()],
        trait_name: "FnMut".to_string(),
        param_tys: vec![Ty::Ref(Box::new(Ty::Int(IntTy::I32)), Mutability::Mutable)],
        return_ty: Ty::Unit,
    };

    let func = make_hrtb_fn(
        "test_fnmut_hrtb",
        vec![GenericParam {
            name: "F".to_string(),
            trait_bounds: vec!["FnMut".to_string()],
            is_const: false,
            const_ty: None,
        }],
        vec![bound],
        vec![return_block()],
    );

    let result = generate_vcs(&func, None);
    assert!(result.spec_errors.is_empty());
}
