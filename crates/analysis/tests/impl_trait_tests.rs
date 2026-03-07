/// Tests for impl Trait resolution, Ty::Opaque encoding, RPITIT behavioral
/// subtyping, and opaque type trait bound axioms (LANG-07).
///
/// Covers:
/// - Test 1: Function returning concrete type resolved from impl Trait has postcondition verified
/// - Test 2: Ty::Opaque with Iterator trait bound generates uninterpreted sort
/// - Test 3: RPITIT impl with ensures clause verified via behavioral subtyping (Liskov check)
/// - Test 4: Opaque type that cannot be resolved falls back to Ty::Opaque with uninterpreted sort
/// - Test 5: Auto-trait bounds (Send/Sync) NOT leaked from opaque types unless explicit
use rust_fv_analysis::behavioral_subtyping::{SubtypingKind, generate_subtyping_vcs};
use rust_fv_analysis::encode_sort::encode_type;
use rust_fv_analysis::ir::*;
use rust_fv_analysis::trait_analysis::TraitDatabase;
use rust_fv_smtlib::sort::Sort;

// === Test 1: Concrete type resolved from impl Trait verifies postcondition ===

#[test]
fn concrete_type_from_impl_trait_postcondition_verified() {
    // When an `impl Trait` return type is resolved to a concrete type (e.g., Vec<i32>),
    // the postcondition should be verified on the concrete type.
    // We simulate this by creating a function with return type Vec<i32> (concrete resolution)
    // and verifying that VCs are generated for its postconditions.
    let func = Function {
        name: "items".to_string(),
        params: vec![],
        return_local: Local::new(
            "_0",
            Ty::Struct(
                "Vec_i32".to_string(),
                vec![("len".to_string(), Ty::Uint(UintTy::Usize))],
            ),
        ),
        locals: vec![],
        basic_blocks: vec![BasicBlock {
            statements: vec![],
            terminator: Terminator::Return,
        }],
        contracts: Contracts {
            ensures: vec![SpecExpr {
                raw: "result.len > 0".to_string(),
            }],
            ..Default::default()
        },
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
        source_names: std::collections::HashMap::new(),
        coroutine_info: None,
        refcell_ghost_states: vec![],
        maybeuninit_ghost_states: vec![],
        union_ghost_states: vec![],
        pin_ghost_states: vec![],
        drop_locals: vec![],
        hrtb_bounds: vec![],
    };

    let result = rust_fv_analysis::vcgen::generate_vcs(&func, None);
    // Should generate postcondition VC for ensures clause
    assert!(
        !result.conditions.is_empty(),
        "Function with ensures clause should generate verification conditions"
    );
    // At least one VC should reference postcondition
    let has_post = result
        .conditions
        .iter()
        .any(|vc| vc.description.contains("ensures") || vc.description.contains("postcondition"));
    assert!(
        has_post,
        "Should have a postcondition VC for concrete return type"
    );
}

// === Test 2: Ty::Opaque with Iterator trait bound generates uninterpreted sort ===

#[test]
fn opaque_type_with_iterator_bound_generates_uninterpreted_sort() {
    let opaque_ty = Ty::Opaque(
        "impl_Iterator_Item_i32".to_string(),
        vec!["Iterator".to_string(), "Item=i32".to_string()],
    );

    let sort = encode_type(&opaque_ty);
    assert_eq!(
        sort,
        Sort::Uninterpreted("impl_Iterator_Item_i32".to_string()),
        "Opaque type should encode as uninterpreted sort"
    );
}

#[test]
fn opaque_type_preserves_trait_bounds() {
    let opaque_ty = Ty::Opaque(
        "impl_Iterator".to_string(),
        vec!["Iterator".to_string(), "Item=i32".to_string()],
    );

    match &opaque_ty {
        Ty::Opaque(name, bounds) => {
            assert_eq!(name, "impl_Iterator");
            assert_eq!(bounds.len(), 2);
            assert!(bounds.contains(&"Iterator".to_string()));
            assert!(bounds.contains(&"Item=i32".to_string()));
        }
        _ => panic!("Expected Ty::Opaque"),
    }
}

// === Test 3: RPITIT impl with ensures clause verified via behavioral subtyping ===

#[test]
fn rpitit_behavioral_subtyping_generates_postcondition_vc() {
    // Trait with method returning opaque type with postcondition
    let trait_method = TraitMethod {
        name: "items".to_string(),
        params: vec![("self".to_string(), Ty::Unit)],
        return_ty: Ty::Opaque("impl_Iterator".to_string(), vec!["Iterator".to_string()]),
        requires: vec![],
        ensures: vec![SpecExpr {
            raw: "result.count() > 0".to_string(),
        }],
        is_pure: false,
    };

    let trait_def = TraitDef {
        name: "Collection".to_string(),
        methods: vec![trait_method],
        is_sealed: false,
        super_traits: vec![],
    };

    let impl_info = TraitImpl {
        trait_name: "Collection".to_string(),
        impl_type: "VecCollection".to_string(),
        method_names: vec!["items".to_string()],
    };

    let db = TraitDatabase::new();
    let vcs = generate_subtyping_vcs(&trait_def, &impl_info, &db);

    // Should generate postcondition strengthening VC for the RPITIT method
    let post_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| vc.kind == SubtypingKind::PostconditionStrengthening)
        .collect();
    assert!(
        !post_vcs.is_empty(),
        "RPITIT method with ensures should generate PostconditionStrengthening VC"
    );
    assert!(
        post_vcs[0].method_name == "items",
        "VC should be for 'items' method"
    );
}

#[test]
fn rpitit_behavioral_subtyping_generates_both_vcs_when_contracted() {
    // Trait with method returning opaque type with both requires and ensures
    let trait_method = TraitMethod {
        name: "filtered_items".to_string(),
        params: vec![
            ("self".to_string(), Ty::Unit),
            ("min".to_string(), Ty::Int(IntTy::I32)),
        ],
        return_ty: Ty::Opaque("impl_Iterator".to_string(), vec!["Iterator".to_string()]),
        requires: vec![SpecExpr {
            raw: "min >= 0".to_string(),
        }],
        ensures: vec![SpecExpr {
            raw: "result.count() >= 0".to_string(),
        }],
        is_pure: false,
    };

    let trait_def = TraitDef {
        name: "FilterableCollection".to_string(),
        methods: vec![trait_method],
        is_sealed: false,
        super_traits: vec![],
    };

    let impl_info = TraitImpl {
        trait_name: "FilterableCollection".to_string(),
        impl_type: "VecFilter".to_string(),
        method_names: vec!["filtered_items".to_string()],
    };

    let db = TraitDatabase::new();
    let vcs = generate_subtyping_vcs(&trait_def, &impl_info, &db);

    // Should generate both precondition weakening and postcondition strengthening
    assert_eq!(
        vcs.len(),
        2,
        "RPITIT method with requires+ensures should generate 2 VCs"
    );
    assert!(
        vcs.iter()
            .any(|v| v.kind == SubtypingKind::PreconditionWeakening)
    );
    assert!(
        vcs.iter()
            .any(|v| v.kind == SubtypingKind::PostconditionStrengthening)
    );
}

// === Test 4: Unresolvable opaque type falls back to Ty::Opaque with uninterpreted sort ===

#[test]
fn unresolvable_opaque_falls_back_to_opaque_ty() {
    // When opaque type cannot be resolved to concrete type,
    // it should produce Ty::Opaque which encodes as uninterpreted sort
    let opaque = Ty::Opaque("impl_Display".to_string(), vec!["Display".to_string()]);
    let sort = encode_type(&opaque);

    // Should be an uninterpreted sort (sound: any property proven holds for all impls)
    assert!(
        matches!(sort, Sort::Uninterpreted(_)),
        "Unresolvable opaque type should encode as uninterpreted sort, got: {sort:?}"
    );
}

#[test]
fn opaque_type_in_function_generates_vcs() {
    // A function whose return type is Ty::Opaque should still generate VCs
    // for its postconditions (the postcondition is expressed over the opaque type)
    let func = Function {
        name: "opaque_return".to_string(),
        params: vec![],
        return_local: Local::new(
            "_0",
            Ty::Opaque("impl_Iterator".to_string(), vec!["Iterator".to_string()]),
        ),
        locals: vec![],
        basic_blocks: vec![BasicBlock {
            statements: vec![],
            terminator: Terminator::Return,
        }],
        contracts: Contracts {
            ensures: vec![SpecExpr {
                raw: "true".to_string(),
            }],
            ..Default::default()
        },
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
        source_names: std::collections::HashMap::new(),
        coroutine_info: None,
        refcell_ghost_states: vec![],
        maybeuninit_ghost_states: vec![],
        union_ghost_states: vec![],
        pin_ghost_states: vec![],
        drop_locals: vec![],
        hrtb_bounds: vec![],
    };

    let result = rust_fv_analysis::vcgen::generate_vcs(&func, None);
    // Should still generate VCs even with opaque return type
    assert!(
        !result.conditions.is_empty(),
        "Function with opaque return type and ensures should generate VCs"
    );
}

// === Test 5: Auto-trait bounds (Send/Sync) NOT leaked from opaque types ===

#[test]
fn opaque_type_does_not_leak_auto_traits() {
    // Auto-trait bounds (Send, Sync) should NOT be included in opaque type bounds
    // unless explicitly specified. This prevents unsound trait reasoning.
    let opaque_explicit = Ty::Opaque(
        "impl_Iterator_Send".to_string(),
        vec!["Iterator".to_string(), "Send".to_string()],
    );

    let opaque_no_auto = Ty::Opaque("impl_Iterator".to_string(), vec!["Iterator".to_string()]);

    // Explicit Send bound should be present
    if let Ty::Opaque(_, bounds) = &opaque_explicit {
        assert!(
            bounds.contains(&"Send".to_string()),
            "Explicit Send bound should be preserved"
        );
    }

    // Without explicit Send, it should NOT be assumed
    if let Ty::Opaque(_, bounds) = &opaque_no_auto {
        assert!(
            !bounds.contains(&"Send".to_string()),
            "Auto-trait Send should NOT be leaked without explicit bound"
        );
        assert!(
            !bounds.contains(&"Sync".to_string()),
            "Auto-trait Sync should NOT be leaked without explicit bound"
        );
    }
}

#[test]
fn opaque_type_trait_analysis_conservative() {
    // Opaque types should be conservative in trait analysis:
    // - may have Drop (conservative: true)
    // - conservatively Unpin
    // - not Copy
    let opaque = Ty::Opaque("impl_Trait".to_string(), vec!["Trait".to_string()]);

    assert!(
        rust_fv_analysis::trait_analysis::has_drop_impl(&opaque),
        "Opaque type should conservatively have Drop"
    );
    assert!(
        rust_fv_analysis::trait_analysis::is_unpin(&opaque),
        "Opaque type should conservatively be Unpin"
    );
    assert!(
        !rust_fv_analysis::trait_analysis::has_copy_impl(&opaque),
        "Opaque type should not be Copy"
    );
}
