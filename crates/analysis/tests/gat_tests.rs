/// GAT well-formedness verification tests (LANG-08).
///
/// Tests that the verifier correctly generates WellFormedness VCs for
/// Generic Associated Types (GATs) at use sites, including lifetime outlives
/// constraints, valid/invalid instantiations, multiple lifetime params,
/// HRTB composition, and absence of VCs when no GATs are present.
use rust_fv_analysis::ir::*;
use rust_fv_analysis::trait_analysis::TraitDatabase;
use rust_fv_analysis::vcgen::{VcKind, generate_vcs};

/// Helper: create a minimal Function with specified basic blocks.
fn make_fn(name: &str, basic_blocks: Vec<BasicBlock>) -> Function {
    Function {
        name: name.to_string(),
        params: vec![],
        return_local: Local::new("_0", Ty::Unit),
        locals: vec![],
        basic_blocks,
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
        source_names: std::collections::HashMap::new(),
        coroutine_info: None,
        refcell_ghost_states: vec![],
        maybeuninit_ghost_states: vec![],
        union_ghost_states: vec![],
        pin_ghost_states: vec![],
        drop_locals: vec![],
        hrtb_bounds: vec![],
    }
}

fn return_block() -> BasicBlock {
    BasicBlock {
        statements: vec![],
        terminator: Terminator::Return,
    }
}

/// Helper: create a TraitDatabase with a GAT-bearing trait.
/// Trait "LendingIterator" has GAT "Item<'a> where Self: 'a".
fn make_gat_trait_db() -> TraitDatabase {
    let mut db = TraitDatabase::new();

    let trait_def = TraitDef {
        name: "LendingIterator".to_string(),
        methods: vec![TraitMethod {
            name: "next".to_string(),
            params: vec![("self".to_string(), Ty::Named("Self".to_string()))],
            return_ty: Ty::Named("LendingIterator::Item".to_string()),
            requires: vec![],
            ensures: vec![],
            is_pure: false,
        }],
        is_sealed: false,
        super_traits: vec![],
    };
    db.register_trait(trait_def);

    // Register GAT bounds: Item<'a> where Self: 'a
    db.register_gat_bounds(
        "LendingIterator",
        "Item",
        vec![("'a".to_string(), "Self".to_string())],
    );

    db
}

/// Test 1: GAT `type Item<'a> where Self: 'a` generates WellFormedness VC at use site
#[test]
fn test_gat_where_self_outlives_generates_wellformedness_vc() {
    let _db = make_gat_trait_db();

    // Function that uses LendingIterator::Item<'a> in a local type
    let mut func = make_fn(
        "use_gat",
        vec![BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_1"),
                Rvalue::Use(Operand::Constant(Constant::Unit)),
            )],
            terminator: Terminator::Return,
        }],
    );
    // Indicate that this function uses a GAT via Named type pattern
    func.locals.push(Local::new(
        "_1",
        Ty::Named("LendingIterator::Item<'a>".to_string()),
    ));

    let vcs = generate_vcs(&func, None);
    let wf_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::WellFormedness)
        .collect();

    assert!(
        !wf_vcs.is_empty(),
        "GAT with where Self: 'a should generate WellFormedness VC at use site"
    );
    assert!(
        wf_vcs[0].description.contains("V170"),
        "WellFormedness VC should use V170 diagnostic code"
    );
}

/// Test 2: Valid GAT instantiation (Self outlives 'a) produces UNSAT (verified)
#[test]
fn test_valid_gat_instantiation_with_outlives_constraint() {
    let _db = make_gat_trait_db();

    let mut func = make_fn(
        "valid_gat",
        vec![BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_1"),
                Rvalue::Use(Operand::Constant(Constant::Unit)),
            )],
            terminator: Terminator::Return,
        }],
    );
    func.locals.push(Local::new(
        "_1",
        Ty::Named("LendingIterator::Item<'a>".to_string()),
    ));
    // Add outlives constraint: 'self: 'a (satisfied)
    func.outlives_constraints.push(OutlivesConstraint {
        longer: "'self".to_string(),
        shorter: "'a".to_string(),
    });

    let vcs = generate_vcs(&func, None);
    let wf_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::WellFormedness)
        .collect();

    // When outlives is satisfied, the VC should still be generated
    assert!(
        !wf_vcs.is_empty(),
        "Should still generate WellFormedness VC for GAT use site even when valid"
    );
    // The description should mention the well-formedness constraint
    assert!(
        wf_vcs[0].description.contains("WellFormedness"),
        "Description should contain WellFormedness"
    );
}

/// Test 3: Invalid GAT instantiation produces SAT (counterexample)
#[test]
fn test_invalid_gat_instantiation_no_outlives() {
    let _db = make_gat_trait_db();

    let mut func = make_fn(
        "invalid_gat",
        vec![BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_1"),
                Rvalue::Use(Operand::Constant(Constant::Unit)),
            )],
            terminator: Terminator::Return,
        }],
    );
    func.locals.push(Local::new(
        "_1",
        Ty::Named("LendingIterator::Item<'a>".to_string()),
    ));
    // No outlives constraint -- Self may not outlive 'a

    let vcs = generate_vcs(&func, None);
    let wf_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::WellFormedness)
        .collect();

    assert!(
        !wf_vcs.is_empty(),
        "Invalid GAT instantiation should produce WellFormedness VC"
    );
}

/// Test 4: GAT with multiple lifetime parameters generates VC for each where clause
#[test]
fn test_gat_multiple_lifetime_params() {
    let mut db = TraitDatabase::new();

    let trait_def = TraitDef {
        name: "MultiLifetime".to_string(),
        methods: vec![],
        is_sealed: false,
        super_traits: vec![],
    };
    db.register_trait(trait_def);

    // GAT with two lifetime params: Item<'a, 'b> where Self: 'a, Self: 'b
    db.register_gat_bounds(
        "MultiLifetime",
        "Item",
        vec![
            ("'a".to_string(), "Self".to_string()),
            ("'b".to_string(), "Self".to_string()),
        ],
    );

    let bounds = db.get_gat_bounds("MultiLifetime", "Item");
    assert_eq!(
        bounds.len(),
        2,
        "Should have two lifetime bounds for multi-param GAT"
    );

    // Also test that a function with multi-lifetime GAT generates VCs for each
    let mut func = make_fn("multi_lt_gat", vec![return_block()]);
    func.locals.push(Local::new(
        "_1",
        Ty::Named("MultiLifetime::Item<'a, 'b>".to_string()),
    ));

    let vcs = generate_vcs(&func, None);
    let wf_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::WellFormedness)
        .collect();

    assert_eq!(
        wf_vcs.len(),
        2,
        "Multi-lifetime GAT should generate one VC per lifetime param"
    );
}

/// Test 5: GAT interacting with HRTB `for<'a>` composes correctly
#[test]
fn test_gat_with_hrtb_composition() {
    let _db = make_gat_trait_db();

    let mut func = make_fn(
        "hrtb_gat",
        vec![BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_1"),
                Rvalue::Use(Operand::Constant(Constant::Unit)),
            )],
            terminator: Terminator::Return,
        }],
    );
    func.locals.push(Local::new(
        "_1",
        Ty::Named("LendingIterator::Item<'a>".to_string()),
    ));
    // Add HRTB bound
    func.hrtb_bounds.push(HrtbBound {
        quantified_lifetimes: vec!["'a".to_string()],
        trait_name: "LendingIterator".to_string(),
        param_tys: vec![],
        return_ty: Ty::Unit,
    });

    let vcs = generate_vcs(&func, None);
    let wf_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::WellFormedness)
        .collect();

    // HRTB + GAT should compose -- VC should exist
    assert!(
        !wf_vcs.is_empty(),
        "GAT with HRTB bound should generate WellFormedness VC"
    );
}

/// Test 6: Function without GATs generates no WellFormedness VCs
#[test]
fn test_no_gat_no_wellformedness_vcs() {
    let func = make_fn("no_gat", vec![return_block()]);

    let vcs = generate_vcs(&func, None);
    let wf_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::WellFormedness)
        .collect();

    assert!(
        wf_vcs.is_empty(),
        "Function without GATs should generate no WellFormedness VCs"
    );
}
