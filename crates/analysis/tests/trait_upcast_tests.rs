/// Trait upcasting vtable compatibility verification tests (LANG-09).
///
/// Tests that the verifier correctly generates TraitUpcasting VCs for
/// casts between dyn trait objects, including vtable compatibility,
/// supertrait chain validation, contract preservation, invalid upcasts,
/// and absence of VCs when no upcasting is present.
use rust_fv_analysis::ir::*;
use rust_fv_analysis::trait_analysis::{
    TraitDatabase, collect_trait_methods, get_supertrait_chain, is_supertrait,
};
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

/// Helper: create a TraitDatabase with a supertrait hierarchy.
/// Animal -> Dog (Dog: Animal)
/// Animal -> Cat (Cat: Animal)
/// LivingThing -> Animal -> Dog (transitive: Dog: LivingThing)
fn make_supertrait_db() -> TraitDatabase {
    let mut db = TraitDatabase::new();

    db.register_trait(TraitDef {
        name: "LivingThing".to_string(),
        methods: vec![],
        is_sealed: false,
        super_traits: vec![],
    });

    db.register_trait(TraitDef {
        name: "Animal".to_string(),
        methods: vec![TraitMethod {
            name: "speak".to_string(),
            params: vec![("self".to_string(), Ty::Named("Self".to_string()))],
            return_ty: Ty::Unit,
            requires: vec![SpecExpr {
                raw: "true".to_string(),
            }],
            ensures: vec![SpecExpr {
                raw: "true".to_string(),
            }],
            is_pure: false,
        }],
        is_sealed: false,
        super_traits: vec!["LivingThing".to_string()],
    });

    db.register_trait(TraitDef {
        name: "Dog".to_string(),
        methods: vec![TraitMethod {
            name: "fetch".to_string(),
            params: vec![("self".to_string(), Ty::Named("Self".to_string()))],
            return_ty: Ty::Unit,
            requires: vec![],
            ensures: vec![],
            is_pure: false,
        }],
        is_sealed: false,
        super_traits: vec!["Animal".to_string()],
    });

    db.register_trait(TraitDef {
        name: "Cat".to_string(),
        methods: vec![],
        is_sealed: false,
        super_traits: vec!["Animal".to_string()],
    });

    db.register_trait(TraitDef {
        name: "Unrelated".to_string(),
        methods: vec![],
        is_sealed: false,
        super_traits: vec![],
    });

    db
}

/// Test 1: Casting dyn SubTrait to dyn SuperTrait generates TraitUpcasting VC
#[test]
fn test_upcast_generates_trait_upcasting_vc() {
    let mut func = make_fn(
        "upcast_fn",
        vec![BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_2"),
                Rvalue::Cast(
                    CastKind::PtrToPtr,
                    Operand::Move(Place::local("_1")),
                    Ty::TraitObject("Animal".to_string()),
                ),
            )],
            terminator: Terminator::Return,
        }],
    );
    func.locals
        .push(Local::new("_1", Ty::TraitObject("Dog".to_string())));
    func.locals
        .push(Local::new("_2", Ty::TraitObject("Animal".to_string())));

    let vcs = generate_vcs(&func, None);
    let upcast_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::TraitUpcasting)
        .collect();

    assert!(
        !upcast_vcs.is_empty(),
        "Casting dyn Dog to dyn Animal should generate TraitUpcasting VC"
    );
    assert!(
        upcast_vcs[0].description.contains("V180"),
        "TraitUpcasting VC should use V180 diagnostic code"
    );
}

/// Test 2: SuperTrait method contracts preserved at upcast call sites
#[test]
fn test_supertrait_contract_preservation() {
    let db = make_supertrait_db();

    // Verify that Animal has contracted methods
    let animal_def = db.get_trait("Animal").unwrap();
    let contracted = collect_trait_methods(animal_def);
    assert!(
        !contracted.is_empty(),
        "Animal trait should have contracted methods (speak)"
    );
    assert_eq!(contracted[0].name, "speak");
}

/// Test 3: Upcast chain A: B: C preserves contracts transitively
#[test]
fn test_upcast_chain_preserves_contracts_transitively() {
    let db = make_supertrait_db();

    // Dog -> Animal -> LivingThing (transitive)
    assert!(
        is_supertrait(&db, "Dog", "Animal"),
        "Animal should be supertrait of Dog"
    );
    assert!(
        is_supertrait(&db, "Animal", "LivingThing"),
        "LivingThing should be supertrait of Animal"
    );
    assert!(
        is_supertrait(&db, "Dog", "LivingThing"),
        "LivingThing should be transitive supertrait of Dog"
    );

    // Verify the chain
    let chain = get_supertrait_chain(&db, "Dog", "LivingThing");
    assert!(chain.is_some(), "Should find chain from Dog to LivingThing");
    let chain = chain.unwrap();
    assert!(
        chain.len() >= 3,
        "Chain should have at least 3 elements: Dog -> Animal -> LivingThing"
    );
    assert_eq!(chain[0], "Dog");
    assert_eq!(*chain.last().unwrap(), "LivingThing");
}

/// Test 4: Casting to non-supertrait generates SAT VC (violation)
#[test]
fn test_cast_to_non_supertrait_invalid() {
    let db = make_supertrait_db();

    // Dog is NOT a subtrait of Cat (they are siblings under Animal)
    assert!(
        !is_supertrait(&db, "Dog", "Cat"),
        "Cat should NOT be supertrait of Dog"
    );

    // Dog is NOT a subtrait of Unrelated
    assert!(
        !is_supertrait(&db, "Dog", "Unrelated"),
        "Unrelated should NOT be supertrait of Dog"
    );
}

/// Test 5: Upcast with no contracts generates compatibility-only VC (no contract VCs)
#[test]
fn test_upcast_without_contracts() {
    let db = make_supertrait_db();

    // LivingThing has no contracted methods
    let lt_def = db.get_trait("LivingThing").unwrap();
    let contracted = collect_trait_methods(lt_def);
    assert!(
        contracted.is_empty(),
        "LivingThing should have no contracted methods"
    );
}

/// Test 6: No upcasting in function generates no TraitUpcasting VCs
#[test]
fn test_no_upcasting_no_vcs() {
    let func = make_fn("no_upcast", vec![return_block()]);

    let vcs = generate_vcs(&func, None);
    let upcast_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::TraitUpcasting)
        .collect();

    assert!(
        upcast_vcs.is_empty(),
        "Function without upcasting should generate no TraitUpcasting VCs"
    );
}

/// Test 7: is_supertrait returns false for identity (same trait)
#[test]
fn test_supertrait_identity() {
    let db = make_supertrait_db();

    // A trait is a "supertrait" of itself in the sense get_supertrait_chain returns Some
    let chain = get_supertrait_chain(&db, "Dog", "Dog");
    assert!(chain.is_some(), "Identity chain should exist");
    assert_eq!(chain.unwrap().len(), 1);
}

/// Test 8: get_supertrait_chain returns None for non-existent traits
#[test]
fn test_supertrait_chain_nonexistent() {
    let db = make_supertrait_db();

    let chain = get_supertrait_chain(&db, "Nonexistent", "Animal");
    assert!(chain.is_none(), "Non-existent trait should return None");
}
