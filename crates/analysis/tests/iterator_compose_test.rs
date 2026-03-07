//! Tests for iterator adapter contract composition.
//!
//! Verifies:
//! - A chain filter(pred).map(f) produces composed contracts
//! - Element-level postconditions compose through filter and map
//! - Composed contracts produce SMT terms (not BoolLit(true) fallbacks)
//! - Single adapter (no chaining) still works correctly
//! - Three-adapter chain (filter.map.take) composes all three contracts

use rust_fv_analysis::contract_db::ContractDatabase;
use rust_fv_analysis::ir::*;
use rust_fv_analysis::stdlib_contracts::StdlibContractRegistry;
use rust_fv_analysis::stdlib_contracts::iterator::{
    compose_adapter_contracts, register_iterator_contracts,
};
use rust_fv_analysis::stdlib_contracts::loader::load_default_contracts;
use rust_fv_analysis::vcgen;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn make_iterator_registry() -> StdlibContractRegistry {
    let mut registry = StdlibContractRegistry::new();
    register_iterator_contracts(&mut registry);
    registry
}

// ---------------------------------------------------------------------------
// Test 1: filter.map chain produces composed contracts
// ---------------------------------------------------------------------------

#[test]
fn iterator_compose_filter_map_chain() {
    let registry = make_iterator_registry();

    let filter_contract = registry.get("Iterator::filter").unwrap();
    let map_contract = registry.get("Iterator::map").unwrap();

    let adapters = vec![
        ("filter".to_string(), filter_contract),
        ("map".to_string(), map_contract),
    ];

    let composed = compose_adapter_contracts(&adapters);

    // The composed contract should have postconditions
    assert!(
        !composed.ensures.is_empty(),
        "Composed filter.map should have postconditions"
    );

    // filter: seq_len <= original; map: seq_len == input_len
    // composed: seq_len <= original (filter dominates length)
    let all_ensures: String = composed
        .ensures
        .iter()
        .map(|e| e.raw.as_str())
        .collect::<Vec<_>>()
        .join("; ");

    assert!(
        all_ensures.contains("seq_len"),
        "Composed contract should mention seq_len, got: {}",
        all_ensures
    );
}

// ---------------------------------------------------------------------------
// Test 2: Element-level postconditions compose
// ---------------------------------------------------------------------------

#[test]
fn iterator_compose_element_level_postconditions() {
    let registry = make_iterator_registry();

    let filter_contract = registry.get("Iterator::filter").unwrap();
    let map_contract = registry.get("Iterator::map").unwrap();

    let adapters = vec![
        ("filter".to_string(), filter_contract),
        ("map".to_string(), map_contract),
    ];

    let composed = compose_adapter_contracts(&adapters);

    // Should have element-level postconditions from both filter and map
    let has_element_ensures = composed.ensures.iter().any(|e| {
        e.raw.contains("element") || e.raw.contains("forall") || e.raw.contains("predicate")
    });

    assert!(
        has_element_ensures,
        "Composed contract should include element-level postconditions"
    );
}

// ---------------------------------------------------------------------------
// Test 3: Composed contracts are not BoolLit(true) fallbacks
// ---------------------------------------------------------------------------

#[test]
fn iterator_compose_not_bool_true_fallback() {
    let registry = make_iterator_registry();

    let filter_contract = registry.get("Iterator::filter").unwrap();
    let map_contract = registry.get("Iterator::map").unwrap();

    let adapters = vec![
        ("filter".to_string(), filter_contract),
        ("map".to_string(), map_contract),
    ];

    let composed = compose_adapter_contracts(&adapters);

    // Verify that no ensures clause is just "true" (a BoolLit fallback)
    for ensure in &composed.ensures {
        assert_ne!(
            ensure.raw, "true",
            "Composed contracts should NOT be BoolLit(true) fallbacks"
        );
    }

    // Must have at least one real postcondition
    assert!(
        !composed.ensures.is_empty(),
        "Composed contracts must have real postconditions"
    );
}

// ---------------------------------------------------------------------------
// Test 4: Single adapter (no chaining) works correctly
// ---------------------------------------------------------------------------

#[test]
fn iterator_compose_single_adapter() {
    let registry = make_iterator_registry();

    let filter_contract = registry.get("Iterator::filter").unwrap();

    let adapters = vec![("filter".to_string(), filter_contract)];

    let composed = compose_adapter_contracts(&adapters);

    // Single adapter should just return its own contract
    assert!(
        !composed.ensures.is_empty(),
        "Single adapter should have postconditions"
    );

    // filter postcondition: seq_len <= original
    let has_filter = composed
        .ensures
        .iter()
        .any(|e| e.raw.contains("seq_len") && e.raw.contains("<="));

    assert!(
        has_filter,
        "Single filter adapter should have seq_len <= postcondition"
    );
}

// ---------------------------------------------------------------------------
// Test 5: Three-adapter chain (filter.map.take) composes all three
// ---------------------------------------------------------------------------

#[test]
fn iterator_compose_three_adapter_chain() {
    let registry = make_iterator_registry();

    let filter_contract = registry.get("Iterator::filter").unwrap();
    let map_contract = registry.get("Iterator::map").unwrap();
    let take_contract = registry.get("Iterator::take").unwrap();

    let adapters = vec![
        ("filter".to_string(), filter_contract),
        ("map".to_string(), map_contract),
        ("take".to_string(), take_contract),
    ];

    let composed = compose_adapter_contracts(&adapters);

    // Three adapter chain should have postconditions from all three
    assert!(
        composed.ensures.len() >= 3,
        "Three-adapter chain should have at least 3 postconditions, got {}",
        composed.ensures.len()
    );

    let all_ensures: String = composed
        .ensures
        .iter()
        .map(|e| e.raw.as_str())
        .collect::<Vec<_>>()
        .join("; ");

    // Should reference seq_len (from filter and map)
    assert!(
        all_ensures.contains("seq_len"),
        "Three-adapter chain should reference seq_len"
    );

    // Should reference take's min constraint
    assert!(
        all_ensures.contains("min") || all_ensures.contains("take"),
        "Three-adapter chain should reference take's constraint, got: {}",
        all_ensures
    );
}

// ---------------------------------------------------------------------------
// VCGen Integration Tests
// ---------------------------------------------------------------------------

/// Build a function with MIR representing `iter.filter(pred).map(f)`:
///   bb0: call _1 = Iterator::filter(iter, pred) -> bb1
///   bb1: call _2 = Iterator::map(_1, f) -> bb2
///   bb2: call _3 = Iterator::collect(_2) -> bb3
///   bb3: return
fn build_adapter_chain_mir() -> Function {
    let return_ty = Ty::Named("Vec_i32".to_string());

    Function {
        name: "adapter_chain_fn".to_string(),
        return_local: Local::new("_0", return_ty),
        params: vec![Local::new("iter", Ty::Named("IntoIter_i32".to_string()))],
        locals: vec![
            Local::new("_1", Ty::Named("Filter_i32".to_string())),
            Local::new("_2", Ty::Named("Map_i32".to_string())),
            Local::new("_3", Ty::Named("Vec_i32".to_string())),
        ],
        basic_blocks: vec![
            // bb0: call Iterator::filter(iter, pred) -> bb1
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Call {
                    func: "Iterator::filter".to_string(),
                    args: vec![
                        Operand::Move(Place::local("iter")),
                        Operand::Copy(Place::local("pred")),
                    ],
                    destination: Place::local("_1"),
                    target: 1,
                },
            },
            // bb1: call Iterator::map(_1, f) -> bb2
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Call {
                    func: "Iterator::map".to_string(),
                    args: vec![
                        Operand::Move(Place::local("_1")),
                        Operand::Copy(Place::local("f")),
                    ],
                    destination: Place::local("_2"),
                    target: 2,
                },
            },
            // bb2: call Iterator::collect(_2) -> bb3
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Call {
                    func: "Iterator::collect".to_string(),
                    args: vec![Operand::Move(Place::local("_2"))],
                    destination: Place::local("_3"),
                    target: 3,
                },
            },
            // bb3: assign and return
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Move(Place::local("_3"))),
                )],
                terminator: Terminator::Return,
            },
        ],
        contracts: Contracts {
            requires: vec![],
            ensures: vec![SpecExpr {
                raw: "true".to_string(),
            }],
            invariants: vec![],
            is_pure: false,
            decreases: None,
            fn_specs: vec![],
            state_invariant: None,
            is_inferred: false,
        },
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
        loops: vec![],
    }
}

// ---------------------------------------------------------------------------
// Test 6: VCGen chain produces composed VCs with seq_len postconditions
// ---------------------------------------------------------------------------

#[test]
fn iterator_compose_vcgen_chain_produces_composed_vcs() {
    let func = build_adapter_chain_mir();

    let mut db = ContractDatabase::new();
    let registry = load_default_contracts();
    registry.merge_into(&mut db);

    let vcs = vcgen::generate_vcs(&func, Some(&db));

    // Get postcondition VCs — these contain callee postcondition assumptions
    let postcondition_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| {
            matches!(
                vc.location.vc_kind,
                rust_fv_analysis::vcgen::VcKind::Postcondition
            )
        })
        .collect();

    assert!(
        !postcondition_vcs.is_empty(),
        "Should generate postcondition VCs for adapter chain function"
    );

    // Serialize postcondition VC scripts and check for seq_len (from iterator contracts)
    let all_scripts: String = postcondition_vcs
        .iter()
        .map(|vc| format!("{:?}", vc.script))
        .collect::<Vec<_>>()
        .join("\n");

    assert!(
        all_scripts.contains("seq_len"),
        "Iterator adapter chain VCs should contain seq_len postconditions, not BoolLit(true). Got:\n{}",
        all_scripts
    );
}

// ---------------------------------------------------------------------------
// Test 7: Single adapter uses direct contract without composition
// ---------------------------------------------------------------------------

#[test]
fn iterator_compose_vcgen_single_adapter_uses_direct_contract() {
    // Build a function with just Iterator::filter (no chain)
    let func = Function {
        name: "single_adapter_fn".to_string(),
        return_local: Local::new("_0", Ty::Named("Filter_i32".to_string())),
        params: vec![Local::new("iter", Ty::Named("IntoIter_i32".to_string()))],
        locals: vec![Local::new("_1", Ty::Named("Filter_i32".to_string()))],
        basic_blocks: vec![
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Call {
                    func: "Iterator::filter".to_string(),
                    args: vec![
                        Operand::Move(Place::local("iter")),
                        Operand::Copy(Place::local("pred")),
                    ],
                    destination: Place::local("_1"),
                    target: 1,
                },
            },
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Move(Place::local("_1"))),
                )],
                terminator: Terminator::Return,
            },
        ],
        contracts: Contracts {
            requires: vec![],
            ensures: vec![SpecExpr {
                raw: "true".to_string(),
            }],
            invariants: vec![],
            is_pure: false,
            decreases: None,
            fn_specs: vec![],
            state_invariant: None,
            is_inferred: false,
        },
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
        loops: vec![],
    };

    let mut db = ContractDatabase::new();
    let registry = load_default_contracts();
    registry.merge_into(&mut db);

    let vcs = vcgen::generate_vcs(&func, Some(&db));

    // Single adapter should still get postcondition from Iterator::filter
    let postcondition_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| {
            matches!(
                vc.location.vc_kind,
                rust_fv_analysis::vcgen::VcKind::Postcondition
            )
        })
        .collect();

    let all_scripts: String = postcondition_vcs
        .iter()
        .map(|vc| format!("{:?}", vc.script))
        .collect::<Vec<_>>()
        .join("\n");

    assert!(
        all_scripts.contains("seq_len"),
        "Single iterator adapter should use direct contract with seq_len, not BoolLit(true). Got:\n{}",
        all_scripts
    );
}
