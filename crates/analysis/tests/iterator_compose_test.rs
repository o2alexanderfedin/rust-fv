//! Tests for iterator adapter contract composition.
//!
//! Verifies:
//! - A chain filter(pred).map(f) produces composed contracts
//! - Element-level postconditions compose through filter and map
//! - Composed contracts produce SMT terms (not BoolLit(true) fallbacks)
//! - Single adapter (no chaining) still works correctly
//! - Three-adapter chain (filter.map.take) composes all three contracts

use rust_fv_analysis::stdlib_contracts::StdlibContractRegistry;
use rust_fv_analysis::stdlib_contracts::iterator::{
    compose_adapter_contracts, register_iterator_contracts,
};

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
