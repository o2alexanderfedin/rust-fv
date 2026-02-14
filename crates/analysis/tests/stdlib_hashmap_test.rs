//! Tests for HashMap<K,V> standard library contracts.
//!
//! These tests verify that HashMap contracts model mathematical map abstraction
//! with proper frame conditions (unmodified entries remain unchanged).

use rust_fv_analysis::stdlib_contracts::{ContractSource, StdlibContractRegistry};

/// Test that HashMap::insert contract exists and has correct properties.
///
/// Expected contract:
/// - post: get(key) == Some(value)
/// - post: forall k != key: get(k) == old(get(k))  [frame condition]
/// - post: if key was new, len() == old(len()) + 1
/// - post: if key existed, len() == old(len())
#[test]
fn test_hashmap_insert_contract() {
    let mut registry = StdlibContractRegistry::new();
    rust_fv_analysis::stdlib_contracts::hashmap::register_hashmap_contracts(&mut registry);

    let contract = registry
        .get("HashMap::insert")
        .expect("HashMap::insert contract should exist");

    assert_eq!(contract.method_name, "insert");
    assert_eq!(contract.type_path, "std::collections::HashMap");
    assert_eq!(contract.source, ContractSource::Builtin);

    // Should have postconditions for:
    // 1. get(key) == Some(value)
    // 2. Frame condition (other entries unchanged)
    // 3. Length changes appropriately
    assert!(
        !contract.summary.contracts.ensures.is_empty(),
        "insert must have postconditions"
    );

    // Check that key postcondition mentions 'get' or similar
    let postconds = &contract.summary.contracts.ensures;
    let has_get_postcond = postconds
        .iter()
        .any(|e| e.raw.contains("get") || e.raw.contains("lookup"));
    assert!(
        has_get_postcond,
        "insert postcondition should mention get/lookup"
    );
}

/// Test that HashMap::get contract exists and is pure.
///
/// Expected contract:
/// - pure: true
/// - post: result == model.lookup(key)
#[test]
fn test_hashmap_get_contract() {
    let mut registry = StdlibContractRegistry::new();
    rust_fv_analysis::stdlib_contracts::hashmap::register_hashmap_contracts(&mut registry);

    let contract = registry
        .get("HashMap::get")
        .expect("HashMap::get contract should exist");

    assert_eq!(contract.method_name, "get");
    assert!(
        contract.summary.contracts.is_pure,
        "HashMap::get must be pure (no side effects)"
    );
}

/// Test that HashMap::remove contract exists and has correct properties.
///
/// Expected contract:
/// - post: get(key) == None
/// - post: forall k != key: get(k) == old(get(k))  [frame condition]
/// - post: if key existed, len() == old(len()) - 1
/// - post: if key didn't exist, len() == old(len())
#[test]
fn test_hashmap_remove_contract() {
    let mut registry = StdlibContractRegistry::new();
    rust_fv_analysis::stdlib_contracts::hashmap::register_hashmap_contracts(&mut registry);

    let contract = registry
        .get("HashMap::remove")
        .expect("HashMap::remove contract should exist");

    assert_eq!(contract.method_name, "remove");

    // Should have postconditions including frame condition
    assert!(
        !contract.summary.contracts.ensures.is_empty(),
        "remove must have postconditions"
    );

    let postconds = &contract.summary.contracts.ensures;
    let has_none_postcond = postconds
        .iter()
        .any(|e| e.raw.contains("None") || e.raw.contains("null"));
    assert!(
        has_none_postcond,
        "remove postcondition should ensure key maps to None"
    );
}

/// Test that HashMap::contains_key contract exists and is pure.
///
/// Expected contract:
/// - pure: true
/// - post: result == get(key).is_some()
#[test]
fn test_hashmap_contains_key_contract() {
    let mut registry = StdlibContractRegistry::new();
    rust_fv_analysis::stdlib_contracts::hashmap::register_hashmap_contracts(&mut registry);

    let contract = registry
        .get("HashMap::contains_key")
        .expect("HashMap::contains_key contract should exist");

    assert_eq!(contract.method_name, "contains_key");
    assert!(
        contract.summary.contracts.is_pure,
        "HashMap::contains_key must be pure"
    );
}

/// Test that HashMap::len contract exists and is pure.
#[test]
fn test_hashmap_len_contract() {
    let mut registry = StdlibContractRegistry::new();
    rust_fv_analysis::stdlib_contracts::hashmap::register_hashmap_contracts(&mut registry);

    let contract = registry
        .get("HashMap::len")
        .expect("HashMap::len contract should exist");

    assert_eq!(contract.method_name, "len");
    assert!(
        contract.summary.contracts.is_pure,
        "HashMap::len must be pure"
    );
}

/// Test that HashMap::is_empty contract exists and is pure.
///
/// Expected contract:
/// - pure: true
/// - post: result == (len() == 0)
#[test]
fn test_hashmap_is_empty_contract() {
    let mut registry = StdlibContractRegistry::new();
    rust_fv_analysis::stdlib_contracts::hashmap::register_hashmap_contracts(&mut registry);

    let contract = registry
        .get("HashMap::is_empty")
        .expect("HashMap::is_empty contract should exist");

    assert_eq!(contract.method_name, "is_empty");
    assert!(
        contract.summary.contracts.is_pure,
        "HashMap::is_empty must be pure"
    );

    // Postcondition should relate to len
    let postconds = &contract.summary.contracts.ensures;
    let relates_to_len = postconds.iter().any(|e| e.raw.contains("len"));
    assert!(relates_to_len, "is_empty should relate to len() == 0");
}

/// Test that HashMap::clear contract exists.
///
/// Expected contract:
/// - post: len() == 0
/// - post: forall k: get(k) == None
#[test]
fn test_hashmap_clear_contract() {
    let mut registry = StdlibContractRegistry::new();
    rust_fv_analysis::stdlib_contracts::hashmap::register_hashmap_contracts(&mut registry);

    let contract = registry
        .get("HashMap::clear")
        .expect("HashMap::clear contract should exist");

    assert_eq!(contract.method_name, "clear");

    // Should have postconditions for empty state
    assert!(
        !contract.summary.contracts.ensures.is_empty(),
        "clear must have postconditions"
    );

    let postconds = &contract.summary.contracts.ensures;
    let has_len_postcond = postconds.iter().any(|e| e.raw.contains("len"));
    assert!(
        has_len_postcond,
        "clear postcondition should mention len == 0"
    );
}
