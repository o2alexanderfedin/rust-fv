//! Tests for Vec<T> standard library contracts.

use rust_fv_analysis::{
    contract_db::FunctionSummary,
    ir::{Contracts, IntTy, SpecExpr, Ty},
    stdlib_contracts::{ContractSource, StdlibContract, StdlibContractRegistry},
};

#[test]
fn test_register_vec_contracts_populates_registry() {
    use rust_fv_analysis::stdlib_contracts::vec::register_vec_contracts;

    let mut registry = StdlibContractRegistry::new();
    register_vec_contracts(&mut registry);

    // Check all expected methods are registered
    assert!(registry.get("Vec::push").is_some());
    assert!(registry.get("Vec::pop").is_some());
    assert!(registry.get("Vec::len").is_some());
    assert!(registry.get("Vec::capacity").is_some());
    assert!(registry.get("Vec::get").is_some());
    assert!(registry.get("Vec::reserve").is_some());
    assert!(registry.get("Vec::shrink_to_fit").is_some());
    assert!(registry.get("Vec::is_empty").is_some());
    assert!(registry.get("Vec::clear").is_some());

    // Registry should have at least 9 contracts
    assert!(registry.len() >= 9);
}

#[test]
fn test_vec_push_contract() {
    use rust_fv_analysis::stdlib_contracts::vec::register_vec_contracts;

    let mut registry = StdlibContractRegistry::new();
    register_vec_contracts(&mut registry);

    let contract = registry.get("Vec::push").expect("Vec::push not found");

    // Check source
    assert_eq!(contract.source, ContractSource::Builtin);

    // Check type path
    assert_eq!(contract.type_path, "std::vec::Vec");
    assert_eq!(contract.method_name, "push");

    // Check summary has param names
    let summary = &contract.summary;
    assert_eq!(summary.param_names.len(), 2); // self, value
    assert_eq!(summary.param_names[0], "self");
    assert_eq!(summary.param_names[1], "value");

    // Check postconditions
    // Post: len == old(len) + 1
    // Post: self[old(len)] == value (element-level precision)
    assert!(!summary.contracts.ensures.is_empty());

    // Verify postcondition mentions length increment
    let ensures_raw: Vec<&str> = summary
        .contracts
        .ensures
        .iter()
        .map(|e| e.raw.as_str())
        .collect();

    assert!(
        ensures_raw
            .iter()
            .any(|s| s.contains("len") && s.contains("old") && s.contains("+ 1"))
    );

    // Verify postcondition mentions element assignment
    assert!(
        ensures_raw
            .iter()
            .any(|s| s.contains("seq.nth") || s.contains("self[") || s.contains("value"))
    );
}

#[test]
fn test_vec_pop_contract() {
    use rust_fv_analysis::stdlib_contracts::vec::register_vec_contracts;

    let mut registry = StdlibContractRegistry::new();
    register_vec_contracts(&mut registry);

    let contract = registry.get("Vec::pop").expect("Vec::pop not found");

    let summary = &contract.summary;

    // pop returns Option<T>
    // Post: is_some ==> len == old(len) - 1
    // Post: is_none ==> old(len) == 0
    assert!(!summary.contracts.ensures.is_empty());

    let ensures_raw: Vec<&str> = summary
        .contracts
        .ensures
        .iter()
        .map(|e| e.raw.as_str())
        .collect();

    // Should mention length decrement for Some case
    assert!(ensures_raw.iter().any(|s| s.contains("len")));
}

#[test]
fn test_vec_len_contract() {
    use rust_fv_analysis::stdlib_contracts::vec::register_vec_contracts;

    let mut registry = StdlibContractRegistry::new();
    register_vec_contracts(&mut registry);

    let contract = registry.get("Vec::len").expect("Vec::len not found");

    let summary = &contract.summary;

    // len is pure
    assert!(summary.contracts.is_pure);

    // No preconditions for len
    assert!(summary.contracts.requires.is_empty());
}

#[test]
fn test_vec_capacity_contract() {
    use rust_fv_analysis::stdlib_contracts::vec::register_vec_contracts;

    let mut registry = StdlibContractRegistry::new();
    register_vec_contracts(&mut registry);

    let contract = registry
        .get("Vec::capacity")
        .expect("Vec::capacity not found");

    let summary = &contract.summary;

    // capacity is pure
    assert!(summary.contracts.is_pure);

    // Ensures result >= len (capacity >= len invariant)
    let ensures_raw: Vec<&str> = summary
        .contracts
        .ensures
        .iter()
        .map(|e| e.raw.as_str())
        .collect();

    assert!(
        ensures_raw
            .iter()
            .any(|s| s.contains("result") && s.contains("len"))
    );
}

#[test]
fn test_vec_get_contract() {
    use rust_fv_analysis::stdlib_contracts::vec::register_vec_contracts;

    let mut registry = StdlibContractRegistry::new();
    register_vec_contracts(&mut registry);

    let contract = registry.get("Vec::get").expect("Vec::get not found");

    let summary = &contract.summary;

    // Pre: index < len (or returns None)
    // Post: result == seq_nth(self, index) for Some case
    assert!(!summary.contracts.ensures.is_empty());

    let ensures_raw: Vec<&str> = summary
        .contracts
        .ensures
        .iter()
        .map(|e| e.raw.as_str())
        .collect();

    // Should mention element access
    assert!(
        ensures_raw
            .iter()
            .any(|s| s.contains("seq.nth") || s.contains("index"))
    );
}

#[test]
fn test_vec_reserve_contract() {
    use rust_fv_analysis::stdlib_contracts::vec::register_vec_contracts;

    let mut registry = StdlibContractRegistry::new();
    register_vec_contracts(&mut registry);

    let contract = registry
        .get("Vec::reserve")
        .expect("Vec::reserve not found");

    let summary = &contract.summary;

    // Post: capacity >= old(capacity) + additional
    // Post: len == old(len)
    // Elements preserved
    let ensures_raw: Vec<&str> = summary
        .contracts
        .ensures
        .iter()
        .map(|e| e.raw.as_str())
        .collect();

    assert!(ensures_raw.iter().any(|s| s.contains("capacity")));
    assert!(
        ensures_raw
            .iter()
            .any(|s| s.contains("len") && s.contains("old"))
    );
}

#[test]
fn test_vec_shrink_to_fit_contract() {
    use rust_fv_analysis::stdlib_contracts::vec::register_vec_contracts;

    let mut registry = StdlibContractRegistry::new();
    register_vec_contracts(&mut registry);

    let contract = registry
        .get("Vec::shrink_to_fit")
        .expect("Vec::shrink_to_fit not found");

    let summary = &contract.summary;

    // Post: capacity == len
    // Elements preserved
    let ensures_raw: Vec<&str> = summary
        .contracts
        .ensures
        .iter()
        .map(|e| e.raw.as_str())
        .collect();

    assert!(
        ensures_raw
            .iter()
            .any(|s| s.contains("capacity") && s.contains("len"))
    );
}

#[test]
fn test_vec_is_empty_contract() {
    use rust_fv_analysis::stdlib_contracts::vec::register_vec_contracts;

    let mut registry = StdlibContractRegistry::new();
    register_vec_contracts(&mut registry);

    let contract = registry
        .get("Vec::is_empty")
        .expect("Vec::is_empty not found");

    let summary = &contract.summary;

    // is_empty is pure
    assert!(summary.contracts.is_pure);

    // Post: result == (len == 0)
    let ensures_raw: Vec<&str> = summary
        .contracts
        .ensures
        .iter()
        .map(|e| e.raw.as_str())
        .collect();

    assert!(
        ensures_raw
            .iter()
            .any(|s| s.contains("len") && s.contains("0"))
    );
}

#[test]
fn test_vec_clear_contract() {
    use rust_fv_analysis::stdlib_contracts::vec::register_vec_contracts;

    let mut registry = StdlibContractRegistry::new();
    register_vec_contracts(&mut registry);

    let contract = registry.get("Vec::clear").expect("Vec::clear not found");

    let summary = &contract.summary;

    // Post: len == 0
    let ensures_raw: Vec<&str> = summary
        .contracts
        .ensures
        .iter()
        .map(|e| e.raw.as_str())
        .collect();

    assert!(
        ensures_raw
            .iter()
            .any(|s| s.contains("len") && s.contains("0"))
    );
}
