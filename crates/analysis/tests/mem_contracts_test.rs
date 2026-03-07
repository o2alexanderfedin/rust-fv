//! Tests for std::mem stdlib contract registration.
//!
//! Verifies that:
//! - register_mem_contracts registers contracts for all mem functions
//! - mem::swap has a_post == b_pre && b_post == a_pre postcondition
//! - mem::replace has result == old(place) && place_post == new_val postcondition
//! - mem::forget is modeled as no-op (postcondition is true)
//! - mem::size_of/align_of have result > 0 postcondition
//! - All mem contracts load via load_default_contracts

use rust_fv_analysis::stdlib_contracts::StdlibContractRegistry;
use rust_fv_analysis::stdlib_contracts::mem::register_mem_contracts;

#[test]
fn register_mem_contracts_registers_all_methods() {
    let mut registry = StdlibContractRegistry::new();
    register_mem_contracts(&mut registry);

    // Should register 5 contracts: swap, replace, forget, size_of, align_of
    let expected_methods = [
        "mem::swap",
        "mem::replace",
        "mem::forget",
        "mem::size_of",
        "mem::align_of",
    ];

    for method in &expected_methods {
        assert!(
            registry.get(method).is_some(),
            "Expected contract for '{}' to be registered",
            method
        );
    }
}

#[test]
fn mem_swap_has_value_exchange_postcondition() {
    let mut registry = StdlibContractRegistry::new();
    register_mem_contracts(&mut registry);

    let contract = registry.get("mem::swap").unwrap();
    let ensures: Vec<&str> = contract
        .summary
        .contracts
        .ensures
        .iter()
        .map(|s| s.raw.as_str())
        .collect();

    // Must have a_post == b_pre && b_post == a_pre
    let has_exchange = ensures
        .iter()
        .any(|e| e.contains("a") && e.contains("b") && e.contains("old"));
    assert!(
        has_exchange,
        "mem::swap should have value exchange postcondition, got: {:?}",
        ensures
    );
}

#[test]
fn mem_replace_has_correct_postcondition() {
    let mut registry = StdlibContractRegistry::new();
    register_mem_contracts(&mut registry);

    let contract = registry.get("mem::replace").unwrap();
    let ensures: Vec<&str> = contract
        .summary
        .contracts
        .ensures
        .iter()
        .map(|s| s.raw.as_str())
        .collect();

    // Must have result == old(dest) && dest_post == src
    let has_result_old = ensures
        .iter()
        .any(|e| e.contains("result") && e.contains("old"));
    let has_dest_new = ensures
        .iter()
        .any(|e| e.contains("dest") && e.contains("src"));
    assert!(
        has_result_old,
        "mem::replace should have result == old(dest) postcondition, got: {:?}",
        ensures
    );
    assert!(
        has_dest_new,
        "mem::replace should have dest == src postcondition, got: {:?}",
        ensures
    );
}

#[test]
fn mem_forget_is_noop() {
    let mut registry = StdlibContractRegistry::new();
    register_mem_contracts(&mut registry);

    let contract = registry.get("mem::forget").unwrap();
    let ensures: Vec<&str> = contract
        .summary
        .contracts
        .ensures
        .iter()
        .map(|s| s.raw.as_str())
        .collect();

    // forget is modeled as no-op: postcondition is just "true"
    let has_true = ensures.iter().any(|e| e.contains("true"));
    assert!(
        has_true,
        "mem::forget should have postcondition 'true' (no-op), got: {:?}",
        ensures
    );
}

#[test]
fn mem_size_of_has_positive_result() {
    let mut registry = StdlibContractRegistry::new();
    register_mem_contracts(&mut registry);

    let contract = registry.get("mem::size_of").unwrap();
    let ensures: Vec<&str> = contract
        .summary
        .contracts
        .ensures
        .iter()
        .map(|s| s.raw.as_str())
        .collect();

    let has_positive = ensures
        .iter()
        .any(|e| e.contains("result") && e.contains("> 0"));
    assert!(
        has_positive,
        "mem::size_of should have result > 0 postcondition, got: {:?}",
        ensures
    );
}

#[test]
fn mem_align_of_has_positive_result() {
    let mut registry = StdlibContractRegistry::new();
    register_mem_contracts(&mut registry);

    let contract = registry.get("mem::align_of").unwrap();
    let ensures: Vec<&str> = contract
        .summary
        .contracts
        .ensures
        .iter()
        .map(|s| s.raw.as_str())
        .collect();

    let has_positive = ensures
        .iter()
        .any(|e| e.contains("result") && e.contains("> 0"));
    assert!(
        has_positive,
        "mem::align_of should have result > 0 postcondition, got: {:?}",
        ensures
    );
}

#[test]
fn mem_contracts_have_correct_type_path() {
    let mut registry = StdlibContractRegistry::new();
    register_mem_contracts(&mut registry);

    let contract = registry.get("mem::swap").unwrap();
    assert_eq!(contract.type_path, "std::mem");
    assert_eq!(contract.method_name, "swap");
}

#[test]
fn mem_contracts_load_via_default_loader() {
    let registry = rust_fv_analysis::stdlib_contracts::loader::load_default_contracts();

    // mem contracts should be available after loading defaults
    assert!(
        registry.get("mem::swap").is_some(),
        "mem::swap should be available via load_default_contracts"
    );
    assert!(
        registry.get("mem::replace").is_some(),
        "mem::replace should be available via load_default_contracts"
    );
}

#[test]
fn mem_swap_is_not_pure() {
    let mut registry = StdlibContractRegistry::new();
    register_mem_contracts(&mut registry);

    let contract = registry.get("mem::swap").unwrap();
    assert!(
        !contract.summary.contracts.is_pure,
        "mem::swap modifies its arguments and should not be pure"
    );
}

#[test]
fn mem_size_of_is_pure() {
    let mut registry = StdlibContractRegistry::new();
    register_mem_contracts(&mut registry);

    let contract = registry.get("mem::size_of").unwrap();
    assert!(
        contract.summary.contracts.is_pure,
        "mem::size_of is a compile-time constant and should be pure"
    );
}
