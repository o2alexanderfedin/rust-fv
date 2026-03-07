//! Tests for std::ptr stdlib contract registration.
//!
//! Verifies that:
//! - register_ptr_contracts registers contracts for all ptr functions
//! - ptr::copy_nonoverlapping has overlap precondition
//! - ptr::copy_nonoverlapping has alignment precondition
//! - ptr::read/write have alignment preconditions
//! - ptr::null/null_mut have result == 0 postconditions
//! - All ptr contracts load via load_default_contracts

use rust_fv_analysis::stdlib_contracts::StdlibContractRegistry;
use rust_fv_analysis::stdlib_contracts::ptr::register_ptr_contracts;

#[test]
fn register_ptr_contracts_registers_all_methods() {
    let mut registry = StdlibContractRegistry::new();
    register_ptr_contracts(&mut registry);

    // Should register 9 contracts: read, write, copy, copy_nonoverlapping,
    // swap, replace, drop_in_place, null, null_mut
    let expected_methods = [
        "ptr::read",
        "ptr::write",
        "ptr::copy",
        "ptr::copy_nonoverlapping",
        "ptr::swap",
        "ptr::replace",
        "ptr::drop_in_place",
        "ptr::null",
        "ptr::null_mut",
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
fn ptr_copy_nonoverlapping_has_overlap_precondition() {
    let mut registry = StdlibContractRegistry::new();
    register_ptr_contracts(&mut registry);

    let contract = registry.get("ptr::copy_nonoverlapping").unwrap();
    let requires: Vec<&str> = contract
        .summary
        .contracts
        .requires
        .iter()
        .map(|s| s.raw.as_str())
        .collect();

    // Must have an overlap check precondition
    let has_overlap = requires.iter().any(|r| {
        r.contains("overlap") || (r.contains("src") && r.contains("dst") && r.contains("count"))
    });
    assert!(
        has_overlap,
        "copy_nonoverlapping should have overlap precondition, got: {:?}",
        requires
    );
}

#[test]
fn ptr_copy_nonoverlapping_has_alignment_precondition() {
    let mut registry = StdlibContractRegistry::new();
    register_ptr_contracts(&mut registry);

    let contract = registry.get("ptr::copy_nonoverlapping").unwrap();
    let requires: Vec<&str> = contract
        .summary
        .contracts
        .requires
        .iter()
        .map(|s| s.raw.as_str())
        .collect();

    // Must have alignment checks for both src and dst
    let has_alignment = requires.iter().any(|r| r.contains("align"));
    assert!(
        has_alignment,
        "copy_nonoverlapping should have alignment precondition, got: {:?}",
        requires
    );
}

#[test]
fn ptr_read_has_alignment_precondition() {
    let mut registry = StdlibContractRegistry::new();
    register_ptr_contracts(&mut registry);

    let contract = registry.get("ptr::read").unwrap();
    let requires: Vec<&str> = contract
        .summary
        .contracts
        .requires
        .iter()
        .map(|s| s.raw.as_str())
        .collect();

    let has_alignment = requires.iter().any(|r| r.contains("align"));
    assert!(
        has_alignment,
        "ptr::read should have alignment precondition, got: {:?}",
        requires
    );
}

#[test]
fn ptr_write_has_alignment_precondition() {
    let mut registry = StdlibContractRegistry::new();
    register_ptr_contracts(&mut registry);

    let contract = registry.get("ptr::write").unwrap();
    let requires: Vec<&str> = contract
        .summary
        .contracts
        .requires
        .iter()
        .map(|s| s.raw.as_str())
        .collect();

    let has_alignment = requires.iter().any(|r| r.contains("align"));
    assert!(
        has_alignment,
        "ptr::write should have alignment precondition, got: {:?}",
        requires
    );
}

#[test]
fn ptr_null_has_result_zero_postcondition() {
    let mut registry = StdlibContractRegistry::new();
    register_ptr_contracts(&mut registry);

    let contract = registry.get("ptr::null").unwrap();
    let ensures: Vec<&str> = contract
        .summary
        .contracts
        .ensures
        .iter()
        .map(|s| s.raw.as_str())
        .collect();

    let has_zero = ensures
        .iter()
        .any(|e| e.contains("result") && e.contains("0"));
    assert!(
        has_zero,
        "ptr::null should have result == 0 postcondition, got: {:?}",
        ensures
    );
}

#[test]
fn ptr_null_mut_has_result_zero_postcondition() {
    let mut registry = StdlibContractRegistry::new();
    register_ptr_contracts(&mut registry);

    let contract = registry.get("ptr::null_mut").unwrap();
    let ensures: Vec<&str> = contract
        .summary
        .contracts
        .ensures
        .iter()
        .map(|s| s.raw.as_str())
        .collect();

    let has_zero = ensures
        .iter()
        .any(|e| e.contains("result") && e.contains("0"));
    assert!(
        has_zero,
        "ptr::null_mut should have result == 0 postcondition, got: {:?}",
        ensures
    );
}

#[test]
fn ptr_contracts_have_correct_type_path() {
    let mut registry = StdlibContractRegistry::new();
    register_ptr_contracts(&mut registry);

    let contract = registry.get("ptr::read").unwrap();
    assert_eq!(contract.type_path, "std::ptr");
    assert_eq!(contract.method_name, "read");
}

#[test]
fn ptr_contracts_load_via_default_loader() {
    let registry = rust_fv_analysis::stdlib_contracts::loader::load_default_contracts();

    // ptr contracts should be available after loading defaults
    assert!(
        registry.get("ptr::read").is_some(),
        "ptr::read should be available via load_default_contracts"
    );
    assert!(
        registry.get("ptr::copy_nonoverlapping").is_some(),
        "ptr::copy_nonoverlapping should be available via load_default_contracts"
    );
}
