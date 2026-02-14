//! Tests for String, str, and slice standard library contracts.
//!
//! These tests verify that String/str are modeled as UTF-8 byte sequences
//! and slice operations have correct length contracts.

use rust_fv_analysis::stdlib_contracts::{ContractSource, StdlibContractRegistry};

/// Test that String::len contract exists and is pure.
///
/// Expected contract:
/// - pure: true
/// - post: result is byte length
#[test]
fn test_string_len_contract() {
    let mut registry = StdlibContractRegistry::new();
    rust_fv_analysis::stdlib_contracts::string::register_string_contracts(&mut registry);

    let contract = registry
        .get("String::len")
        .expect("String::len contract should exist");

    assert_eq!(contract.method_name, "len");
    assert_eq!(contract.type_path, "std::string::String");
    assert_eq!(contract.source, ContractSource::Builtin);
    assert!(
        contract.summary.contracts.is_pure,
        "String::len must be pure"
    );
}

/// Test that String::is_empty contract exists and is pure.
///
/// Expected contract:
/// - pure: true
/// - post: result == (self.len() == 0)
#[test]
fn test_string_is_empty_contract() {
    let mut registry = StdlibContractRegistry::new();
    rust_fv_analysis::stdlib_contracts::string::register_string_contracts(&mut registry);

    let contract = registry
        .get("String::is_empty")
        .expect("String::is_empty contract should exist");

    assert_eq!(contract.method_name, "is_empty");
    assert!(
        contract.summary.contracts.is_pure,
        "String::is_empty must be pure"
    );

    // Should relate to len
    let postconds = &contract.summary.contracts.ensures;
    let relates_to_len = postconds.iter().any(|e| e.raw.contains("len"));
    assert!(relates_to_len, "is_empty should relate to len() == 0");
}

/// Test that String::push_str contract updates length.
///
/// Expected contract:
/// - post: self.len() == old(self.len()) + other.len()
#[test]
fn test_string_push_str_contract() {
    let mut registry = StdlibContractRegistry::new();
    rust_fv_analysis::stdlib_contracts::string::register_string_contracts(&mut registry);

    let contract = registry
        .get("String::push_str")
        .expect("String::push_str contract should exist");

    assert_eq!(contract.method_name, "push_str");
    assert!(
        !contract.summary.contracts.is_pure,
        "push_str modifies the string"
    );

    // Should have postcondition about length
    let postconds = &contract.summary.contracts.ensures;
    let has_len_postcond = postconds
        .iter()
        .any(|e| e.raw.contains("len") && (e.raw.contains("old") || e.raw.contains("+")));
    assert!(
        has_len_postcond,
        "push_str should update length appropriately"
    );
}

/// Test that str::len contract exists and is pure.
#[test]
fn test_str_len_contract() {
    let mut registry = StdlibContractRegistry::new();
    rust_fv_analysis::stdlib_contracts::string::register_string_contracts(&mut registry);

    let contract = registry
        .get("str::len")
        .expect("str::len contract should exist");

    assert_eq!(contract.method_name, "len");
    assert_eq!(contract.type_path, "str");
    assert!(contract.summary.contracts.is_pure, "str::len must be pure");
}

/// Test that str::is_empty contract exists and is pure.
#[test]
fn test_str_is_empty_contract() {
    let mut registry = StdlibContractRegistry::new();
    rust_fv_analysis::stdlib_contracts::string::register_string_contracts(&mut registry);

    let contract = registry
        .get("str::is_empty")
        .expect("str::is_empty contract should exist");

    assert_eq!(contract.method_name, "is_empty");
    assert!(
        contract.summary.contracts.is_pure,
        "str::is_empty must be pure"
    );
}

/// Test that str::contains contract exists and is pure.
#[test]
fn test_str_contains_contract() {
    let mut registry = StdlibContractRegistry::new();
    rust_fv_analysis::stdlib_contracts::string::register_string_contracts(&mut registry);

    let contract = registry
        .get("str::contains")
        .expect("str::contains contract should exist");

    assert_eq!(contract.method_name, "contains");
    assert!(
        contract.summary.contracts.is_pure,
        "str::contains must be pure"
    );
}

/// Test that str::as_bytes contract exists.
///
/// Expected contract:
/// - pure: true
/// - post: result.len() == self.len()
#[test]
fn test_str_as_bytes_contract() {
    let mut registry = StdlibContractRegistry::new();
    rust_fv_analysis::stdlib_contracts::string::register_string_contracts(&mut registry);

    let contract = registry
        .get("str::as_bytes")
        .expect("str::as_bytes contract should exist");

    assert_eq!(contract.method_name, "as_bytes");
    assert!(
        contract.summary.contracts.is_pure,
        "str::as_bytes must be pure"
    );

    // Should have postcondition about length preservation
    let postconds = &contract.summary.contracts.ensures;
    let preserves_length = postconds.iter().any(|e| e.raw.contains("len"));
    assert!(preserves_length, "as_bytes should preserve length");
}

/// Test that slice::len contract exists and is pure.
#[test]
fn test_slice_len_contract() {
    let mut registry = StdlibContractRegistry::new();
    rust_fv_analysis::stdlib_contracts::string::register_string_contracts(&mut registry);

    let contract = registry
        .get("slice::len")
        .expect("slice::len contract should exist");

    assert_eq!(contract.method_name, "len");
    assert_eq!(contract.type_path, "slice");
    assert!(
        contract.summary.contracts.is_pure,
        "slice::len must be pure"
    );
}

/// Test that slice::get contract exists with bounds check.
///
/// Expected contract:
/// - pre: index < self.len()
/// - post: result is i-th element
#[test]
fn test_slice_get_contract() {
    let mut registry = StdlibContractRegistry::new();
    rust_fv_analysis::stdlib_contracts::string::register_string_contracts(&mut registry);

    let contract = registry
        .get("slice::get")
        .expect("slice::get contract should exist");

    assert_eq!(contract.method_name, "get");
    assert!(
        contract.summary.contracts.is_pure,
        "slice::get must be pure"
    );

    // Should have precondition about bounds
    let preconds = &contract.summary.contracts.requires;
    let has_bounds_check = preconds
        .iter()
        .any(|e| e.raw.contains("index") && (e.raw.contains("<") || e.raw.contains("len")));
    assert!(
        has_bounds_check,
        "slice::get should have bounds check precondition"
    );
}

/// Test that slice::is_empty contract exists and is pure.
#[test]
fn test_slice_is_empty_contract() {
    let mut registry = StdlibContractRegistry::new();
    rust_fv_analysis::stdlib_contracts::string::register_string_contracts(&mut registry);

    let contract = registry
        .get("slice::is_empty")
        .expect("slice::is_empty contract should exist");

    assert_eq!(contract.method_name, "is_empty");
    assert!(
        contract.summary.contracts.is_pure,
        "slice::is_empty must be pure"
    );

    // Should relate to len
    let postconds = &contract.summary.contracts.ensures;
    let relates_to_len = postconds.iter().any(|e| e.raw.contains("len"));
    assert!(relates_to_len, "is_empty should relate to len() == 0");
}
