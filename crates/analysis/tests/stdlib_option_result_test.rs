//! Tests for Option<T> and Result<T,E> standard library contracts.

use rust_fv_analysis::stdlib_contracts::{ContractSource, StdlibContractRegistry};

// ============================================================================
// Option<T> Tests
// ============================================================================

#[test]
fn test_register_option_contracts_populates_registry() {
    use rust_fv_analysis::stdlib_contracts::option::register_option_contracts;

    let mut registry = StdlibContractRegistry::new();
    register_option_contracts(&mut registry);

    // Check all expected methods are registered
    assert!(registry.get("Option::is_some").is_some());
    assert!(registry.get("Option::is_none").is_some());
    assert!(registry.get("Option::unwrap").is_some());
    assert!(registry.get("Option::map").is_some());
    assert!(registry.get("Option::and_then").is_some());
    assert!(registry.get("Option::ok_or").is_some());
    assert!(registry.get("Option::unwrap_or").is_some());
    assert!(registry.get("Option::unwrap_or_else").is_some());

    // Registry should have at least 8 contracts
    assert!(registry.len() >= 8);
}

#[test]
fn test_option_is_some_contract() {
    use rust_fv_analysis::stdlib_contracts::option::register_option_contracts;

    let mut registry = StdlibContractRegistry::new();
    register_option_contracts(&mut registry);

    let contract = registry
        .get("Option::is_some")
        .expect("Option::is_some not found");

    assert_eq!(contract.source, ContractSource::Builtin);
    assert_eq!(contract.type_path, "std::option::Option");
    assert_eq!(contract.method_name, "is_some");

    // is_some is pure
    assert!(contract.summary.contracts.is_pure);

    // Post: result == !is_none
    let ensures_raw: Vec<&str> = contract
        .summary
        .contracts
        .ensures
        .iter()
        .map(|e| e.raw.as_str())
        .collect();

    assert!(
        ensures_raw
            .iter()
            .any(|s| s.contains("is_none") || s.contains("result"))
    );
}

#[test]
fn test_option_is_none_contract() {
    use rust_fv_analysis::stdlib_contracts::option::register_option_contracts;

    let mut registry = StdlibContractRegistry::new();
    register_option_contracts(&mut registry);

    let contract = registry
        .get("Option::is_none")
        .expect("Option::is_none not found");

    // is_none is pure
    assert!(contract.summary.contracts.is_pure);
}

#[test]
fn test_option_unwrap_contract() {
    use rust_fv_analysis::stdlib_contracts::option::register_option_contracts;

    let mut registry = StdlibContractRegistry::new();
    register_option_contracts(&mut registry);

    let contract = registry
        .get("Option::unwrap")
        .expect("Option::unwrap not found");

    // Pre: is_some (panics if None)
    assert!(!contract.summary.contracts.requires.is_empty());

    let requires_raw: Vec<&str> = contract
        .summary
        .contracts
        .requires
        .iter()
        .map(|e| e.raw.as_str())
        .collect();

    assert!(requires_raw.iter().any(|s| s.contains("is_some")));
}

#[test]
fn test_option_map_contract() {
    use rust_fv_analysis::stdlib_contracts::option::register_option_contracts;

    let mut registry = StdlibContractRegistry::new();
    register_option_contracts(&mut registry);

    let contract = registry.get("Option::map").expect("Option::map not found");

    // Should have postconditions about Some/None cases
    assert!(!contract.summary.contracts.ensures.is_empty());

    let ensures_raw: Vec<&str> = contract
        .summary
        .contracts
        .ensures
        .iter()
        .map(|e| e.raw.as_str())
        .collect();

    assert!(
        ensures_raw
            .iter()
            .any(|s| s.contains("is_some") || s.contains("is_none"))
    );
}

#[test]
fn test_option_and_then_contract() {
    use rust_fv_analysis::stdlib_contracts::option::register_option_contracts;

    let mut registry = StdlibContractRegistry::new();
    register_option_contracts(&mut registry);

    let contract = registry
        .get("Option::and_then")
        .expect("Option::and_then not found");

    // Should have postconditions
    assert!(!contract.summary.contracts.ensures.is_empty());
}

#[test]
fn test_option_ok_or_contract() {
    use rust_fv_analysis::stdlib_contracts::option::register_option_contracts;

    let mut registry = StdlibContractRegistry::new();
    register_option_contracts(&mut registry);

    let contract = registry
        .get("Option::ok_or")
        .expect("Option::ok_or not found");

    // Converts Option to Result
    let ensures_raw: Vec<&str> = contract
        .summary
        .contracts
        .ensures
        .iter()
        .map(|e| e.raw.as_str())
        .collect();

    assert!(
        ensures_raw
            .iter()
            .any(|s| s.contains("is_ok") || s.contains("is_err"))
    );
}

#[test]
fn test_option_unwrap_or_contract() {
    use rust_fv_analysis::stdlib_contracts::option::register_option_contracts;

    let mut registry = StdlibContractRegistry::new();
    register_option_contracts(&mut registry);

    let contract = registry
        .get("Option::unwrap_or")
        .expect("Option::unwrap_or not found");

    // Should have postconditions for Some/None cases
    assert!(!contract.summary.contracts.ensures.is_empty());
}

// ============================================================================
// Result<T,E> Tests
// ============================================================================

#[test]
fn test_register_result_contracts_populates_registry() {
    use rust_fv_analysis::stdlib_contracts::result::register_result_contracts;

    let mut registry = StdlibContractRegistry::new();
    register_result_contracts(&mut registry);

    // Check all expected methods are registered
    assert!(registry.get("Result::is_ok").is_some());
    assert!(registry.get("Result::is_err").is_some());
    assert!(registry.get("Result::unwrap").is_some());
    assert!(registry.get("Result::unwrap_err").is_some());
    assert!(registry.get("Result::map").is_some());
    assert!(registry.get("Result::map_err").is_some());
    assert!(registry.get("Result::and_then").is_some());
    assert!(registry.get("Result::ok").is_some());
    assert!(registry.get("Result::err").is_some());

    // Registry should have at least 9 contracts
    assert!(registry.len() >= 9);
}

#[test]
fn test_result_is_ok_contract() {
    use rust_fv_analysis::stdlib_contracts::result::register_result_contracts;

    let mut registry = StdlibContractRegistry::new();
    register_result_contracts(&mut registry);

    let contract = registry
        .get("Result::is_ok")
        .expect("Result::is_ok not found");

    assert_eq!(contract.source, ContractSource::Builtin);
    assert_eq!(contract.type_path, "std::result::Result");
    assert_eq!(contract.method_name, "is_ok");

    // is_ok is pure
    assert!(contract.summary.contracts.is_pure);
}

#[test]
fn test_result_is_err_contract() {
    use rust_fv_analysis::stdlib_contracts::result::register_result_contracts;

    let mut registry = StdlibContractRegistry::new();
    register_result_contracts(&mut registry);

    let contract = registry
        .get("Result::is_err")
        .expect("Result::is_err not found");

    // is_err is pure
    assert!(contract.summary.contracts.is_pure);
}

#[test]
fn test_result_unwrap_contract() {
    use rust_fv_analysis::stdlib_contracts::result::register_result_contracts;

    let mut registry = StdlibContractRegistry::new();
    register_result_contracts(&mut registry);

    let contract = registry
        .get("Result::unwrap")
        .expect("Result::unwrap not found");

    // Pre: is_ok (panics if Err)
    assert!(!contract.summary.contracts.requires.is_empty());

    let requires_raw: Vec<&str> = contract
        .summary
        .contracts
        .requires
        .iter()
        .map(|e| e.raw.as_str())
        .collect();

    assert!(requires_raw.iter().any(|s| s.contains("is_ok")));
}

#[test]
fn test_result_unwrap_err_contract() {
    use rust_fv_analysis::stdlib_contracts::result::register_result_contracts;

    let mut registry = StdlibContractRegistry::new();
    register_result_contracts(&mut registry);

    let contract = registry
        .get("Result::unwrap_err")
        .expect("Result::unwrap_err not found");

    // Pre: is_err (panics if Ok)
    assert!(!contract.summary.contracts.requires.is_empty());

    let requires_raw: Vec<&str> = contract
        .summary
        .contracts
        .requires
        .iter()
        .map(|e| e.raw.as_str())
        .collect();

    assert!(requires_raw.iter().any(|s| s.contains("is_err")));
}

#[test]
fn test_result_map_contract() {
    use rust_fv_analysis::stdlib_contracts::result::register_result_contracts;

    let mut registry = StdlibContractRegistry::new();
    register_result_contracts(&mut registry);

    let contract = registry.get("Result::map").expect("Result::map not found");

    // Should have postconditions about Ok/Err cases
    assert!(!contract.summary.contracts.ensures.is_empty());
}

#[test]
fn test_result_map_err_contract() {
    use rust_fv_analysis::stdlib_contracts::result::register_result_contracts;

    let mut registry = StdlibContractRegistry::new();
    register_result_contracts(&mut registry);

    let contract = registry
        .get("Result::map_err")
        .expect("Result::map_err not found");

    // Should have postconditions about Ok/Err cases
    assert!(!contract.summary.contracts.ensures.is_empty());
}

#[test]
fn test_result_and_then_contract() {
    use rust_fv_analysis::stdlib_contracts::result::register_result_contracts;

    let mut registry = StdlibContractRegistry::new();
    register_result_contracts(&mut registry);

    let contract = registry
        .get("Result::and_then")
        .expect("Result::and_then not found");

    // Should have postconditions
    assert!(!contract.summary.contracts.ensures.is_empty());
}

#[test]
fn test_result_ok_contract() {
    use rust_fv_analysis::stdlib_contracts::result::register_result_contracts;

    let mut registry = StdlibContractRegistry::new();
    register_result_contracts(&mut registry);

    let contract = registry.get("Result::ok").expect("Result::ok not found");

    // Converts Result to Option
    let ensures_raw: Vec<&str> = contract
        .summary
        .contracts
        .ensures
        .iter()
        .map(|e| e.raw.as_str())
        .collect();

    assert!(
        ensures_raw
            .iter()
            .any(|s| s.contains("is_some") || s.contains("is_none"))
    );
}

#[test]
fn test_result_err_contract() {
    use rust_fv_analysis::stdlib_contracts::result::register_result_contracts;

    let mut registry = StdlibContractRegistry::new();
    register_result_contracts(&mut registry);

    let contract = registry.get("Result::err").expect("Result::err not found");

    // Converts Result to Option
    let ensures_raw: Vec<&str> = contract
        .summary
        .contracts
        .ensures
        .iter()
        .map(|e| e.raw.as_str())
        .collect();

    assert!(
        ensures_raw
            .iter()
            .any(|s| s.contains("is_some") || s.contains("is_none"))
    );
}
