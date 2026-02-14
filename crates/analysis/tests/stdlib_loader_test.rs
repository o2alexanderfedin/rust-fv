//! Tests for stdlib contract loader.

use rust_fv_analysis::stdlib_contracts::loader;

#[test]
fn test_load_default_contracts_creates_non_empty_registry() {
    let registry = loader::load_default_contracts();
    assert!(!registry.is_empty(), "Registry should have contracts");
}

#[test]
fn test_load_default_contracts_includes_vec() {
    let registry = loader::load_default_contracts();
    assert!(registry.get("Vec::push").is_some(), "Should have Vec::push");
    assert!(registry.get("Vec::pop").is_some(), "Should have Vec::pop");
    assert!(registry.get("Vec::len").is_some(), "Should have Vec::len");
}

#[test]
fn test_load_default_contracts_includes_option() {
    let registry = loader::load_default_contracts();
    assert!(
        registry.get("Option::unwrap").is_some(),
        "Should have Option::unwrap"
    );
    assert!(
        registry.get("Option::is_some").is_some(),
        "Should have Option::is_some"
    );
}

#[test]
fn test_load_default_contracts_includes_result() {
    let registry = loader::load_default_contracts();
    assert!(
        registry.get("Result::unwrap").is_some(),
        "Should have Result::unwrap"
    );
    assert!(
        registry.get("Result::is_ok").is_some(),
        "Should have Result::is_ok"
    );
}

#[test]
fn test_load_default_contracts_includes_hashmap() {
    let registry = loader::load_default_contracts();
    assert!(
        registry.get("HashMap::insert").is_some(),
        "Should have HashMap::insert"
    );
    assert!(
        registry.get("HashMap::get").is_some(),
        "Should have HashMap::get"
    );
}

#[test]
fn test_load_default_contracts_includes_iterator() {
    let registry = loader::load_default_contracts();
    assert!(
        registry.get("Iterator::map").is_some(),
        "Should have Iterator::map"
    );
    assert!(
        registry.get("Iterator::filter").is_some(),
        "Should have Iterator::filter"
    );
}

#[test]
fn test_load_default_contracts_includes_string() {
    let registry = loader::load_default_contracts();
    assert!(
        registry.get("String::len").is_some(),
        "Should have String::len"
    );
    assert!(registry.get("str::len").is_some(), "Should have str::len");
}

#[test]
fn test_load_default_contracts_registry_is_enabled() {
    let registry = loader::load_default_contracts();
    assert!(registry.is_enabled(), "Registry should be enabled");
}
