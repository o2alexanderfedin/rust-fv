//! Standard library contract loader.
//!
//! This module provides the `load_default_contracts()` function that creates
//! and populates a `StdlibContractRegistry` with all Tier 1 stdlib contracts.

use crate::stdlib_contracts::StdlibContractRegistry;

/// Load all default stdlib contracts into a new registry.
///
/// This function creates a registry and calls all registration functions
/// for Tier 1 stdlib types:
/// - Vec<T>
/// - Option<T>
/// - Result<T, E>
/// - HashMap<K, V>
/// - Iterator trait adaptors
/// - String/&str/slice
///
/// Returns a fully populated registry ready to merge into the contract database.
///
/// # Example
///
/// ```ignore
/// let stdlib_registry = load_default_contracts();
/// stdlib_registry.merge_into(&mut contract_db);
/// ```
pub fn load_default_contracts() -> StdlibContractRegistry {
    let mut registry = StdlibContractRegistry::new();

    // Register Tier 1 contracts
    super::vec::register_vec_contracts(&mut registry);
    super::option::register_option_contracts(&mut registry);
    super::result::register_result_contracts(&mut registry);
    super::hashmap::register_hashmap_contracts(&mut registry);
    super::iterator::register_iterator_contracts(&mut registry);
    super::string::register_string_contracts(&mut registry);

    registry
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_load_default_contracts_returns_populated_registry() {
        let registry = load_default_contracts();
        assert!(registry.is_enabled());
        assert!(!registry.is_empty());
    }

    #[test]
    fn test_load_default_contracts_has_vec_contracts() {
        let registry = load_default_contracts();

        // Check for Vec contracts
        assert!(registry.get("Vec::push").is_some());
        assert!(registry.get("Vec::pop").is_some());
        assert!(registry.get("Vec::len").is_some());
        assert!(registry.get("Vec::get").is_some());
    }

    #[test]
    fn test_load_default_contracts_has_option_contracts() {
        let registry = load_default_contracts();

        // Check for Option contracts
        assert!(registry.get("Option::is_some").is_some());
        assert!(registry.get("Option::is_none").is_some());
        assert!(registry.get("Option::unwrap").is_some());
        assert!(registry.get("Option::map").is_some());
    }

    #[test]
    fn test_load_default_contracts_has_result_contracts() {
        let registry = load_default_contracts();

        // Check for Result contracts
        assert!(registry.get("Result::is_ok").is_some());
        assert!(registry.get("Result::is_err").is_some());
        assert!(registry.get("Result::unwrap").is_some());
    }

    #[test]
    fn test_load_default_contracts_has_hashmap_contracts() {
        let registry = load_default_contracts();

        // Check for HashMap contracts
        assert!(registry.get("HashMap::insert").is_some());
        assert!(registry.get("HashMap::get").is_some());
        assert!(registry.get("HashMap::remove").is_some());
    }

    #[test]
    fn test_load_default_contracts_has_iterator_contracts() {
        let registry = load_default_contracts();

        // Check for Iterator contracts
        assert!(registry.get("Iterator::next").is_some());
        assert!(registry.get("Iterator::map").is_some());
        assert!(registry.get("Iterator::filter").is_some());
        assert!(registry.get("Iterator::collect").is_some());
    }

    #[test]
    fn test_load_default_contracts_has_string_contracts() {
        let registry = load_default_contracts();

        // Check for String contracts
        assert!(registry.get("String::len").is_some());
        assert!(registry.get("String::is_empty").is_some());
    }

    #[test]
    fn test_load_default_contracts_expected_count() {
        let registry = load_default_contracts();

        // Tier 1 should have:
        // - Vec: 9 contracts
        // - Option: 8 contracts
        // - Result: 9 contracts
        // - HashMap: 7 contracts
        // - Iterator: 11 contracts
        // - String/str/slice: 10 contracts
        // Total: 54 contracts
        assert!(
            registry.len() >= 50,
            "Expected at least 50 Tier 1 contracts, got {}",
            registry.len()
        );
    }
}
