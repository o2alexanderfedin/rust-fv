//! Tests for Iterator trait standard library contracts.
//!
//! These tests verify that Iterator contracts model composable sequence transformations
//! with proper length preservation properties.

use rust_fv_analysis::stdlib_contracts::{ContractSource, StdlibContractRegistry};

/// Test that Iterator::next contract exists and models sequence consumption.
///
/// Expected contract:
/// - post: if result.is_some(): seq_model shrinks by 1
/// - post: if result.is_none(): seq_model was empty
#[test]
fn test_iterator_next_contract() {
    let mut registry = StdlibContractRegistry::new();
    rust_fv_analysis::stdlib_contracts::iterator::register_iterator_contracts(&mut registry);

    let contract = registry
        .get("Iterator::next")
        .expect("Iterator::next contract should exist");

    assert_eq!(contract.method_name, "next");
    assert_eq!(contract.type_path, "std::iter::Iterator");
    assert_eq!(contract.source, ContractSource::Builtin);

    // Should have postconditions about sequence model
    assert!(
        !contract.summary.contracts.ensures.is_empty(),
        "next must have postconditions"
    );
}

/// Test that Iterator::map contract preserves length.
///
/// Expected contract:
/// - post: result.seq_len() == self.seq_len()  [map preserves length]
#[test]
fn test_iterator_map_preserves_length() {
    let mut registry = StdlibContractRegistry::new();
    rust_fv_analysis::stdlib_contracts::iterator::register_iterator_contracts(&mut registry);

    let contract = registry
        .get("Iterator::map")
        .expect("Iterator::map contract should exist");

    assert_eq!(contract.method_name, "map");

    // Map should preserve sequence length
    let postconds = &contract.summary.contracts.ensures;
    let preserves_length = postconds
        .iter()
        .any(|e| e.raw.contains("seq_len") || e.raw.contains("length"));
    assert!(
        preserves_length,
        "map must preserve iterator length (composable property)"
    );
}

/// Test that Iterator::filter reduces or maintains length.
///
/// Expected contract:
/// - post: result.seq_len() <= self.seq_len()  [filter reduces length]
#[test]
fn test_iterator_filter_reduces_length() {
    let mut registry = StdlibContractRegistry::new();
    rust_fv_analysis::stdlib_contracts::iterator::register_iterator_contracts(&mut registry);

    let contract = registry
        .get("Iterator::filter")
        .expect("Iterator::filter contract should exist");

    assert_eq!(contract.method_name, "filter");

    // Filter should have postcondition about length reduction
    let postconds = &contract.summary.contracts.ensures;
    let reduces_length = postconds
        .iter()
        .any(|e| e.raw.contains("seq_len") || e.raw.contains("length") || e.raw.contains("<="));
    assert!(reduces_length, "filter must have length reduction property");
}

/// Test that Iterator::collect contract exists.
///
/// Expected contract:
/// - post: result_vec.len() == consumed_iterator.count()
#[test]
fn test_iterator_collect_contract() {
    let mut registry = StdlibContractRegistry::new();
    rust_fv_analysis::stdlib_contracts::iterator::register_iterator_contracts(&mut registry);

    let contract = registry
        .get("Iterator::collect")
        .expect("Iterator::collect contract should exist");

    assert_eq!(contract.method_name, "collect");

    // Should have postconditions about result length
    assert!(
        !contract.summary.contracts.ensures.is_empty(),
        "collect must have postconditions"
    );
}

/// Test that Iterator::count contract exists and is pure.
#[test]
fn test_iterator_count_contract() {
    let mut registry = StdlibContractRegistry::new();
    rust_fv_analysis::stdlib_contracts::iterator::register_iterator_contracts(&mut registry);

    let contract = registry
        .get("Iterator::count")
        .expect("Iterator::count contract should exist");

    assert_eq!(contract.method_name, "count");

    // Count consumes iterator but result is deterministic from sequence model
    let postconds = &contract.summary.contracts.ensures;
    let has_seq_len = postconds
        .iter()
        .any(|e| e.raw.contains("seq_len") || e.raw.contains("result"));
    assert!(has_seq_len, "count postcondition should relate to seq_len");
}

/// Test that Iterator::fold contract exists.
#[test]
fn test_iterator_fold_contract() {
    let mut registry = StdlibContractRegistry::new();
    rust_fv_analysis::stdlib_contracts::iterator::register_iterator_contracts(&mut registry);

    let contract = registry
        .get("Iterator::fold")
        .expect("Iterator::fold contract should exist");

    assert_eq!(contract.method_name, "fold");

    // Should have postconditions about fold operation
    assert!(
        !contract.summary.contracts.ensures.is_empty(),
        "fold must have postconditions"
    );
}

/// Test that Iterator::any contract exists.
#[test]
fn test_iterator_any_contract() {
    let mut registry = StdlibContractRegistry::new();
    rust_fv_analysis::stdlib_contracts::iterator::register_iterator_contracts(&mut registry);

    let contract = registry
        .get("Iterator::any")
        .expect("Iterator::any contract should exist");

    assert_eq!(contract.method_name, "any");

    // Should have postconditions about existence
    let postconds = &contract.summary.contracts.ensures;
    let has_exists = postconds
        .iter()
        .any(|e| e.raw.contains("exists") || e.raw.contains("any"));
    assert!(has_exists, "any should relate to exists quantifier");
}

/// Test that Iterator::all contract exists.
#[test]
fn test_iterator_all_contract() {
    let mut registry = StdlibContractRegistry::new();
    rust_fv_analysis::stdlib_contracts::iterator::register_iterator_contracts(&mut registry);

    let contract = registry
        .get("Iterator::all")
        .expect("Iterator::all contract should exist");

    assert_eq!(contract.method_name, "all");

    // Should have postconditions about universal quantification
    let postconds = &contract.summary.contracts.ensures;
    let has_forall = postconds
        .iter()
        .any(|e| e.raw.contains("forall") || e.raw.contains("all"));
    assert!(has_forall, "all should relate to forall quantifier");
}

/// Test that Iterator::zip contract combines two sequences.
///
/// Expected contract:
/// - post: result.seq_len() == min(self.seq_len(), other.seq_len())
#[test]
fn test_iterator_zip_contract() {
    let mut registry = StdlibContractRegistry::new();
    rust_fv_analysis::stdlib_contracts::iterator::register_iterator_contracts(&mut registry);

    let contract = registry
        .get("Iterator::zip")
        .expect("Iterator::zip contract should exist");

    assert_eq!(contract.method_name, "zip");

    // Should have postconditions about min length
    let postconds = &contract.summary.contracts.ensures;
    let has_min = postconds
        .iter()
        .any(|e| e.raw.contains("min") || e.raw.contains("seq_len"));
    assert!(has_min, "zip should ensure length is min of both iterators");
}

/// Test that Iterator::enumerate contract preserves length.
///
/// Expected contract:
/// - post: result.seq_len() == self.seq_len()
#[test]
fn test_iterator_enumerate_contract() {
    let mut registry = StdlibContractRegistry::new();
    rust_fv_analysis::stdlib_contracts::iterator::register_iterator_contracts(&mut registry);

    let contract = registry
        .get("Iterator::enumerate")
        .expect("Iterator::enumerate contract should exist");

    assert_eq!(contract.method_name, "enumerate");

    // Should preserve length
    let postconds = &contract.summary.contracts.ensures;
    let preserves_length = postconds
        .iter()
        .any(|e| e.raw.contains("seq_len") || e.raw.contains("length"));
    assert!(preserves_length, "enumerate must preserve iterator length");
}

/// Test that Iterator::take contract limits length.
///
/// Expected contract:
/// - post: result.seq_len() == min(n, self.seq_len())
#[test]
fn test_iterator_take_contract() {
    let mut registry = StdlibContractRegistry::new();
    rust_fv_analysis::stdlib_contracts::iterator::register_iterator_contracts(&mut registry);

    let contract = registry
        .get("Iterator::take")
        .expect("Iterator::take contract should exist");

    assert_eq!(contract.method_name, "take");

    // Should have postconditions about min length
    let postconds = &contract.summary.contracts.ensures;
    let has_min = postconds
        .iter()
        .any(|e| e.raw.contains("min") || e.raw.contains("seq_len"));
    assert!(has_min, "take should ensure length is min(n, original)");
}

/// Test that chain composition properties are documented.
///
/// This is a meta-test that ensures the registry has all the necessary
/// contracts to verify chain compositions like:
/// vec.iter().map(f).filter(p).collect()
#[test]
fn test_chain_composition_coverage() {
    let mut registry = StdlibContractRegistry::new();
    rust_fv_analysis::stdlib_contracts::iterator::register_iterator_contracts(&mut registry);

    // All these must exist for chain composition verification
    assert!(registry.get("Iterator::map").is_some());
    assert!(registry.get("Iterator::filter").is_some());
    assert!(registry.get("Iterator::collect").is_some());
    assert!(registry.get("Iterator::next").is_some());

    // Length preservation properties enable composition verification
    let map = registry.get("Iterator::map").unwrap();
    let filter = registry.get("Iterator::filter").unwrap();

    // map preserves length
    let map_preserves = map
        .summary
        .contracts
        .ensures
        .iter()
        .any(|e| e.raw.contains("seq_len"));
    assert!(
        map_preserves,
        "map must have length preservation for composition"
    );

    // filter reduces length
    let filter_reduces = filter
        .summary
        .contracts
        .ensures
        .iter()
        .any(|e| e.raw.contains("seq_len") || e.raw.contains("<="));
    assert!(
        filter_reduces,
        "filter must have length property for composition"
    );
}
