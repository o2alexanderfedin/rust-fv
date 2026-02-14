//! Tests for stdlib contract override validation.

use rust_fv_analysis::contract_db::FunctionSummary;
use rust_fv_analysis::ir::{Contracts, SpecExpr, Ty, UintTy};
use rust_fv_analysis::stdlib_contracts::override_check::{OverrideError, validate_override};
use rust_fv_analysis::stdlib_contracts::{ContractSource, StdlibContract};

fn make_test_contract(
    type_path: &str,
    method: &str,
    param_count: usize,
    requires: Vec<&str>,
    ensures: Vec<&str>,
) -> StdlibContract {
    StdlibContract {
        type_path: type_path.to_string(),
        method_name: method.to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: requires
                    .into_iter()
                    .map(|s| SpecExpr { raw: s.to_string() })
                    .collect(),
                ensures: ensures
                    .into_iter()
                    .map(|s| SpecExpr { raw: s.to_string() })
                    .collect(),
                invariants: vec![],
                is_pure: false,
                decreases: None,
            },
            param_names: (0..param_count).map(|i| format!("arg{}", i)).collect(),
            param_types: vec![Ty::Uint(UintTy::Usize); param_count],
            return_ty: Ty::Unit,
        },
        source: ContractSource::Builtin,
    }
}

#[test]
fn test_validate_override_accepts_compatible_contract() {
    let original = make_test_contract("Vec", "push", 2, vec![], vec!["self.len() > 0"]);
    let override_contract = make_test_contract(
        "Vec",
        "push",
        2,
        vec![],
        vec!["self.len() >= old(self.len())"],
    );

    let result = validate_override(&original, &override_contract);
    assert!(result.is_ok(), "Compatible override should be accepted");
}

#[test]
fn test_validate_override_rejects_param_count_mismatch() {
    let original = make_test_contract("Vec", "push", 2, vec![], vec![]);
    let override_contract = make_test_contract("Vec", "push", 3, vec![], vec![]);

    let result = validate_override(&original, &override_contract);
    assert!(matches!(
        result,
        Err(OverrideError::ParamCountMismatch { .. })
    ));
}

#[test]
fn test_validate_override_rejects_contradictory_postcondition() {
    let original = make_test_contract("Vec", "len", 1, vec![], vec!["result >= 0"]);
    let override_contract = make_test_contract("Vec", "len", 1, vec![], vec!["false"]);

    let result = validate_override(&original, &override_contract);
    assert!(matches!(
        result,
        Err(OverrideError::ContradictoryPostcondition { .. })
    ));
}

#[test]
fn test_validate_override_allows_unreachable_precondition_with_warning() {
    let original = make_test_contract("Vec", "push", 2, vec![], vec![]);
    let override_contract = make_test_contract("Vec", "push", 2, vec!["false"], vec![]);

    // Should accept (user may know what they're doing) but we'll log a warning
    let result = validate_override(&original, &override_contract);
    assert!(result.is_ok(), "Unreachable precondition should be allowed");
}

#[test]
fn test_validate_extension_accepts_valid_extra_conditions() {
    use rust_fv_analysis::stdlib_contracts::override_check::validate_extension;

    let original = make_test_contract("Vec", "push", 2, vec![], vec![]);
    let extra_requires = vec![SpecExpr {
        raw: "self.valid()".to_string(),
    }];
    let extra_ensures = vec![SpecExpr {
        raw: "self.len() == old(self.len()) + 1".to_string(),
    }];

    let result = validate_extension(&original, &extra_requires, &extra_ensures);
    assert!(result.is_ok(), "Valid extension should be accepted");
}

#[test]
fn test_override_error_param_count_mismatch_has_details() {
    let original = make_test_contract("Vec", "push", 2, vec![], vec![]);
    let override_contract = make_test_contract("Vec", "push", 3, vec![], vec![]);

    let result = validate_override(&original, &override_contract);
    match result {
        Err(OverrideError::ParamCountMismatch { expected, got }) => {
            assert_eq!(expected, 2);
            assert_eq!(got, 3);
        }
        _ => panic!("Expected ParamCountMismatch error"),
    }
}
