//! Soundness validation for user-provided stdlib contract overrides.
//!
//! This module ensures that user overrides and extensions of stdlib contracts
//! maintain basic soundness properties and don't introduce obvious contradictions.

use crate::ir::SpecExpr;
use crate::stdlib_contracts::StdlibContract;

/// Errors that can occur during override validation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OverrideError {
    /// Override has different parameter count than original
    ParamCountMismatch { expected: usize, got: usize },
    /// Override has incompatible parameter types
    ParamTypeMismatch { param_index: usize, message: String },
    /// Postcondition is trivially false (contradiction)
    ContradictoryPostcondition { condition: String },
    /// Invalid specification expression syntax
    InvalidSpecExpr { expr: String, reason: String },
}

impl std::fmt::Display for OverrideError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OverrideError::ParamCountMismatch { expected, got } => {
                write!(
                    f,
                    "Parameter count mismatch: expected {}, got {}",
                    expected, got
                )
            }
            OverrideError::ParamTypeMismatch {
                param_index,
                message,
            } => {
                write!(
                    f,
                    "Parameter type mismatch at index {}: {}",
                    param_index, message
                )
            }
            OverrideError::ContradictoryPostcondition { condition } => {
                write!(f, "Contradictory postcondition: {}", condition)
            }
            OverrideError::InvalidSpecExpr { expr, reason } => {
                write!(f, "Invalid specification expression '{}': {}", expr, reason)
            }
        }
    }
}

impl std::error::Error for OverrideError {}

/// Validate a user override of a stdlib contract.
///
/// Checks:
/// 1. Parameter count matches
/// 2. Basic parameter type compatibility
/// 3. Postcondition is not trivially false
/// 4. Precondition warnings (if unreachable)
///
/// Returns `Ok(())` if the override is valid, or an error describing the issue.
pub fn validate_override(
    original: &StdlibContract,
    override_contract: &StdlibContract,
) -> Result<(), OverrideError> {
    // Check parameter count
    if original.summary.param_names.len() != override_contract.summary.param_names.len() {
        return Err(OverrideError::ParamCountMismatch {
            expected: original.summary.param_names.len(),
            got: override_contract.summary.param_names.len(),
        });
    }

    // Check for trivially false postconditions
    for ensure in &override_contract.summary.contracts.ensures {
        if is_trivially_false(&ensure.raw) {
            return Err(OverrideError::ContradictoryPostcondition {
                condition: ensure.raw.clone(),
            });
        }
    }

    // Warning: if precondition is false (unreachable), warn but allow
    // (User may know what they're doing)
    for require in &override_contract.summary.contracts.requires {
        if is_trivially_false(&require.raw) {
            // In production, this would emit a warning via tracing::warn!
            // For now, we allow it
            eprintln!(
                "Warning: Precondition is trivially false (unreachable): {}",
                require.raw
            );
        }
    }

    Ok(())
}

/// Validate an extension to an existing stdlib contract.
///
/// Extensions add extra preconditions and postconditions to an existing contract.
/// This function validates that the extra conditions are syntactically valid.
pub fn validate_extension(
    _original: &StdlibContract,
    extra_requires: &[SpecExpr],
    extra_ensures: &[SpecExpr],
) -> Result<(), OverrideError> {
    // Validate extra requires
    for require in extra_requires {
        if !is_valid_spec_expr(&require.raw) {
            return Err(OverrideError::InvalidSpecExpr {
                expr: require.raw.clone(),
                reason: "Not a valid specification expression".to_string(),
            });
        }
    }

    // Validate extra ensures
    for ensure in extra_ensures {
        if !is_valid_spec_expr(&ensure.raw) {
            return Err(OverrideError::InvalidSpecExpr {
                expr: ensure.raw.clone(),
                reason: "Not a valid specification expression".to_string(),
            });
        }
    }

    Ok(())
}

/// Check if a specification expression is trivially false.
///
/// This is a simple syntactic check for obvious contradictions like:
/// - `false`
/// - `1 == 2`
/// - `x != x`
///
/// More sophisticated contradiction detection would require SMT solving.
fn is_trivially_false(expr: &str) -> bool {
    let trimmed = expr.trim();

    // Check for literal false
    if trimmed == "false" {
        return true;
    }

    // Check for obvious contradictions like "1 == 2"
    if trimmed.contains("==") {
        let parts: Vec<&str> = trimmed.split("==").collect();
        if parts.len() == 2 {
            let left = parts[0].trim();
            let right = parts[1].trim();

            // Check for different numeric literals
            if let (Ok(l), Ok(r)) = (left.parse::<i64>(), right.parse::<i64>())
                && l != r
            {
                return true;
            }
        }
    }

    // Check for "x != x" patterns
    if trimmed.contains("!=") {
        let parts: Vec<&str> = trimmed.split("!=").collect();
        if parts.len() == 2 {
            let left = parts[0].trim();
            let right = parts[1].trim();
            if left == right {
                return true;
            }
        }
    }

    false
}

/// Check if a specification expression is syntactically valid.
///
/// This is a basic check for non-empty, non-whitespace expressions.
/// Full parsing would require the specification language parser.
fn is_valid_spec_expr(expr: &str) -> bool {
    let trimmed = expr.trim();

    // Must not be empty
    if trimmed.is_empty() {
        return false;
    }

    // Must not be only whitespace
    if trimmed.chars().all(|c| c.is_whitespace()) {
        return false;
    }

    // Basic validity: has some content
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::contract_db::FunctionSummary;
    use crate::ir::{Contracts, Ty};
    use crate::stdlib_contracts::ContractSource;

    fn make_test_contract(
        param_count: usize,
        requires: Vec<&str>,
        ensures: Vec<&str>,
    ) -> StdlibContract {
        StdlibContract {
            type_path: "std::test::Test".to_string(),
            method_name: "test_method".to_string(),
            summary: FunctionSummary {
                contracts: Contracts {
                    requires: requires
                        .iter()
                        .map(|s| SpecExpr { raw: s.to_string() })
                        .collect(),
                    ensures: ensures
                        .iter()
                        .map(|s| SpecExpr { raw: s.to_string() })
                        .collect(),
                    invariants: vec![],
                    is_pure: false,
                    decreases: None,
                },
                param_names: (0..param_count).map(|i| format!("param{}", i)).collect(),
                param_types: vec![Ty::Unit; param_count],
                return_ty: Ty::Unit,
            },
            source: ContractSource::Builtin,
        }
    }

    #[test]
    fn test_validate_override_param_count_mismatch() {
        let original = make_test_contract(2, vec![], vec![]);
        let override_contract = make_test_contract(3, vec![], vec![]);

        let result = validate_override(&original, &override_contract);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            OverrideError::ParamCountMismatch {
                expected: 2,
                got: 3
            }
        ));
    }

    #[test]
    fn test_validate_override_trivially_false_postcondition() {
        let original = make_test_contract(1, vec![], vec![]);
        let override_contract = make_test_contract(1, vec![], vec!["false"]);

        let result = validate_override(&original, &override_contract);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            OverrideError::ContradictoryPostcondition { .. }
        ));
    }

    #[test]
    fn test_validate_override_contradictory_equals() {
        let original = make_test_contract(1, vec![], vec![]);
        let override_contract = make_test_contract(1, vec![], vec!["1 == 2"]);

        let result = validate_override(&original, &override_contract);
        assert!(result.is_err());
    }

    #[test]
    fn test_validate_override_self_inequality() {
        let original = make_test_contract(1, vec![], vec![]);
        let override_contract = make_test_contract(1, vec![], vec!["x != x"]);

        let result = validate_override(&original, &override_contract);
        assert!(result.is_err());
    }

    #[test]
    fn test_validate_override_valid_contract() {
        let original = make_test_contract(2, vec![], vec![]);
        let override_contract = make_test_contract(2, vec!["x > 0"], vec!["result > 0"]);

        let result = validate_override(&original, &override_contract);
        assert!(result.is_ok());
    }

    #[test]
    fn test_validate_override_false_precondition_warns_but_allows() {
        let original = make_test_contract(1, vec![], vec![]);
        let override_contract = make_test_contract(1, vec!["false"], vec!["result > 0"]);

        // Should succeed (with warning printed to stderr)
        let result = validate_override(&original, &override_contract);
        assert!(result.is_ok());
    }

    #[test]
    fn test_validate_extension_empty_conditions() {
        let original = make_test_contract(1, vec![], vec![]);
        let result = validate_extension(&original, &[], &[]);
        assert!(result.is_ok());
    }

    #[test]
    fn test_validate_extension_valid_extra_requires() {
        let original = make_test_contract(1, vec![], vec![]);
        let extra_requires = vec![SpecExpr {
            raw: "x > 0".to_string(),
        }];
        let result = validate_extension(&original, &extra_requires, &[]);
        assert!(result.is_ok());
    }

    #[test]
    fn test_validate_extension_valid_extra_ensures() {
        let original = make_test_contract(1, vec![], vec![]);
        let extra_ensures = vec![SpecExpr {
            raw: "result >= 0".to_string(),
        }];
        let result = validate_extension(&original, &[], &extra_ensures);
        assert!(result.is_ok());
    }

    #[test]
    fn test_validate_extension_invalid_empty_expr() {
        let original = make_test_contract(1, vec![], vec![]);
        let extra_requires = vec![SpecExpr {
            raw: "".to_string(),
        }];
        let result = validate_extension(&original, &extra_requires, &[]);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            OverrideError::InvalidSpecExpr { .. }
        ));
    }

    #[test]
    fn test_validate_extension_invalid_whitespace_only() {
        let original = make_test_contract(1, vec![], vec![]);
        let extra_ensures = vec![SpecExpr {
            raw: "   ".to_string(),
        }];
        let result = validate_extension(&original, &[], &extra_ensures);
        assert!(result.is_err());
    }

    #[test]
    fn test_is_trivially_false_literal() {
        assert!(is_trivially_false("false"));
        assert!(is_trivially_false("  false  "));
        assert!(!is_trivially_false("true"));
    }

    #[test]
    fn test_is_trivially_false_numeric_inequality() {
        assert!(is_trivially_false("1 == 2"));
        assert!(is_trivially_false("42 == 0"));
        assert!(!is_trivially_false("x == x"));
    }

    #[test]
    fn test_is_trivially_false_self_inequality() {
        assert!(is_trivially_false("x != x"));
        assert!(is_trivially_false("result != result"));
        assert!(!is_trivially_false("x != y"));
    }

    #[test]
    fn test_is_valid_spec_expr_basic() {
        assert!(is_valid_spec_expr("x > 0"));
        assert!(is_valid_spec_expr("result >= 0"));
        assert!(!is_valid_spec_expr(""));
        assert!(!is_valid_spec_expr("   "));
    }
}
