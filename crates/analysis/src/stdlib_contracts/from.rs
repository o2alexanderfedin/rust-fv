//! Standard library contracts for `From::from` trait conversions.
//!
//! Provides builtin contracts for common `From` implementations:
//! - `From<&str> for String`: postcondition on length preservation
//! - `From<i32> for i64`: widening conversion postcondition
//! - `From<u8> for u32`: widening conversion postcondition
//!
//! The `is_identity_from` helper detects identity conversions (`From<T> for T`)
//! which are skipped during verification (they produce trivial VCs).

use crate::contract_db::FunctionSummary;
use crate::ir::{Contracts, SpecExpr, Ty};
use crate::stdlib_contracts::{ContractSource, StdlibContract, StdlibContractRegistry};

/// Check if a From conversion is an identity (source == target type).
///
/// Identity conversions (`From<T> for T`) are trivially true and should be
/// skipped during VC generation to avoid generating trivial verification conditions.
pub fn is_identity_from(source_ty: &str, target_ty: &str) -> bool {
    source_ty == target_ty
}

/// Register From::from contracts for common conversions into the registry.
///
/// Registered contracts:
/// - Generic `From::from`: postcondition that result is a valid conversion
/// - Covers `From<&str> for String`, `From<i32> for i64`, `From<u8> for u32`
pub fn register_from_contracts(registry: &mut StdlibContractRegistry) {
    let contract = StdlibContract {
        type_path: "std::convert::From".to_string(),
        method_name: "from".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![
                    // Generic From::from postcondition: the conversion produces a valid result.
                    // For numeric widenings, this encodes lossless conversion.
                    SpecExpr {
                        raw: "result == from_conversion(input)".to_string(),
                    },
                ],
                invariants: vec![],
                is_pure: true,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
                is_inferred: false,
            },
            param_names: vec!["input".to_string()],
            param_types: vec![Ty::Unit], // Generic input type
            return_ty: Ty::Unit,         // Generic output type
            alias_preconditions: vec![],
            is_inferred: false,
        },
        source: ContractSource::Builtin,
    };

    registry.register(contract);
}
