//! Formal verification contracts for `std::mem` functions.
//!
//! This module provides prebuilt contracts for memory operations to enable
//! verification of code using mem functions without requiring manual contracts.
//!
//! ## Memory Model
//!
//! Memory operations are modeled at the value level:
//! - `swap` exchanges values at two mutable references
//! - `replace` returns old value while storing new value
//! - `forget` skips destructor (modeled as no-op)
//! - `size_of`/`align_of` return positive compile-time constants
//!
//! ## Contracts Provided
//!
//! - `swap(a, b)` — exchange values (postcondition: a_post == b_pre, b_post == a_pre)
//! - `replace(dest, src)` — replace and return old (postcondition: result == old, dest == new)
//! - `forget(val)` — skip destructor (no-op, postcondition: true)
//! - `size_of()` — type size (pure, result > 0)
//! - `align_of()` — type alignment (pure, result > 0)

use crate::contract_db::FunctionSummary;
use crate::ir::{Contracts, SpecExpr, Ty, UintTy};
use crate::stdlib_contracts::{ContractSource, StdlibContract, StdlibContractRegistry};

/// Register all std::mem contracts into the registry.
pub fn register_mem_contracts(registry: &mut StdlibContractRegistry) {
    registry.register(mem_swap_contract());
    registry.register(mem_replace_contract());
    registry.register(mem_forget_contract());
    registry.register(mem_size_of_contract());
    registry.register(mem_align_of_contract());
}

/// Contract for `mem::swap`.
///
/// ```rust,ignore
/// pub fn swap<T>(a: &mut T, b: &mut T)
/// ```
///
/// **Preconditions:** None
///
/// **Postconditions:**
/// - `*a == old(*b)` (a gets b's old value)
/// - `*b == old(*a)` (b gets a's old value)
fn mem_swap_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::mem".to_string(),
        method_name: "swap".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "*a == old(*b) && *b == old(*a)".to_string(),
                }],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
                is_inferred: false,
            },
            param_names: vec!["a".to_string(), "b".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit], // &mut T, &mut T
            return_ty: Ty::Unit,
            alias_preconditions: vec![],
            is_inferred: false,
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `mem::replace`.
///
/// ```rust,ignore
/// pub fn replace<T>(dest: &mut T, src: T) -> T
/// ```
///
/// **Preconditions:** None
///
/// **Postconditions:**
/// - `result == old(*dest)` (returns the old value)
/// - `*dest == src` (stores the new value)
fn mem_replace_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::mem".to_string(),
        method_name: "replace".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![
                    SpecExpr {
                        raw: "result == old(*dest)".to_string(),
                    },
                    SpecExpr {
                        raw: "*dest == src".to_string(),
                    },
                ],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
                is_inferred: false,
            },
            param_names: vec!["dest".to_string(), "src".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit], // &mut T, T
            return_ty: Ty::Unit,                   // T
            alias_preconditions: vec![],
            is_inferred: false,
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `mem::forget`.
///
/// ```rust,ignore
/// pub fn forget<T>(val: T)
/// ```
///
/// **Preconditions:** None
///
/// **Postconditions:**
/// - `true` (no-op: destructor is skipped, no observable effect)
fn mem_forget_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::mem".to_string(),
        method_name: "forget".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "true".to_string(),
                }],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
                is_inferred: false,
            },
            param_names: vec!["val".to_string()],
            param_types: vec![Ty::Unit], // T
            return_ty: Ty::Unit,
            alias_preconditions: vec![],
            is_inferred: false,
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `mem::size_of`.
///
/// ```rust,ignore
/// pub const fn size_of<T>() -> usize
/// ```
///
/// **Preconditions:** None
///
/// **Postconditions:**
/// - `result > 0` (all types have positive size)
///
/// **Pure:** Yes (compile-time constant)
fn mem_size_of_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::mem".to_string(),
        method_name: "size_of".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "result > 0".to_string(),
                }],
                invariants: vec![],
                is_pure: true,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
                is_inferred: false,
            },
            param_names: vec![],
            param_types: vec![],
            return_ty: Ty::Uint(UintTy::Usize),
            alias_preconditions: vec![],
            is_inferred: false,
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `mem::align_of`.
///
/// ```rust,ignore
/// pub const fn align_of<T>() -> usize
/// ```
///
/// **Preconditions:** None
///
/// **Postconditions:**
/// - `result > 0` (all types have positive alignment)
///
/// **Pure:** Yes (compile-time constant)
fn mem_align_of_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::mem".to_string(),
        method_name: "align_of".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "result > 0".to_string(),
                }],
                invariants: vec![],
                is_pure: true,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
                is_inferred: false,
            },
            param_names: vec![],
            param_types: vec![],
            return_ty: Ty::Uint(UintTy::Usize),
            alias_preconditions: vec![],
            is_inferred: false,
        },
        source: ContractSource::Builtin,
    }
}
