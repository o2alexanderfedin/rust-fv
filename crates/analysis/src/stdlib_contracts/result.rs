//! Formal verification contracts for `std::result::Result<T, E>`.
//!
//! This module provides prebuilt contracts for Result methods to enable
//! verification of user code using Result without requiring manual contracts.
//!
//! ## Result Model
//!
//! Result is modeled as an SMT datatype:
//! ```smt
//! (declare-datatype Result
//!   ((Ok (ok_value T))
//!    (Err (err_value E))))
//! ```
//!
//! ## Ghost Accessors
//!
//! - `ok_value(x)` — extracts inner value from Ok (only valid when is_ok)
//! - `err_value(x)` — extracts error from Err (only valid when is_err)
//!
//! ## Contracts Provided
//!
//! - `is_ok()` — check if contains Ok value (pure)
//! - `is_err()` — check if is Err (pure)
//! - `unwrap()` — extract Ok value (panics if Err)
//! - `unwrap_err()` — extract Err value (panics if Ok)
//! - `map(f)` — transform Ok value
//! - `map_err(f)` — transform Err value
//! - `and_then(f)` — chain Result-returning operations
//! - `ok()` — convert to Option of Ok value
//! - `err()` — convert to Option of Err value

use crate::contract_db::FunctionSummary;
use crate::ir::{Contracts, SpecExpr, Ty};
use crate::stdlib_contracts::{ContractSource, StdlibContract, StdlibContractRegistry};

/// Register all Result<T, E> contracts into the registry.
pub fn register_result_contracts(registry: &mut StdlibContractRegistry) {
    registry.register(result_is_ok_contract());
    registry.register(result_is_err_contract());
    registry.register(result_unwrap_contract());
    registry.register(result_unwrap_err_contract());
    registry.register(result_map_contract());
    registry.register(result_map_err_contract());
    registry.register(result_and_then_contract());
    registry.register(result_ok_contract());
    registry.register(result_err_contract());
}

/// Contract for `Result::is_ok`.
///
/// ```rust,ignore
/// pub fn is_ok(&self) -> bool
/// ```
///
/// **Pure:** Yes
///
/// **Postconditions:**
/// - `result == !self.is_err()`
fn result_is_ok_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::result::Result".to_string(),
        method_name: "is_ok".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "result == !self.is_err()".to_string(),
                }],
                invariants: vec![],
                is_pure: true,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
            },
            param_names: vec!["self".to_string()],
            param_types: vec![Ty::Unit],
            return_ty: Ty::Bool,
            alias_preconditions: vec![],
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `Result::is_err`.
///
/// ```rust,ignore
/// pub fn is_err(&self) -> bool
/// ```
///
/// **Pure:** Yes
///
/// **Postconditions:**
/// - `result == !self.is_ok()`
fn result_is_err_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::result::Result".to_string(),
        method_name: "is_err".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "result == !self.is_ok()".to_string(),
                }],
                invariants: vec![],
                is_pure: true,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
            },
            param_names: vec!["self".to_string()],
            param_types: vec![Ty::Unit],
            return_ty: Ty::Bool,
            alias_preconditions: vec![],
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `Result::unwrap`.
///
/// ```rust,ignore
/// pub fn unwrap(self) -> T
/// ```
///
/// **Preconditions:**
/// - `self.is_ok()` (panics if Err)
///
/// **Postconditions:**
/// - `result == ok_value(self)` (ghost accessor for Ok value)
fn result_unwrap_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::result::Result".to_string(),
        method_name: "unwrap".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![SpecExpr {
                    raw: "self.is_ok()".to_string(),
                }],
                ensures: vec![SpecExpr {
                    raw: "result == ok_value(self)".to_string(),
                }],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
            },
            param_names: vec!["self".to_string()],
            param_types: vec![Ty::Unit],
            return_ty: Ty::Unit, // T
            alias_preconditions: vec![],
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `Result::unwrap_err`.
///
/// ```rust,ignore
/// pub fn unwrap_err(self) -> E
/// ```
///
/// **Preconditions:**
/// - `self.is_err()` (panics if Ok)
///
/// **Postconditions:**
/// - `result == err_value(self)` (ghost accessor for Err value)
fn result_unwrap_err_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::result::Result".to_string(),
        method_name: "unwrap_err".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![SpecExpr {
                    raw: "self.is_err()".to_string(),
                }],
                ensures: vec![SpecExpr {
                    raw: "result == err_value(self)".to_string(),
                }],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
            },
            param_names: vec!["self".to_string()],
            param_types: vec![Ty::Unit],
            return_ty: Ty::Unit, // E
            alias_preconditions: vec![],
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `Result::map`.
///
/// ```rust,ignore
/// pub fn map<U, F>(self, f: F) -> Result<U, E>
/// where F: FnOnce(T) -> U
/// ```
///
/// **Postconditions:**
/// - `self.is_ok() ==> result.is_ok() && ok_value(result) == f(ok_value(self))`
/// - `self.is_err() ==> result.is_err() && err_value(result) == err_value(self)`
fn result_map_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::result::Result".to_string(),
        method_name: "map".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![
                    SpecExpr {
                        raw: "self.is_ok() ==> result.is_ok()".to_string(),
                    },
                    SpecExpr {
                        raw: "self.is_err() ==> result.is_err()".to_string(),
                    },
                ],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
            },
            param_names: vec!["self".to_string(), "f".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit],
            return_ty: Ty::Unit, // Result<U, E>
            alias_preconditions: vec![],
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `Result::map_err`.
///
/// ```rust,ignore
/// pub fn map_err<F, O>(self, f: F) -> Result<T, O>
/// where F: FnOnce(E) -> O
/// ```
///
/// **Postconditions:**
/// - `self.is_ok() ==> result.is_ok() && ok_value(result) == ok_value(self)`
/// - `self.is_err() ==> result.is_err() && err_value(result) == f(err_value(self))`
fn result_map_err_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::result::Result".to_string(),
        method_name: "map_err".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![
                    SpecExpr {
                        raw: "self.is_ok() ==> result.is_ok()".to_string(),
                    },
                    SpecExpr {
                        raw: "self.is_err() ==> result.is_err()".to_string(),
                    },
                ],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
            },
            param_names: vec!["self".to_string(), "f".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit],
            return_ty: Ty::Unit, // Result<T, O>
            alias_preconditions: vec![],
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `Result::and_then`.
///
/// ```rust,ignore
/// pub fn and_then<U, F>(self, f: F) -> Result<U, E>
/// where F: FnOnce(T) -> Result<U, E>
/// ```
///
/// **Postconditions:**
/// - `self.is_ok() ==> result == f(ok_value(self))`
/// - `self.is_err() ==> result.is_err() && err_value(result) == err_value(self)`
fn result_and_then_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::result::Result".to_string(),
        method_name: "and_then".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "self.is_err() ==> result.is_err()".to_string(),
                }],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
            },
            param_names: vec!["self".to_string(), "f".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit],
            return_ty: Ty::Unit, // Result<U, E>
            alias_preconditions: vec![],
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `Result::ok`.
///
/// ```rust,ignore
/// pub fn ok(self) -> Option<T>
/// ```
///
/// **Postconditions:**
/// - `self.is_ok() ==> result.is_some() && option_value(result) == ok_value(self)`
/// - `self.is_err() ==> result.is_none()`
fn result_ok_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::result::Result".to_string(),
        method_name: "ok".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![
                    SpecExpr {
                        raw: "self.is_ok() ==> result.is_some()".to_string(),
                    },
                    SpecExpr {
                        raw: "self.is_err() ==> result.is_none()".to_string(),
                    },
                ],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
            },
            param_names: vec!["self".to_string()],
            param_types: vec![Ty::Unit],
            return_ty: Ty::Unit, // Option<T>
            alias_preconditions: vec![],
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `Result::err`.
///
/// ```rust,ignore
/// pub fn err(self) -> Option<E>
/// ```
///
/// **Postconditions:**
/// - `self.is_ok() ==> result.is_none()`
/// - `self.is_err() ==> result.is_some() && option_value(result) == err_value(self)`
fn result_err_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::result::Result".to_string(),
        method_name: "err".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![
                    SpecExpr {
                        raw: "self.is_ok() ==> result.is_none()".to_string(),
                    },
                    SpecExpr {
                        raw: "self.is_err() ==> result.is_some()".to_string(),
                    },
                ],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
            },
            param_names: vec!["self".to_string()],
            param_types: vec![Ty::Unit],
            return_ty: Ty::Unit, // Option<E>
            alias_preconditions: vec![],
        },
        source: ContractSource::Builtin,
    }
}
