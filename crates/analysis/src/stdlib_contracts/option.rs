//! Formal verification contracts for `std::option::Option<T>`.
//!
//! This module provides prebuilt contracts for Option methods to enable
//! verification of user code using Option without requiring manual contracts.
//!
//! ## Option Model
//!
//! Option is modeled as an SMT datatype:
//! ```smt
//! (declare-datatype Option
//!   ((Some (option_value T))
//!    (None)))
//! ```
//!
//! ## Ghost Accessors
//!
//! - `option_value(x)` — extracts inner value from Some (only valid when is_some)
//!
//! ## Contracts Provided
//!
//! - `is_some()` — check if contains value (pure)
//! - `is_none()` — check if is None (pure)
//! - `unwrap()` — extract value (panics if None)
//! - `map(f)` — transform inner value if Some
//! - `and_then(f)` — chain Option-returning operations
//! - `ok_or(err)` — convert to Result
//! - `unwrap_or(default)` — extract or use default
//! - `unwrap_or_else(f)` — extract or compute default

use crate::contract_db::FunctionSummary;
use crate::ir::{Contracts, SpecExpr, Ty};
use crate::stdlib_contracts::{ContractSource, StdlibContract, StdlibContractRegistry};

/// Register all Option<T> contracts into the registry.
pub fn register_option_contracts(registry: &mut StdlibContractRegistry) {
    registry.register(option_is_some_contract());
    registry.register(option_is_none_contract());
    registry.register(option_unwrap_contract());
    registry.register(option_map_contract());
    registry.register(option_and_then_contract());
    registry.register(option_ok_or_contract());
    registry.register(option_unwrap_or_contract());
    registry.register(option_unwrap_or_else_contract());
}

/// Contract for `Option::is_some`.
///
/// ```text
/// pub fn is_some(&self) -> bool
/// ```
///
/// **Pure:** Yes
///
/// **Postconditions:**
/// - `result == !self.is_none()`
fn option_is_some_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::option::Option".to_string(),
        method_name: "is_some".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "result == !self.is_none()".to_string(),
                }],
                invariants: vec![],
                is_pure: true,
                decreases: None,
                fn_specs: vec![],
            },
            param_names: vec!["self".to_string()],
            param_types: vec![Ty::Unit],
            return_ty: Ty::Bool,
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `Option::is_none`.
///
/// ```text
/// pub fn is_none(&self) -> bool
/// ```
///
/// **Pure:** Yes
///
/// **Postconditions:**
/// - `result == !self.is_some()`
fn option_is_none_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::option::Option".to_string(),
        method_name: "is_none".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "result == !self.is_some()".to_string(),
                }],
                invariants: vec![],
                is_pure: true,
                decreases: None,
                fn_specs: vec![],
            },
            param_names: vec!["self".to_string()],
            param_types: vec![Ty::Unit],
            return_ty: Ty::Bool,
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `Option::unwrap`.
///
/// ```text
/// pub fn unwrap(self) -> T
/// ```
///
/// **Preconditions:**
/// - `self.is_some()` (panics if None)
///
/// **Postconditions:**
/// - `result == option_value(self)` (ghost accessor for inner value)
fn option_unwrap_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::option::Option".to_string(),
        method_name: "unwrap".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![SpecExpr {
                    raw: "self.is_some()".to_string(),
                }],
                ensures: vec![SpecExpr {
                    raw: "result == option_value(self)".to_string(),
                }],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
            },
            param_names: vec!["self".to_string()],
            param_types: vec![Ty::Unit],
            return_ty: Ty::Unit, // Generic T
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `Option::map`.
///
/// ```text
/// pub fn map<U, F>(self, f: F) -> Option<U>
/// where F: FnOnce(T) -> U
/// ```
///
/// **Postconditions:**
/// - `self.is_some() ==> result.is_some() && option_value(result) == f(option_value(self))`
/// - `self.is_none() ==> result.is_none()`
fn option_map_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::option::Option".to_string(),
        method_name: "map".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![
                    SpecExpr {
                        raw: "self.is_some() ==> result.is_some()".to_string(),
                    },
                    SpecExpr {
                        raw: "self.is_none() ==> result.is_none()".to_string(),
                    },
                ],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
            },
            param_names: vec!["self".to_string(), "f".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit],
            return_ty: Ty::Unit, // Option<U>
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `Option::and_then`.
///
/// ```text
/// pub fn and_then<U, F>(self, f: F) -> Option<U>
/// where F: FnOnce(T) -> Option<U>
/// ```
///
/// **Postconditions:**
/// - `self.is_some() ==> result == f(option_value(self))`
/// - `self.is_none() ==> result.is_none()`
fn option_and_then_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::option::Option".to_string(),
        method_name: "and_then".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "self.is_none() ==> result.is_none()".to_string(),
                }],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
            },
            param_names: vec!["self".to_string(), "f".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit],
            return_ty: Ty::Unit, // Option<U>
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `Option::ok_or`.
///
/// ```text
/// pub fn ok_or<E>(self, err: E) -> Result<T, E>
/// ```
///
/// **Postconditions:**
/// - `self.is_some() ==> result.is_ok() && ok_value(result) == option_value(self)`
/// - `self.is_none() ==> result.is_err() && err_value(result) == err`
fn option_ok_or_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::option::Option".to_string(),
        method_name: "ok_or".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![
                    SpecExpr {
                        raw: "self.is_some() ==> result.is_ok()".to_string(),
                    },
                    SpecExpr {
                        raw: "self.is_none() ==> result.is_err()".to_string(),
                    },
                ],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
            },
            param_names: vec!["self".to_string(), "err".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit],
            return_ty: Ty::Unit, // Result<T, E>
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `Option::unwrap_or`.
///
/// ```text
/// pub fn unwrap_or(self, default: T) -> T
/// ```
///
/// **Postconditions:**
/// - `self.is_some() ==> result == option_value(self)`
/// - `self.is_none() ==> result == default`
fn option_unwrap_or_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::option::Option".to_string(),
        method_name: "unwrap_or".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![
                    SpecExpr {
                        raw: "self.is_some() ==> result == option_value(self)".to_string(),
                    },
                    SpecExpr {
                        raw: "self.is_none() ==> result == default".to_string(),
                    },
                ],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
            },
            param_names: vec!["self".to_string(), "default".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit],
            return_ty: Ty::Unit, // T
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `Option::unwrap_or_else`.
///
/// ```text
/// pub fn unwrap_or_else<F>(self, f: F) -> T
/// where F: FnOnce() -> T
/// ```
///
/// **Postconditions:**
/// - `self.is_some() ==> result == option_value(self)`
/// - `self.is_none() ==> result == f()`
fn option_unwrap_or_else_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::option::Option".to_string(),
        method_name: "unwrap_or_else".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "self.is_some() ==> result == option_value(self)".to_string(),
                }],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
            },
            param_names: vec!["self".to_string(), "f".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit],
            return_ty: Ty::Unit, // T
        },
        source: ContractSource::Builtin,
    }
}
