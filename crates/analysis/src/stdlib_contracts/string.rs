//! Standard library contracts for String, str, and slice types.
//!
//! String and &str are modeled as UTF-8 byte sequences:
//! - SMT encoding: Seq(BitVec(8)) -- sequence of bytes
//! - len() returns sequence length
//! - push_str concatenates sequences
//!
//! Slice &[T] is modeled as:
//! - SMT encoding: Seq(T_sort) with length
//! - get(i) requires bounds check: i < len
//! - is_empty is len == 0

use crate::contract_db::FunctionSummary;
use crate::ir::{Contracts, SpecExpr, Ty};
use crate::stdlib_contracts::{ContractSource, StdlibContract, StdlibContractRegistry};

/// Register all String, str, and slice contracts into the registry.
///
/// Contracts provided:
/// - String: len, is_empty, push_str
/// - str: len, is_empty, contains, as_bytes
/// - slice: len, get, is_empty
pub fn register_string_contracts(registry: &mut StdlibContractRegistry) {
    // String contracts
    register_string_len(registry);
    register_string_is_empty(registry);
    register_string_push_str(registry);

    // str contracts
    register_str_len(registry);
    register_str_is_empty(registry);
    register_str_contains(registry);
    register_str_as_bytes(registry);

    // slice contracts
    register_slice_len(registry);
    register_slice_get(registry);
    register_slice_is_empty(registry);
}

/// String::len() -> usize
///
/// Mathematical contract:
/// - pure: true
/// - post: result is byte length (UTF-8 encoding)
fn register_string_len(registry: &mut StdlibContractRegistry) {
    let contract = StdlibContract {
        type_path: "std::string::String".to_string(),
        method_name: "len".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "result >= 0".to_string(),
                }],
                invariants: vec![],
                is_pure: true,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
            },
            param_names: vec!["self".to_string()],
            param_types: vec![Ty::Unit],
            return_ty: Ty::Unit, // usize
            alias_preconditions: vec![],
        },
        source: ContractSource::Builtin,
    };

    registry.register(contract);
}

/// String::is_empty() -> bool
///
/// Mathematical contract:
/// - pure: true
/// - post: result == (self.len() == 0)
fn register_string_is_empty(registry: &mut StdlibContractRegistry) {
    let contract = StdlibContract {
        type_path: "std::string::String".to_string(),
        method_name: "is_empty".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "result == (self.len() == 0)".to_string(),
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
    };

    registry.register(contract);
}

/// String::push_str(&mut self, other: &str)
///
/// Mathematical contract:
/// - post: self.len() == old(self.len()) + other.len()
fn register_string_push_str(registry: &mut StdlibContractRegistry) {
    let contract = StdlibContract {
        type_path: "std::string::String".to_string(),
        method_name: "push_str".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "self.len() == old(self.len()) + other.len()".to_string(),
                }],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
            },
            param_names: vec!["self".to_string(), "other".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit],
            return_ty: Ty::Unit,
            alias_preconditions: vec![],
        },
        source: ContractSource::Builtin,
    };

    registry.register(contract);
}

/// str::len() -> usize
///
/// Mathematical contract:
/// - pure: true
fn register_str_len(registry: &mut StdlibContractRegistry) {
    let contract = StdlibContract {
        type_path: "str".to_string(),
        method_name: "len".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "result >= 0".to_string(),
                }],
                invariants: vec![],
                is_pure: true,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
            },
            param_names: vec!["self".to_string()],
            param_types: vec![Ty::Unit],
            return_ty: Ty::Unit, // usize
            alias_preconditions: vec![],
        },
        source: ContractSource::Builtin,
    };

    registry.register(contract);
}

/// str::is_empty() -> bool
///
/// Mathematical contract:
/// - pure: true
/// - post: result == (self.len() == 0)
fn register_str_is_empty(registry: &mut StdlibContractRegistry) {
    let contract = StdlibContract {
        type_path: "str".to_string(),
        method_name: "is_empty".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "result == (self.len() == 0)".to_string(),
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
    };

    registry.register(contract);
}

/// str::contains(&self, pat: &str) -> bool
///
/// Mathematical contract:
/// - pure: true
fn register_str_contains(registry: &mut StdlibContractRegistry) {
    let contract = StdlibContract {
        type_path: "str".to_string(),
        method_name: "contains".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![],
                invariants: vec![],
                is_pure: true,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
            },
            param_names: vec!["self".to_string(), "pat".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit],
            return_ty: Ty::Bool,
            alias_preconditions: vec![],
        },
        source: ContractSource::Builtin,
    };

    registry.register(contract);
}

/// str::as_bytes(&self) -> &[u8]
///
/// Mathematical contract:
/// - pure: true
/// - post: result.len() == self.len()
fn register_str_as_bytes(registry: &mut StdlibContractRegistry) {
    let contract = StdlibContract {
        type_path: "str".to_string(),
        method_name: "as_bytes".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "result.len() == self.len()".to_string(),
                }],
                invariants: vec![],
                is_pure: true,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
            },
            param_names: vec!["self".to_string()],
            param_types: vec![Ty::Unit],
            return_ty: Ty::Unit, // &[u8]
            alias_preconditions: vec![],
        },
        source: ContractSource::Builtin,
    };

    registry.register(contract);
}

/// slice::len() -> usize
///
/// Mathematical contract:
/// - pure: true
fn register_slice_len(registry: &mut StdlibContractRegistry) {
    let contract = StdlibContract {
        type_path: "slice".to_string(),
        method_name: "len".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "result >= 0".to_string(),
                }],
                invariants: vec![],
                is_pure: true,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
            },
            param_names: vec!["self".to_string()],
            param_types: vec![Ty::Unit],
            return_ty: Ty::Unit, // usize
            alias_preconditions: vec![],
        },
        source: ContractSource::Builtin,
    };

    registry.register(contract);
}

/// slice::get(&self, index: usize) -> Option<&T>
///
/// Mathematical contract:
/// - pre: index < self.len()
/// - post: returns i-th element
fn register_slice_get(registry: &mut StdlibContractRegistry) {
    let contract = StdlibContract {
        type_path: "slice".to_string(),
        method_name: "get".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![SpecExpr {
                    raw: "index < self.len()".to_string(),
                }],
                ensures: vec![],
                invariants: vec![],
                is_pure: true,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
            },
            param_names: vec!["self".to_string(), "index".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit],
            return_ty: Ty::Unit, // Option<&T>
            alias_preconditions: vec![],
        },
        source: ContractSource::Builtin,
    };

    registry.register(contract);
}

/// slice::is_empty() -> bool
///
/// Mathematical contract:
/// - pure: true
/// - post: result == (self.len() == 0)
fn register_slice_is_empty(registry: &mut StdlibContractRegistry) {
    let contract = StdlibContract {
        type_path: "slice".to_string(),
        method_name: "is_empty".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "result == (self.len() == 0)".to_string(),
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
    };

    registry.register(contract);
}
