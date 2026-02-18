//! Formal verification contracts for `std::vec::Vec<T>`.
//!
//! This module provides prebuilt contracts for Vec methods to enable
//! verification of user code using Vec without requiring manual contracts.
//!
//! ## Vec Model
//!
//! Vec is modeled as:
//! - `len: usize` — current number of elements
//! - `capacity: usize` — allocated capacity
//! - `data: Seq<T>` — SMT sequence containing elements
//!
//! Element-level precision: `vec.push(x)` ensures `vec[len-1] == x`.
//!
//! ## Contracts Provided
//!
//! - `push(value)` — append element
//! - `pop()` — remove and return last element
//! - `len()` — get element count (pure)
//! - `capacity()` — get allocated capacity (pure)
//! - `get(index)` — safe indexing returning `Option<&T>`
//! - `reserve(additional)` — ensure capacity for additional elements
//! - `shrink_to_fit()` — reduce capacity to len
//! - `is_empty()` — check if len is zero (pure)
//! - `clear()` — remove all elements

use crate::contract_db::FunctionSummary;
use crate::ir::{Contracts, SpecExpr, Ty, UintTy};
use crate::stdlib_contracts::{ContractSource, StdlibContract, StdlibContractRegistry};

/// Register all Vec<T> contracts into the registry.
pub fn register_vec_contracts(registry: &mut StdlibContractRegistry) {
    registry.register(vec_push_contract());
    registry.register(vec_pop_contract());
    registry.register(vec_len_contract());
    registry.register(vec_capacity_contract());
    registry.register(vec_get_contract());
    registry.register(vec_reserve_contract());
    registry.register(vec_shrink_to_fit_contract());
    registry.register(vec_is_empty_contract());
    registry.register(vec_clear_contract());
}

/// Contract for `Vec::push`.
///
/// ```text
/// pub fn push(&mut self, value: T)
/// ```
///
/// **Preconditions:** None (Rust allocator handles capacity automatically)
///
/// **Postconditions:**
/// - `self.len() == old(self.len()) + 1`
/// - `seq.nth(self.data, old(self.len())) == value` (element-level precision)
fn vec_push_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::vec::Vec".to_string(),
        method_name: "push".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![
                    SpecExpr {
                        raw: "self.len() == old(self.len()) + 1".to_string(),
                    },
                    SpecExpr {
                        raw: "seq.nth(self.data, old(self.len())) == value".to_string(),
                    },
                ],
                invariants: vec![],
                is_pure: false,
                decreases: None,
            },
            param_names: vec!["self".to_string(), "value".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit], // Generic T
            return_ty: Ty::Unit,
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `Vec::pop`.
///
/// ```text
/// pub fn pop(&mut self) -> Option<T>
/// ```
///
/// **Preconditions:** None
///
/// **Postconditions:**
/// - `result.is_some() ==> self.len() == old(self.len()) - 1`
/// - `result.is_none() ==> old(self.len()) == 0`
fn vec_pop_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::vec::Vec".to_string(),
        method_name: "pop".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![
                    SpecExpr {
                        raw: "result.is_some() ==> self.len() == old(self.len()) - 1".to_string(),
                    },
                    SpecExpr {
                        raw: "result.is_none() ==> old(self.len()) == 0".to_string(),
                    },
                ],
                invariants: vec![],
                is_pure: false,
                decreases: None,
            },
            param_names: vec!["self".to_string()],
            param_types: vec![Ty::Unit],
            return_ty: Ty::Unit, // Option<T>
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `Vec::len`.
///
/// ```text
/// pub fn len(&self) -> usize
/// ```
///
/// **Preconditions:** None
///
/// **Postconditions:** None (pure query, returns the length field)
///
/// **Pure:** Yes
fn vec_len_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::vec::Vec".to_string(),
        method_name: "len".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![],
                invariants: vec![],
                is_pure: true,
                decreases: None,
            },
            param_names: vec!["self".to_string()],
            param_types: vec![Ty::Unit],
            return_ty: Ty::Uint(UintTy::Usize),
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `Vec::capacity`.
///
/// ```text
/// pub fn capacity(&self) -> usize
/// ```
///
/// **Preconditions:** None
///
/// **Postconditions:**
/// - `result >= self.len()` (capacity is always >= len)
///
/// **Pure:** Yes
fn vec_capacity_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::vec::Vec".to_string(),
        method_name: "capacity".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "result >= self.len()".to_string(),
                }],
                invariants: vec![],
                is_pure: true,
                decreases: None,
            },
            param_names: vec!["self".to_string()],
            param_types: vec![Ty::Unit],
            return_ty: Ty::Uint(UintTy::Usize),
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `Vec::get`.
///
/// ```text
/// pub fn get(&self, index: usize) -> Option<&T>
/// ```
///
/// **Preconditions:** None (returns None if out of bounds)
///
/// **Postconditions:**
/// - `result.is_some() ==> index < self.len()`
/// - `result.is_some() ==> *result.unwrap() == seq.nth(self.data, index)`
/// - `result.is_none() ==> index >= self.len()`
fn vec_get_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::vec::Vec".to_string(),
        method_name: "get".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![
                    SpecExpr {
                        raw: "result.is_some() ==> index < self.len()".to_string(),
                    },
                    SpecExpr {
                        raw: "result.is_some() ==> *result.unwrap() == seq.nth(self.data, index)"
                            .to_string(),
                    },
                    SpecExpr {
                        raw: "result.is_none() ==> index >= self.len()".to_string(),
                    },
                ],
                invariants: vec![],
                is_pure: true,
                decreases: None,
            },
            param_names: vec!["self".to_string(), "index".to_string()],
            param_types: vec![Ty::Unit, Ty::Uint(UintTy::Usize)],
            return_ty: Ty::Unit, // Option<&T>
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `Vec::reserve`.
///
/// ```text
/// pub fn reserve(&mut self, additional: usize)
/// ```
///
/// **Preconditions:** None
///
/// **Postconditions:**
/// - `self.capacity() >= old(self.capacity()) + additional`
/// - `self.len() == old(self.len())` (reserve doesn't change length)
/// - `forall i: 0 <= i < self.len() ==> seq.nth(self.data, i) == seq.nth(old(self.data), i)` (elements preserved)
fn vec_reserve_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::vec::Vec".to_string(),
        method_name: "reserve".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![
                    SpecExpr {
                        raw: "self.capacity() >= old(self.capacity()) + additional".to_string(),
                    },
                    SpecExpr {
                        raw: "self.len() == old(self.len())".to_string(),
                    },
                    SpecExpr {
                        raw: "forall i: 0 <= i < self.len() ==> seq.nth(self.data, i) == seq.nth(old(self.data), i)".to_string(),
                    },
                ],
                invariants: vec![],
                is_pure: false,
                decreases: None,
            },
            param_names: vec!["self".to_string(), "additional".to_string()],
            param_types: vec![Ty::Unit, Ty::Uint(UintTy::Usize)],
            return_ty: Ty::Unit,
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `Vec::shrink_to_fit`.
///
/// ```text
/// pub fn shrink_to_fit(&mut self)
/// ```
///
/// **Preconditions:** None
///
/// **Postconditions:**
/// - `self.capacity() == self.len()`
/// - `self.len() == old(self.len())` (doesn't change length)
/// - `forall i: 0 <= i < self.len() ==> seq.nth(self.data, i) == seq.nth(old(self.data), i)` (elements preserved)
fn vec_shrink_to_fit_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::vec::Vec".to_string(),
        method_name: "shrink_to_fit".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![
                    SpecExpr {
                        raw: "self.capacity() == self.len()".to_string(),
                    },
                    SpecExpr {
                        raw: "self.len() == old(self.len())".to_string(),
                    },
                    SpecExpr {
                        raw: "forall i: 0 <= i < self.len() ==> seq.nth(self.data, i) == seq.nth(old(self.data), i)".to_string(),
                    },
                ],
                invariants: vec![],
                is_pure: false,
                decreases: None,
            },
            param_names: vec!["self".to_string()],
            param_types: vec![Ty::Unit],
            return_ty: Ty::Unit,
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `Vec::is_empty`.
///
/// ```text
/// pub fn is_empty(&self) -> bool
/// ```
///
/// **Preconditions:** None
///
/// **Postconditions:**
/// - `result == (self.len() == 0)`
///
/// **Pure:** Yes
fn vec_is_empty_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::vec::Vec".to_string(),
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
            },
            param_names: vec!["self".to_string()],
            param_types: vec![Ty::Unit],
            return_ty: Ty::Bool,
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `Vec::clear`.
///
/// ```text
/// pub fn clear(&mut self)
/// ```
///
/// **Preconditions:** None
///
/// **Postconditions:**
/// - `self.len() == 0`
fn vec_clear_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::vec::Vec".to_string(),
        method_name: "clear".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "self.len() == 0".to_string(),
                }],
                invariants: vec![],
                is_pure: false,
                decreases: None,
            },
            param_names: vec!["self".to_string()],
            param_types: vec![Ty::Unit],
            return_ty: Ty::Unit,
        },
        source: ContractSource::Builtin,
    }
}
