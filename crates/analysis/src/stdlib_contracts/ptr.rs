//! Formal verification contracts for `std::ptr` functions.
//!
//! This module provides prebuilt contracts for raw pointer operations to enable
//! verification of unsafe code using ptr functions without requiring manual contracts.
//!
//! ## Pointer Model
//!
//! Pointers are modeled as `BitVec(64)` addresses. Alignment is checked via
//! `addr % align == 0`. Overlap for copy_nonoverlapping is checked via address
//! range non-intersection.
//!
//! ## Contracts Provided
//!
//! - `read(src)` — read value from pointer (alignment precondition)
//! - `write(dst, val)` — write value to pointer (alignment precondition)
//! - `copy(src, dst, count)` — copy with possible overlap (alignment precondition)
//! - `copy_nonoverlapping(src, dst, count)` — copy without overlap (overlap + alignment)
//! - `swap(x, y)` — swap values at two pointers
//! - `replace(dest, src)` — replace value at pointer, returning old
//! - `drop_in_place(ptr)` — drop value at pointer
//! - `null()` — create null pointer (result == 0)
//! - `null_mut()` — create mutable null pointer (result == 0)

use crate::contract_db::FunctionSummary;
use crate::ir::{Contracts, SpecExpr, Ty, UintTy};
use crate::stdlib_contracts::{ContractSource, StdlibContract, StdlibContractRegistry};

/// Register all std::ptr contracts into the registry.
pub fn register_ptr_contracts(registry: &mut StdlibContractRegistry) {
    registry.register(ptr_read_contract());
    registry.register(ptr_write_contract());
    registry.register(ptr_copy_contract());
    registry.register(ptr_copy_nonoverlapping_contract());
    registry.register(ptr_swap_contract());
    registry.register(ptr_replace_contract());
    registry.register(ptr_drop_in_place_contract());
    registry.register(ptr_null_contract());
    registry.register(ptr_null_mut_contract());
}

/// Contract for `ptr::read`.
///
/// ```rust,ignore
/// pub unsafe fn read<T>(src: *const T) -> T
/// ```
///
/// **Preconditions:**
/// - `src` must be properly aligned: `src % align_of::<T>() == 0`
///
/// **Postconditions:** None (returns the value at the pointer)
fn ptr_read_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::ptr".to_string(),
        method_name: "read".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![SpecExpr {
                    raw: "src % align_of::<T>() == 0".to_string(),
                }],
                ensures: vec![],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
                is_inferred: false,
            },
            param_names: vec!["src".to_string()],
            param_types: vec![Ty::Unit], // *const T
            return_ty: Ty::Unit,         // T
            alias_preconditions: vec![],
            is_inferred: false,
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `ptr::write`.
///
/// ```rust,ignore
/// pub unsafe fn write<T>(dst: *mut T, src: T)
/// ```
///
/// **Preconditions:**
/// - `dst` must be properly aligned: `dst % align_of::<T>() == 0`
///
/// **Postconditions:** None
fn ptr_write_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::ptr".to_string(),
        method_name: "write".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![SpecExpr {
                    raw: "dst % align_of::<T>() == 0".to_string(),
                }],
                ensures: vec![],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
                is_inferred: false,
            },
            param_names: vec!["dst".to_string(), "src".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit], // *mut T, T
            return_ty: Ty::Unit,
            alias_preconditions: vec![],
            is_inferred: false,
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `ptr::copy`.
///
/// ```rust,ignore
/// pub unsafe fn copy<T>(src: *const T, dst: *mut T, count: usize)
/// ```
///
/// **Preconditions:**
/// - `src` must be properly aligned
/// - `dst` must be properly aligned
///
/// **Postconditions:** None (may overlap, copies count * size_of::<T>() bytes)
fn ptr_copy_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::ptr".to_string(),
        method_name: "copy".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![
                    SpecExpr {
                        raw: "src % align_of::<T>() == 0".to_string(),
                    },
                    SpecExpr {
                        raw: "dst % align_of::<T>() == 0".to_string(),
                    },
                ],
                ensures: vec![],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
                is_inferred: false,
            },
            param_names: vec!["src".to_string(), "dst".to_string(), "count".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit, Ty::Uint(UintTy::Usize)],
            return_ty: Ty::Unit,
            alias_preconditions: vec![],
            is_inferred: false,
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `ptr::copy_nonoverlapping`.
///
/// ```rust,ignore
/// pub unsafe fn copy_nonoverlapping<T>(src: *const T, dst: *mut T, count: usize)
/// ```
///
/// **Preconditions:**
/// - No overlap: `!(src <= dst + count * size && dst <= src + count * size)`
/// - `src` must be properly aligned
/// - `dst` must be properly aligned
///
/// **Postconditions:** None
fn ptr_copy_nonoverlapping_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::ptr".to_string(),
        method_name: "copy_nonoverlapping".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![
                    SpecExpr {
                        raw: "no_overlap(src, dst, count * size_of::<T>())".to_string(),
                    },
                    SpecExpr {
                        raw: "src % align_of::<T>() == 0".to_string(),
                    },
                    SpecExpr {
                        raw: "dst % align_of::<T>() == 0".to_string(),
                    },
                ],
                ensures: vec![],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
                is_inferred: false,
            },
            param_names: vec!["src".to_string(), "dst".to_string(), "count".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit, Ty::Uint(UintTy::Usize)],
            return_ty: Ty::Unit,
            alias_preconditions: vec![],
            is_inferred: false,
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `ptr::swap`.
///
/// ```rust,ignore
/// pub unsafe fn swap<T>(x: *mut T, y: *mut T)
/// ```
///
/// **Preconditions:**
/// - Both pointers must be properly aligned
///
/// **Postconditions:**
/// - Values are exchanged
fn ptr_swap_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::ptr".to_string(),
        method_name: "swap".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![
                    SpecExpr {
                        raw: "x % align_of::<T>() == 0".to_string(),
                    },
                    SpecExpr {
                        raw: "y % align_of::<T>() == 0".to_string(),
                    },
                ],
                ensures: vec![SpecExpr {
                    raw: "*x == old(*y) && *y == old(*x)".to_string(),
                }],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
                is_inferred: false,
            },
            param_names: vec!["x".to_string(), "y".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit], // *mut T, *mut T
            return_ty: Ty::Unit,
            alias_preconditions: vec![],
            is_inferred: false,
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `ptr::replace`.
///
/// ```rust,ignore
/// pub unsafe fn replace<T>(dst: *mut T, src: T) -> T
/// ```
///
/// **Preconditions:**
/// - `dst` must be properly aligned
///
/// **Postconditions:**
/// - result == old(*dst) (returns old value)
/// - *dst == src (stores new value)
fn ptr_replace_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::ptr".to_string(),
        method_name: "replace".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![SpecExpr {
                    raw: "dst % align_of::<T>() == 0".to_string(),
                }],
                ensures: vec![
                    SpecExpr {
                        raw: "result == old(*dst)".to_string(),
                    },
                    SpecExpr {
                        raw: "*dst == src".to_string(),
                    },
                ],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
                is_inferred: false,
            },
            param_names: vec!["dst".to_string(), "src".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit], // *mut T, T
            return_ty: Ty::Unit,                   // T
            alias_preconditions: vec![],
            is_inferred: false,
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `ptr::drop_in_place`.
///
/// ```rust,ignore
/// pub unsafe fn drop_in_place<T: ?Sized>(to_drop: *mut T)
/// ```
///
/// **Preconditions:**
/// - `to_drop` must be properly aligned
///
/// **Postconditions:** None (drops the value)
fn ptr_drop_in_place_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::ptr".to_string(),
        method_name: "drop_in_place".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![SpecExpr {
                    raw: "to_drop % align_of::<T>() == 0".to_string(),
                }],
                ensures: vec![],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
                is_inferred: false,
            },
            param_names: vec!["to_drop".to_string()],
            param_types: vec![Ty::Unit], // *mut T
            return_ty: Ty::Unit,
            alias_preconditions: vec![],
            is_inferred: false,
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `ptr::null`.
///
/// ```rust,ignore
/// pub const fn null<T: ?Sized + Thin>() -> *const T
/// ```
///
/// **Preconditions:** None
///
/// **Postconditions:**
/// - `result == 0` (null pointer)
fn ptr_null_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::ptr".to_string(),
        method_name: "null".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "result == 0".to_string(),
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
            return_ty: Ty::Unit, // *const T
            alias_preconditions: vec![],
            is_inferred: false,
        },
        source: ContractSource::Builtin,
    }
}

/// Contract for `ptr::null_mut`.
///
/// ```rust,ignore
/// pub const fn null_mut<T: ?Sized + Thin>() -> *mut T
/// ```
///
/// **Preconditions:** None
///
/// **Postconditions:**
/// - `result == 0` (null pointer)
fn ptr_null_mut_contract() -> StdlibContract {
    StdlibContract {
        type_path: "std::ptr".to_string(),
        method_name: "null_mut".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "result == 0".to_string(),
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
            return_ty: Ty::Unit, // *mut T
            alias_preconditions: vec![],
            is_inferred: false,
        },
        source: ContractSource::Builtin,
    }
}
