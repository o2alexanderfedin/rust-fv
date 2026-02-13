//! Unsafe code analysis and classification.
//!
//! This module provides functions to detect and analyze unsafe blocks and operations
//! in Rust functions. It classifies raw pointer operations, determines which require
//! null checks or bounds checks, and identifies missing safety contracts.

use crate::ir::{Function, RawPtrProvenance, SpecExpr, UnsafeBlockInfo, UnsafeOperation};

/// Detects all unsafe blocks in a function.
///
/// If the function is declared as `unsafe fn` but has no explicit unsafe blocks,
/// this creates a synthetic block representing the entire function body.
pub fn detect_unsafe_blocks(func: &Function) -> Vec<UnsafeBlockInfo> {
    if func.is_unsafe_fn && func.unsafe_blocks.is_empty() {
        // Unsafe function with no explicit unsafe blocks - create synthetic block
        vec![UnsafeBlockInfo {
            block_index: 0,
            source_description: format!("unsafe function '{}'", func.name),
            reason: "function declared unsafe".to_string(),
        }]
    } else {
        func.unsafe_blocks.clone()
    }
}

/// Extracts all unsafe operations from a function.
pub fn extract_unsafe_operations(func: &Function) -> Vec<UnsafeOperation> {
    func.unsafe_operations.clone()
}

/// Classifies the provenance of a raw pointer operation.
///
/// For pointer arithmetic, provenance is always Unknown (arithmetic invalidates provenance).
pub fn classify_provenance(op: &UnsafeOperation) -> RawPtrProvenance {
    match op {
        UnsafeOperation::RawDeref { provenance, .. } => provenance.clone(),
        UnsafeOperation::PtrCast { provenance, .. } => provenance.clone(),
        UnsafeOperation::PtrArithmetic { .. } => RawPtrProvenance::Unknown,
    }
}

/// Returns true if the operation requires a null-check VC.
///
/// FromRef pointers are derived from safe references (guaranteed non-null by Rust type system).
/// Only RawDeref operations require null checks (PtrArithmetic and PtrCast don't dereference).
pub fn needs_null_check(op: &UnsafeOperation) -> bool {
    match op {
        UnsafeOperation::RawDeref { provenance, .. } => {
            !matches!(provenance, RawPtrProvenance::FromRef)
        }
        UnsafeOperation::PtrArithmetic { .. } | UnsafeOperation::PtrCast { .. } => false,
    }
}

/// Returns true if the operation requires a bounds-check VC.
///
/// Only PtrArithmetic operations require bounds checks (pointer offset must stay within allocation).
pub fn needs_bounds_check(op: &UnsafeOperation) -> bool {
    matches!(op, UnsafeOperation::PtrArithmetic { .. })
}

/// Checks if an unsafe function is missing safety contracts.
///
/// Returns a warning message if the function is `unsafe fn` but has no
/// #[unsafe_requires], #[unsafe_ensures], or #[trusted] annotation.
pub fn check_missing_unsafe_contracts(func: &Function) -> Option<String> {
    if !func.is_unsafe_fn {
        return None;
    }

    let has_contracts = match &func.unsafe_contracts {
        None => false,
        Some(contracts) => {
            !contracts.requires.is_empty() || !contracts.ensures.is_empty() || contracts.is_trusted
        }
    };

    if has_contracts {
        None
    } else {
        Some(format!(
            "unsafe function '{}' has no safety contracts -- consider adding #[unsafe_requires] / #[unsafe_ensures] or #[trusted]",
            func.name
        ))
    }
}

/// Returns true if the function is marked as trusted.
///
/// Trusted functions have body verification skipped, but contracts are enforced at call sites.
pub fn is_trusted_function(func: &Function) -> bool {
    func.unsafe_contracts
        .as_ref()
        .map(|c| c.is_trusted)
        .unwrap_or(false)
}

/// Returns references to the function's unsafe preconditions.
pub fn get_unsafe_requires(func: &Function) -> Vec<&SpecExpr> {
    func.unsafe_contracts
        .as_ref()
        .map(|c| c.requires.iter().collect())
        .unwrap_or_default()
}

/// Returns references to the function's unsafe postconditions.
pub fn get_unsafe_ensures(func: &Function) -> Vec<&SpecExpr> {
    func.unsafe_contracts
        .as_ref()
        .map(|c| c.ensures.iter().collect())
        .unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{BasicBlock, Contracts, Local, Ty, UnsafeContracts};

    fn make_test_function(
        is_unsafe_fn: bool,
        unsafe_blocks: Vec<UnsafeBlockInfo>,
        unsafe_operations: Vec<UnsafeOperation>,
        unsafe_contracts: Option<UnsafeContracts>,
    ) -> Function {
        Function {
            name: "test_fn".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Bool),
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: crate::ir::Terminator::Return,
            }],
            contracts: Contracts::default(),
            loops: vec![],
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks,
            unsafe_operations,
            unsafe_contracts,
            is_unsafe_fn,
        }
    }

    #[test]
    fn test_detect_unsafe_blocks_empty() {
        let func = make_test_function(false, vec![], vec![], None);
        let blocks = detect_unsafe_blocks(&func);
        assert!(blocks.is_empty());
    }

    #[test]
    fn test_detect_unsafe_blocks_with_blocks() {
        let block_info = UnsafeBlockInfo {
            block_index: 1,
            source_description: "unsafe block at line 42".to_string(),
            reason: "raw pointer dereference".to_string(),
        };
        let func = make_test_function(false, vec![block_info.clone()], vec![], None);
        let blocks = detect_unsafe_blocks(&func);
        assert_eq!(blocks.len(), 1);
        assert_eq!(blocks[0].block_index, 1);
    }

    #[test]
    fn test_detect_unsafe_blocks_unsafe_fn_synthetic() {
        let func = make_test_function(true, vec![], vec![], None);
        let blocks = detect_unsafe_blocks(&func);
        assert_eq!(blocks.len(), 1);
        assert_eq!(blocks[0].block_index, 0);
        assert!(blocks[0].source_description.contains("unsafe function"));
        assert!(blocks[0].reason.contains("function declared unsafe"));
    }

    #[test]
    fn test_extract_unsafe_operations() {
        let op = UnsafeOperation::RawDeref {
            ptr_local: "p".to_string(),
            ptr_ty: Ty::RawPtr(
                Box::new(Ty::Int(crate::ir::IntTy::I32)),
                crate::ir::Mutability::Shared,
            ),
            provenance: RawPtrProvenance::Unknown,
            block_index: 1,
        };
        let func = make_test_function(false, vec![], vec![op.clone()], None);
        let ops = extract_unsafe_operations(&func);
        assert_eq!(ops.len(), 1);
        assert_eq!(ops[0], op);
    }

    #[test]
    fn test_classify_provenance_raw_deref() {
        let op = UnsafeOperation::RawDeref {
            ptr_local: "p".to_string(),
            ptr_ty: Ty::RawPtr(
                Box::new(Ty::Int(crate::ir::IntTy::I32)),
                crate::ir::Mutability::Shared,
            ),
            provenance: RawPtrProvenance::FromRef,
            block_index: 1,
        };
        assert_eq!(classify_provenance(&op), RawPtrProvenance::FromRef);
    }

    #[test]
    fn test_classify_provenance_ptr_arithmetic() {
        let op = UnsafeOperation::PtrArithmetic {
            ptr_local: "p".to_string(),
            offset_local: "off".to_string(),
            ptr_ty: Ty::RawPtr(
                Box::new(Ty::Int(crate::ir::IntTy::I32)),
                crate::ir::Mutability::Shared,
            ),
            is_signed_offset: false,
            block_index: 1,
        };
        assert_eq!(classify_provenance(&op), RawPtrProvenance::Unknown);
    }

    #[test]
    fn test_needs_null_check_from_ref() {
        let op = UnsafeOperation::RawDeref {
            ptr_local: "p".to_string(),
            ptr_ty: Ty::RawPtr(
                Box::new(Ty::Int(crate::ir::IntTy::I32)),
                crate::ir::Mutability::Shared,
            ),
            provenance: RawPtrProvenance::FromRef,
            block_index: 1,
        };
        assert!(!needs_null_check(&op)); // FromRef is guaranteed non-null
    }

    #[test]
    fn test_needs_null_check_from_int() {
        let op = UnsafeOperation::RawDeref {
            ptr_local: "p".to_string(),
            ptr_ty: Ty::RawPtr(
                Box::new(Ty::Int(crate::ir::IntTy::I32)),
                crate::ir::Mutability::Shared,
            ),
            provenance: RawPtrProvenance::FromInt,
            block_index: 1,
        };
        assert!(needs_null_check(&op));
    }

    #[test]
    fn test_needs_null_check_unknown() {
        let op = UnsafeOperation::RawDeref {
            ptr_local: "p".to_string(),
            ptr_ty: Ty::RawPtr(
                Box::new(Ty::Int(crate::ir::IntTy::I32)),
                crate::ir::Mutability::Shared,
            ),
            provenance: RawPtrProvenance::Unknown,
            block_index: 1,
        };
        assert!(needs_null_check(&op));
    }

    #[test]
    fn test_needs_bounds_check_arithmetic() {
        let op = UnsafeOperation::PtrArithmetic {
            ptr_local: "p".to_string(),
            offset_local: "off".to_string(),
            ptr_ty: Ty::RawPtr(
                Box::new(Ty::Int(crate::ir::IntTy::I32)),
                crate::ir::Mutability::Shared,
            ),
            is_signed_offset: false,
            block_index: 1,
        };
        assert!(needs_bounds_check(&op));
    }

    #[test]
    fn test_needs_bounds_check_deref() {
        let op = UnsafeOperation::RawDeref {
            ptr_local: "p".to_string(),
            ptr_ty: Ty::RawPtr(
                Box::new(Ty::Int(crate::ir::IntTy::I32)),
                crate::ir::Mutability::Shared,
            ),
            provenance: RawPtrProvenance::Unknown,
            block_index: 1,
        };
        assert!(!needs_bounds_check(&op));
    }

    #[test]
    fn test_check_missing_contracts_unsafe_fn() {
        let func = make_test_function(true, vec![], vec![], None);
        let warning = check_missing_unsafe_contracts(&func);
        assert!(warning.is_some());
        let msg = warning.unwrap();
        assert!(msg.contains("unsafe function"));
        assert!(msg.contains("no safety contracts"));
    }

    #[test]
    fn test_check_missing_contracts_annotated() {
        let contracts = UnsafeContracts {
            requires: vec![SpecExpr {
                raw: "true".to_string(),
            }],
            ensures: vec![],
            is_trusted: false,
        };
        let func = make_test_function(true, vec![], vec![], Some(contracts));
        let warning = check_missing_unsafe_contracts(&func);
        assert!(warning.is_none());
    }

    #[test]
    fn test_check_missing_contracts_safe_fn() {
        let func = make_test_function(false, vec![], vec![], None);
        let warning = check_missing_unsafe_contracts(&func);
        assert!(warning.is_none());
    }

    #[test]
    fn test_is_trusted_function_true() {
        let contracts = UnsafeContracts {
            requires: vec![],
            ensures: vec![],
            is_trusted: true,
        };
        let func = make_test_function(true, vec![], vec![], Some(contracts));
        assert!(is_trusted_function(&func));
    }

    #[test]
    fn test_is_trusted_function_false() {
        let func = make_test_function(true, vec![], vec![], None);
        assert!(!is_trusted_function(&func));
    }

    #[test]
    fn test_get_unsafe_requires() {
        let contracts = UnsafeContracts {
            requires: vec![
                SpecExpr {
                    raw: "true".to_string(),
                },
                SpecExpr {
                    raw: "false".to_string(),
                },
            ],
            ensures: vec![],
            is_trusted: false,
        };
        let func = make_test_function(true, vec![], vec![], Some(contracts));
        let requires = get_unsafe_requires(&func);
        assert_eq!(requires.len(), 2);
    }

    #[test]
    fn test_get_unsafe_ensures() {
        let contracts = UnsafeContracts {
            requires: vec![],
            ensures: vec![SpecExpr {
                raw: "true".to_string(),
            }],
            is_trusted: false,
        };
        let func = make_test_function(true, vec![], vec![], Some(contracts));
        let ensures = get_unsafe_ensures(&func);
        assert_eq!(ensures.len(), 1);
    }

    #[test]
    fn test_get_unsafe_requires_none() {
        let func = make_test_function(false, vec![], vec![], None);
        let requires = get_unsafe_requires(&func);
        assert!(requires.is_empty());
    }
}
