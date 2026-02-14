//! Unit tests for unsafe code IR types (Task 1 - Phase 10-01).
//!
//! Tests RawPtrProvenance, UnsafeBlockInfo, UnsafeOperation, UnsafeContracts,
//! Function extensions, VcKind::MemorySafety, and ptr_addr_sort helper.

use rust_fv_analysis::encode_sort::ptr_addr_sort;
use rust_fv_analysis::ir::*;
use rust_fv_analysis::vcgen::VcKind;
use rust_fv_smtlib::sort::Sort;

// ====== RawPtrProvenance tests ======

#[test]
fn test_raw_ptr_provenance_variants() {
    let from_ref = RawPtrProvenance::FromRef;
    let from_int = RawPtrProvenance::FromInt;
    let unknown = RawPtrProvenance::Unknown;

    assert_eq!(from_ref, RawPtrProvenance::FromRef);
    assert_ne!(from_ref, from_int);
    assert_ne!(from_ref, unknown);
    assert_ne!(from_int, unknown);
}

// ====== UnsafeBlockInfo tests ======

#[test]
fn test_unsafe_block_info_creation() {
    let block_info = UnsafeBlockInfo {
        block_index: 3,
        source_description: "unsafe block at line 42".to_string(),
        reason: "raw pointer dereference".to_string(),
    };

    assert_eq!(block_info.block_index, 3);
    assert_eq!(block_info.source_description, "unsafe block at line 42");
    assert_eq!(block_info.reason, "raw pointer dereference");
}

// ====== UnsafeOperation tests ======

#[test]
fn test_unsafe_operation_raw_deref() {
    let op = UnsafeOperation::RawDeref {
        ptr_local: "_1".to_string(),
        ptr_ty: Ty::Uint(UintTy::Usize),
        provenance: RawPtrProvenance::FromRef,
        block_index: 2,
    };

    match op {
        UnsafeOperation::RawDeref {
            ptr_local,
            ptr_ty,
            provenance,
            block_index,
        } => {
            assert_eq!(ptr_local, "_1");
            assert_eq!(ptr_ty, Ty::Uint(UintTy::Usize));
            assert_eq!(provenance, RawPtrProvenance::FromRef);
            assert_eq!(block_index, 2);
        }
        _ => panic!("Expected RawDeref variant"),
    }
}

#[test]
fn test_unsafe_operation_ptr_arithmetic() {
    let op = UnsafeOperation::PtrArithmetic {
        ptr_local: "_2".to_string(),
        offset_local: "_3".to_string(),
        ptr_ty: Ty::Uint(UintTy::Usize),
        is_signed_offset: false,
        block_index: 4,
    };

    match op {
        UnsafeOperation::PtrArithmetic {
            ptr_local,
            offset_local,
            ptr_ty,
            is_signed_offset,
            block_index,
        } => {
            assert_eq!(ptr_local, "_2");
            assert_eq!(offset_local, "_3");
            assert_eq!(ptr_ty, Ty::Uint(UintTy::Usize));
            assert!(!is_signed_offset);
            assert_eq!(block_index, 4);
        }
        _ => panic!("Expected PtrArithmetic variant"),
    }
}

#[test]
fn test_unsafe_operation_ptr_cast() {
    let op = UnsafeOperation::PtrCast {
        source_local: "_4".to_string(),
        source_ty: Ty::Uint(UintTy::Usize),
        target_ty: Ty::Uint(UintTy::U64),
        provenance: RawPtrProvenance::FromInt,
        block_index: 5,
    };

    match op {
        UnsafeOperation::PtrCast {
            source_local,
            source_ty,
            target_ty,
            provenance,
            block_index,
        } => {
            assert_eq!(source_local, "_4");
            assert_eq!(source_ty, Ty::Uint(UintTy::Usize));
            assert_eq!(target_ty, Ty::Uint(UintTy::U64));
            assert_eq!(provenance, RawPtrProvenance::FromInt);
            assert_eq!(block_index, 5);
        }
        _ => panic!("Expected PtrCast variant"),
    }
}

// ====== UnsafeContracts tests ======

#[test]
fn test_unsafe_contracts_default() {
    let contracts = UnsafeContracts::default();
    assert!(contracts.requires.is_empty());
    assert!(contracts.ensures.is_empty());
    assert!(!contracts.is_trusted);
}

#[test]
fn test_unsafe_contracts_with_requires() {
    let contracts = UnsafeContracts {
        requires: vec![SpecExpr {
            raw: "ptr != null".to_string(),
        }],
        ensures: vec![],
        is_trusted: false,
    };
    assert_eq!(contracts.requires.len(), 1);
    assert!(contracts.ensures.is_empty());
    assert!(!contracts.is_trusted);
}

#[test]
fn test_unsafe_contracts_trusted() {
    let contracts = UnsafeContracts {
        requires: vec![],
        ensures: vec![],
        is_trusted: true,
    };
    assert!(contracts.requires.is_empty());
    assert!(contracts.ensures.is_empty());
    assert!(contracts.is_trusted);
}

// ====== Function unsafe fields tests ======

#[test]
fn test_function_unsafe_fields() {
    let func = Function {
        name: "test_unsafe".to_string(),
        params: vec![],
        return_local: Local::new("_0", Ty::Unit),
        locals: vec![],
        basic_blocks: vec![],
        contracts: Contracts::default(),
        loops: vec![],
        generic_params: vec![],
        prophecies: vec![],
        lifetime_params: vec![],
        outlives_constraints: vec![],
        borrow_info: vec![],
        reborrow_chains: vec![],
        unsafe_blocks: vec![UnsafeBlockInfo {
            block_index: 1,
            source_description: "unsafe block".to_string(),
            reason: "raw deref".to_string(),
        }],
        unsafe_operations: vec![],
        unsafe_contracts: None,
        is_unsafe_fn: false,
        thread_spawns: vec![],
        atomic_ops: vec![],
        sync_ops: vec![],
        lock_invariants: vec![],
        concurrency_config: None,
    };

    assert_eq!(func.unsafe_blocks.len(), 1);
    assert_eq!(func.unsafe_operations.len(), 0);
    assert!(func.unsafe_contracts.is_none());
    assert!(!func.is_unsafe_fn);
}

#[test]
fn test_function_is_unsafe_fn() {
    let func = Function {
        name: "unsafe_function".to_string(),
        params: vec![],
        return_local: Local::new("_0", Ty::Unit),
        locals: vec![],
        basic_blocks: vec![],
        contracts: Contracts::default(),
        loops: vec![],
        generic_params: vec![],
        prophecies: vec![],
        lifetime_params: vec![],
        outlives_constraints: vec![],
        borrow_info: vec![],
        reborrow_chains: vec![],
        unsafe_blocks: vec![],
        unsafe_operations: vec![],
        unsafe_contracts: Some(UnsafeContracts::default()),
        is_unsafe_fn: true,
        thread_spawns: vec![],
        atomic_ops: vec![],
        sync_ops: vec![],
        lock_invariants: vec![],
        concurrency_config: None,
    };

    assert!(func.is_unsafe_fn);
    assert!(func.unsafe_contracts.is_some());
}

// ====== ptr_addr_sort tests ======

#[test]
fn test_ptr_addr_sort() {
    let sort = ptr_addr_sort();
    assert_eq!(sort, Sort::BitVec(64));
}

// ====== VcKind::MemorySafety tests ======

#[test]
fn test_vc_kind_memory_safety_eq() {
    let ms1 = VcKind::MemorySafety;
    let ms2 = VcKind::MemorySafety;
    let bv = VcKind::BorrowValidity;

    assert_eq!(ms1, ms2);
    assert_ne!(ms1, bv);
}

#[test]
fn test_vc_kind_memory_safety_clone() {
    let original = VcKind::MemorySafety;
    let cloned = original.clone();
    assert_eq!(original, cloned);
}
