//! Tests for NonNull<T> type encoding and null-check suppression.
//!
//! Verifies that:
//! - Ty::NonNull(Box::new(Ty::Uint(UintTy::U32))) correctly represents NonNull<u32>
//! - needs_null_check returns false when ptr_ty is Ty::NonNull
//! - needs_null_check returns true when ptr_ty is Ty::RawPtr (standard raw pointer)
//! - NonNull::as_ptr() result inherits non-null guarantee (FromRef provenance)
//! - VCGen skips both null-check AND alignment VCs for NonNull types

use rust_fv_analysis::ir::{
    BasicBlock, Contracts, Function, IntTy, Local, Mutability, RawPtrProvenance, Terminator, Ty,
    UintTy, UnsafeOperation,
};
use rust_fv_analysis::unsafe_analysis::needs_null_check;

fn make_test_function(unsafe_operations: Vec<UnsafeOperation>) -> Function {
    Function {
        name: "test_fn".to_string(),
        params: vec![],
        return_local: Local::new("_0", Ty::Bool),
        locals: vec![],
        basic_blocks: vec![BasicBlock {
            statements: vec![],
            terminator: Terminator::Return,
        }],
        contracts: Contracts::default(),
        loops: vec![],
        generic_params: vec![],
        prophecies: vec![],
        lifetime_params: vec![],
        outlives_constraints: vec![],
        borrow_info: vec![],
        reborrow_chains: vec![],
        unsafe_blocks: vec![],
        unsafe_operations,
        unsafe_contracts: None,
        is_unsafe_fn: false,
        thread_spawns: vec![],
        atomic_ops: vec![],
        sync_ops: vec![],
        lock_invariants: vec![],
        concurrency_config: None,
        source_names: std::collections::HashMap::new(),
        coroutine_info: None,
        refcell_ghost_states: vec![],
        maybeuninit_ghost_states: vec![],
    }
}

#[test]
fn nonnull_type_represents_nonnull_u32() {
    // Test 1: Ty::NonNull(Box::new(Ty::Uint(UintTy::U32))) correctly represents NonNull<u32>
    let ty = Ty::NonNull(Box::new(Ty::Uint(UintTy::U32)));
    match &ty {
        Ty::NonNull(inner) => {
            assert_eq!(**inner, Ty::Uint(UintTy::U32));
        }
        _ => panic!("Expected Ty::NonNull variant"),
    }
}

#[test]
fn nonnull_needs_null_check_returns_false() {
    // Test 2: needs_null_check returns false when ptr_ty is Ty::NonNull
    let op = UnsafeOperation::RawDeref {
        ptr_local: "p".to_string(),
        ptr_ty: Ty::NonNull(Box::new(Ty::Uint(UintTy::U32))),
        provenance: RawPtrProvenance::Unknown,
        block_index: 0,
    };
    assert!(
        !needs_null_check(&op),
        "NonNull type should not require null check"
    );
}

#[test]
fn rawptr_needs_null_check_returns_true() {
    // Test 3: needs_null_check returns true when ptr_ty is Ty::RawPtr (standard raw pointer)
    let op = UnsafeOperation::RawDeref {
        ptr_local: "p".to_string(),
        ptr_ty: Ty::RawPtr(Box::new(Ty::Uint(UintTy::U32)), Mutability::Shared),
        provenance: RawPtrProvenance::Unknown,
        block_index: 0,
    };
    assert!(
        needs_null_check(&op),
        "RawPtr with Unknown provenance should require null check"
    );
}

#[test]
fn nonnull_as_ptr_inherits_nonnull_guarantee() {
    // Test 4: NonNull::as_ptr() result (a *const T) inherits non-null guarantee
    // When a raw pointer has FromRef provenance (derived from NonNull), needs_null_check returns false
    let op = UnsafeOperation::RawDeref {
        ptr_local: "p".to_string(),
        ptr_ty: Ty::RawPtr(Box::new(Ty::Uint(UintTy::U32)), Mutability::Shared),
        provenance: RawPtrProvenance::FromRef,
        block_index: 0,
    };
    assert!(
        !needs_null_check(&op),
        "FromRef provenance (derived from NonNull via as_ptr()) should not require null check"
    );
}

#[test]
fn nonnull_vcgen_skips_null_and_alignment_vcs() {
    // Test 5: VCGen skips both null-check AND alignment VCs for NonNull types
    let func = make_test_function(vec![UnsafeOperation::RawDeref {
        ptr_local: "p".to_string(),
        ptr_ty: Ty::NonNull(Box::new(Ty::Uint(UintTy::U32))),
        provenance: RawPtrProvenance::Unknown,
        block_index: 0,
    }]);

    let result = rust_fv_analysis::vcgen::generate_vcs(&func, None);

    // NonNull should skip null-check VCs entirely
    let has_null_check_vc = result
        .conditions
        .iter()
        .any(|vc| vc.description.contains("null-check"));
    assert!(
        !has_null_check_vc,
        "NonNull type should skip null-check VCs, but found one"
    );

    // NonNull should also skip alignment VCs
    let has_alignment_vc = result
        .conditions
        .iter()
        .any(|vc| vc.description.contains("alignment"));
    assert!(
        !has_alignment_vc,
        "NonNull type should skip alignment VCs, but found one"
    );
}

#[test]
fn nonnull_smt_encoding_as_bitvec64() {
    // NonNull should encode as BitVec(64) in SMT (same as RawPtr -- it's still a pointer)
    let ty = Ty::NonNull(Box::new(Ty::Int(IntTy::I32)));
    let sort = rust_fv_analysis::encode_sort::encode_type(&ty);
    assert_eq!(sort, rust_fv_smtlib::sort::Sort::BitVec(64));
}
