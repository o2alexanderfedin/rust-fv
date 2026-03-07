//! End-to-end tests for pointer alignment safety verification (COMPL-02).
//!
//! Tests that PtrToPtr casts with alignment > 1 produce AlignmentSafety VCs,
//! and that the solver correctly determines aligned (UNSAT) vs unaligned (SAT) cases.
//!
//! Uses the analysis-level generate_vcs directly (not the full driver pipeline)
//! since alignment VCs are generated in the vcgen layer and don't require
//! rustc integration.

use rust_fv_analysis::ir::*;
use rust_fv_analysis::vcgen::{VcKind, generate_vcs};
use std::collections::HashMap;

/// Build a synthetic function that performs a PtrToPtr cast from *const u8 to *const T.
fn make_ptr_cast_function(name: &str, target_pointee: Ty) -> Function {
    Function {
        name: name.to_string(),
        return_local: Local::new("_0", Ty::Uint(UintTy::U32)),
        params: vec![Local::new(
            "_1",
            Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Shared),
        )],
        locals: vec![Local::new(
            "_2",
            Ty::RawPtr(Box::new(target_pointee.clone()), Mutability::Shared),
        )],
        basic_blocks: vec![BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_2"),
                Rvalue::Cast(
                    CastKind::PtrToPtr,
                    Operand::Copy(Place::local("_1")),
                    Ty::RawPtr(Box::new(target_pointee), Mutability::Shared),
                ),
            )],
            terminator: Terminator::Return,
        }],
        contracts: Contracts::default(),
        generic_params: vec![],
        prophecies: vec![],
        lifetime_params: vec![],
        outlives_constraints: vec![],
        borrow_info: vec![],
        reborrow_chains: vec![],
        unsafe_blocks: vec![],
        unsafe_operations: vec![],
        unsafe_contracts: None,
        is_unsafe_fn: false,
        thread_spawns: vec![],
        atomic_ops: vec![],
        sync_ops: vec![],
        lock_invariants: vec![],
        concurrency_config: None,
        source_names: HashMap::new(),
        coroutine_info: None,
        refcell_ghost_states: vec![],
        maybeuninit_ghost_states: vec![],
        loops: vec![],
    }
}

// ===========================================================================
// Test 1: PtrToPtr cast to *const u32 generates AlignmentSafety VC
// ===========================================================================

/// A function casting *const u8 to *const u32 must produce an AlignmentSafety VC
/// because u32 requires 4-byte alignment.
#[test]
fn alignment_e2e_ptr_to_u32_generates_alignment_vc() {
    let func = make_ptr_cast_function("ptr_cast_u32", Ty::Uint(UintTy::U32));
    let result = generate_vcs(&func, None);

    let alignment_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::AlignmentSafety)
        .collect();

    assert!(
        !alignment_vcs.is_empty(),
        "PtrToPtr cast to *const u32 must produce AlignmentSafety VC. \
         Got {} total VCs: {:?}",
        result.conditions.len(),
        result
            .conditions
            .iter()
            .map(|vc| format!("{:?}: {}", vc.location.vc_kind, &vc.description))
            .collect::<Vec<_>>()
    );

    // Verify the VC mentions 4-byte alignment
    let vc = &alignment_vcs[0];
    assert!(
        vc.description.contains("4-byte"),
        "VC should mention 4-byte alignment: {}",
        vc.description
    );

    // Verify the SMT script contains bvsmod for alignment check
    let smt = vc.script.to_string();
    assert!(
        smt.contains("bvsmod"),
        "SMT script should contain bvsmod for alignment modulo: {}",
        smt
    );
}

// ===========================================================================
// Test 2: PtrToPtr cast to *const u64 generates 8-byte alignment VC
// ===========================================================================

/// A function casting *const u8 to *const u64 must produce an AlignmentSafety VC
/// because u64 requires 8-byte alignment.
#[test]
fn alignment_e2e_ptr_to_u64_generates_8byte_alignment_vc() {
    let func = make_ptr_cast_function("ptr_cast_u64", Ty::Uint(UintTy::U64));
    let result = generate_vcs(&func, None);

    let alignment_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::AlignmentSafety)
        .collect();

    assert!(
        !alignment_vcs.is_empty(),
        "PtrToPtr cast to *const u64 must produce AlignmentSafety VC"
    );

    let vc = &alignment_vcs[0];
    assert!(
        vc.description.contains("8-byte"),
        "VC should mention 8-byte alignment: {}",
        vc.description
    );
}

// ===========================================================================
// Test 3: PtrToPtr cast to *const u8 does NOT generate alignment VC
// ===========================================================================

/// A function casting *const u32 to *const u8 should NOT produce an AlignmentSafety VC
/// because u8 has alignment=1 (trivially aligned).
#[test]
fn alignment_e2e_ptr_to_u8_no_alignment_vc() {
    let func = make_ptr_cast_function("ptr_cast_u8", Ty::Uint(UintTy::U8));
    let result = generate_vcs(&func, None);

    let alignment_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::AlignmentSafety)
        .collect();

    assert!(
        alignment_vcs.is_empty(),
        "PtrToPtr cast to *const u8 should NOT produce AlignmentSafety VC (align=1). \
         Got {} alignment VCs",
        alignment_vcs.len()
    );
}

// ===========================================================================
// Test 4: Alignment VC SMT script structure validation
// ===========================================================================

/// Verify the SMT-LIB script structure for an alignment VC:
/// - Contains set-logic
/// - Contains declare-const for the pointer variable
/// - Contains (assert (not (= (bvsmod ...) #x...)))
/// - Contains check-sat and get-model
#[test]
fn alignment_e2e_smt_script_structure() {
    let func = make_ptr_cast_function("ptr_cast_smt", Ty::Uint(UintTy::U32));
    let result = generate_vcs(&func, None);

    let alignment_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::AlignmentSafety)
        .collect();

    assert!(!alignment_vcs.is_empty(), "Expected alignment VC");

    let smt = alignment_vcs[0].script.to_string();

    // Structural checks
    assert!(
        smt.contains("set-logic"),
        "SMT script must contain set-logic: {smt}"
    );
    assert!(
        smt.contains("check-sat"),
        "SMT script must contain check-sat: {smt}"
    );
    assert!(
        smt.contains("get-model"),
        "SMT script must contain get-model: {smt}"
    );
    assert!(
        smt.contains("bvsmod"),
        "SMT script must contain bvsmod for modulo: {smt}"
    );
    assert!(
        smt.contains("not"),
        "SMT script must negate alignment check (UNSAT = verified): {smt}"
    );
}

// ===========================================================================
// Test 5: Multiple PtrToPtr casts generate multiple alignment VCs
// ===========================================================================

/// A function with two PtrToPtr casts (to u32 and u64) should generate two AlignmentSafety VCs.
#[test]
fn alignment_e2e_multiple_casts_multiple_vcs() {
    let func = Function {
        name: "multi_cast".to_string(),
        return_local: Local::new("_0", Ty::Uint(UintTy::U32)),
        params: vec![Local::new(
            "_1",
            Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Shared),
        )],
        locals: vec![
            Local::new(
                "_2",
                Ty::RawPtr(Box::new(Ty::Uint(UintTy::U32)), Mutability::Shared),
            ),
            Local::new(
                "_3",
                Ty::RawPtr(Box::new(Ty::Uint(UintTy::U64)), Mutability::Shared),
            ),
        ],
        basic_blocks: vec![BasicBlock {
            statements: vec![
                Statement::Assign(
                    Place::local("_2"),
                    Rvalue::Cast(
                        CastKind::PtrToPtr,
                        Operand::Copy(Place::local("_1")),
                        Ty::RawPtr(Box::new(Ty::Uint(UintTy::U32)), Mutability::Shared),
                    ),
                ),
                Statement::Assign(
                    Place::local("_3"),
                    Rvalue::Cast(
                        CastKind::PtrToPtr,
                        Operand::Copy(Place::local("_1")),
                        Ty::RawPtr(Box::new(Ty::Uint(UintTy::U64)), Mutability::Shared),
                    ),
                ),
            ],
            terminator: Terminator::Return,
        }],
        contracts: Contracts::default(),
        generic_params: vec![],
        prophecies: vec![],
        lifetime_params: vec![],
        outlives_constraints: vec![],
        borrow_info: vec![],
        reborrow_chains: vec![],
        unsafe_blocks: vec![],
        unsafe_operations: vec![],
        unsafe_contracts: None,
        is_unsafe_fn: false,
        thread_spawns: vec![],
        atomic_ops: vec![],
        sync_ops: vec![],
        lock_invariants: vec![],
        concurrency_config: None,
        source_names: HashMap::new(),
        coroutine_info: None,
        refcell_ghost_states: vec![],
        maybeuninit_ghost_states: vec![],
        loops: vec![],
    };

    let result = generate_vcs(&func, None);
    let alignment_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::AlignmentSafety)
        .collect();

    assert_eq!(
        alignment_vcs.len(),
        2,
        "Two PtrToPtr casts (u32 + u64) should produce 2 alignment VCs, got {}",
        alignment_vcs.len()
    );

    // First VC should be 4-byte, second should be 8-byte
    assert!(alignment_vcs[0].description.contains("4-byte"));
    assert!(alignment_vcs[1].description.contains("8-byte"));
}
