//! Unit tests for all five CastKind variants.
//!
//! Verifies that each CastKind variant produces structurally distinct Term output,
//! and that the SMT-LIB serialization is different for each variant (snapshot regression).
//! Also tests VcKind::AlignmentSafety serialization and PtrToPtr alignment VC generation.

use rust_fv_analysis::encode_term::{encode_cast, encode_ptr_to_ptr_cast};
use rust_fv_analysis::ir::CastKind;
use rust_fv_analysis::vcgen::VcKind;
use rust_fv_smtlib::term::Term;
use std::collections::HashSet;

// ---- Per-variant structural tests ----

#[test]
fn cast_kind_ptr_to_ptr_returns_identity() {
    let src = Term::Const("addr".to_string());
    let result = encode_cast(&CastKind::PtrToPtr, src.clone(), 64, 64, false, false);
    // PtrToPtr is identity: result should be the same as src
    assert_eq!(result.to_string(), src.to_string());
}

#[test]
fn cast_kind_ptr_to_ptr_via_helper() {
    let src = Term::Const("ptr".to_string());
    let result = encode_ptr_to_ptr_cast(src.clone());
    assert_eq!(result.to_string(), src.to_string());
}

#[test]
fn cast_kind_int_to_int_produces_extend_or_extract() {
    // Widening: u32 -> u64 (zero-extend)
    let src = Term::Const("x".to_string());
    let result = encode_cast(&CastKind::IntToInt, src.clone(), 32, 64, false, false);
    let smt = result.to_string();
    // Should produce zero_extend or sign_extend, NOT identity
    assert!(
        smt.contains("zero_extend") || smt.contains("sign_extend"),
        "IntToInt widening should produce extend, got: {smt}"
    );
    assert_ne!(smt, src.to_string(), "IntToInt should differ from identity");
}

#[test]
fn cast_kind_int_to_int_narrowing() {
    // Narrowing: u64 -> u32 (extract)
    let src = Term::Const("x".to_string());
    let result = encode_cast(&CastKind::IntToInt, src, 64, 32, false, false);
    let smt = result.to_string();
    assert!(
        smt.contains("extract"),
        "IntToInt narrowing should produce extract, got: {smt}"
    );
}

#[test]
fn cast_kind_int_to_float_produces_to_fp() {
    let src = Term::Const("x".to_string());
    let result = encode_cast(&CastKind::IntToFloat, src.clone(), 32, 32, false, false);
    let smt = result.to_string();
    assert!(
        smt.contains("to_fp"),
        "IntToFloat should produce to_fp term, got: {smt}"
    );
    assert_ne!(smt, src.to_string());
}

#[test]
fn cast_kind_float_to_int_produces_fp_to_bv() {
    let src = Term::Const("f".to_string());
    let result = encode_cast(
        &CastKind::FloatToInt,
        src.clone(),
        32,
        32,
        false,
        false, // unsigned target
    );
    let smt = result.to_string();
    assert!(
        smt.contains("fp.to_ubv") || smt.contains("fp.to_sbv"),
        "FloatToInt should produce fp.to_ubv/sbv, got: {smt}"
    );
    assert_ne!(smt, src.to_string());
}

#[test]
fn cast_kind_float_to_float_produces_to_fp_conversion() {
    // f32 -> f64 conversion
    let src = Term::Const("f".to_string());
    let result = encode_cast(&CastKind::FloatToFloat, src.clone(), 32, 64, false, false);
    let smt = result.to_string();
    assert!(
        smt.contains("to_fp"),
        "FloatToFloat should produce to_fp, got: {smt}"
    );
    assert_ne!(smt, src.to_string());
}

// ---- Cross-variant distinctness test ----

#[test]
fn all_five_cast_kinds_produce_distinct_smt_output() {
    let src = Term::Const("v".to_string());

    let outputs: Vec<String> = vec![
        encode_cast(&CastKind::IntToInt, src.clone(), 32, 64, false, false).to_string(),
        encode_cast(&CastKind::IntToFloat, src.clone(), 32, 32, false, false).to_string(),
        encode_cast(&CastKind::FloatToInt, src.clone(), 32, 32, false, false).to_string(),
        encode_cast(&CastKind::FloatToFloat, src.clone(), 32, 64, false, false).to_string(),
        encode_cast(&CastKind::PtrToPtr, src.clone(), 64, 64, false, false).to_string(),
    ];

    let unique: HashSet<&String> = outputs.iter().collect();
    assert_eq!(
        unique.len(),
        5,
        "All 5 CastKind variants must produce distinct SMT output.\nOutputs: {:#?}",
        outputs
    );
}

// ---- VcKind::AlignmentSafety tests ----

#[test]
fn vc_kind_alignment_safety_exists() {
    let kind = VcKind::AlignmentSafety;
    // Just verify the variant exists and can be compared
    assert_eq!(kind, VcKind::AlignmentSafety);
    assert_ne!(kind, VcKind::MemorySafety);
}

#[test]
fn vc_kind_alignment_safety_debug_format() {
    let kind = VcKind::AlignmentSafety;
    let debug = format!("{kind:?}");
    assert_eq!(debug, "AlignmentSafety");
}

// ---- Helper for building test functions ----

fn make_ptr_cast_function(
    name: &str,
    target_pointee_ty: rust_fv_analysis::ir::Ty,
) -> rust_fv_analysis::ir::Function {
    use rust_fv_analysis::ir::*;

    Function {
        name: name.to_string(),
        return_local: Local::new("_0", Ty::Uint(UintTy::U32)),
        params: vec![Local::new(
            "_1",
            Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Shared),
        )],
        locals: vec![Local::new(
            "_2",
            Ty::RawPtr(Box::new(target_pointee_ty.clone()), Mutability::Shared),
        )],
        basic_blocks: vec![BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_2"),
                Rvalue::Cast(
                    CastKind::PtrToPtr,
                    Operand::Copy(Place::local("_1")),
                    Ty::RawPtr(Box::new(target_pointee_ty), Mutability::Shared),
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
        source_names: std::collections::HashMap::new(),
        coroutine_info: None,
        loops: vec![],
    }
}

// ---- Alignment VC generation integration test ----

#[test]
fn ptr_to_ptr_cast_generates_alignment_vc() {
    use rust_fv_analysis::ir::*;
    use rust_fv_analysis::vcgen::generate_vcs;

    // Build a synthetic function with a PtrToPtr cast: *const u8 -> *const u32
    let func = make_ptr_cast_function("test_ptr_cast", Ty::Uint(UintTy::U32));

    let result = generate_vcs(&func, None);
    let alignment_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::AlignmentSafety)
        .collect();

    assert!(
        !alignment_vcs.is_empty(),
        "PtrToPtr cast to *const u32 should generate AlignmentSafety VC"
    );

    // The VC should mention 4-byte alignment
    let vc = &alignment_vcs[0];
    assert!(
        vc.description.contains("4-byte alignment"),
        "VC description should mention 4-byte alignment: {}",
        vc.description
    );
    assert!(
        vc.location
            .contract_text
            .as_ref()
            .unwrap()
            .contains("addr % 4 == 0"),
        "VC contract text should contain alignment modulo check"
    );
}

#[test]
fn ptr_to_ptr_cast_u8_no_alignment_vc() {
    use rust_fv_analysis::ir::*;
    use rust_fv_analysis::vcgen::generate_vcs;

    // Cast to *const u8: alignment=1, should NOT generate alignment VC
    let func = make_ptr_cast_function("test_ptr_cast_u8", Ty::Uint(UintTy::U8));

    let result = generate_vcs(&func, None);
    let alignment_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::AlignmentSafety)
        .collect();

    assert!(
        alignment_vcs.is_empty(),
        "PtrToPtr cast to *const u8 should NOT generate AlignmentSafety VC (alignment=1)"
    );
}

// ---- SMT-LIB snapshot regression ----

#[test]
fn cast_kind_smt_snapshot_int_to_int() {
    let src = Term::Const("x".to_string());
    let result = encode_cast(&CastKind::IntToInt, src, 32, 64, false, false);
    let smt = result.to_string();
    assert!(smt.contains("zero_extend"), "snapshot: {smt}");
}

#[test]
fn cast_kind_smt_snapshot_int_to_float() {
    let src = Term::Const("x".to_string());
    let result = encode_cast(&CastKind::IntToFloat, src, 32, 32, false, false);
    let smt = result.to_string();
    assert!(
        smt.contains("to_fp") && smt.contains("RNE"),
        "snapshot: {smt}"
    );
}

#[test]
fn cast_kind_smt_snapshot_float_to_int() {
    let src = Term::Const("f".to_string());
    let result = encode_cast(&CastKind::FloatToInt, src, 32, 32, false, false);
    let smt = result.to_string();
    assert!(smt.contains("fp.to_ubv"), "snapshot: {smt}");
}

#[test]
fn cast_kind_smt_snapshot_float_to_float() {
    let src = Term::Const("f".to_string());
    let result = encode_cast(&CastKind::FloatToFloat, src, 32, 64, false, false);
    let smt = result.to_string();
    assert!(
        smt.contains("to_fp") && smt.contains("11") && smt.contains("53"),
        "snapshot: {smt}"
    );
}

#[test]
fn cast_kind_smt_snapshot_ptr_to_ptr() {
    let src = Term::Const("addr".to_string());
    let result = encode_cast(&CastKind::PtrToPtr, src.clone(), 64, 64, false, false);
    let smt = result.to_string();
    // PtrToPtr is identity
    assert_eq!(smt, src.to_string(), "PtrToPtr should be identity: {smt}");
}
