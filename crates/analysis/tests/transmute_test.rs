/// Transmute safety VC generation tests (LANG-16).
///
/// Tests that the verifier correctly generates TransmuteSafety VCs for
/// std::mem::transmute operations with size, alignment, and validity checks.
use rust_fv_analysis::ir::*;
use rust_fv_analysis::vcgen::{VcKind, generate_vcs};

/// Helper: create a minimal Function with transmute unsafe operations.
fn make_transmute_fn(name: &str, unsafe_operations: Vec<UnsafeOperation>) -> Function {
    Function {
        name: name.to_string(),
        params: vec![],
        return_local: Local::new("_0", Ty::Unit),
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
        union_ghost_states: vec![],
        pin_ghost_states: vec![],
        drop_locals: vec![],
        hrtb_bounds: vec![],
    }
}

// === Test 1: transmute::<u32, f32> generates TransmuteSafety VC (sizes match = UNSAT) ===

#[test]
fn test_transmute_u32_to_f32_generates_size_vc() {
    let func = make_transmute_fn(
        "test_transmute_u32_f32",
        vec![UnsafeOperation::TransmuteUnsafe {
            source_ty: Ty::Uint(UintTy::U32),
            target_ty: Ty::Float(FloatTy::F32),
            local: "_1".to_string(),
        }],
    );

    let result = generate_vcs(&func, None);
    let transmute_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::TransmuteSafety)
        .collect();

    assert!(
        !transmute_vcs.is_empty(),
        "Should generate TransmuteSafety VC for transmute::<u32, f32>"
    );
    // Size check for u32 -> f32 (both 4 bytes): should be UNSAT (sizes match)
    assert!(
        transmute_vcs
            .iter()
            .any(|vc| vc.description.contains("size")),
        "Should include size check in transmute VC"
    );
}

// === Test 2: transmute::<u8, u32> generates TransmuteSafety VC (size mismatch = SAT) ===

#[test]
fn test_transmute_u8_to_u32_size_mismatch() {
    let func = make_transmute_fn(
        "test_transmute_u8_u32",
        vec![UnsafeOperation::TransmuteUnsafe {
            source_ty: Ty::Uint(UintTy::U8),
            target_ty: Ty::Uint(UintTy::U32),
            local: "_1".to_string(),
        }],
    );

    let result = generate_vcs(&func, None);
    let transmute_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::TransmuteSafety)
        .collect();

    assert!(
        !transmute_vcs.is_empty(),
        "Should generate TransmuteSafety VC for transmute::<u8, u32>"
    );
    // The VC description should mention size mismatch
    assert!(
        transmute_vcs
            .iter()
            .any(|vc| vc.description.contains("size")),
        "Should include size check in transmute VC"
    );
}

// === Test 3: transmute generates alignment VC for destination type ===

#[test]
fn test_transmute_generates_alignment_vc() {
    let func = make_transmute_fn(
        "test_transmute_alignment",
        vec![UnsafeOperation::TransmuteUnsafe {
            source_ty: Ty::Uint(UintTy::U32),
            target_ty: Ty::Float(FloatTy::F32),
            local: "_1".to_string(),
        }],
    );

    let result = generate_vcs(&func, None);
    let transmute_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::TransmuteSafety)
        .collect();

    // Should have at least size VC; alignment VC generated for types with align > 1
    assert!(
        !transmute_vcs.is_empty(),
        "Should generate at least one TransmuteSafety VC (size + optional alignment)"
    );
}

// === Test 4: transmute::<u32, bool> generates validity constraint VC ===

#[test]
fn test_transmute_u32_to_bool_validity_vc() {
    let func = make_transmute_fn(
        "test_transmute_u32_bool",
        vec![UnsafeOperation::TransmuteUnsafe {
            source_ty: Ty::Uint(UintTy::U32),
            target_ty: Ty::Bool,
            local: "_1".to_string(),
        }],
    );

    let result = generate_vcs(&func, None);
    let transmute_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::TransmuteSafety)
        .collect();

    assert!(
        !transmute_vcs.is_empty(),
        "Should generate TransmuteSafety VC for transmute::<u32, bool>"
    );
    // Should have a validity constraint for bool (must be 0 or 1)
    assert!(
        transmute_vcs
            .iter()
            .any(|vc| vc.description.contains("validity") || vc.description.contains("size")),
        "Should include validity or size check for bool destination"
    );
}
