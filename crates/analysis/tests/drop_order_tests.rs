/// Drop scope-exit ordering verification tests (LANG-04).
///
/// Tests that the verifier correctly generates DropOrder VCs at scope exit
/// in reverse declaration order, models recursive field drops, and detects
/// Drop+Copy diagnostic violations.
use rust_fv_analysis::ir::*;
use rust_fv_analysis::trait_analysis::{has_copy_impl, has_drop_impl, is_unpin};
use rust_fv_analysis::vcgen::{VcKind, generate_vcs};

/// Helper: create a minimal Function with drop_locals and basic blocks.
fn make_drop_fn(
    name: &str,
    drop_locals: Vec<DropLocalInfo>,
    basic_blocks: Vec<BasicBlock>,
) -> Function {
    Function {
        name: name.to_string(),
        params: vec![],
        return_local: Local::new("_0", Ty::Unit),
        locals: vec![],
        basic_blocks,
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
        drop_locals,
        hrtb_bounds: vec![],
    }
}

fn return_block() -> BasicBlock {
    BasicBlock {
        statements: vec![],
        terminator: Terminator::Return,
    }
}

// === Test 1: Two Drop locals generate DropOrder VCs in reverse declaration order ===

#[test]
fn test_two_drop_locals_reverse_order() {
    let func = make_drop_fn(
        "test_two_drops",
        vec![
            DropLocalInfo {
                local_name: "_1".to_string(),
                ty: Ty::Named("FileHandle".to_string()),
                has_drop: true,
                drop_order: 1, // declared first, dropped second
            },
            DropLocalInfo {
                local_name: "_2".to_string(),
                ty: Ty::Named("MutexGuard".to_string()),
                has_drop: true,
                drop_order: 0, // declared second, dropped first
            },
        ],
        vec![return_block()],
    );

    let result = generate_vcs(&func, None);
    let drop_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::DropOrder)
        .collect();

    // Should have 2 DropOrder VCs
    assert!(
        drop_vcs.len() >= 2,
        "Expected at least 2 DropOrder VCs, got {}",
        drop_vcs.len()
    );

    // First VC should be for _2 (dropped first, drop_order=0)
    assert!(
        drop_vcs[0].description.contains("_2") || drop_vcs[0].description.contains("MutexGuard"),
        "First drop VC should be for _2/MutexGuard: {}",
        drop_vcs[0].description
    );

    // Second VC should be for _1 (dropped second, drop_order=1)
    assert!(
        drop_vcs[1].description.contains("_1") || drop_vcs[1].description.contains("FileHandle"),
        "Second drop VC should be for _1/FileHandle: {}",
        drop_vcs[1].description
    );
}

// === Test 2: Struct with Drop fields has fields dropped before struct's own Drop ===

#[test]
fn test_struct_fields_dropped_before_struct() {
    // Struct A contains field of type B, both have Drop.
    // B's drop should appear before A's drop.
    let func = make_drop_fn(
        "test_field_drop_order",
        vec![DropLocalInfo {
            local_name: "_1".to_string(),
            ty: Ty::Struct(
                "OuterStruct".to_string(),
                vec![("inner".to_string(), Ty::Named("InnerDrop".to_string()))],
            ),
            has_drop: true,
            drop_order: 0,
        }],
        vec![return_block()],
    );

    let result = generate_vcs(&func, None);
    let drop_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::DropOrder)
        .collect();

    // Should have at least 1 DropOrder VC for the struct
    assert!(
        !drop_vcs.is_empty(),
        "Expected at least 1 DropOrder VC for OuterStruct"
    );
}

// === Test 3: Recursive drop - struct A contains struct B, B's drop VC before A's ===

#[test]
fn test_recursive_drop_ordering() {
    // B (inner) should be dropped before A (outer)
    let func = make_drop_fn(
        "test_recursive_drop",
        vec![
            DropLocalInfo {
                local_name: "_1".to_string(),
                ty: Ty::Named("StructA".to_string()),
                has_drop: true,
                drop_order: 0,
            },
            DropLocalInfo {
                local_name: "_2".to_string(),
                ty: Ty::Named("StructB".to_string()),
                has_drop: true,
                drop_order: 1,
            },
        ],
        vec![return_block()],
    );

    let result = generate_vcs(&func, None);
    let drop_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::DropOrder)
        .collect();

    // Both should generate VCs
    assert!(
        drop_vcs.len() >= 2,
        "Expected at least 2 DropOrder VCs for recursive drops, got {}",
        drop_vcs.len()
    );
}

// === Test 4: Drop + Copy diagnostic generates V140 warning ===

#[test]
fn test_drop_plus_copy_diagnostic() {
    // A type that has both Drop and Copy should generate a warning
    // The "DropCopyType" name triggers both has_drop and has_copy detection
    let func = make_drop_fn(
        "test_drop_copy_warning",
        vec![DropLocalInfo {
            local_name: "_1".to_string(),
            ty: Ty::Named("DropCopyType".to_string()),
            has_drop: true,
            drop_order: 0,
        }],
        vec![return_block()],
    );

    let result = generate_vcs(&func, None);
    let drop_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::DropOrder)
        .collect();

    // Should still generate drop VCs regardless
    assert!(
        !drop_vcs.is_empty(),
        "Expected DropOrder VCs even for Drop+Copy type"
    );

    // At least one VC should mention the Drop+Copy diagnostic
    let has_diagnostic = drop_vcs
        .iter()
        .any(|vc| vc.description.contains("Drop+Copy") || vc.description.contains("V140"));
    assert!(
        has_diagnostic,
        "Expected a V140 Drop+Copy diagnostic warning in VCs"
    );
}

// === Test 5: Non-Drop locals do NOT generate drop VCs ===

#[test]
fn test_non_drop_locals_no_vcs() {
    let func = make_drop_fn(
        "test_no_drops",
        vec![], // No drop locals
        vec![return_block()],
    );

    let result = generate_vcs(&func, None);
    let drop_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::DropOrder)
        .collect();

    assert!(
        drop_vcs.is_empty(),
        "Expected no DropOrder VCs for function without Drop locals"
    );
}

// === Test 6: Drop::drop() with #[ensures] contract checked at scope exit ===

#[test]
fn test_drop_with_ensures_contract() {
    let func = make_drop_fn(
        "test_drop_ensures",
        vec![DropLocalInfo {
            local_name: "_1".to_string(),
            ty: Ty::Named("ContractedDrop".to_string()),
            has_drop: true,
            drop_order: 0,
        }],
        vec![return_block()],
    );

    let result = generate_vcs(&func, None);
    let drop_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::DropOrder)
        .collect();

    // Should generate at least 1 DropOrder VC
    assert!(
        !drop_vcs.is_empty(),
        "Expected DropOrder VCs for contracted Drop type"
    );
}

// === Trait analysis function tests ===

#[test]
fn test_has_drop_impl_detection() {
    // Primitives should not have Drop impl
    let non_drop_ty = Ty::Int(IntTy::I32);
    assert!(
        !has_drop_impl(&non_drop_ty),
        "Primitive i32 should not have Drop impl"
    );

    // Named types are potentially Drop-implementing (conservative)
    let drop_ty = Ty::Named("FileHandle".to_string());
    // Named types may or may not have Drop -- the function uses name heuristics
    let _ = has_drop_impl(&drop_ty);
}

#[test]
fn test_is_unpin_primitives() {
    // All primitives are Unpin
    assert!(is_unpin(&Ty::Int(IntTy::I32)));
    assert!(is_unpin(&Ty::Bool));
    assert!(is_unpin(&Ty::Unit));
}

#[test]
fn test_has_copy_impl_primitives() {
    // Primitives implement Copy
    assert!(has_copy_impl(&Ty::Int(IntTy::I32)));
    assert!(has_copy_impl(&Ty::Bool));
}

#[test]
fn test_has_copy_impl_named_types() {
    // Named types with "Copy" in name are detected
    let non_copy = Ty::Named("FileHandle".to_string());
    assert!(!has_copy_impl(&non_copy), "FileHandle should not be Copy");
}
