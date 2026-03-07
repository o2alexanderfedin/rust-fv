/// Pin move-prevention verification tests (LANG-05).
///
/// Tests that the verifier correctly generates PinSafety and MemorySafety VCs
/// for Pin operations on Unpin and non-Unpin types.
use rust_fv_analysis::ir::*;
use rust_fv_analysis::vcgen::{VcKind, generate_vcs};

/// Helper: create a minimal Function with pin_ghost_states and basic blocks.
fn make_pin_fn(
    name: &str,
    pin_ghost_states: Vec<PinGhostState>,
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
        pin_ghost_states,
        drop_locals: vec![],
        hrtb_bounds: vec![],
    }
}

fn return_block() -> BasicBlock {
    BasicBlock {
        statements: vec![],
        terminator: Terminator::Return,
    }
}

fn pin_call_block(method: &str, target: BlockId) -> BasicBlock {
    BasicBlock {
        statements: vec![],
        terminator: Terminator::Call {
            func: format!("std::pin::Pin::{}", method),
            args: vec![Operand::Move(Place::local("_1"))],
            destination: Place::local("_2"),
            target,
        },
    }
}

// === Test 1: Pin::new_unchecked on non-Unpin type generates PinSafety VC ===

#[test]
fn test_pin_new_unchecked_non_unpin_generates_pin_safety() {
    let func = make_pin_fn(
        "test_pin_unchecked",
        vec![PinGhostState {
            local_name: "_1".to_string(),
            inner_ty: Ty::Named("SelfReferential!Unpin".to_string()), // !Unpin type
        }],
        vec![pin_call_block("new_unchecked", 1), return_block()],
    );

    let result = generate_vcs(&func, None);
    let pin_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::PinSafety)
        .collect();

    assert!(
        !pin_vcs.is_empty(),
        "Expected PinSafety VC for Pin::new_unchecked on !Unpin type"
    );

    // Should mention V150
    assert!(
        pin_vcs[0].description.contains("V150") || pin_vcs[0].description.contains("PinSafety"),
        "PinSafety VC should mention V150: {}",
        pin_vcs[0].description
    );
}

// === Test 2: Moving pinned non-Unpin value generates MemorySafety VC ===

#[test]
fn test_move_pinned_non_unpin_generates_memory_safety() {
    let func = make_pin_fn(
        "test_move_pinned",
        vec![PinGhostState {
            local_name: "_1".to_string(),
            inner_ty: Ty::Named("SelfReferential!Unpin".to_string()),
        }],
        vec![
            pin_call_block("new_unchecked", 1),
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_3"),
                    Rvalue::Use(Operand::Move(Place::local("_1"))),
                )],
                terminator: Terminator::Return,
            },
        ],
    );

    let result = generate_vcs(&func, None);
    let mem_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::MemorySafety)
        .collect();

    assert!(
        !mem_vcs.is_empty(),
        "Expected MemorySafety VC for moving pinned !Unpin value"
    );
    assert!(
        mem_vcs[0].description.contains("pinned") && mem_vcs[0].description.contains("!Unpin"),
        "MemorySafety VC should mention pinned and !Unpin: {}",
        mem_vcs[0].description
    );
}

// === Test 3: Pin::new on Unpin type -- move is allowed ===

#[test]
fn test_pin_new_unpin_allows_move() {
    let func = make_pin_fn(
        "test_pin_unpin",
        vec![PinGhostState {
            local_name: "_1".to_string(),
            inner_ty: Ty::Int(IntTy::I32), // Unpin type
        }],
        vec![pin_call_block("new", 1), return_block()],
    );

    let result = generate_vcs(&func, None);
    let pin_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::PinSafety)
        .collect();

    // Should have a PinSafety VC but it should be UNSAT (safe)
    assert!(
        !pin_vcs.is_empty(),
        "Expected PinSafety VC for Pin::new on Unpin type"
    );
    assert!(
        pin_vcs[0].description.contains("Unpin") && pin_vcs[0].description.contains("allowed"),
        "Should indicate move is allowed for Unpin type: {}",
        pin_vcs[0].description
    );
}

// === Test 4: Structural pinning on struct with !Unpin field ===

#[test]
fn test_structural_pinning_non_unpin_field() {
    let func = make_pin_fn(
        "test_structural_pin",
        vec![PinGhostState {
            local_name: "_1".to_string(),
            inner_ty: Ty::Struct(
                "PinnedStruct".to_string(),
                vec![
                    ("data".to_string(), Ty::Int(IntTy::I32)),
                    (
                        "self_ref".to_string(),
                        Ty::Named("PhantomPinned".to_string()),
                    ),
                ],
            ),
        }],
        vec![return_block()],
    );

    let result = generate_vcs(&func, None);
    let pin_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::PinSafety)
        .collect();

    // Should have structural pinning VC for the PhantomPinned field
    assert!(
        !pin_vcs.is_empty(),
        "Expected PinSafety VC for structural pinning with !Unpin field"
    );
    assert!(
        pin_vcs
            .iter()
            .any(|vc| vc.description.contains("self_ref") || vc.description.contains("Structural")),
        "Should mention structural pinning for the !Unpin field"
    );
}

// === Test 5: Pin::new_unchecked without contract generates PinSafety VC ===

#[test]
fn test_pin_new_unchecked_requires_contract() {
    let func = make_pin_fn(
        "test_pin_needs_contract",
        vec![PinGhostState {
            local_name: "_1".to_string(),
            inner_ty: Ty::Named("Future!Unpin".to_string()),
        }],
        vec![pin_call_block("new_unchecked", 1), return_block()],
    );

    let result = generate_vcs(&func, None);
    let pin_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::PinSafety)
        .collect();

    assert!(
        !pin_vcs.is_empty(),
        "Expected PinSafety VC requiring user contract"
    );
    assert!(
        pin_vcs[0].description.contains("unsafe_ensures")
            || pin_vcs[0].description.contains("contract"),
        "Should require #[unsafe_ensures] contract: {}",
        pin_vcs[0].description
    );
}

// === Test 6: Non-pinned value move generates no Pin-related VCs ===

#[test]
fn test_non_pinned_move_no_pin_vcs() {
    let func = make_pin_fn(
        "test_no_pin",
        vec![], // No pin ghost states
        vec![BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_2"),
                Rvalue::Use(Operand::Move(Place::local("_1"))),
            )],
            terminator: Terminator::Return,
        }],
    );

    let result = generate_vcs(&func, None);
    let pin_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::PinSafety)
        .collect();

    assert!(
        pin_vcs.is_empty(),
        "Expected no PinSafety VCs for non-pinned values"
    );
}
