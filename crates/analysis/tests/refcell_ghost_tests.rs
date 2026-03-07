/// RefCell ghost state VC generation tests (COMPL-09).
///
/// Tests that the verifier correctly generates BorrowConflict VCs for
/// RefCell borrow/borrow_mut calls based on ghost state tracking.
use rust_fv_analysis::ir::*;
use rust_fv_analysis::vcgen::{VcKind, generate_vcs};

/// Helper: create a minimal Function with refcell ghost states and basic blocks
fn make_refcell_fn(
    name: &str,
    refcell_ghost_states: Vec<RefCellGhostState>,
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
        refcell_ghost_states,
        maybeuninit_ghost_states: vec![],
    }
}

/// Helper: create a RefCellGhostState for a given local
fn ghost_state(local: &str) -> RefCellGhostState {
    RefCellGhostState {
        local_name: local.to_string(),
        borrow_count_var: format!("{}_borrow_count", local),
        is_mut_borrowed_var: format!("{}_is_mut_borrowed", local),
        inner_ty: Ty::Int(IntTy::I32),
    }
}

/// Helper: create a Call terminator for a RefCell method
fn refcell_call(method: &str, target: BlockId) -> Terminator {
    Terminator::Call {
        func: format!("RefCell::{}", method),
        args: vec![Operand::Move(Place::local("_1"))],
        destination: Place::local("_2"),
        target,
    }
}

/// Helper: create a block with a call terminator
fn call_block(method: &str, target: BlockId) -> BasicBlock {
    BasicBlock {
        statements: vec![],
        terminator: refcell_call(method, target),
    }
}

fn return_block() -> BasicBlock {
    BasicBlock {
        statements: vec![],
        terminator: Terminator::Return,
    }
}

// === Test 1: borrow() when is_mut_borrowed=true generates BorrowConflict VC ===

#[test]
fn test_refcell_borrow_when_mut_borrowed_generates_conflict() {
    // Scenario: borrow_mut() then borrow() on same RefCell
    // Expected: BorrowConflict VC generated for the borrow() call
    let func = make_refcell_fn(
        "test_borrow_conflict",
        vec![ghost_state("_1")],
        vec![
            call_block("borrow_mut", 1), // BB0: borrow_mut()
            call_block("borrow", 2),     // BB1: borrow() -- conflict!
            return_block(),              // BB2: return
        ],
    );

    let result = generate_vcs(&func, None);
    let conflict_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::BorrowConflict)
        .collect();

    assert!(
        !conflict_vcs.is_empty(),
        "Expected BorrowConflict VC for borrow() after borrow_mut(), got none"
    );
}

// === Test 2: borrow_mut() when borrow_count>0 generates BorrowConflict VC ===

#[test]
fn test_refcell_borrow_mut_when_shared_borrowed_generates_conflict() {
    // Scenario: borrow() then borrow_mut() on same RefCell
    // Expected: BorrowConflict VC generated for the borrow_mut() call
    let func = make_refcell_fn(
        "test_mut_borrow_conflict",
        vec![ghost_state("_1")],
        vec![
            call_block("borrow", 1),     // BB0: borrow()
            call_block("borrow_mut", 2), // BB1: borrow_mut() -- conflict!
            return_block(),              // BB2: return
        ],
    );

    let result = generate_vcs(&func, None);
    let conflict_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::BorrowConflict)
        .collect();

    assert!(
        !conflict_vcs.is_empty(),
        "Expected BorrowConflict VC for borrow_mut() after borrow(), got none"
    );
}

// === Test 3: Sequential borrow() then borrow() generates no BorrowConflict VC ===

#[test]
fn test_refcell_sequential_shared_borrows_no_conflict() {
    // Scenario: borrow() then borrow() on same RefCell
    // Expected: No BorrowConflict VC (shared borrows don't conflict)
    let func = make_refcell_fn(
        "test_shared_no_conflict",
        vec![ghost_state("_1")],
        vec![
            call_block("borrow", 1), // BB0: borrow()
            call_block("borrow", 2), // BB1: borrow() -- no conflict
            return_block(),          // BB2: return
        ],
    );

    let result = generate_vcs(&func, None);
    let conflict_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::BorrowConflict)
        .collect();

    assert!(
        conflict_vcs.is_empty(),
        "Expected no BorrowConflict VC for sequential shared borrows, got {}",
        conflict_vcs.len()
    );
}

// === Test 4: borrow() increments borrow_count; drop of Ref decrements it ===

#[test]
fn test_refcell_borrow_count_tracking() {
    // Scenario: borrow(), then drop (via another local), then borrow_mut()
    // Expected: No conflict because borrow_count goes back to 0 after drop
    // We model this with the call sequence: borrow -> drop -> borrow_mut
    let func = make_refcell_fn(
        "test_borrow_count_drop",
        vec![ghost_state("_1")],
        vec![
            call_block("borrow", 1), // BB0: borrow() -> borrow_count=1
            // BB1: drop the Ref (modeled as drop::Ref call)
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Call {
                    func: "drop::Ref".to_string(),
                    args: vec![Operand::Move(Place::local("_2"))],
                    destination: Place::local("_3"),
                    target: 2,
                },
            },
            call_block("borrow_mut", 3), // BB2: borrow_mut() -> should be ok
            return_block(),              // BB3: return
        ],
    );

    let result = generate_vcs(&func, None);
    let conflict_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::BorrowConflict)
        .collect();

    assert!(
        conflict_vcs.is_empty(),
        "Expected no BorrowConflict VC after drop of Ref, got {}",
        conflict_vcs.len()
    );
}

// === Test 5: borrow_mut() sets is_mut_borrowed=true; drop of RefMut clears it ===

#[test]
fn test_refcell_mut_borrowed_cleared_by_drop() {
    // Scenario: borrow_mut(), then drop (via RefMut drop), then borrow()
    // Expected: No conflict because is_mut_borrowed cleared after drop
    let func = make_refcell_fn(
        "test_mut_borrow_drop",
        vec![ghost_state("_1")],
        vec![
            call_block("borrow_mut", 1), // BB0: borrow_mut() -> is_mut_borrowed=true
            // BB1: drop the RefMut
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Call {
                    func: "drop::RefMut".to_string(),
                    args: vec![Operand::Move(Place::local("_2"))],
                    destination: Place::local("_3"),
                    target: 2,
                },
            },
            call_block("borrow", 3), // BB2: borrow() -> should be ok
            return_block(),          // BB3: return
        ],
    );

    let result = generate_vcs(&func, None);
    let conflict_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::BorrowConflict)
        .collect();

    assert!(
        conflict_vcs.is_empty(),
        "Expected no BorrowConflict VC after drop of RefMut, got {}",
        conflict_vcs.len()
    );
}

// === Test 6: Function with no RefCellGhostState generates no RefCell VCs ===

#[test]
fn test_no_refcell_ghost_state_no_vcs() {
    // Scenario: Function without RefCellGhostState but with RefCell-like calls
    // Expected: No BorrowConflict VCs (backward compatible)
    let func = make_refcell_fn(
        "test_no_ghost",
        vec![], // No ghost states
        vec![
            call_block("borrow_mut", 1),
            call_block("borrow", 2),
            return_block(),
        ],
    );

    let result = generate_vcs(&func, None);
    let conflict_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::BorrowConflict)
        .collect();

    assert!(
        conflict_vcs.is_empty(),
        "Expected no BorrowConflict VC without RefCellGhostState, got {}",
        conflict_vcs.len()
    );
}

// === Additional tests for other RefCell API methods ===

#[test]
fn test_refcell_try_borrow_generates_conflict() {
    // try_borrow() should generate same VC as borrow()
    let func = make_refcell_fn(
        "test_try_borrow_conflict",
        vec![ghost_state("_1")],
        vec![
            call_block("borrow_mut", 1),
            call_block("try_borrow", 2), // try_borrow -- conflict!
            return_block(),
        ],
    );

    let result = generate_vcs(&func, None);
    let conflict_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::BorrowConflict)
        .collect();

    assert!(
        !conflict_vcs.is_empty(),
        "Expected BorrowConflict VC for try_borrow() after borrow_mut()"
    );
}

#[test]
fn test_refcell_try_borrow_mut_generates_conflict() {
    // try_borrow_mut() should generate same VC as borrow_mut()
    let func = make_refcell_fn(
        "test_try_borrow_mut_conflict",
        vec![ghost_state("_1")],
        vec![
            call_block("borrow", 1),
            call_block("try_borrow_mut", 2), // try_borrow_mut -- conflict!
            return_block(),
        ],
    );

    let result = generate_vcs(&func, None);
    let conflict_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::BorrowConflict)
        .collect();

    assert!(
        !conflict_vcs.is_empty(),
        "Expected BorrowConflict VC for try_borrow_mut() after borrow()"
    );
}

#[test]
fn test_refcell_into_inner_generates_conflict_when_borrowed() {
    // into_inner() requires no outstanding borrows
    let func = make_refcell_fn(
        "test_into_inner_conflict",
        vec![ghost_state("_1")],
        vec![
            call_block("borrow", 1),
            call_block("into_inner", 2), // conflict! borrow outstanding
            return_block(),
        ],
    );

    let result = generate_vcs(&func, None);
    let conflict_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::BorrowConflict)
        .collect();

    assert!(
        !conflict_vcs.is_empty(),
        "Expected BorrowConflict VC for into_inner() with outstanding borrow"
    );
}

#[test]
fn test_refcell_replace_generates_conflict_when_borrowed() {
    // replace() requires exclusive access
    let func = make_refcell_fn(
        "test_replace_conflict",
        vec![ghost_state("_1")],
        vec![
            call_block("borrow", 1),
            call_block("replace", 2), // conflict! borrow outstanding
            return_block(),
        ],
    );

    let result = generate_vcs(&func, None);
    let conflict_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::BorrowConflict)
        .collect();

    assert!(
        !conflict_vcs.is_empty(),
        "Expected BorrowConflict VC for replace() with outstanding borrow"
    );
}

#[test]
fn test_refcell_swap_generates_conflict_when_borrowed() {
    // swap() requires exclusive access
    let func = make_refcell_fn(
        "test_swap_conflict",
        vec![ghost_state("_1")],
        vec![
            call_block("borrow_mut", 1),
            call_block("swap", 2), // conflict! mut borrow outstanding
            return_block(),
        ],
    );

    let result = generate_vcs(&func, None);
    let conflict_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::BorrowConflict)
        .collect();

    assert!(
        !conflict_vcs.is_empty(),
        "Expected BorrowConflict VC for swap() with outstanding borrow_mut"
    );
}
