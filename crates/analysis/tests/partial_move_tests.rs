/// Partial struct move tracking tests (COMPL-14).
///
/// Tests that the verifier correctly generates UseAfterPartialMove VCs
/// when a struct field is read after being moved, and generates no VCs
/// when accessing unmoved fields of a partially-moved struct.
use rust_fv_analysis::ir::*;
use rust_fv_analysis::vcgen::{VcKind, generate_vcs};

/// Helper: create a minimal Function with basic blocks for partial move testing
fn make_fn(name: &str, basic_blocks: Vec<BasicBlock>) -> Function {
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
        drop_locals: vec![],
        hrtb_bounds: vec![],
    }
}

/// Filter VCs to only UseAfterPartialMove
fn partial_move_vcs(
    vcs: &[rust_fv_analysis::vcgen::VerificationCondition],
) -> Vec<&rust_fv_analysis::vcgen::VerificationCondition> {
    vcs.iter()
        .filter(|vc| vc.location.vc_kind == VcKind::UseAfterPartialMove)
        .collect()
}

// Test 1: Move of s.field_a marks (s, [Field(0)]) as moved; read of s.field_b (Field(1)) produces no VC
#[test]
fn partial_move_field_a_then_read_field_b_no_vc() {
    // s.field_a is moved, then s.field_b is read -> no UseAfterPartialMove VC
    let func = make_fn(
        "test_partial_move_no_vc",
        vec![BasicBlock {
            statements: vec![
                // _1 = Move(s.field_a) -- move field 0
                Statement::Assign(
                    Place::local("_1"),
                    Rvalue::Use(Operand::Move(Place::local("s").field(0))),
                ),
                // _2 = Copy(s.field_b) -- read field 1 (should be fine)
                Statement::Assign(
                    Place::local("_2"),
                    Rvalue::Use(Operand::Copy(Place::local("s").field(1))),
                ),
            ],
            terminator: Terminator::Return,
        }],
    );

    let result = generate_vcs(&func, None);
    let pm_vcs = partial_move_vcs(&result.conditions);
    assert_eq!(
        pm_vcs.len(),
        0,
        "Reading unmoved field after partial move should produce no VC"
    );
}

// Test 2: Move of s.field_a then read of s.field_a generates UseAfterPartialMove VC
#[test]
fn partial_move_field_a_then_read_field_a_generates_vc() {
    let func = make_fn(
        "test_partial_move_vc",
        vec![BasicBlock {
            statements: vec![
                // _1 = Move(s.field_a) -- move field 0
                Statement::Assign(
                    Place::local("_1"),
                    Rvalue::Use(Operand::Move(Place::local("s").field(0))),
                ),
                // _2 = Copy(s.field_a) -- read field 0 after move (should generate VC)
                Statement::Assign(
                    Place::local("_2"),
                    Rvalue::Use(Operand::Copy(Place::local("s").field(0))),
                ),
            ],
            terminator: Terminator::Return,
        }],
    );

    let result = generate_vcs(&func, None);
    let pm_vcs = partial_move_vcs(&result.conditions);
    assert_eq!(
        pm_vcs.len(),
        1,
        "Reading moved field should produce UseAfterPartialMove VC"
    );
    assert!(pm_vcs[0].description.contains("s"));
}

// Test 3: Move of s.inner.x marks (s, [Field(0), Field(0)]) as moved; read of s.inner.y produces no VC
#[test]
fn partial_move_nested_field_disjoint_no_vc() {
    let func = make_fn(
        "test_nested_partial_move_no_vc",
        vec![BasicBlock {
            statements: vec![
                // _1 = Move(s.inner.x) -- move s.field(0).field(0)
                Statement::Assign(
                    Place::local("_1"),
                    Rvalue::Use(Operand::Move(Place::local("s").field(0).field(0))),
                ),
                // _2 = Copy(s.inner.y) -- read s.field(0).field(1) (should be fine)
                Statement::Assign(
                    Place::local("_2"),
                    Rvalue::Use(Operand::Copy(Place::local("s").field(0).field(1))),
                ),
            ],
            terminator: Terminator::Return,
        }],
    );

    let result = generate_vcs(&func, None);
    let pm_vcs = partial_move_vcs(&result.conditions);
    assert_eq!(
        pm_vcs.len(),
        0,
        "Reading disjoint nested field should produce no VC"
    );
}

// Test 4: Move of entire struct s marks all fields as moved; read of any field generates UseAfterPartialMove VC
#[test]
fn whole_struct_move_then_read_field_generates_vc() {
    let func = make_fn(
        "test_whole_move_vc",
        vec![BasicBlock {
            statements: vec![
                // _1 = Move(s) -- move entire struct
                Statement::Assign(
                    Place::local("_1"),
                    Rvalue::Use(Operand::Move(Place::local("s"))),
                ),
                // _2 = Copy(s.field_a) -- read field 0 after whole move (should generate VC)
                Statement::Assign(
                    Place::local("_2"),
                    Rvalue::Use(Operand::Copy(Place::local("s").field(0))),
                ),
            ],
            terminator: Terminator::Return,
        }],
    );

    let result = generate_vcs(&func, None);
    let pm_vcs = partial_move_vcs(&result.conditions);
    assert_eq!(
        pm_vcs.len(),
        1,
        "Reading field after whole struct move should produce UseAfterPartialMove VC"
    );
}

// Test 5: Re-assignment to a moved field clears the moved state; subsequent read produces no VC
#[test]
fn reassignment_clears_moved_state() {
    let func = make_fn(
        "test_reassignment_clears",
        vec![BasicBlock {
            statements: vec![
                // _1 = Move(s.field_a) -- move field 0
                Statement::Assign(
                    Place::local("_1"),
                    Rvalue::Use(Operand::Move(Place::local("s").field(0))),
                ),
                // s.field_a = _3 -- re-assign field 0
                Statement::Assign(
                    Place::local("s").field(0),
                    Rvalue::Use(Operand::Copy(Place::local("_3"))),
                ),
                // _2 = Copy(s.field_a) -- read field 0 after re-assignment (should be fine)
                Statement::Assign(
                    Place::local("_2"),
                    Rvalue::Use(Operand::Copy(Place::local("s").field(0))),
                ),
            ],
            terminator: Terminator::Return,
        }],
    );

    let result = generate_vcs(&func, None);
    let pm_vcs = partial_move_vcs(&result.conditions);
    assert_eq!(
        pm_vcs.len(),
        0,
        "Re-assignment should clear moved state, producing no VC"
    );
}

// Test 6: Function with no partial moves generates no UseAfterPartialMove VCs (backward compatible)
#[test]
fn no_partial_moves_no_vcs() {
    let func = make_fn(
        "test_no_moves",
        vec![BasicBlock {
            statements: vec![
                // Simple copy, no moves
                Statement::Assign(
                    Place::local("_1"),
                    Rvalue::Use(Operand::Copy(Place::local("_2"))),
                ),
            ],
            terminator: Terminator::Return,
        }],
    );

    let result = generate_vcs(&func, None);
    let pm_vcs = partial_move_vcs(&result.conditions);
    assert_eq!(
        pm_vcs.len(),
        0,
        "No moves should produce no UseAfterPartialMove VCs"
    );
}
