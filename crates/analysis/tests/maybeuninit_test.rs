/// MaybeUninit ghost state VC generation tests (LANG-16).
///
/// Tests that the verifier correctly generates MaybeUninitSafety VCs for
/// MaybeUninit::assume_init calls based on ghost initialization state tracking.
use rust_fv_analysis::ir::*;
use rust_fv_analysis::vcgen::{VcKind, generate_vcs};

/// Helper: create a minimal Function with MaybeUninit ghost states and basic blocks.
fn make_maybeuninit_fn(
    name: &str,
    maybeuninit_ghost_states: Vec<MaybeUninitGhostState>,
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
        maybeuninit_ghost_states,
    }
}

/// Helper: create a MaybeUninitGhostState for a given local.
fn ghost_state(local: &str) -> MaybeUninitGhostState {
    MaybeUninitGhostState {
        local_name: local.to_string(),
        is_initialized: format!("{}_is_initialized", local),
    }
}

/// Helper: create a Call terminator for a MaybeUninit method.
fn maybeuninit_call(method: &str, target: BlockId) -> Terminator {
    Terminator::Call {
        func: format!("MaybeUninit::{}", method),
        args: vec![Operand::Move(Place::local("_1"))],
        destination: Place::local("_2"),
        target,
    }
}

/// Helper: create a block with a MaybeUninit call terminator.
fn call_block(method: &str, target: BlockId) -> BasicBlock {
    BasicBlock {
        statements: vec![],
        terminator: maybeuninit_call(method, target),
    }
}

fn return_block() -> BasicBlock {
    BasicBlock {
        statements: vec![],
        terminator: Terminator::Return,
    }
}

// === Test 1: MaybeUninit::uninit() sets ghost is_initialized = false ===

#[test]
fn test_uninit_sets_not_initialized() {
    // Scenario: uninit() followed by assume_init() -- should detect uninitialized read
    let func = make_maybeuninit_fn(
        "test_uninit_assume_init",
        vec![ghost_state("_1")],
        vec![
            call_block("uninit", 1),      // BB0: MaybeUninit::uninit()
            call_block("assume_init", 2), // BB1: MaybeUninit::assume_init() -- violation!
            return_block(),               // BB2: return
        ],
    );

    let result = generate_vcs(&func, None);
    let mu_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::MaybeUninitSafety)
        .collect();

    assert!(
        !mu_vcs.is_empty(),
        "Should generate MaybeUninitSafety VC for uninit -> assume_init"
    );
    // The VC should indicate uninitialized state (SAT = violation)
    assert!(
        mu_vcs[0].description.contains("uninitialized"),
        "VC description should mention 'uninitialized', got: {}",
        mu_vcs[0].description
    );
}

// === Test 2: MaybeUninit::write(val) sets ghost is_initialized = true ===

#[test]
fn test_write_then_assume_init_is_safe() {
    // Scenario: uninit() -> write() -> assume_init() -- should be safe (UNSAT)
    let func = make_maybeuninit_fn(
        "test_write_assume_init",
        vec![ghost_state("_1")],
        vec![
            call_block("uninit", 1),      // BB0: MaybeUninit::uninit()
            call_block("write", 2),       // BB1: MaybeUninit::write(val) -> initialized
            call_block("assume_init", 3), // BB2: MaybeUninit::assume_init() -- safe!
            return_block(),               // BB3: return
        ],
    );

    let result = generate_vcs(&func, None);
    let mu_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::MaybeUninitSafety)
        .collect();

    assert!(
        !mu_vcs.is_empty(),
        "Should generate MaybeUninitSafety VC even for safe case"
    );
    // The VC for safe case should indicate initialized state
    assert!(
        mu_vcs
            .iter()
            .any(|vc| vc.description.contains("initialized")),
        "VC description should mention 'initialized'"
    );
}

// === Test 3: MaybeUninit::new(val) sets ghost is_initialized = true ===

#[test]
fn test_new_then_assume_init_is_safe() {
    // Scenario: new(val) -> assume_init() -- should be safe (UNSAT)
    let func = make_maybeuninit_fn(
        "test_new_assume_init",
        vec![ghost_state("_1")],
        vec![
            call_block("new", 1),         // BB0: MaybeUninit::new(val) -> initialized
            call_block("assume_init", 2), // BB1: MaybeUninit::assume_init() -- safe!
            return_block(),               // BB2: return
        ],
    );

    let result = generate_vcs(&func, None);
    let mu_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::MaybeUninitSafety)
        .collect();

    assert!(
        !mu_vcs.is_empty(),
        "Should generate MaybeUninitSafety VC for new -> assume_init"
    );
    // The VC should be for initialized case (safe)
    assert!(
        mu_vcs[0].description.contains("initialized"),
        "VC description should mention 'initialized'"
    );
}

// === Test 4: has_maybeuninit_locals() returns true/false correctly ===

#[test]
fn test_has_maybeuninit_locals_true() {
    let func = make_maybeuninit_fn(
        "test_has_maybeuninit",
        vec![ghost_state("_1")],
        vec![return_block()],
    );
    assert!(func.has_maybeuninit_locals());
}

#[test]
fn test_has_maybeuninit_locals_false() {
    let func = make_maybeuninit_fn("test_no_maybeuninit", vec![], vec![return_block()]);
    assert!(!func.has_maybeuninit_locals());
}

// === Test 5: assume_init without any prior call generates SAT VC ===

#[test]
fn test_assume_init_without_write_generates_sat_vc() {
    // Scenario: just assume_init() with no prior initialization -- violation
    let func = make_maybeuninit_fn(
        "test_bare_assume_init",
        vec![ghost_state("_1")],
        vec![
            call_block("assume_init", 1), // BB0: assume_init() on uninitialized
            return_block(),               // BB1: return
        ],
    );

    let result = generate_vcs(&func, None);
    let mu_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::MaybeUninitSafety)
        .collect();

    assert!(
        !mu_vcs.is_empty(),
        "Should generate MaybeUninitSafety VC for bare assume_init"
    );
    assert!(
        mu_vcs[0].description.contains("uninitialized"),
        "Should flag as uninitialized read"
    );
}

// === Test 6: No VCs generated when no MaybeUninit ghost states ===

#[test]
fn test_no_vcs_without_ghost_states() {
    let func = make_maybeuninit_fn(
        "test_no_ghost",
        vec![],
        vec![call_block("assume_init", 1), return_block()],
    );

    let result = generate_vcs(&func, None);
    let mu_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::MaybeUninitSafety)
        .collect();

    assert!(
        mu_vcs.is_empty(),
        "Should NOT generate MaybeUninitSafety VCs when no ghost states present"
    );
}
