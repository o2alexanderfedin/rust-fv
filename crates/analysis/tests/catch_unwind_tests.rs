/// catch_unwind dual-path verification tests (LANG-06).
///
/// Tests that the verifier correctly generates PanicSafety VCs for catch_unwind
/// call sites, including success path, panic path, drop cleanup, closure contracts,
/// UnwindSafe warnings, and absence of VCs when no catch_unwind is present.
use rust_fv_analysis::ir::*;
use rust_fv_analysis::vcgen::{VcKind, generate_vcs};

/// Helper: create a minimal Function with specified basic blocks.
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

fn return_block() -> BasicBlock {
    BasicBlock {
        statements: vec![],
        terminator: Terminator::Return,
    }
}

/// Helper: create a basic block with a catch_unwind call terminator.
fn catch_unwind_call_block() -> BasicBlock {
    BasicBlock {
        statements: vec![],
        terminator: Terminator::Call {
            func: "std::panic::catch_unwind".to_string(),
            args: vec![Operand::Copy(Place::local("_1"))],
            destination: Place::local("_0"),
            target: 1,
        },
    }
}

/// Helper: create a basic block with a catch_unwind call that captures &mut T.
fn catch_unwind_mut_ref_block() -> BasicBlock {
    BasicBlock {
        statements: vec![],
        terminator: Terminator::Call {
            func: "std::panic::catch_unwind".to_string(),
            args: vec![Operand::Copy(Place::local("_2"))],
            destination: Place::local("_0"),
            target: 1,
        },
    }
}

/// Test 1: Function calling catch_unwind generates PanicSafety VC for success path (Ok result)
#[test]
fn test_catch_unwind_success_path_vc() {
    let func = make_fn("test_fn", vec![catch_unwind_call_block(), return_block()]);
    let vcs = generate_vcs(&func, None);

    let panic_safety_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::PanicSafety)
        .collect();

    assert!(
        !panic_safety_vcs.is_empty(),
        "catch_unwind should generate PanicSafety VCs"
    );

    // At least one VC should mention the success/Ok path
    let has_success_vc = panic_safety_vcs
        .iter()
        .any(|vc| vc.description.contains("success") || vc.description.contains("Ok"));
    assert!(
        has_success_vc,
        "Should have a success path VC for catch_unwind"
    );
}

/// Test 2: Function calling catch_unwind generates PanicSafety VC for panic path (Err payload)
#[test]
fn test_catch_unwind_panic_path_vc() {
    let func = make_fn("test_fn", vec![catch_unwind_call_block(), return_block()]);
    let vcs = generate_vcs(&func, None);

    let panic_safety_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::PanicSafety)
        .collect();

    // At least one VC should mention the panic/Err path
    let has_panic_vc = panic_safety_vcs
        .iter()
        .any(|vc| vc.description.contains("panic") || vc.description.contains("Err"));
    assert!(has_panic_vc, "Should have a panic path VC for catch_unwind");
}

/// Test 3: Panic path includes drop-order VCs for in-scope variables with Drop impls
#[test]
fn test_catch_unwind_panic_path_drop_cleanup() {
    let mut func = make_fn("test_fn", vec![catch_unwind_call_block(), return_block()]);
    // Add a local with Drop impl to trigger drop cleanup on panic path
    func.drop_locals = vec![DropLocalInfo {
        local_name: "_3".to_string(),
        ty: Ty::Named("MyStruct".to_string()),
        drop_order: 0,
        has_drop: true,
    }];

    let vcs = generate_vcs(&func, None);

    let panic_safety_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::PanicSafety)
        .collect();

    // Should have a drop cleanup VC on the panic path
    let has_drop_cleanup = panic_safety_vcs
        .iter()
        .any(|vc| vc.description.contains("drop") || vc.description.contains("cleanup"));
    assert!(
        has_drop_cleanup,
        "Panic path should include drop cleanup VCs for in-scope Drop types"
    );
}

/// Test 4: Closure body contracts within catch_unwind are checked as normal
#[test]
fn test_catch_unwind_closure_contracts_checked() {
    let mut func = make_fn("test_fn", vec![catch_unwind_call_block(), return_block()]);
    // Add contracts to the function -- they should still be checked normally
    func.contracts.requires = vec![SpecExpr {
        raw: "_1 > 0".to_string(),
    }];
    func.contracts.ensures = vec![SpecExpr {
        raw: "_0 > 0".to_string(),
    }];
    func.params = vec![Local::new("_1", Ty::Int(IntTy::I32))];
    func.return_local = Local::new("_0", Ty::Int(IntTy::I32));

    let vcs = generate_vcs(&func, None);

    // Should still generate contract VCs in addition to PanicSafety
    let has_postcondition = vcs
        .conditions
        .iter()
        .any(|vc| vc.location.vc_kind == VcKind::Postcondition);
    assert!(
        has_postcondition,
        "Closure contracts should still be checked within catch_unwind functions"
    );

    let has_panic_safety = vcs
        .conditions
        .iter()
        .any(|vc| vc.location.vc_kind == VcKind::PanicSafety);
    assert!(
        has_panic_safety,
        "PanicSafety VCs should coexist with normal contract VCs"
    );
}

/// Test 5: UnwindSafe trait bound violation generates warning VC
#[test]
fn test_catch_unwind_unwindsafe_warning() {
    // Use a function where catch_unwind captures &mut T (potential UnwindSafe violation)
    let mut func = make_fn(
        "test_fn",
        vec![catch_unwind_mut_ref_block(), return_block()],
    );
    func.locals = vec![Local::new(
        "_2",
        Ty::Ref(Box::new(Ty::Int(IntTy::I32)), Mutability::Mutable),
    )];

    let vcs = generate_vcs(&func, None);

    let panic_safety_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::PanicSafety)
        .collect();

    // Should have an UnwindSafe warning VC
    let has_unwindsafe_warning = panic_safety_vcs
        .iter()
        .any(|vc| vc.description.contains("UnwindSafe"));
    assert!(
        has_unwindsafe_warning,
        "catch_unwind with &mut captures should generate UnwindSafe warning"
    );
}

/// Test 6: Function without catch_unwind generates no PanicSafety VCs
#[test]
fn test_no_catch_unwind_no_panic_safety_vcs() {
    let func = make_fn("test_fn", vec![return_block()]);
    let vcs = generate_vcs(&func, None);

    let panic_safety_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::PanicSafety)
        .collect();

    assert!(
        panic_safety_vcs.is_empty(),
        "Function without catch_unwind should not generate PanicSafety VCs"
    );
}
