/// FFI opaque callee V110 VC generation tests (LANG-15).
///
/// Tests that the verifier correctly generates FfiOpaqueCallee VCs for
/// extern "C" function calls without user contracts, and suppresses them
/// when contracts are provided.
use rust_fv_analysis::ir::*;
use rust_fv_analysis::vcgen::{VcKind, generate_vcs};

/// Helper: create a minimal Function with call sites to extern "C" functions.
fn make_ffi_fn(
    name: &str,
    basic_blocks: Vec<BasicBlock>,
    unsafe_operations: Vec<UnsafeOperation>,
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
    }
}

fn return_block() -> BasicBlock {
    BasicBlock {
        statements: vec![],
        terminator: Terminator::Return,
    }
}

// === Test 1: extern "C" call without contract generates FfiOpaqueCallee VC ===

#[test]
fn test_ffi_call_without_contract_generates_v110() {
    let func = make_ffi_fn(
        "test_ffi_opaque",
        vec![
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Call {
                    func: "extern_c_function".to_string(),
                    args: vec![],
                    destination: Place::local("_1"),
                    target: 1,
                },
            },
            return_block(),
        ],
        vec![UnsafeOperation::FfiCall {
            callee_name: "extern_c_function".to_string(),
            has_contract: false,
        }],
    );

    let result = generate_vcs(&func, None);
    let ffi_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::FfiOpaqueCallee)
        .collect();

    assert!(
        !ffi_vcs.is_empty(),
        "Should generate FfiOpaqueCallee VC for uncontracted extern C call"
    );
    assert!(
        ffi_vcs[0].description.contains("extern"),
        "FfiOpaqueCallee description should mention 'extern'"
    );
}

// === Test 2: extern "C" call WITH contract does NOT generate FfiOpaqueCallee VC ===

#[test]
fn test_ffi_call_with_contract_no_v110() {
    let func = make_ffi_fn(
        "test_ffi_contracted",
        vec![
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Call {
                    func: "extern_c_contracted".to_string(),
                    args: vec![],
                    destination: Place::local("_1"),
                    target: 1,
                },
            },
            return_block(),
        ],
        vec![UnsafeOperation::FfiCall {
            callee_name: "extern_c_contracted".to_string(),
            has_contract: true,
        }],
    );

    let result = generate_vcs(&func, None);
    let ffi_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::FfiOpaqueCallee)
        .collect();

    assert!(
        ffi_vcs.is_empty(),
        "Should NOT generate FfiOpaqueCallee VC when extern C call has contracts"
    );
}
