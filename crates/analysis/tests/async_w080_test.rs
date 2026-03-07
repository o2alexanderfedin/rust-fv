//! Tests for W080 async multi-thread sequential model warning.
//!
//! COMPL-25: When an async function spawns threads (tokio::spawn, std::thread::spawn,
//! rayon::spawn, crossbeam::scope), a W080 warning is emitted indicating that
//! multi-threaded execution is not modeled and sequential polling is assumed.

use rust_fv_analysis::ir::*;
use rust_fv_analysis::vcgen::{VcKind, generate_vcs};

/// Helper: build a minimal function with optional async (coroutine_info) and optional
/// call to a spawn-like function in a Terminator::Call.
fn build_test_function(name: &str, is_async: bool, callee_name: Option<&str>) -> Function {
    let mut bbs = vec![];

    if let Some(callee) = callee_name {
        // Block 0: Call to callee, then goto block 1
        bbs.push(BasicBlock {
            statements: vec![],
            terminator: Terminator::Call {
                func: callee.to_string(),
                args: vec![],
                destination: Place {
                    local: "_1".to_string(),
                    projections: vec![],
                },
                target: 1,
            },
        });
        // Block 1: Return
        bbs.push(BasicBlock {
            statements: vec![],
            terminator: Terminator::Return,
        });
    } else {
        // Block 0: Just return
        bbs.push(BasicBlock {
            statements: vec![],
            terminator: Terminator::Return,
        });
    }

    let coroutine_info = if is_async {
        Some(CoroutineInfo {
            states: vec![],
            persistent_fields: vec![],
        })
    } else {
        None
    };

    Function {
        name: name.to_string(),
        params: vec![],
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Unit,
            is_ghost: false,
        },
        locals: vec![],
        basic_blocks: bbs,
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
        coroutine_info,
        refcell_ghost_states: vec![],
        maybeuninit_ghost_states: vec![],
        union_ghost_states: vec![],
        pin_ghost_states: vec![],
        drop_locals: vec![],
    }
}

#[test]
fn async_with_tokio_spawn_generates_async_sequential_model_vc() {
    let func = build_test_function("async_fn_tokio", true, Some("tokio::spawn"));
    let result = generate_vcs(&func, None);
    let w080_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::AsyncSequentialModel)
        .collect();
    assert!(
        !w080_vcs.is_empty(),
        "Async function with tokio::spawn should produce AsyncSequentialModel VC"
    );
}

#[test]
fn async_with_std_thread_spawn_generates_async_sequential_model_vc() {
    let func = build_test_function("async_fn_thread", true, Some("std::thread::spawn"));
    let result = generate_vcs(&func, None);
    let w080_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::AsyncSequentialModel)
        .collect();
    assert!(
        !w080_vcs.is_empty(),
        "Async function with std::thread::spawn should produce AsyncSequentialModel VC"
    );
}

#[test]
fn async_without_spawn_no_async_sequential_model_vc() {
    let func = build_test_function("async_fn_plain", true, None);
    let result = generate_vcs(&func, None);
    let w080_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::AsyncSequentialModel)
        .collect();
    assert!(
        w080_vcs.is_empty(),
        "Async function without spawn should NOT produce AsyncSequentialModel VC"
    );
}

#[test]
fn non_async_with_spawn_no_async_sequential_model_vc() {
    let func = build_test_function("sync_fn_spawn", false, Some("tokio::spawn"));
    let result = generate_vcs(&func, None);
    let w080_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::AsyncSequentialModel)
        .collect();
    assert!(
        w080_vcs.is_empty(),
        "Non-async function with spawn should NOT produce AsyncSequentialModel VC"
    );
}

#[test]
fn async_sequential_model_vc_description_contains_warning_text() {
    let func = build_test_function("async_fn_desc", true, Some("tokio::spawn"));
    let result = generate_vcs(&func, None);
    let w080_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::AsyncSequentialModel)
        .collect();
    assert!(!w080_vcs.is_empty(), "Should have W080 VC");
    assert!(
        w080_vcs[0]
            .description
            .contains("async multi-threaded execution not modeled"),
        "W080 description should contain warning text, got: {}",
        w080_vcs[0].description
    );
    assert!(
        w080_vcs[0]
            .description
            .contains("sequential polling assumed"),
        "W080 description should mention sequential polling, got: {}",
        w080_vcs[0].description
    );
}

#[test]
fn async_sequential_model_vc_kind_is_distinct() {
    // VcKind::AsyncSequentialModel should be a distinct variant
    let kind = VcKind::AsyncSequentialModel;
    assert_ne!(kind, VcKind::AsyncPostcondition);
    assert_ne!(kind, VcKind::AsyncStateInvariantSuspend);
    assert_ne!(kind, VcKind::AsyncStateInvariantResume);
    assert_ne!(kind, VcKind::OpaqueCallee);
    assert_ne!(kind, VcKind::Postcondition);
}

#[test]
fn async_with_spawn_still_produces_other_vcs() {
    let mut func = build_test_function("async_fn_post", true, Some("tokio::spawn"));
    // Add a postcondition so we can verify the function still gets postcondition VCs
    func.contracts.ensures.push(SpecExpr {
        raw: "result == 0".to_string(),
    });
    let result = generate_vcs(&func, None);
    let has_w080 = result
        .conditions
        .iter()
        .any(|vc| vc.location.vc_kind == VcKind::AsyncSequentialModel);
    // We should have at least the W080 VC; postcondition VCs may also be generated
    // depending on the function's structure. The key test is that W080 does not prevent
    // other VCs from being generated.
    assert!(has_w080, "Should have W080 VC");
    // The total VC count should be > 1 (W080 + at least postcondition attempt)
    assert!(
        result.conditions.len() > 1,
        "Function with W080 should still produce other VCs, got {} total",
        result.conditions.len()
    );
}

#[test]
fn async_with_rayon_spawn_generates_vc() {
    let func = build_test_function("async_fn_rayon", true, Some("rayon::spawn"));
    let result = generate_vcs(&func, None);
    let has_w080 = result
        .conditions
        .iter()
        .any(|vc| vc.location.vc_kind == VcKind::AsyncSequentialModel);
    assert!(
        has_w080,
        "Async function with rayon::spawn should produce W080"
    );
}

#[test]
fn async_with_crossbeam_scope_generates_vc() {
    let func = build_test_function("async_fn_crossbeam", true, Some("crossbeam::scope"));
    let result = generate_vcs(&func, None);
    let has_w080 = result
        .conditions
        .iter()
        .any(|vc| vc.location.vc_kind == VcKind::AsyncSequentialModel);
    assert!(
        has_w080,
        "Async function with crossbeam::scope should produce W080"
    );
}
