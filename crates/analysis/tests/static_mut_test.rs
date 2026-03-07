//! Tests for mutable static access data-race freedom VCs.
//!
//! Verifies that:
//! - StaticMutAccess generates DataRaceFreedom VCs for both reads and writes
//! - Synchronized (Mutex guard) accesses do NOT generate DataRaceFreedom VCs
//! - V100 diagnostic message contains appropriate text

use rust_fv_analysis::ir::{
    BasicBlock, Contracts, Function, Local, Terminator, Ty, UnsafeOperation,
};
use rust_fv_analysis::unsafe_analysis::needs_data_race_check;
use rust_fv_analysis::vcgen::VcKind;

fn make_test_function(unsafe_operations: Vec<UnsafeOperation>) -> Function {
    Function {
        name: "test_fn".to_string(),
        params: vec![],
        return_local: Local::new("_0", Ty::Bool),
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
    }
}

#[test]
fn static_mut_read_generates_data_race_check() {
    // Test 1: A function accessing `static mut X: i32` generates a StaticMutAccess UnsafeOperation
    let op = UnsafeOperation::StaticMutAccess {
        static_name: "COUNTER".to_string(),
        is_write: false,
        synchronized: false,
        block_index: 0,
    };
    assert!(
        needs_data_race_check(&op),
        "Unsynchronized static mut read should require data-race check"
    );
}

#[test]
fn static_mut_write_generates_data_race_check() {
    // Test 5: Both reads and writes to static mut generate VCs (not just writes)
    let op = UnsafeOperation::StaticMutAccess {
        static_name: "COUNTER".to_string(),
        is_write: true,
        synchronized: false,
        block_index: 0,
    };
    assert!(
        needs_data_race_check(&op),
        "Unsynchronized static mut write should require data-race check"
    );
}

#[test]
fn static_mut_generates_data_race_freedom_vc() {
    // Test 2: StaticMutAccess generates a DataRaceFreedom VC (VcKind::DataRaceFreedom)
    let func = make_test_function(vec![UnsafeOperation::StaticMutAccess {
        static_name: "COUNTER".to_string(),
        is_write: false,
        synchronized: false,
        block_index: 0,
    }]);

    let result = rust_fv_analysis::vcgen::generate_vcs(&func, None);

    let has_data_race_vc = result
        .conditions
        .iter()
        .any(|vc| vc.location.vc_kind == VcKind::DataRaceFreedom);
    assert!(
        has_data_race_vc,
        "StaticMutAccess should generate a DataRaceFreedom VC"
    );
}

#[test]
fn synchronized_static_mut_no_data_race_vc() {
    // Test 3: When static mut access is inside a Mutex::lock() guard scope,
    // the DataRaceFreedom VC is NOT generated
    let func = make_test_function(vec![UnsafeOperation::StaticMutAccess {
        static_name: "COUNTER".to_string(),
        is_write: true,
        synchronized: true,
        block_index: 0,
    }]);

    let result = rust_fv_analysis::vcgen::generate_vcs(&func, None);

    let has_data_race_vc = result
        .conditions
        .iter()
        .any(|vc| vc.location.vc_kind == VcKind::DataRaceFreedom);
    assert!(
        !has_data_race_vc,
        "Synchronized static mut access should NOT generate a DataRaceFreedom VC"
    );
}

#[test]
fn data_race_vc_description_contains_mutable_static() {
    // Test 4: VC description mentions mutable static access and synchronization
    let func = make_test_function(vec![UnsafeOperation::StaticMutAccess {
        static_name: "GLOBAL_STATE".to_string(),
        is_write: false,
        synchronized: false,
        block_index: 0,
    }]);

    let result = rust_fv_analysis::vcgen::generate_vcs(&func, None);

    let data_race_vc = result
        .conditions
        .iter()
        .find(|vc| vc.location.vc_kind == VcKind::DataRaceFreedom);

    assert!(data_race_vc.is_some(), "Should have a DataRaceFreedom VC");
    let vc = data_race_vc.unwrap();
    assert!(
        vc.description.contains("mutable static") || vc.description.contains("GLOBAL_STATE"),
        "DataRaceFreedom VC description should mention mutable static or the static name, got: {}",
        vc.description
    );
}
