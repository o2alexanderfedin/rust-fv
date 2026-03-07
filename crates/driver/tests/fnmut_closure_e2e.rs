//! End-to-end driver integration tests for FnMut closure prophecy wiring (Phase 42).
//!
//! These tests confirm that the Phase 39 prophecy machinery (detect_closure_prophecies)
//! is reachable from the driver pipeline when a function parameter has Ty::Closure with
//! CaptureMode::ByMutRef env_fields.
//!
//! Tests construct IR directly — no rustc compilation needed — following generics_driver_e2e.rs.
//!
//! Prophecy assertion strategy:
//! Since `VerificationResult.condition` is a human-readable description (not the SMT script),
//! we check the SMT-level prophecy declarations by calling `generate_vcs_with_db` directly
//! from the analysis crate. The driver pipeline test separately confirms the production
//! pipeline is reachable (non-empty results from verify_functions_parallel).

use rust_fv_analysis::ghost_predicate_db::GhostPredicateDatabase;
use rust_fv_analysis::ir::{
    BasicBlock, CaptureMode, ClosureInfo, ClosureTrait, Contracts, Function, IntTy, Local,
    SpecExpr, Terminator, Ty,
};
use rust_fv_analysis::monomorphize::MonomorphizationRegistry;
use rust_fv_driver::cache::VcCache;
use rust_fv_driver::invalidation::{InvalidationDecision, InvalidationReason};
use rust_fv_driver::parallel::{VerificationTask, verify_functions_parallel};
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;

fn temp_cache_dir(name: &str) -> PathBuf {
    let mut dir = std::env::temp_dir();
    dir.push(format!("rust-fv-fnmut-e2e-{}-{}", name, std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    dir
}

fn make_fnmut_closure_func() -> Function {
    let closure_info = ClosureInfo {
        name: "mutator".to_string(),
        env_fields: vec![(
            "count".to_string(),
            Ty::Int(IntTy::I32),
            CaptureMode::ByMutRef,
        )],
        params: vec![],
        return_ty: Ty::Unit,
        trait_kind: ClosureTrait::FnMut,
    };
    Function {
        name: "apply_increment".to_string(),
        params: vec![Local::new("_1", Ty::Closure(Box::new(closure_info)))],
        return_local: Local::new("_0", Ty::Unit),
        locals: vec![],
        basic_blocks: vec![BasicBlock {
            statements: vec![],
            terminator: Terminator::Return,
        }],
        contracts: Contracts {
            requires: vec![],
            ensures: vec![SpecExpr {
                raw: "true".to_string(),
            }],
            invariants: vec![],
            is_pure: false,
            decreases: None,
            fn_specs: vec![],
            state_invariant: None,
            is_inferred: false,
        },
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
        source_names: HashMap::new(),
        coroutine_info: None,
        refcell_ghost_states: vec![],
        maybeuninit_ghost_states: vec![],
        union_ghost_states: vec![],
        pin_ghost_states: vec![],
        drop_locals: vec![],
    }
}

fn make_task(func: Function, cache_dir: PathBuf) -> (VerificationTask, VcCache) {
    let task = VerificationTask {
        name: func.name.clone(),
        ir_func: func,
        contract_db: Arc::new(rust_fv_analysis::contract_db::ContractDatabase::new()),
        ghost_pred_db: Arc::new(GhostPredicateDatabase::new()),
        monomorphization_registry: Arc::new(MonomorphizationRegistry::new()),
        cache_key: [0u8; 32],
        mir_hash: [0u8; 32],
        contract_hash: [0u8; 32],
        dependencies: vec![],
        invalidation_decision: InvalidationDecision::verify(InvalidationReason::Fresh),
        source_locations: HashMap::new(),
    };
    let cache = VcCache::new(cache_dir);
    (task, cache)
}

/// Confirms Phase 39 detect_closure_prophecies is reachable from production pipeline.
///
/// Truth: A FnMut closure with CaptureMode::ByMutRef on "count" causes prophecy variables
/// to appear in the generated SMT output (observable: SMT script contains 'count_prophecy').
///
/// Two checks:
/// 1. SMT-level: generate_vcs_with_db produces a script containing "count_prophecy"
///    (verifies the Phase 39 detect_closure_prophecies path fired)
/// 2. Driver-level: verify_functions_parallel produces non-empty results
///    (verifies the production pipeline is wired end-to-end)
#[test]
fn test_fnmut_closure_prophecy_pipeline_produces_vcs() {
    let func = make_fnmut_closure_func();

    // -- SMT-level check: verify that detect_closure_prophecies emits prophecy declarations --
    {
        let func_vcs = rust_fv_analysis::vcgen::generate_vcs(&func, None);
        assert!(
            !func_vcs.conditions.is_empty(),
            "Expected at least one VC for FnMut closure function with ensures contract. \
             Got 0 conditions — Phase 39 prophecy machinery may not be reached."
        );
        // Check the first VC's SMT script for prophecy variable declarations.
        // detect_closure_prophecies(closure_info_with_ByMutRef) emits:
        //   (declare-const count_initial Int)
        //   (declare-const count_prophecy Int)
        let script_str = format!("{}", func_vcs.conditions[0].script);
        assert!(
            script_str.contains("prophecy"),
            "Expected SMT script to contain 'prophecy' (from detect_closure_prophecies for \
             ByMutRef capture 'count'). Phase 39 machinery may not be wired. Script:\n{}",
            script_str
        );
    }

    // -- Driver-level check: verify_functions_parallel produces non-empty results --
    {
        let func2 = make_fnmut_closure_func();
        let cache_dir = temp_cache_dir("fnmut_prophecy");
        let (task, mut cache) = make_task(func2, cache_dir);

        let results = verify_functions_parallel(vec![task], &mut cache, 1, false, false);

        assert_eq!(
            results.len(),
            1,
            "Expected one TaskResult for apply_increment"
        );
        let task_results = &results[0].results;
        assert!(
            !task_results.is_empty(),
            "Expected non-empty VC results for FnMut closure function. \
             Got 0 — Phase 39 prophecy machinery may not be reachable from driver pipeline."
        );
    }
}

/// Fn closure with ByMove captures should produce VCs but no prophecy declarations.
///
/// Truth: An Fn closure with only ByMove captures produces VCs but no prophecy variable
/// declarations in the SMT output.
#[test]
fn test_fnmut_closure_no_mut_capture_no_prophecy_vars() {
    let closure_info = ClosureInfo {
        name: "capturer".to_string(),
        env_fields: vec![(
            "value".to_string(),
            Ty::Int(IntTy::I32),
            CaptureMode::ByMove,
        )],
        params: vec![],
        return_ty: Ty::Unit,
        trait_kind: ClosureTrait::Fn,
    };
    let func = Function {
        name: "apply_fn".to_string(),
        params: vec![Local::new("_1", Ty::Closure(Box::new(closure_info)))],
        return_local: Local::new("_0", Ty::Unit),
        locals: vec![],
        basic_blocks: vec![BasicBlock {
            statements: vec![],
            terminator: Terminator::Return,
        }],
        contracts: Contracts {
            requires: vec![],
            ensures: vec![SpecExpr {
                raw: "true".to_string(),
            }],
            invariants: vec![],
            is_pure: false,
            decreases: None,
            fn_specs: vec![],
            state_invariant: None,
            is_inferred: false,
        },
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
        source_names: HashMap::new(),
        coroutine_info: None,
        refcell_ghost_states: vec![],
        maybeuninit_ghost_states: vec![],
        union_ghost_states: vec![],
        pin_ghost_states: vec![],
        drop_locals: vec![],
    };

    // -- SMT-level check: no prophecy declarations for ByMove-only captures --
    {
        let func_vcs = rust_fv_analysis::vcgen::generate_vcs(&func, None);
        assert!(
            !func_vcs.conditions.is_empty(),
            "Expected VCs for Fn closure function (no regression). Got 0 results."
        );
        let script_str = format!("{}", func_vcs.conditions[0].script);
        assert!(
            !script_str.contains("_prophecy"),
            "Unexpected prophecy variable in SMT script for ByMove-only closure. \
             No prophety declarations expected (no ByMutRef captures). Script:\n{}",
            script_str
        );
    }

    // -- Driver-level check: pipeline produces non-empty results --
    {
        let closure_info2 = ClosureInfo {
            name: "capturer".to_string(),
            env_fields: vec![(
                "value".to_string(),
                Ty::Int(IntTy::I32),
                CaptureMode::ByMove,
            )],
            params: vec![],
            return_ty: Ty::Unit,
            trait_kind: ClosureTrait::Fn,
        };
        let func2 = Function {
            name: "apply_fn".to_string(),
            params: vec![Local::new("_1", Ty::Closure(Box::new(closure_info2)))],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "true".to_string(),
                }],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
                is_inferred: false,
            },
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
            source_names: HashMap::new(),
            coroutine_info: None,
            refcell_ghost_states: vec![],
            maybeuninit_ghost_states: vec![],
            union_ghost_states: vec![],
            pin_ghost_states: vec![],
            drop_locals: vec![],
        };
        let cache_dir = temp_cache_dir("fn_no_prophecy");
        let (task, mut cache) = make_task(func2, cache_dir);
        let results = verify_functions_parallel(vec![task], &mut cache, 1, false, false);

        assert_eq!(results.len(), 1, "Expected one TaskResult for apply_fn");
        let task_results = &results[0].results;
        assert!(
            !task_results.is_empty(),
            "Expected VCs for Fn closure function (no regression). Got 0 results."
        );
        // No ByMutRef captures means no prophecy variables in any condition.
        let spurious_prophecy = task_results
            .iter()
            .any(|r| r.condition.contains("prophecy"));
        assert!(
            !spurious_prophecy,
            "Unexpected 'prophecy' in VC condition description for ByMove-only closure. \
             Conditions: {:?}",
            task_results
                .iter()
                .map(|r| &r.condition)
                .collect::<Vec<_>>()
        );
    }
}
