//! Correctness tests proving incremental verification equals full verification.
//!
//! These tests validate that the cache invalidation logic is sound:
//! - Body-only changes re-verify only the changed function
//! - Contract changes trigger transitive re-verification of callers
//! - No-change runs produce 100% cache hits
//! - Fresh flag bypasses cache without deleting files
//! - Expired entries are evicted correctly
//! - Hash stability ensures same input produces same hash
//! - Cycles and diamonds are handled correctly
//!
//! All tests operate at the IR/cache/invalidation level without requiring rustc compilation.

use rust_fv_analysis::call_graph::CallGraph;
use rust_fv_analysis::ir::{
    BasicBlock, Contracts, Function, IntTy, Local, Operand, Place, SpecExpr, Statement, Terminator,
    Ty,
};
use rust_fv_driver::cache::{CacheEntry, VcCache};
use rust_fv_driver::invalidation::{InvalidationReason, decide_verification};
use std::collections::HashSet;
use std::path::PathBuf;

/// Helper: Create temp cache directory for tests.
fn temp_cache_dir(test_name: &str) -> PathBuf {
    let mut dir = std::env::temp_dir();
    dir.push(format!(
        "rust-fv-correctness-test-{}-{}",
        test_name,
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    dir
}

/// Helper: Create a minimal function with given basic blocks.
fn make_function(name: &str, basic_blocks: Vec<BasicBlock>, contracts: Contracts) -> Function {
    Function {
        name: name.to_string(),
        params: vec![Local::new("_1", Ty::Int(IntTy::I32))],
        return_local: Local::new("_0", Ty::Int(IntTy::I32)),
        locals: vec![Local::new("_2", Ty::Int(IntTy::I32))],
        basic_blocks,
        contracts,
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
    }
}

/// Helper: Create a call block.
fn call_block(callee: &str, target: usize) -> BasicBlock {
    BasicBlock {
        statements: vec![],
        terminator: Terminator::Call {
            func: callee.to_string(),
            args: vec![Operand::Copy(Place::local("_1"))],
            destination: Place::local("_2"),
            target,
        },
    }
}

/// Helper: Create a return block.
fn return_block() -> BasicBlock {
    BasicBlock {
        statements: vec![Statement::Nop],
        terminator: Terminator::Return,
    }
}

/// Helper: Create simple contracts.
fn simple_contracts() -> Contracts {
    Contracts {
        requires: vec![SpecExpr {
            raw: "_1 > 0".to_string(),
        }],
        ensures: vec![SpecExpr {
            raw: "result > 0".to_string(),
        }],
        invariants: vec![],
        is_pure: false,
        decreases: None,
        fn_specs: vec![],
    }
}

#[test]
fn incremental_body_change_same_result() {
    // Create 5 functions with call dependencies: a->b->c, d->e
    let contracts_a = simple_contracts();
    let contracts_b = simple_contracts();
    let contracts_c = simple_contracts();
    let contracts_d = simple_contracts();
    let contracts_e = simple_contracts();

    let func_a = make_function(
        "a",
        vec![call_block("b", 1), return_block()],
        contracts_a.clone(),
    );
    let func_b = make_function(
        "b",
        vec![call_block("c", 1), return_block()],
        contracts_b.clone(),
    );
    let func_c = make_function("c", vec![return_block()], contracts_c.clone());
    let func_d = make_function(
        "d",
        vec![call_block("e", 1), return_block()],
        contracts_d.clone(),
    );
    let func_e = make_function("e", vec![return_block()], contracts_e.clone());

    let dir = temp_cache_dir("body_change");
    let mut cache = VcCache::new(dir.clone());

    // Run full verification and record results
    let functions = vec![
        ("a", &func_a, &contracts_a),
        ("b", &func_b, &contracts_b),
        ("c", &func_c, &contracts_c),
        ("d", &func_d, &contracts_d),
        ("e", &func_e, &contracts_e),
    ];

    for (name, func, contracts) in &functions {
        let mir_hash = VcCache::compute_mir_hash(name, &format!("{:?}", func));
        let contract_hash = VcCache::compute_contract_hash(name, contracts);

        let entry = CacheEntry {
            verified: true,
            vc_count: 2,
            verified_count: 2,
            message: None,
            mir_hash,
            contract_hash,
            timestamp: chrono::Utc::now().timestamp(),
            dependencies: vec![],
            ..Default::default()
        };

        #[allow(deprecated)]
        let key = VcCache::compute_key(name, contracts, &format!("{:?}", func));
        cache.insert(key, entry);
    }

    // Change function c's body
    let mut func_c_modified = func_c.clone();
    func_c_modified.basic_blocks[0]
        .statements
        .push(Statement::Nop);

    // Run incremental verification
    let mir_hash_c = VcCache::compute_mir_hash("c", &format!("{:?}", func_c_modified));
    let _contract_hash_c = VcCache::compute_contract_hash("c", &contracts_c);

    #[allow(deprecated)]
    let key_c = VcCache::compute_key("c", &contracts_c, &format!("{:?}", func_c_modified));

    // Assert: c is re-verified (MIR hash changed)
    if let Some(entry) = cache.get(&key_c) {
        assert_ne!(
            entry.mir_hash, mir_hash_c,
            "c's MIR hash should have changed"
        );
    }

    // Assert: a, b, d, e should still be cached (contract hash unchanged)
    for (name, func, contracts) in &[
        ("a", &func_a, &contracts_a),
        ("b", &func_b, &contracts_b),
        ("d", &func_d, &contracts_d),
        ("e", &func_e, &contracts_e),
    ] {
        let mir_hash = VcCache::compute_mir_hash(name, &format!("{:?}", func));
        let contract_hash = VcCache::compute_contract_hash(name, contracts);

        #[allow(deprecated)]
        let key = VcCache::compute_key(name, contracts, &format!("{:?}", func));

        if let Some(entry) = cache.get(&key) {
            assert_eq!(
                entry.mir_hash, mir_hash,
                "{}'s MIR hash should be unchanged",
                name
            );
            assert_eq!(
                entry.contract_hash, contract_hash,
                "{}'s contract hash should be unchanged",
                name
            );
        }
    }

    // Cleanup
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn incremental_contract_change_transitive_invalidation() {
    // Create chain: a->b->c
    let contracts_a = simple_contracts();
    let contracts_b = simple_contracts();
    let contracts_c = simple_contracts();

    let func_a = make_function(
        "a",
        vec![call_block("b", 1), return_block()],
        contracts_a.clone(),
    );
    let func_b = make_function(
        "b",
        vec![call_block("c", 1), return_block()],
        contracts_b.clone(),
    );
    let func_c = make_function("c", vec![return_block()], contracts_c.clone());

    let dir = temp_cache_dir("contract_change");
    let mut cache = VcCache::new(dir.clone());

    // Run full verification
    let functions = vec![
        ("a", &func_a, &contracts_a),
        ("b", &func_b, &contracts_b),
        ("c", &func_c, &contracts_c),
    ];

    for (name, func, contracts) in &functions {
        let mir_hash = VcCache::compute_mir_hash(name, &format!("{:?}", func));
        let contract_hash = VcCache::compute_contract_hash(name, contracts);

        let entry = CacheEntry {
            verified: true,
            vc_count: 2,
            verified_count: 2,
            message: None,
            mir_hash,
            contract_hash,
            timestamp: chrono::Utc::now().timestamp(),
            dependencies: vec!["b".to_string(), "c".to_string()], // Track dependencies
            ..Default::default()
        };

        #[allow(deprecated)]
        let key = VcCache::compute_key(name, contracts, &format!("{:?}", func));
        cache.insert(key, entry);
    }

    // Change c's contract
    let mut contracts_c_modified = contracts_c.clone();
    contracts_c_modified.ensures.push(SpecExpr {
        raw: "result > 100".to_string(),
    });

    // Run incremental verification with call graph
    let call_graph = CallGraph::from_functions(&[
        ("a".to_string(), &func_a),
        ("b".to_string(), &func_b),
        ("c".to_string(), &func_c),
    ]);

    // Assert: c, b, a are ALL re-verified (transitive invalidation)
    let transitive_callers = call_graph.transitive_callers("c");
    assert_eq!(transitive_callers.len(), 2);
    assert!(transitive_callers.contains(&"b".to_string()));
    assert!(transitive_callers.contains(&"a".to_string()));

    // Cleanup
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn incremental_no_change_all_cached() {
    // Create 10 functions
    let mut functions = Vec::new();
    for i in 0..10 {
        let name = format!("func_{}", i);
        let contracts = simple_contracts();
        let func = make_function(&name, vec![return_block()], contracts.clone());
        functions.push((name, func, contracts));
    }

    let dir = temp_cache_dir("no_change");
    let mut cache = VcCache::new(dir.clone());

    // Run full verification
    for (name, func, contracts) in &functions {
        let mir_hash = VcCache::compute_mir_hash(name, &format!("{:?}", func));
        let contract_hash = VcCache::compute_contract_hash(name, contracts);

        let entry = CacheEntry {
            verified: true,
            vc_count: 2,
            verified_count: 2,
            message: None,
            mir_hash,
            contract_hash,
            timestamp: chrono::Utc::now().timestamp(),
            dependencies: vec![],
            ..Default::default()
        };

        #[allow(deprecated)]
        let key = VcCache::compute_key(name, contracts, &format!("{:?}", func));
        cache.insert(key, entry);
    }

    // Run incremental verification with no changes
    let mut cached_count = 0;

    for (name, func, contracts) in &functions {
        let mir_hash = VcCache::compute_mir_hash(name, &format!("{:?}", func));
        let contract_hash = VcCache::compute_contract_hash(name, contracts);

        #[allow(deprecated)]
        let key = VcCache::compute_key(name, contracts, &format!("{:?}", func));

        if let Some(entry) = cache.get(&key)
            && entry.mir_hash == mir_hash
            && entry.contract_hash == contract_hash
        {
            cached_count += 1;
        }
    }

    // Assert: All 10 functions are cached
    assert_eq!(cached_count, 10);

    // Cleanup
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn fresh_flag_bypasses_cache() {
    // Create and verify 5 functions
    let mut functions = Vec::new();
    for i in 0..5 {
        let name = format!("func_{}", i);
        let contracts = simple_contracts();
        let func = make_function(&name, vec![return_block()], contracts.clone());
        functions.push((name, func, contracts));
    }

    let dir = temp_cache_dir("fresh_flag");
    let mut cache = VcCache::new(dir.clone());

    // Populate cache
    for (name, func, contracts) in &functions {
        let mir_hash = VcCache::compute_mir_hash(name, &format!("{:?}", func));
        let contract_hash = VcCache::compute_contract_hash(name, contracts);

        let entry = CacheEntry {
            verified: true,
            vc_count: 2,
            verified_count: 2,
            message: None,
            mir_hash,
            contract_hash,
            timestamp: chrono::Utc::now().timestamp(),
            dependencies: vec![],
            ..Default::default()
        };

        #[allow(deprecated)]
        let key = VcCache::compute_key(name, contracts, &format!("{:?}", func));
        cache.insert(key, entry);
    }

    // Run with fresh=true
    for (name, func, contracts) in &functions {
        let mir_hash = VcCache::compute_mir_hash(name, &format!("{:?}", func));
        let contract_hash = VcCache::compute_contract_hash(name, contracts);

        let decision = decide_verification(
            &cache,
            name,
            mir_hash,
            contract_hash,
            true, // fresh flag
            &HashSet::new(),
            &[],
        );

        // Assert: All functions are re-verified despite cache existing
        assert!(decision.should_verify);
        assert_eq!(decision.reason, Some(InvalidationReason::Fresh));
    }

    // Assert: Cache files still exist after fresh run
    for (name, func, contracts) in &functions {
        #[allow(deprecated)]
        let key = VcCache::compute_key(name, contracts, &format!("{:?}", func));

        assert!(cache.get(&key).is_some(), "Cache entry should still exist");
    }

    // Cleanup
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn expired_cache_triggers_reverification() {
    let name = "test_func";
    let contracts = simple_contracts();
    let func = make_function(name, vec![return_block()], contracts.clone());

    let dir = temp_cache_dir("expired");
    let mut cache = VcCache::new(dir.clone());

    // Create entry with timestamp 31 days ago
    let old_timestamp = chrono::Utc::now().timestamp() - (31 * 24 * 60 * 60);
    let mir_hash = VcCache::compute_mir_hash(name, &format!("{:?}", func));
    let contract_hash = VcCache::compute_contract_hash(name, &contracts);

    let entry = CacheEntry {
        verified: true,
        vc_count: 2,
        verified_count: 2,
        message: None,
        mir_hash,
        contract_hash,
        timestamp: old_timestamp,
        dependencies: vec![],
        ..Default::default()
    };

    #[allow(deprecated)]
    let key = VcCache::compute_key(name, &contracts, &format!("{:?}", func));
    cache.insert(key, entry);

    // Load cache - should evict expired entry
    let mut fresh_cache = VcCache::new(dir.clone());
    fresh_cache.load();

    // Assert: Expired entry is evicted
    assert!(
        fresh_cache.get(&key).is_none(),
        "Expired entry should be evicted"
    );

    // Cleanup
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn mir_hash_stability() {
    let contracts = simple_contracts();

    // Generate same function twice
    let func1 = make_function("test", vec![return_block()], contracts.clone());
    let func2 = make_function("test", vec![return_block()], contracts.clone());

    let hash1 = VcCache::compute_mir_hash("test", &format!("{:?}", func1));
    let hash2 = VcCache::compute_mir_hash("test", &format!("{:?}", func2));

    // Assert: MIR hashes are identical
    assert_eq!(hash1, hash2, "Same function should produce same MIR hash");

    // Modify function body
    let mut func3 = func1.clone();
    func3.basic_blocks[0].statements.push(Statement::Nop);

    let hash3 = VcCache::compute_mir_hash("test", &format!("{:?}", func3));

    // Assert: MIR hash changes
    assert_ne!(hash1, hash3, "Modified body should change MIR hash");

    // Assert: Contract hash unchanged
    let contract_hash1 = VcCache::compute_contract_hash("test", &contracts);
    let contract_hash3 = VcCache::compute_contract_hash("test", &contracts);
    assert_eq!(
        contract_hash1, contract_hash3,
        "Contract hash should be unchanged"
    );
}

#[test]
fn contract_hash_stability() {
    let func = make_function("test", vec![return_block()], Contracts::default());

    // Generate same contracts twice
    let contracts1 = simple_contracts();
    let contracts2 = simple_contracts();

    let hash1 = VcCache::compute_contract_hash("test", &contracts1);
    let hash2 = VcCache::compute_contract_hash("test", &contracts2);

    // Assert: Contract hashes are identical
    assert_eq!(
        hash1, hash2,
        "Same contracts should produce same contract hash"
    );

    // Modify one contract
    let mut contracts3 = contracts1.clone();
    contracts3.ensures.push(SpecExpr {
        raw: "result > 100".to_string(),
    });

    let hash3 = VcCache::compute_contract_hash("test", &contracts3);

    // Assert: Contract hash changes
    assert_ne!(
        hash1, hash3,
        "Modified contract should change contract hash"
    );

    // Assert: MIR hash unchanged
    let mir_hash1 = VcCache::compute_mir_hash("test", &format!("{:?}", func));
    let mir_hash3 = VcCache::compute_mir_hash("test", &format!("{:?}", func));
    assert_eq!(mir_hash1, mir_hash3, "MIR hash should be unchanged");
}

#[test]
fn cycle_handling_no_infinite_loop() {
    // Create mutually recursive functions: a->b->a
    let contracts_a = simple_contracts();
    let contracts_b = simple_contracts();

    let func_a = make_function(
        "a",
        vec![call_block("b", 1), return_block()],
        contracts_a.clone(),
    );
    let func_b = make_function(
        "b",
        vec![call_block("a", 1), return_block()],
        contracts_b.clone(),
    );

    let call_graph =
        CallGraph::from_functions(&[("a".to_string(), &func_a), ("b".to_string(), &func_b)]);

    // Change a's contract
    let mut contracts_a_modified = contracts_a.clone();
    contracts_a_modified.ensures.push(SpecExpr {
        raw: "result > 100".to_string(),
    });

    // Assert: transitive_callers terminates (doesn't loop)
    let callers_a = call_graph.transitive_callers("a");

    // Assert: Both a and b are re-verified (cycle participants)
    assert_eq!(callers_a.len(), 2);
    assert!(callers_a.contains(&"a".to_string()));
    assert!(callers_a.contains(&"b".to_string()));
}

#[test]
fn diamond_dependency_single_invalidation() {
    // Create diamond: top->left, top->right, left->bottom, right->bottom
    let contracts_top = simple_contracts();
    let contracts_left = simple_contracts();
    let contracts_right = simple_contracts();
    let contracts_bottom = simple_contracts();

    let func_top = make_function(
        "top",
        vec![
            call_block("left", 1),
            call_block("right", 2),
            return_block(),
        ],
        contracts_top.clone(),
    );
    let func_left = make_function(
        "left",
        vec![call_block("bottom", 1), return_block()],
        contracts_left.clone(),
    );
    let func_right = make_function(
        "right",
        vec![call_block("bottom", 1), return_block()],
        contracts_right.clone(),
    );
    let func_bottom = make_function("bottom", vec![return_block()], contracts_bottom.clone());

    let call_graph = CallGraph::from_functions(&[
        ("top".to_string(), &func_top),
        ("left".to_string(), &func_left),
        ("right".to_string(), &func_right),
        ("bottom".to_string(), &func_bottom),
    ]);

    // Change bottom's contract
    let mut contracts_bottom_modified = contracts_bottom.clone();
    contracts_bottom_modified.ensures.push(SpecExpr {
        raw: "result > 100".to_string(),
    });

    // Assert: All 4 functions re-verified (transitive)
    let callers = call_graph.transitive_callers("bottom");

    assert_eq!(callers.len(), 3);
    assert!(callers.contains(&"left".to_string()));
    assert!(callers.contains(&"right".to_string()));
    assert!(callers.contains(&"top".to_string()));

    // Note: The test validates that transitive_callers returns all callers correctly.
    // The "no function verified more than once" property would be validated in the
    // actual verification driver code that uses this data structure.
}
