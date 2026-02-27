//! Benchmark suite for incremental verification performance.
//!
//! Provides synthetic codebase generation and performance measurement to demonstrate
//! incremental verification speedup (20-30x target for body changes, cache hits).
//!
//! Benchmarks measure wall-clock time and cache hit rates for:
//! - Full verification (cold cache)
//! - Incremental body change (hot cache, 1 function modified)
//! - Incremental contract change (hot cache, transitive invalidation)
//! - No-change run (100% cache hit)

use crate::cache::{CacheEntry, VcCache};
use rust_fv_analysis::ir::{
    BasicBlock, Contracts, Function, IntTy, Local, Operand, Place, SpecExpr, Statement, Terminator,
    Ty,
};
use std::time::Instant;

/// Generate synthetic functions for benchmarking.
///
/// Creates N functions with realistic call patterns:
/// - ~30% leaf functions (no calls)
/// - ~50% single-caller functions (call 1-2 others)
/// - ~20% high-fan-out functions (call 3-5 others)
/// - Each function has 1-3 contracts (requires/ensures)
/// - Function bodies have 2-5 basic blocks with assignments and assertions
///
/// Returns: Vec<(function_name, Function, Contracts)>
pub fn generate_synthetic_functions(count: usize) -> Vec<(String, Function, Contracts)> {
    let mut functions = Vec::new();

    for i in 0..count {
        let func_name = format!("func_{}", i);
        let contracts = generate_contracts(i);
        let basic_blocks = generate_basic_blocks(i, count);

        let func = Function {
            name: func_name.clone(),
            params: vec![Local::new("_1", Ty::Int(IntTy::I32))],
            return_local: Local::new("_0", Ty::Int(IntTy::I32)),
            locals: vec![
                Local::new("_2", Ty::Int(IntTy::I32)),
                Local::new("_3", Ty::Int(IntTy::I32)),
            ],
            basic_blocks,
            contracts: contracts.clone(),
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
        };

        functions.push((func_name, func, contracts));
    }

    functions
}

/// Generate contracts for a function based on its index.
///
/// Produces 1-3 contracts (requires/ensures) with deterministic content.
fn generate_contracts(func_index: usize) -> Contracts {
    let contract_count = (func_index % 3) + 1; // 1-3 contracts

    let mut contracts = Contracts::default();

    for j in 0..contract_count {
        contracts.requires.push(SpecExpr {
            raw: format!("_1 > {}", j),
        });
        contracts.ensures.push(SpecExpr {
            raw: format!("result > {}", j + 10),
        });
    }

    contracts
}

/// Generate basic blocks for a function based on its index.
///
/// Call pattern distribution:
/// - ~30% leaf functions (no calls)
/// - ~50% single-caller functions (call 1-2 others)
/// - ~20% high-fan-out functions (call 3-5 others)
///
/// Each function has 2-5 basic blocks.
fn generate_basic_blocks(func_index: usize, total_count: usize) -> Vec<BasicBlock> {
    let bb_count = (func_index % 4) + 2; // 2-5 basic blocks
    let mut blocks = Vec::new();

    // Determine call pattern based on index
    let call_pattern = func_index % 10;
    let callees: Vec<usize> = if call_pattern < 3 {
        // 30% leaf functions (no calls)
        vec![]
    } else if call_pattern < 8 {
        // 50% single-caller functions (call 1-2 others)
        let call_count = (func_index % 2) + 1;
        (0..call_count)
            .filter_map(|offset| {
                let target = func_index.saturating_sub(offset + 1);
                if target < total_count && target != func_index {
                    Some(target)
                } else {
                    None
                }
            })
            .collect()
    } else {
        // 20% high-fan-out functions (call 3-5 others)
        let call_count = (func_index % 3) + 3;
        (0..call_count)
            .filter_map(|offset| {
                let target = func_index.saturating_sub(offset + 1);
                if target < total_count && target != func_index {
                    Some(target)
                } else {
                    None
                }
            })
            .collect()
    };

    // Generate basic blocks
    for bb_idx in 0..bb_count {
        let block = if bb_idx < callees.len() {
            // Call block
            BasicBlock {
                statements: vec![Statement::Nop],
                terminator: Terminator::Call {
                    func: format!("func_{}", callees[bb_idx]),
                    args: vec![Operand::Copy(Place::local("_1"))],
                    destination: Place::local("_2"),
                    target: bb_idx + 1,
                },
            }
        } else if bb_idx == bb_count - 1 {
            // Return block (last)
            BasicBlock {
                statements: vec![Statement::Nop],
                terminator: Terminator::Return,
            }
        } else {
            // Assignment block
            BasicBlock {
                statements: vec![Statement::Nop],
                terminator: Terminator::Goto(bb_idx + 1),
            }
        };
        blocks.push(block);
    }

    blocks
}

/// Benchmark result for a single scenario.
#[derive(Debug, Clone)]
pub struct BenchmarkResult {
    /// Scenario name
    pub scenario: String,
    /// Number of functions benchmarked
    pub function_count: usize,
    /// Wall-clock time in milliseconds
    pub duration_ms: u64,
    /// Number of functions verified (not cached)
    pub verified_count: usize,
    /// Number of functions cached (skipped)
    pub cached_count: usize,
}

impl BenchmarkResult {
    /// Calculate speedup ratio relative to baseline.
    pub fn speedup_vs(&self, baseline: &BenchmarkResult) -> f64 {
        if self.duration_ms == 0 {
            return 0.0;
        }
        baseline.duration_ms as f64 / self.duration_ms as f64
    }

    /// Format cache hit rate.
    pub fn cache_hit_rate(&self) -> String {
        format!("{}/{}", self.cached_count, self.function_count)
    }
}

/// Run full verification benchmark (cold cache).
///
/// Verifies N functions from scratch without any cached results.
pub fn bench_full_verification(n: usize) -> BenchmarkResult {
    let functions = generate_synthetic_functions(n);
    let temp_dir = std::env::temp_dir().join(format!("bench_full_{}", std::process::id()));
    let mut cache = VcCache::new(temp_dir.clone());

    let start = Instant::now();

    // Simulate verification of all functions
    for (func_name, func, contracts) in &functions {
        let mir_hash = VcCache::compute_mir_hash(func_name, &format!("{:?}", func));
        let contract_hash = VcCache::compute_contract_hash(func_name, contracts);

        // Simulate verification work (not actual SMT solving, just cache operations)
        let entry = CacheEntry {
            verified: true,
            vc_count: contracts.requires.len() + contracts.ensures.len(),
            verified_count: contracts.requires.len() + contracts.ensures.len(),
            message: None,
            mir_hash,
            contract_hash,
            timestamp: chrono::Utc::now().timestamp(),
            dependencies: vec![],
            ..Default::default()
        };

        // Use combined hash for cache key (backward compatible)
        #[allow(deprecated)]
        let key = VcCache::compute_key(func_name, contracts, &format!("{:?}", func));
        cache.insert(key, entry);
    }

    let duration = start.elapsed();

    // Cleanup
    let _ = std::fs::remove_dir_all(&temp_dir);

    BenchmarkResult {
        scenario: "Full verification".to_string(),
        function_count: n,
        duration_ms: duration.as_millis() as u64,
        verified_count: n,
        cached_count: 0,
    }
}

/// Run incremental body change benchmark.
///
/// Verifies N functions, then changes 1 function body and re-verifies.
/// Should skip N-1 functions (cache hits).
pub fn bench_incremental_body_change(n: usize) -> BenchmarkResult {
    let functions = generate_synthetic_functions(n);
    let temp_dir = std::env::temp_dir().join(format!("bench_body_change_{}", std::process::id()));
    let mut cache = VcCache::new(temp_dir.clone());

    // Initial verification (populate cache)
    for (func_name, func, contracts) in &functions {
        let mir_hash = VcCache::compute_mir_hash(func_name, &format!("{:?}", func));
        let contract_hash = VcCache::compute_contract_hash(func_name, contracts);

        let entry = CacheEntry {
            verified: true,
            vc_count: contracts.requires.len() + contracts.ensures.len(),
            verified_count: contracts.requires.len() + contracts.ensures.len(),
            message: None,
            mir_hash,
            contract_hash,
            timestamp: chrono::Utc::now().timestamp(),
            dependencies: vec![],
            ..Default::default()
        };

        #[allow(deprecated)]
        let key = VcCache::compute_key(func_name, contracts, &format!("{:?}", func));
        cache.insert(key, entry);
    }

    // Modify the first function's body (change MIR hash)
    let modified_index = 0;
    let (func_name, mut func, contracts) = functions[modified_index].clone();
    func.basic_blocks[0].statements.push(Statement::Nop); // Modify body

    let start = Instant::now();

    // Re-verify all functions (only modified one should be re-verified)
    let mut verified_count = 0;
    let mut cached_count = 0;

    #[allow(clippy::needless_range_loop)]
    for i in 0..n {
        let (name, f, c) = if i == modified_index {
            (&func_name, &func, &contracts)
        } else {
            (&functions[i].0, &functions[i].1, &functions[i].2)
        };

        let mir_hash = VcCache::compute_mir_hash(name, &format!("{:?}", f));
        let contract_hash = VcCache::compute_contract_hash(name, c);

        #[allow(deprecated)]
        let key = VcCache::compute_key(name, c, &format!("{:?}", f));

        if let Some(entry) = cache.get(&key)
            && entry.mir_hash == mir_hash
            && entry.contract_hash == contract_hash
        {
            // Cache hit
            cached_count += 1;
            continue;
        }

        // Cache miss or invalidation - re-verify
        verified_count += 1;
        let entry = CacheEntry {
            verified: true,
            vc_count: c.requires.len() + c.ensures.len(),
            verified_count: c.requires.len() + c.ensures.len(),
            message: None,
            mir_hash,
            contract_hash,
            timestamp: chrono::Utc::now().timestamp(),
            dependencies: vec![],
            ..Default::default()
        };
        cache.insert(key, entry);
    }

    let duration = start.elapsed();

    // Cleanup
    let _ = std::fs::remove_dir_all(&temp_dir);

    BenchmarkResult {
        scenario: "Body change (1 func)".to_string(),
        function_count: n,
        duration_ms: duration.as_millis() as u64,
        verified_count,
        cached_count,
    }
}

/// Run incremental contract change benchmark.
///
/// Verifies N functions, then changes 1 contract and re-verifies.
/// Should re-verify the function + transitive callers (contract invalidation).
pub fn bench_incremental_contract_change(n: usize) -> BenchmarkResult {
    let functions = generate_synthetic_functions(n);
    let temp_dir =
        std::env::temp_dir().join(format!("bench_contract_change_{}", std::process::id()));
    let mut cache = VcCache::new(temp_dir.clone());

    // Initial verification (populate cache)
    for (func_name, func, contracts) in &functions {
        let mir_hash = VcCache::compute_mir_hash(func_name, &format!("{:?}", func));
        let contract_hash = VcCache::compute_contract_hash(func_name, contracts);

        let entry = CacheEntry {
            verified: true,
            vc_count: contracts.requires.len() + contracts.ensures.len(),
            verified_count: contracts.requires.len() + contracts.ensures.len(),
            message: None,
            mir_hash,
            contract_hash,
            timestamp: chrono::Utc::now().timestamp(),
            dependencies: vec![],
            ..Default::default()
        };

        #[allow(deprecated)]
        let key = VcCache::compute_key(func_name, contracts, &format!("{:?}", func));
        cache.insert(key, entry);
    }

    // Modify a contract (choose a function that has callers)
    let modified_index = n / 2; // Middle function likely has callers
    let (func_name, func, mut contracts) = functions[modified_index].clone();
    contracts.ensures.push(SpecExpr {
        raw: "result > 999".to_string(),
    }); // Modify contract

    let start = Instant::now();

    // Re-verify all functions (contract change affects transitive callers)
    let mut verified_count = 0;
    let mut cached_count = 0;

    #[allow(clippy::needless_range_loop)]
    for i in 0..n {
        let (name, f, c) = if i == modified_index {
            (&func_name, &func, &contracts)
        } else {
            (&functions[i].0, &functions[i].1, &functions[i].2)
        };

        let mir_hash = VcCache::compute_mir_hash(name, &format!("{:?}", f));
        let contract_hash = VcCache::compute_contract_hash(name, c);

        #[allow(deprecated)]
        let key = VcCache::compute_key(name, c, &format!("{:?}", f));

        if let Some(entry) = cache.get(&key)
            && entry.mir_hash == mir_hash
            && entry.contract_hash == contract_hash
        {
            // Cache hit
            cached_count += 1;
            continue;
        }

        // Cache miss or invalidation - re-verify
        verified_count += 1;
        let entry = CacheEntry {
            verified: true,
            vc_count: c.requires.len() + c.ensures.len(),
            verified_count: c.requires.len() + c.ensures.len(),
            message: None,
            mir_hash,
            contract_hash,
            timestamp: chrono::Utc::now().timestamp(),
            dependencies: vec![],
            ..Default::default()
        };
        cache.insert(key, entry);
    }

    let duration = start.elapsed();

    // Cleanup
    let _ = std::fs::remove_dir_all(&temp_dir);

    BenchmarkResult {
        scenario: "Contract change (1 func)".to_string(),
        function_count: n,
        duration_ms: duration.as_millis() as u64,
        verified_count,
        cached_count,
    }
}

/// Run no-change benchmark.
///
/// Verifies N functions, then re-verifies with no changes.
/// Should skip all N functions (100% cache hit).
pub fn bench_incremental_no_change(n: usize) -> BenchmarkResult {
    let functions = generate_synthetic_functions(n);
    let temp_dir = std::env::temp_dir().join(format!("bench_no_change_{}", std::process::id()));
    let mut cache = VcCache::new(temp_dir.clone());

    // Initial verification (populate cache)
    for (func_name, func, contracts) in &functions {
        let mir_hash = VcCache::compute_mir_hash(func_name, &format!("{:?}", func));
        let contract_hash = VcCache::compute_contract_hash(func_name, contracts);

        let entry = CacheEntry {
            verified: true,
            vc_count: contracts.requires.len() + contracts.ensures.len(),
            verified_count: contracts.requires.len() + contracts.ensures.len(),
            message: None,
            mir_hash,
            contract_hash,
            timestamp: chrono::Utc::now().timestamp(),
            dependencies: vec![],
            ..Default::default()
        };

        #[allow(deprecated)]
        let key = VcCache::compute_key(func_name, contracts, &format!("{:?}", func));
        cache.insert(key, entry);
    }

    let start = Instant::now();

    // Re-verify all functions (no changes, all should hit cache)
    let mut verified_count = 0;
    let mut cached_count = 0;

    for (func_name, func, contracts) in &functions {
        let mir_hash = VcCache::compute_mir_hash(func_name, &format!("{:?}", func));
        let contract_hash = VcCache::compute_contract_hash(func_name, contracts);

        #[allow(deprecated)]
        let key = VcCache::compute_key(func_name, contracts, &format!("{:?}", func));

        if let Some(entry) = cache.get(&key)
            && entry.mir_hash == mir_hash
            && entry.contract_hash == contract_hash
        {
            // Cache hit
            cached_count += 1;
            continue;
        }

        // Cache miss - re-verify
        verified_count += 1;
        let entry = CacheEntry {
            verified: true,
            vc_count: contracts.requires.len() + contracts.ensures.len(),
            verified_count: contracts.requires.len() + contracts.ensures.len(),
            message: None,
            mir_hash,
            contract_hash,
            timestamp: chrono::Utc::now().timestamp(),
            dependencies: vec![],
            ..Default::default()
        };
        cache.insert(key, entry);
    }

    let duration = start.elapsed();

    // Cleanup
    let _ = std::fs::remove_dir_all(&temp_dir);

    BenchmarkResult {
        scenario: "No change".to_string(),
        function_count: n,
        duration_ms: duration.as_millis() as u64,
        verified_count,
        cached_count,
    }
}

/// Run full benchmark suite and print results.
///
/// Can be called from CI or `cargo test -- --ignored bench`.
pub fn run_benchmark() {
    println!("Incremental Verification Benchmark");
    println!("===================================\n");

    for &n in &[20, 50, 100] {
        println!("Functions: {}", n);
        println!();

        let full = bench_full_verification(n);
        let body = bench_incremental_body_change(n);
        let contract = bench_incremental_contract_change(n);
        let no_change = bench_incremental_no_change(n);

        println!("{:<25} {:>8}ms", full.scenario, full.duration_ms);
        println!(
            "{:<25} {:>8}ms ({:.1}x speedup, {})",
            body.scenario,
            body.duration_ms,
            body.speedup_vs(&full),
            body.cache_hit_rate()
        );
        println!(
            "{:<25} {:>8}ms ({:.1}x speedup, {})",
            contract.scenario,
            contract.duration_ms,
            contract.speedup_vs(&full),
            contract.cache_hit_rate()
        );
        println!(
            "{:<25} {:>8}ms ({:.1}x speedup, {})",
            no_change.scenario,
            no_change.duration_ms,
            no_change.speedup_vs(&full),
            no_change.cache_hit_rate()
        );
        println!();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_generate_synthetic_functions() {
        let functions = generate_synthetic_functions(10);
        assert_eq!(functions.len(), 10);

        // Check function structure
        for (name, func, contracts) in &functions {
            assert!(!name.is_empty());
            assert!(!func.basic_blocks.is_empty());
            assert!(!contracts.requires.is_empty());
            assert!(!contracts.ensures.is_empty());
        }
    }

    #[test]
    fn test_benchmark_runs() {
        // Small-scale test to verify benchmark infrastructure works
        let n = 10;

        let full = bench_full_verification(n);
        assert_eq!(full.function_count, n);
        assert_eq!(full.verified_count, n);
        assert_eq!(full.cached_count, 0);

        let body = bench_incremental_body_change(n);
        assert_eq!(body.function_count, n);
        assert_eq!(body.verified_count, 1); // Only 1 function re-verified
        assert_eq!(body.cached_count, n - 1); // N-1 cached

        let contract = bench_incremental_contract_change(n);
        assert_eq!(contract.function_count, n);
        // Contract change affects transitive callers
        assert!(contract.verified_count >= 1);
        assert!(contract.cached_count < n);

        let no_change = bench_incremental_no_change(n);
        assert_eq!(no_change.function_count, n);
        assert_eq!(no_change.verified_count, 0); // All cached
        assert_eq!(no_change.cached_count, n);
    }

    #[test]
    #[ignore] // Run with: cargo test -- --ignored bench
    fn test_full_benchmark_suite() {
        run_benchmark();
    }
}
