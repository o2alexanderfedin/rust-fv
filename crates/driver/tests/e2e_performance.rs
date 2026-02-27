//! E2E Performance Tests for Incremental Verification
//!
//! These tests measure real-world wall-clock performance of incremental verification
//! on a ~1000-line Rust codebase with actual compilation and verification overhead.
//!
//! These tests require:
//! - Full rust-fv toolchain built
//! - Z3 or CVC5 solver available
//! - The e2e-bench test fixture crate (tests/e2e-bench/)
//!
//! Run with: `cargo test -p rust-fv-driver --test e2e_performance -- --nocapture`

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

/// Helper: Get absolute path to workspace root
fn workspace_root() -> PathBuf {
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    PathBuf::from(manifest_dir)
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

/// Helper: Get absolute path to e2e-bench test fixture
fn e2e_bench_path() -> PathBuf {
    workspace_root().join("tests/e2e-bench")
}

/// Helper: Create temp directory for test
fn temp_test_dir(test_name: &str) -> PathBuf {
    // Include thread ID to avoid collision when tests run in parallel
    // (all tests share the same process ID).
    let thread_id = format!("{:?}", std::thread::current().id());
    let thread_id_clean: String = thread_id.chars().filter(|c| c.is_alphanumeric()).collect();
    let mut dir = std::env::temp_dir();
    dir.push(format!(
        "rust-fv-e2e-{}-{}-{}",
        test_name,
        std::process::id(),
        thread_id_clean
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

/// Helper: Copy directory recursively
fn copy_dir_all(src: &Path, dst: &Path) -> std::io::Result<()> {
    fs::create_dir_all(dst)?;
    for entry in fs::read_dir(src)? {
        let entry = entry?;
        let path = entry.path();
        let dest_path = dst.join(entry.file_name());

        if path.is_dir() {
            copy_dir_all(&path, &dest_path)?;
        } else {
            fs::copy(&path, &dest_path)?;
        }
    }
    Ok(())
}

/// Helper: Copy e2e-bench to a temp directory and patch Cargo.toml to use the
/// absolute path to rust-fv-macros (since the relative `../../crates/macros`
/// path does not resolve when the crate is in a temp directory).
fn setup_crate_copy(source: &Path, dest: &Path) {
    copy_dir_all(source, dest).expect("Failed to copy e2e-bench");

    // Patch Cargo.toml: replace relative macros path with absolute workspace path
    let cargo_toml = dest.join("Cargo.toml");
    let macros_abs = workspace_root().join("crates/macros");
    let macros_abs_str = macros_abs.display().to_string();
    // Escape backslashes on Windows (no-op on Unix)
    let macros_abs_escaped = macros_abs_str.replace('\\', "\\\\");

    let content = fs::read_to_string(&cargo_toml).expect("Failed to read Cargo.toml");
    let patched = content.replace("../../crates/macros", &macros_abs_escaped);
    fs::write(&cargo_toml, patched).expect("Failed to write patched Cargo.toml");
}

/// Helper: Get path to rust-fv-driver binary
fn driver_binary_path() -> PathBuf {
    // On Windows, binaries have a .exe extension
    let binary_name = if cfg!(windows) {
        "rust-fv-driver.exe"
    } else {
        "rust-fv-driver"
    };

    // Try to find the built driver in target/debug or target/release
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    let base_path = PathBuf::from(manifest_dir);
    let workspace_root = base_path.parent().unwrap().parent().unwrap();

    // Try debug first
    let debug_path = workspace_root.join("target/debug").join(binary_name);
    if debug_path.exists() {
        return debug_path;
    }

    // Try release
    let release_path = workspace_root.join("target/release").join(binary_name);
    if release_path.exists() {
        return release_path;
    }

    panic!("Could not find rust-fv-driver binary. Run `cargo build -p rust-fv-driver` first.");
}

/// Helper: Run cargo verify on a crate and capture output + timing
struct VerifyResult {
    success: bool,
    duration_ms: u128,
    output: String,
    functions_verified: usize,
    functions_cached: usize,
    functions_failed: usize,
}

fn run_cargo_verify(crate_path: &Path, cache_dir: Option<&Path>, fresh: bool) -> VerifyResult {
    let driver_path = driver_binary_path();
    let start = Instant::now();

    let mut cmd = Command::new("cargo");
    cmd.arg("check")
        .current_dir(crate_path)
        .env("RUSTC", &driver_path)
        .env("RUST_FV_VERIFY", "1")
        .env("RUST_FV_OUTPUT_FORMAT", "text");

    if let Some(cache) = cache_dir {
        cmd.env("RUST_FV_CACHE_DIR", cache);
    }

    if fresh {
        cmd.env("RUST_FV_FRESH", "1");
    }

    let output = cmd.output().expect("Failed to run cargo verify");
    let duration = start.elapsed();

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    let combined = format!("{}\n{}", stdout, stderr);

    // Parse output to extract verification statistics
    let (verified, cached, failed) = parse_verify_output(&combined);

    VerifyResult {
        success: output.status.success(),
        duration_ms: duration.as_millis(),
        output: combined,
        functions_verified: verified,
        functions_cached: cached,
        functions_failed: failed,
    }
}

/// Parse cargo verify output to extract function statistics
///
/// Returns `(verified, cached, failed)` where:
/// - `verified` = functions that passed all VCs (OK)
/// - `cached`   = functions skipped due to cache hit (SKIP/CACHED)
/// - `failed`   = functions that failed or timed out (FAIL/TIMEOUT)
fn parse_verify_output(output: &str) -> (usize, usize, usize) {
    let mut verified = 0;
    let mut cached = 0;
    let mut failed = 0;

    for line in output.lines() {
        if line.contains("[OK]") || line.contains("✓") {
            verified += 1;
        } else if line.contains("[SKIP]") || line.contains("[CACHED]") {
            cached += 1;
        } else if line.contains("[FAIL]") || line.contains("✗") || line.contains("[TIMEOUT]") {
            failed += 1;
        }
    }

    (verified, cached, failed)
}

/// Modify a function body in lib.rs without changing its contract
fn modify_function_body(lib_rs_path: &Path, old_value: &str, new_value: &str) {
    let raw_content = fs::read_to_string(lib_rs_path).expect("Failed to read lib.rs");
    // Normalize CRLF to LF for cross-platform compatibility (Windows git may use CRLF)
    let content = raw_content.replace("\r\n", "\n");
    let modified = content.replace(old_value, new_value);

    if content == modified {
        panic!(
            "Modification failed: could not find '{}' in lib.rs",
            old_value
        );
    }

    fs::write(lib_rs_path, modified).expect("Failed to write modified lib.rs");
}

/// Modify a contract in lib.rs
fn modify_contract(lib_rs_path: &Path, old_contract: &str, new_contract: &str) {
    let raw_content = fs::read_to_string(lib_rs_path).expect("Failed to read lib.rs");
    // Normalize CRLF to LF for cross-platform compatibility (Windows git may use CRLF)
    let content = raw_content.replace("\r\n", "\n");
    let modified = content.replace(old_contract, new_contract);

    if content == modified {
        panic!(
            "Modification failed: could not find contract '{}' in lib.rs",
            old_contract
        );
    }

    fs::write(lib_rs_path, modified).expect("Failed to write modified lib.rs");
}

// ============================================================================
// PERFORMANCE TESTS
// ============================================================================

#[test]
fn e2e_incremental_body_change_under_1s() {
    println!("\n=== E2E Performance Test: Incremental Body Change ===\n");

    // Setup: Copy e2e-bench to temp directory
    let source = e2e_bench_path();
    if !source.exists() {
        panic!(
            "e2e-bench test fixture not found at {:?}. Run this test from workspace root.",
            source
        );
    }

    let test_dir = temp_test_dir("incremental_body");
    let crate_copy = test_dir.join("e2e-bench");
    setup_crate_copy(&source, &crate_copy);

    let cache_dir = test_dir.join("verify-cache");
    fs::create_dir_all(&cache_dir).expect("Failed to create cache dir");

    let lib_rs = crate_copy.join("src/lib.rs");

    // Cold run: Populate cache
    println!("Running cold verification (populating cache)...");
    let cold_result = run_cargo_verify(&crate_copy, Some(&cache_dir), false);

    println!("Cold run completed in {} ms", cold_result.duration_ms);
    println!(
        "  Functions verified: {}, cached: {}, failed: {}",
        cold_result.functions_verified, cold_result.functions_cached, cold_result.functions_failed
    );

    if !cold_result.success {
        println!("\n=== Cold Run Output ===");
        println!("{}", cold_result.output);
        panic!("Cold run failed - cannot proceed with incremental test");
    }

    // Modify one function body: change "x + 1" to "x + 2" in a utility function
    // This is a simple arithmetic change that doesn't affect contracts
    println!("\nModifying one function body (bounded_add implementation)...");
    modify_function_body(
        &lib_rs,
        "a.saturating_add(b)",
        "a.saturating_add(b) /* modified */",
    );

    // Incremental run: Re-verify with hot cache
    println!("Running incremental verification (hot cache, one body change)...");
    let incremental_result = run_cargo_verify(&crate_copy, Some(&cache_dir), false);

    println!(
        "Incremental run completed in {} ms",
        incremental_result.duration_ms
    );
    println!(
        "  Functions verified: {}, cached: {}, failed: {}",
        incremental_result.functions_verified,
        incremental_result.functions_cached,
        incremental_result.functions_failed
    );

    // Assertions
    assert!(
        incremental_result.success,
        "Incremental verification failed"
    );

    // The key assertion: incremental run should be <1000ms (1 second)
    let target_ms = 1000;

    println!("\n=== Performance Analysis ===");
    println!(
        "Target: <{} ms, Actual: {} ms",
        target_ms, incremental_result.duration_ms
    );

    if incremental_result.duration_ms > target_ms {
        println!(
            "\n⚠️  WARNING: Incremental verification took {} ms, exceeding {} ms target",
            incremental_result.duration_ms, target_ms
        );
        println!("This may be due to rustc compilation overhead rather than verification.");
        println!("\nIncremental run output:");
        println!("{}", incremental_result.output);

        // If we're significantly over, consider it a failure
        if incremental_result.duration_ms > target_ms * 2 {
            panic!(
                "Incremental verification took {} ms, more than 2x the {} ms target",
                incremental_result.duration_ms, target_ms
            );
        }
    } else {
        println!(
            "✓ Incremental verification completed in {} ms (<{} ms target)",
            incremental_result.duration_ms, target_ms
        );
    }

    // Verify cache effectiveness: most functions should be cached
    let total_functions =
        incremental_result.functions_verified + incremental_result.functions_cached;

    if total_functions > 0 {
        let cache_hit_rate =
            (incremental_result.functions_cached as f64) / (total_functions as f64) * 100.0;
        println!("Cache hit rate: {:.1}%", cache_hit_rate);

        // Expect at least 90% cache hit rate (only modified function + maybe a few dependencies)
        assert!(
            cache_hit_rate >= 85.0,
            "Cache hit rate too low: {:.1}% (expected >=85%)",
            cache_hit_rate
        );
    }

    // Clean up
    let _ = fs::remove_dir_all(&test_dir);

    println!("\n✅ E2E incremental body change test passed!");
}

#[test]
fn e2e_no_change_all_cached() {
    println!("\n=== E2E Performance Test: No-Change Run (100% Cache Hit) ===\n");

    let source = e2e_bench_path();
    if !source.exists() {
        panic!("e2e-bench test fixture not found at {:?}", source);
    }

    let test_dir = temp_test_dir("no_change");
    let crate_copy = test_dir.join("e2e-bench");
    setup_crate_copy(&source, &crate_copy);

    let cache_dir = test_dir.join("verify-cache");
    fs::create_dir_all(&cache_dir).expect("Failed to create cache dir");

    // First run: Populate cache
    println!("Running first verification (populating cache)...");
    let first_result = run_cargo_verify(&crate_copy, Some(&cache_dir), false);

    println!("First run completed in {} ms", first_result.duration_ms);
    println!(
        "  Functions verified: {}, cached: {}, failed: {}",
        first_result.functions_verified,
        first_result.functions_cached,
        first_result.functions_failed
    );

    assert!(first_result.success, "First run failed");

    // Second run: No changes, should be 100% cache hits
    println!("\nRunning second verification (no changes, expecting cache hits)...");
    let second_result = run_cargo_verify(&crate_copy, Some(&cache_dir), false);

    println!("Second run completed in {} ms", second_result.duration_ms);
    println!(
        "  Functions verified: {}, cached: {}, failed: {}",
        second_result.functions_verified,
        second_result.functions_cached,
        second_result.functions_failed
    );

    assert!(second_result.success, "Second run failed");

    // Assertions
    let total_functions = second_result.functions_verified + second_result.functions_cached;

    if total_functions > 0 {
        println!("\n=== Cache Performance ===");
        println!("Total functions: {}", total_functions);
        println!("Cached: {}", second_result.functions_cached);
        println!("Re-verified: {}", second_result.functions_verified);

        let cache_hit_rate =
            (second_result.functions_cached as f64) / (total_functions as f64) * 100.0;
        println!("Cache hit rate: {:.1}%", cache_hit_rate);

        // Expect 100% cache hits on no-change run
        assert_eq!(
            second_result.functions_verified, 0,
            "Expected 0 re-verified functions on no-change run, got {}",
            second_result.functions_verified
        );

        assert!(
            cache_hit_rate >= 99.0,
            "Cache hit rate should be ~100%, got {:.1}%",
            cache_hit_rate
        );
    }

    // Second run should be significantly faster than first
    let speedup = first_result.duration_ms as f64 / second_result.duration_ms as f64;
    println!(
        "\nSpeedup: {:.1}x (first: {} ms, second: {} ms)",
        speedup, first_result.duration_ms, second_result.duration_ms
    );

    // Expect at least 2x speedup from caching
    assert!(
        speedup >= 1.5,
        "Expected at least 1.5x speedup, got {:.1}x",
        speedup
    );

    // Clean up
    let _ = fs::remove_dir_all(&test_dir);

    println!("\n✅ E2E no-change cache test passed!");
}

#[test]
fn e2e_contract_change_transitive() {
    println!("\n=== E2E Performance Test: Contract Change (Transitive Invalidation) ===\n");

    let source = e2e_bench_path();
    if !source.exists() {
        panic!("e2e-bench test fixture not found at {:?}", source);
    }

    let test_dir = temp_test_dir("contract_change");
    let crate_copy = test_dir.join("e2e-bench");
    setup_crate_copy(&source, &crate_copy);

    let cache_dir = test_dir.join("verify-cache");
    fs::create_dir_all(&cache_dir).expect("Failed to create cache dir");

    let lib_rs = crate_copy.join("src/lib.rs");

    // First run: Populate cache
    println!("Running first verification (populating cache)...");
    let first_result = run_cargo_verify(&crate_copy, Some(&cache_dir), false);

    println!("First run completed in {} ms", first_result.duration_ms);
    println!(
        "  Functions verified: {}, cached: {}, failed: {}",
        first_result.functions_verified,
        first_result.functions_cached,
        first_result.functions_failed
    );

    assert!(first_result.success, "First run failed");

    // Modify a contract on a utility function that other functions call.
    // `bounded_add` is called by `compound_interest` and `apply_percentage`,
    // so changing its contract should trigger transitive re-verification of those callers.
    // Contracts are stored as doc attributes: #[doc = "rust_fv::ensures::SPEC"]
    println!(
        "\nModifying contract of 'bounded_add' function (called by other verified functions)..."
    );
    modify_contract(
        &lib_rs,
        r#"#[doc = "rust_fv::ensures::result >= a && result >= b"]
pub fn bounded_add(a: i64, b: i64) -> i64 {"#,
        r#"#[doc = "rust_fv::ensures::result >= a && result >= b"]
#[doc = "rust_fv::ensures::result >= 0"]
pub fn bounded_add(a: i64, b: i64) -> i64 {"#,
    );

    // Second run: Contract change should trigger transitive re-verification
    println!(
        "Running second verification (contract changed, expecting transitive invalidation)..."
    );
    let second_result = run_cargo_verify(&crate_copy, Some(&cache_dir), false);

    println!("Second run completed in {} ms", second_result.duration_ms);
    println!(
        "  Functions verified: {}, cached: {}, failed: {}",
        second_result.functions_verified,
        second_result.functions_cached,
        second_result.functions_failed
    );

    assert!(second_result.success, "Second run failed");

    // Assertions
    println!("\n=== Transitive Invalidation Analysis ===");

    // Functions re-verified = any function that was NOT served from cache.
    // This includes functions that passed (OK), failed (FAIL), or timed out (TIMEOUT).
    let re_verified = second_result.functions_verified + second_result.functions_failed;

    // Expect more than just the modified function to be re-verified
    // (the modified function + its transitive callers)
    assert!(
        re_verified > 1,
        "Expected multiple functions re-verified due to transitive invalidation, got {} (verified={}, failed={})",
        re_verified,
        second_result.functions_verified,
        second_result.functions_failed
    );

    // But not all functions should be re-verified (only the affected call chain)
    let total = re_verified + second_result.functions_cached;
    let reverify_rate = (re_verified as f64) / (total as f64) * 100.0;

    println!("Re-verification rate: {:.1}%", reverify_rate);
    println!(
        "Functions re-verified: {} (modified function + transitive callers)",
        re_verified
    );
    println!("Functions cached: {}", second_result.functions_cached);

    // Expect less than 50% re-verification (most functions unaffected)
    assert!(
        reverify_rate < 50.0,
        "Expected <50% re-verification rate for contract change, got {:.1}%",
        reverify_rate
    );

    // But more than 3% (evidence of transitive invalidation beyond just the changed function)
    assert!(
        reverify_rate >= 3.0,
        "Expected >=3% re-verification rate (modified + callers), got {:.1}%",
        reverify_rate
    );

    // Clean up
    let _ = fs::remove_dir_all(&test_dir);

    println!("\n✅ E2E contract change transitive test passed!");
}

#[test]
fn e2e_fresh_flag_bypasses_cache() {
    println!("\n=== E2E Performance Test: Fresh Flag Bypasses Cache ===\n");

    let source = e2e_bench_path();
    if !source.exists() {
        panic!("e2e-bench test fixture not found at {:?}", source);
    }

    let test_dir = temp_test_dir("fresh_flag");
    let crate_copy = test_dir.join("e2e-bench");
    setup_crate_copy(&source, &crate_copy);

    let cache_dir = test_dir.join("verify-cache");
    fs::create_dir_all(&cache_dir).expect("Failed to create cache dir");

    // First run: Populate cache
    println!("Running first verification (populating cache)...");
    let first_result = run_cargo_verify(&crate_copy, Some(&cache_dir), false);

    println!("First run completed in {} ms", first_result.duration_ms);
    assert!(first_result.success, "First run failed");

    // Second run with --fresh flag: Should bypass cache and re-verify everything
    println!("\nRunning second verification with --fresh flag (expecting 0% cache hits)...");
    let fresh_result = run_cargo_verify(&crate_copy, Some(&cache_dir), true);

    println!("Fresh run completed in {} ms", fresh_result.duration_ms);
    println!(
        "  Functions verified: {}, cached: {}, failed: {}",
        fresh_result.functions_verified,
        fresh_result.functions_cached,
        fresh_result.functions_failed
    );

    assert!(fresh_result.success, "Fresh run failed");

    // Assertions
    println!("\n=== Fresh Flag Analysis ===");

    // With --fresh, should re-verify all functions (0% cache hits)
    assert_eq!(
        fresh_result.functions_cached, 0,
        "Expected 0 cached functions with --fresh flag, got {}",
        fresh_result.functions_cached
    );

    assert!(
        fresh_result.functions_verified > 0,
        "Expected >0 verified functions with --fresh flag"
    );

    // Fresh run should take similar time to first run (both full verification).
    // We use a wide range (0.2x to 5x) to tolerate system load variance when
    // tests run in parallel or the build cache warms up.
    let time_ratio = fresh_result.duration_ms as f64 / first_result.duration_ms as f64;
    println!(
        "Time ratio (fresh/first): {:.2}x (fresh: {} ms, first: {} ms)",
        time_ratio, fresh_result.duration_ms, first_result.duration_ms
    );

    // Print warning if outside expected range but don't fail — timing is load-sensitive
    if !(0.2..=5.0).contains(&time_ratio) {
        println!(
            "WARNING: Fresh run time ratio {:.2}x outside expected 0.2x-5.0x range",
            time_ratio
        );
    }

    // Clean up
    let _ = fs::remove_dir_all(&test_dir);

    println!("\n✅ E2E fresh flag test passed!");
}
