# Testing Patterns

**Analysis Date:** 2026-02-10

## Test Framework

**Runner:**
- cargo test (built-in Rust test runner)
- Config: no `Cargo.toml` test configuration (uses defaults)
- Nightly toolchain: `rust-toolchain.toml` specifies `nightly-2026-02-11` (enables nightly features if needed)

**Assertion Library:**
- Built-in `assert!`, `assert_eq!`, `assert_ne!` macros
- No external assertion library (proptest, quickcheck, etc.)

**Run Commands:**
```bash
cargo test                    # Run all tests
cargo test --lib              # Library tests only
cargo test --test "*"         # Integration tests only
cargo test -- --nocapture     # Show print output
cargo test -- --test-threads=1 # Run sequentially
```

## Test File Organization

**Location:**
- Unit tests: Co-located in `src/` files using `#[cfg(test)] mod tests { }`
- Integration tests: Separate files in `crates/*/tests/` directory
- Pattern: File tests stay close to implementation; cross-module tests in `tests/`

**Naming:**
- Test functions: `#[test]` attribute, snake_case names describing behavior
- Examples: `test_overflow_verification_unconstrained_add`, `format_sort_bool`, `raw_simple_sat`
- Test modules: `#[cfg(test)] mod tests` (inline) or directory name (integration)

**Structure:**

```
crates/solver/
├── src/
│   ├── lib.rs         (re-exports, doc examples marked `no_run`)
│   ├── error.rs       (inline #[cfg(test)] mod tests)
│   ├── solver.rs      (inline unit tests for format_* helpers)
│   ├── config.rs      (inline tests for builder pattern)
│   └── ...
└── tests/
    └── z3_integration.rs  (integration tests requiring Z3 binary)

crates/analysis/
└── tests/
    └── e2e_verification.rs (end-to-end pipeline tests)

crates/macros/
└── tests/
    └── basic.rs           (proc-macro compilation tests)
```

## Test Structure

**Suite Organization:**

From `crates/solver/tests/z3_integration.rs`:

```rust
//! Integration tests for the Z3 solver interface.
//!
//! These tests call the real Z3 binary and verify end-to-end behavior.

// === Helper ===
fn make_solver() -> Z3Solver { ... }

// ============================================================
// Raw SMT-LIB string tests (no dependency on formatter)
// ============================================================

#[test]
fn raw_simple_sat() { ... }

#[test]
fn raw_simple_unsat() { ... }

// ============================================================
// Script-based tests (using check_sat which auto-appends)
// ============================================================

#[test]
fn script_simple_sat() { ... }

// ============================================================
// Error handling
// ============================================================

#[test]
fn error_missing_binary() { ... }
```

**Patterns:**
- Module-level doc comment explaining test scope and dependencies
- Helper functions extracted at top (skip file indent for clarity)
- Tests grouped by behavior category using comment delimiters
- Each group has descriptive banner

**Setup/Teardown:**
- No explicit setup/teardown framework used
- Helpers called at test start: `let solver = make_solver();`
- Resources automatically cleaned on scope exit (Rust RAII)
- No global state or shared fixtures

**Assertion Pattern:**

```rust
#[test]
fn raw_simple_sat() {
    let solver = make_solver();
    let result = solver.check_sat_raw(...).unwrap();

    assert!(result.is_sat(), "Expected SAT, got: {result:?}");
    let model = result.model().expect("Expected model in SAT result");
    let x_val = model.get("x").expect("Model should contain x");
    let x: i64 = x_val.parse().expect("x should be a plain integer");
    assert!(x > 0 && x < 10, "x = {x}, expected 0 < x < 10");
}
```

- Multi-step assertions with context messages
- `expect()` used for assertions that must succeed
- Debug output included in assertion messages: `{result:?}`
- Early bounds checks before value extraction

## Mocking

**Framework:** No mocking framework (mockito, mock, etc.)

**Patterns:**
- Test doubles created manually via builder pattern or direct construction
- Example from `crates/analysis/tests/e2e_verification.rs`:

```rust
fn make_add_function(contracts: Contracts) -> Function {
    Function {
        name: "add".to_string(),
        params: vec![
            Local { name: "_1".to_string(), ty: Ty::Int(IntTy::I32) },
            Local { name: "_2".to_string(), ty: Ty::Int(IntTy::I32) },
        ],
        return_local: Local { name: "_0".to_string(), ty: Ty::Int(IntTy::I32) },
        locals: vec![],
        basic_blocks: vec![BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::BinaryOp(BinOp::Add, ...),
            )],
            terminator: Terminator::Return,
        }],
        contracts,
    }
}
```

- Builder construction for complex objects
- Minimal viable test instances (only required fields)

**What to Mock:**
- External processes: Z3 solver mocked by running real Z3 binary with controlled input
- File I/O: Not mocked in visible tests (few file operations in core logic)
- Time-dependent behavior: Not mocked (nondeterministic in formal verification context)

**What NOT to Mock:**
- SMT solver operations: actual Z3 invoked for correctness (integration tests)
- Data structures: built directly for clarity
- Core algorithms: no mocks; test actual implementation

## Fixtures and Factories

**Test Data:**

From `crates/analysis/tests/e2e_verification.rs`:

```rust
fn make_add_function(contracts: Contracts) -> Function {
    Function { ... }
}

fn solver_or_skip() -> Z3Solver {
    match Z3Solver::with_default_config() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Skipping test -- Z3 not available: {e}");
            panic!("Z3_NOT_AVAILABLE: {e}");
        }
    }
}

fn script_to_smtlib(script: &rust_fv_smtlib::script::Script) -> String {
    // Format script to SMT-LIB2 text for inspection
    let mut out = String::new();
    for cmd in script.commands() {
        format_command(&mut out, cmd);
        out.push('\n');
    }
    out
}
```

**Location:**
- Factories defined in same test file (inline or at module level)
- No shared fixture directory observed
- Per-test customization via factory parameters

**Common Builders:**
- `make_*` prefix for constructors: `make_solver()`, `make_add_function()`
- Builder methods for configuration: `SolverConfig::new().with_timeout()`

## Coverage

**Requirements:** Not enforced (no `tarpaulin`, codecov, or coverage config observed)

**View Coverage:**
```bash
# Not configured in this codebase; would require tarpaulin or llvm-cov
cargo tarpaulin  # if installed
```

**Observed Coverage:**
- Solver error types: fully tested (error.rs has 100% coverage in test block)
- Formatting functions: extensively tested (solver.rs has 50+ test cases for format_*)
- Integration path: tested end-to-end (z3_integration.rs, e2e_verification.rs)
- Edge cases: explicitly tested (timeout, missing binary, invalid SMT-LIB)

## Test Types

**Unit Tests:**

Location: `crates/solver/src/error.rs`, `crates/solver/src/config.rs`, `crates/solver/src/result.rs`

Scope: Single function or small module

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn display_not_found() {
        let err = SolverError::NotFound(PathBuf::from("/no/z3"));
        assert_eq!(err.to_string(), "Z3 binary not found at: /no/z3");
    }

    #[test]
    fn builder_pattern() {
        let config = SolverConfig::new(PathBuf::from("/opt/homebrew/bin/z3"))
            .with_timeout(5000);
        assert_eq!(config.timeout_ms, 5000);
    }
}
```

Approach:
- Test isolated functionality
- No external dependencies (no Z3 required)
- Fast execution (milliseconds)
- Assert exact output or state

**Integration Tests:**

Location: `crates/solver/tests/z3_integration.rs`, `crates/analysis/tests/e2e_verification.rs`

Scope: Multiple components + external services (Z3)

```rust
#[test]
fn script_simple_sat() {
    let solver = make_solver();

    let mut script = Script::new();
    script.push(SmtCmd::SetLogic("QF_LIA".to_string()));
    script.push(SmtCmd::DeclareConst("x".to_string(), Sort::Int));
    script.push(SmtCmd::Assert(Term::IntGt(...)));

    let result = solver.check_sat(&script).unwrap();
    assert!(result.is_sat());
}
```

Approach:
- Call Z3 binary for real solver behavior verification
- Build full SMT scripts and verify output
- Verify pipeline: IR → VCGen → SMT → Z3 → result
- Test real counterexamples and proofs

**E2E Tests:**

Scope: Full verification pipeline (IR → VCGen → SMT → Z3)

From `crates/analysis/tests/e2e_verification.rs`:

```rust
#[test]
fn test_overflow_verification_unconstrained_add() {
    let func = make_add_function(Contracts { ... });

    // Step 1: Generate VCs
    let vcs = vcgen::generate_vcs(&func);
    assert_eq!(vcs.function_name, "add");

    // Step 2: Verify overflow VC exists
    let overflow_vcs: Vec<_> = vcs.conditions.iter()
        .filter(|vc| vc.description.contains("overflow"))
        .collect();
    assert!(!overflow_vcs.is_empty());

    // Step 3: Inspect SMT-LIB for correctness
    for vc in &overflow_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        assert!(smtlib.contains("(set-logic QF_BV)"));
    }

    // Step 4: Run Z3
    let solver = solver_or_skip();
    for vc in &overflow_vcs {
        let result = solver.check_sat_raw(&smtlib).unwrap();
        assert!(result.is_sat());
    }
}
```

Approach:
- Verify each component output
- Inspect intermediate representations
- Run actual solver to verify correctness
- Test both provable and unprovable properties

## Common Patterns

**Async Testing:**
- Not used (no async Rust; SMT solver is synchronous subprocess)

**Error Testing:**

```rust
#[test]
fn error_missing_binary() {
    let config = SolverConfig::new(PathBuf::from("/nonexistent/path/z3"));
    let solver = Z3Solver::new(config);

    let result = solver.check_sat_raw("(check-sat)");
    assert!(result.is_err());
    match result.unwrap_err() {
        SolverError::NotFound(path) => {
            assert_eq!(path, PathBuf::from("/nonexistent/path/z3"));
        }
        other => panic!("Expected NotFound, got: {other:?}"),
    }
}
```

Approach:
- Assert error type using pattern matching
- Verify error context/parameters
- Use `panic!` with descriptive message on unexpected variant

**Conditional Test Execution:**

```rust
fn solver_or_skip() -> Z3Solver {
    match Z3Solver::with_default_config() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Skipping test -- Z3 not available: {e}");
            panic!("Z3_NOT_AVAILABLE: {e}");
        }
    }
}
```

Approach:
- Manual skip via panic with recognizable prefix
- CI can detect and count skips
- Avoids hard failure when Z3 not installed

**Timeout Testing:**

```rust
#[test]
fn timeout_with_short_limit() {
    let config = SolverConfig::new(PathBuf::from("/opt/homebrew/bin/z3"))
        .with_timeout(1); // 1ms
    let solver = Z3Solver::new(config);

    match solver.check_sat_raw(...) {
        Ok(SolverResult::Unknown(_)) => {} // Expected: timeout
        Ok(SolverResult::Unsat) => {}      // Also valid
        Err(_) => {}                       // Parse error is ok too
        other => panic!("Unexpected result with 1ms timeout: {other:?}"),
    }
}
```

Approach:
- Test with extremely short timeout
- Accept multiple valid outcomes (timeout might not trigger on fast machine)
- Verify we don't hang forever

---

*Testing analysis: 2026-02-10*
