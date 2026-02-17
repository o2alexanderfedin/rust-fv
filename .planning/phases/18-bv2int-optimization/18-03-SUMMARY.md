---
phase: 18-bv2int-optimization
plan: 03
subsystem: driver
tags: [bv2int, cli, pipeline, output, diagnostics, differential-testing, reporting]

# Dependency graph
requires:
  - phase: 18-01
    provides: EncodingMode enum, is_bv2int_eligible, bv2int eligibility analysis
  - phase: 18-02
    provides: test_encoding_equivalence, SolverInterface trait, EquivalenceResult, generate_vcs_with_mode
  - phase: 14-incremental-verification
    provides: VcCache for incremental verification infrastructure
provides:
  - parse_bv2int_flag: --bv2int CLI flag + RUST_FV_BV2INT env var activation (CLI precedence)
  - parse_bv2int_report_flag: --bv2int-report flag for summary table mode
  - parse_bv2int_threshold: --bv2int-threshold + RUST_FV_BV2INT_THRESHOLD env var (default 2.0)
  - Z3SolverAdapter: implements SolverInterface for real solver calls in callbacks
  - run_differential_test: wires generate_vcs_with_mode + test_encoding_equivalence for eligible functions
  - Bv2intFunctionReport struct: structured per-function report entry with from_record() constructor
  - format_bv2int_timing: formats "bitvector: Xms, bv2int: Yms (Z.Zx faster/slower)"
  - check_slowdown_warning: slowdown detection with configurable threshold (default 2x)
  - report_bv2int_divergence: error diagnostic for encoding divergence (V002)
  - report_bv2int_ineligibility: warning diagnostic for ineligible functions (V003)
  - ENV_MUTEX: serializes env var tests to fix race conditions in parallel test execution
affects: [cargo-verify binary, rustc driver callbacks, output formatting, diagnostics]

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "Z3SolverAdapter wraps CliSolver to implement SolverInterface -- enables differential testing without binary coupling in unit tests"
    - "ENV_MUTEX static in tests module serializes env var manipulation across parallel test threads"
    - "run_differential_test gracefully degrades when Z3 unavailable (returns None timing)"
    - "Bv2intFunctionReport::from_record converts records to structured report entries for display"
    - "print_bv2int_report uses Bv2intFunctionReport internally for structured access and encoding_used field"

key-files:
  created: []
  modified:
    - crates/driver/src/cargo_verify.rs
    - crates/driver/src/callbacks.rs
    - crates/driver/src/output.rs
    - crates/driver/src/diagnostics.rs

key-decisions:
  - "Z3SolverAdapter defined in callbacks.rs (not solver crate) -- keeps differential testing wiring local to where it's used"
  - "run_differential_test returns (None, None, None) when Z3 unavailable -- graceful degradation, no hard failure"
  - "ENV_MUTEX serializes bv2int env var tests -- fixes pre-existing flaky race between RUST_FV_BV2INT tests"
  - "print_bv2int_report converts to Bv2intFunctionReport via from_record -- makes struct used in production code, not just tests"
  - "callbacks.rs uses output::format_bv2int_timing and check_slowdown_warning -- DRY, consistent formatting"

patterns-established:
  - "Pattern: ENV_MUTEX for env var tests -- use static Mutex<()> to serialize tests that manipulate process-global env vars"
  - "Pattern: Z3SolverAdapter implementing trait -- connects solver crate to analysis crate's SolverInterface without circular deps"
  - "Pattern: graceful solver degradation -- try_new() returns None when solver unavailable, feature degrades cleanly"

requirements-completed: [PERF-05, PERF-06]

# Metrics
duration: 18min
completed: 2026-02-17
---

# Phase 18 Plan 03: CLI Integration and bv2int Pipeline Summary

**Full bv2int pipeline wired into cargo verify with --bv2int/--bv2int-report/--bv2int-threshold flags, per-function eligibility warnings via structured diagnostics, Z3-based differential testing, timing display, report table, and slowdown threshold warnings**

## Performance

- **Duration:** 18 min
- **Started:** 2026-02-17T19:02:54Z
- **Completed:** 2026-02-17T19:20:37Z
- **Tasks:** 2
- **Files modified:** 4

## Accomplishments

### Task 1: CLI/env activation and pipeline integration

- `parse_bv2int_flag`: `--bv2int` flag + `RUST_FV_BV2INT=1` env var; CLI takes precedence
- `parse_bv2int_report_flag`: `--bv2int-report` flag for candidate listing / summary mode
- `parse_bv2int_threshold`: `--bv2int-threshold=N` + `RUST_FV_BV2INT_THRESHOLD` env var; default 2.0
- Help text fully updated with all three flags and their env var counterparts
- `VerificationCallbacks`: per-function eligibility checked; ineligible functions use `diagnostics::report_bv2int_ineligibility`
- `Z3SolverAdapter` struct implements `SolverInterface` using `CliSolver::check_sat_raw`
- `run_differential_test`: calls `generate_vcs_with_mode` for both BV and Integer modes, calls `test_encoding_equivalence`, emits `report_bv2int_divergence` on divergence
- Candidate list emitted when `--bv2int-report` used without `--bv2int`
- `ENV_MUTEX` added to serialize `RUST_FV_BV2INT` and `RUST_FV_BV2INT_THRESHOLD` env var tests (fixed flaky test race)

### Task 2: Output formatting, report mode, slowdown warnings, and tests

- `Bv2intFunctionReport` struct with `from_record()` constructor for structured report access
- `format_bv2int_timing(func, bv_ms, int_ms)`: formats "bitvector: Xms, bv2int: Yms (Z.Zx faster/slower)"
- `check_slowdown_warning(func, speedup, threshold)`: returns `Option<String>` warning when threshold exceeded
- `print_bv2int_report` refactored to use `Bv2intFunctionReport` internally
- `callbacks.rs` uses `output::format_bv2int_timing` and `output::check_slowdown_warning` (DRY)
- 20 new integration tests in `output.rs`: timing format, slowdown warning variants, report struct, smoke tests
- 4 new diagnostic tests in `diagnostics.rs`: divergence and ineligibility report smoke tests

## Task Commits

1. **Task 1: CLI/env activation and pipeline integration** - `a3c4b83` (feat)
2. **Task 2: Output formatting, report mode, slowdown warnings, diagnostics tests** - `7ffbf65` (feat)

## Files Created/Modified

- `crates/driver/src/cargo_verify.rs` - parse_bv2int_flag, parse_bv2int_report_flag, parse_bv2int_threshold, help text, ENV_MUTEX for tests
- `crates/driver/src/callbacks.rs` - Z3SolverAdapter, run_differential_test, bv2int eligibility wiring, DRY timing via output module
- `crates/driver/src/output.rs` - Bv2intFunctionReport, format_bv2int_timing, check_slowdown_warning, print_bv2int_report refactor, 20 tests
- `crates/driver/src/diagnostics.rs` - 4 bv2int diagnostic smoke tests

## Decisions Made

- `Z3SolverAdapter` in `callbacks.rs` (not solver crate) -- keeps differential testing wiring local to where it's used
- `run_differential_test` returns `(None, None, None)` when Z3 unavailable -- graceful degradation, no hard failure on missing solver
- `ENV_MUTEX` serializes bv2int env var tests -- fixed pre-existing flaky race between parallel tests
- `print_bv2int_report` converts to `Bv2intFunctionReport` via `from_record` -- makes struct used in production code, not just tests
- `callbacks.rs` uses `output::format_bv2int_timing` and `check_slowdown_warning` -- DRY, consistent formatting with test coverage

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Fixed 8 clippy errors in pre-existing code**
- **Found during:** Task 1 (initial clippy check)
- **Issues:** `if` statements that can be collapsed (cargo_verify.rs: 3, callbacks.rs: 1), literal with empty format string (output.rs), identical if-else blocks (output.rs), unused `report_bv2int_divergence` and `report_bv2int_ineligibility` functions (diagnostics.rs)
- **Fix:** Collapsed nested `if` chains to use `&&` let chains; fixed format string; simplified encoding selection; wired `report_bv2int_ineligibility` call from callbacks; implemented `Z3SolverAdapter` + `run_differential_test` to use `report_bv2int_divergence`
- **Files modified:** `cargo_verify.rs`, `callbacks.rs`, `output.rs`, `diagnostics.rs`
- **Commit:** `a3c4b83`

**2. [Rule 1 - Bug] Fixed flaky env var test race condition**
- **Found during:** Task 1 (test run)
- **Issue:** `test_parse_bv2int_threshold_invalid_falls_back_to_default` intermittently failed because parallel tests racing on `RUST_FV_BV2INT_THRESHOLD` env var
- **Fix:** Added `static ENV_MUTEX: std::sync::Mutex<()>` and added `let _lock = ENV_MUTEX.lock()` to all bv2int flag and threshold tests
- **Files modified:** `crates/driver/src/cargo_verify.rs`
- **Commit:** `a3c4b83`

---

**Total deviations:** 2 auto-fixed (Rule 1 - bugs and pre-existing issues)
**Impact on plan:** Auto-fixes were required for clippy compliance and test reliability. The wiring of `Z3SolverAdapter` and `run_differential_test` extended the original plan scope but was necessary to make `report_bv2int_divergence` non-dead-code.

## Issues Encountered

- Pre-existing doc test failures in `crates/analysis/src/stdlib_contracts/option.rs` (26 failures with `self` parameter in doc examples). These are out of scope for 18-03 and were deferred.
- The `Z3SolverAdapter` integration required more work than anticipated since differential testing wasn't previously wired into callbacks. The wiring completes the full pipeline as the plan intended.

## Next Phase Readiness

- Phase 18 is now complete: all 3 plans executed (18-01: encoding, 18-02: differential testing, 18-03: CLI integration)
- `cargo verify --bv2int` activates bv2int mode for eligible functions with per-function warnings
- `RUST_FV_BV2INT=1 cargo verify` works as env var alternative
- `cargo verify --bv2int-report` shows summary table (with --bv2int) or candidate list (without)
- Slowdown threshold configurable via `--bv2int-threshold=N` or `RUST_FV_BV2INT_THRESHOLD=N`

---
*Phase: 18-bv2int-optimization*
*Completed: 2026-02-17*
