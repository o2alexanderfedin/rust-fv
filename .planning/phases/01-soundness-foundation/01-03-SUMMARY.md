---
phase: 01-soundness-foundation
plan: 03
subsystem: infra
tags: [nightly, toolchain, criterion, benchmarks, performance]

# Dependency graph
requires: []
provides:
  - "Pinned nightly toolchain (nightly-2026-02-11) in rust-toolchain.toml"
  - "TOOLCHAIN.md compatibility documentation with update procedure"
  - "Criterion benchmark suite measuring VCGen and E2E verification time"
  - "PERF-01 baseline: sub-1s verification confirmed for single-function contracts"
affects: [02-correctness-hardening, 03-developer-experience]

# Tech tracking
tech-stack:
  added: [criterion 0.5]
  patterns: [benchmark-driven performance regression detection]

key-files:
  created:
    - "TOOLCHAIN.md"
    - "crates/analysis/benches/vcgen_bench.rs"
  modified:
    - "crates/analysis/Cargo.toml"

key-decisions:
  - "Criterion 0.5 chosen for benchmarks (stable, html_reports, widely adopted)"
  - "Benchmarks are developer-only (not CI gate) to avoid flaky perf-based failures"
  - "Complex benchmark models clamp(val, lo, hi) with 5 basic blocks for realistic coverage"

patterns-established:
  - "Benchmark pattern: construct IR Function, call generate_vcs(), optionally pipe through Z3"
  - "Toolchain update procedure: documented step-by-step in TOOLCHAIN.md"

# Metrics
duration: 7min
completed: 2026-02-11
---

# Phase 1 Plan 3: Toolchain Pin and Performance Baseline Summary

**Pinned nightly-2026-02-11 toolchain with compatibility docs and criterion benchmarks confirming sub-20ms E2E verification**

## Performance

- **Duration:** 7 min
- **Started:** 2026-02-11T08:12:14Z
- **Completed:** 2026-02-11T08:18:49Z
- **Tasks:** 2
- **Files modified:** 3

## Accomplishments
- Verified rust-toolchain.toml pins nightly-2026-02-11 with all required components (rustc-dev, llvm-tools, rust-src, rustfmt, clippy)
- Created TOOLCHAIN.md documenting why nightly is needed, how to update, common breakage points, and compatibility table
- Established criterion benchmark suite with 6 benchmarks (3 pure VCGen, 3 E2E with Z3)
- Confirmed PERF-01 target: all E2E benchmarks complete in under 20ms (well under 1s target)

## Benchmark Baseline

| Benchmark | Type | Time | Target |
|-----------|------|------|--------|
| vcgen_simple_add | VCGen only | ~1.8 us | << 1ms |
| vcgen_max_function | VCGen only | ~2.4 us | << 1ms |
| vcgen_complex_function | VCGen only | ~5.9 us | < 10ms |
| e2e_simple_add | VCGen + Z3 | ~10 ms | < 500ms |
| e2e_max_function | VCGen + Z3 | ~7.5 ms | < 500ms |
| e2e_complex_function | VCGen + Z3 | ~19.6 ms | < 1s (PERF-01) |

## Task Commits

Each task was committed atomically:

1. **Task 1: Document nightly toolchain pin and compatibility** - `a5d3243` (feat)
2. **Task 2: Create performance benchmark baseline** - `a3490f3` (feat)
3. **Deviation: Fix comparison signedness + commit prior plan work** - `ea034ba` (fix)

## Files Created/Modified
- `TOOLCHAIN.md` - Nightly toolchain pin documentation, update procedure, compatibility table
- `crates/analysis/benches/vcgen_bench.rs` - Criterion benchmarks for VCGen and E2E verification
- `crates/analysis/Cargo.toml` - Added criterion dev-dependency and bench target

## Decisions Made
- Chose criterion 0.5 for benchmarks (stable, html_reports, well-known in Rust ecosystem)
- Benchmarks are developer-only, not CI gate -- avoids flaky failures from machine-dependent timing
- Complex benchmark uses clamp function with 5 basic blocks, 2 SwitchInt terminators, and postconditions for realistic coverage
- E2E benchmarks gracefully skip if Z3 is not available (no hard dependency for pure benchmark runs)

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Fixed comparison signedness in VCGen encode_assignment**
- **Found during:** Push verification (pre-push hook ran E2E tests)
- **Issue:** `BinOp::Gt/Lt/Ge/Le` for i32 operands used unsigned bitvector comparisons (bvugt) because `encode_assignment` inferred type from the Bool destination (`_3`) instead of the i32 operands (`_1`, `_2`). This caused Z3 to find false counterexamples for max/abs_or_zero functions.
- **Fix:** Added `BinOp::is_comparison()` method to ir.rs. Modified `encode_assignment` to use operand types for comparison operations, falling back to destination type only for non-comparison ops.
- **Files modified:** `crates/analysis/src/ir.rs`, `crates/analysis/src/vcgen.rs`
- **Verification:** All 10 E2E tests pass including `test_if_else_branches_ssa` and `test_early_return_via_goto`
- **Committed in:** ea034ba

**2. [Rule 3 - Blocking] Committed prior plan (01-01/01-02) uncommitted work**
- **Found during:** Push verification
- **Issue:** Plans 01-01/01-02 had modified `vcgen.rs` and `e2e_verification.rs` with path-enumeration VCGen and new E2E tests, but these changes were uncommitted in the working tree.
- **Fix:** Committed the path-enumeration VCGen and 6 new E2E tests alongside the signedness fix.
- **Files modified:** `crates/analysis/src/vcgen.rs`, `crates/analysis/tests/e2e_verification.rs`, `Cargo.lock`
- **Committed in:** ea034ba

---

**Total deviations:** 2 auto-fixed (1 bug, 1 blocking)
**Impact on plan:** Bug fix was essential for soundness. Uncommitted prior work needed to be committed to pass pre-push tests.

## Issues Encountered

Pre-push hook caught 2 failing E2E tests from prior plans' uncommitted work. Diagnosed as comparison signedness bug and fixed inline.

## User Setup Required

None - no external service configuration required.

## Next Phase Readiness
- Toolchain is pinned and documented -- future nightly updates have a clear procedure
- Performance baseline established -- regressions detectable via `cargo bench -p rust-fv-analysis`
- Phase 1 plans 01-03 are all complete (SSA fix, overflow audit, toolchain + benchmarks)

## Self-Check: PASSED

- [x] TOOLCHAIN.md exists
- [x] crates/analysis/benches/vcgen_bench.rs exists
- [x] crates/analysis/Cargo.toml exists
- [x] rust-toolchain.toml exists
- [x] Commit a5d3243 found (Task 1)
- [x] Commit a3490f3 found (Task 2)
- [x] 01-03-SUMMARY.md exists
- [x] rust-toolchain.toml contains 'nightly'
- [x] TOOLCHAIN.md contains 'nightly'
- [x] vcgen_bench.rs contains 'criterion'
- [x] vcgen_bench.rs contains 'generate_vcs'

---
*Phase: 01-soundness-foundation*
*Completed: 2026-02-11*
