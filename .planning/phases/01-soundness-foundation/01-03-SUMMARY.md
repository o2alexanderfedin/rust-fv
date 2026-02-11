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

None - plan executed exactly as written.

## Issues Encountered

None.

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
