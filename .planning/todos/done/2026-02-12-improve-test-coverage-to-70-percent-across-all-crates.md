---
created: 2026-02-12T03:58:20.344Z
title: Improve test coverage to 70%+ across all crates
area: testing
files:
  - crates/driver/src/callbacks.rs
  - crates/driver/src/cargo_verify.rs
  - crates/driver/src/parallel.rs
  - crates/driver/src/cache.rs
  - crates/analysis/src/vcgen.rs
  - crates/solver/src/solver.rs
  - crates/solver/src/z3_native.rs
---

## Problem

Current code coverage measured by `cargo llvm-cov` is at 70.10% line coverage, 70.19% region coverage, and 77.86% function coverage across the workspace. While overall line coverage barely meets the 70% threshold, individual crates likely have significant gaps — especially in the driver crate (callbacks, cargo_verify, parallel, cache modules) which contains integration-heavy code that's harder to unit test. Coverage should be consistently 70%+ per-crate, not just overall.

Key metrics (as of 2026-02-12):
- Lines: 6,342 / 9,047 (70.10%)
- Regions: 10,871 / 15,489 (70.19%)
- Functions: 640 / 822 (77.86%)

## Solution

1. Run `cargo llvm-cov --workspace` with per-file breakdown to identify lowest-coverage files
2. Focus on crates/files below 70% line coverage
3. Add unit tests for untested functions (especially driver crate modules)
4. Add integration tests for error paths and edge cases
5. Target: every crate individually at 70%+ line coverage
6. Consider adding coverage gate to CI to prevent regression
