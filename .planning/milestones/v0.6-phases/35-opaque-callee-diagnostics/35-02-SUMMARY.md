---
phase: 35-opaque-callee-diagnostics
plan: 02
subsystem: formal-verification
tags: [rust, vcgen, diagnostics, vckind, opaque-callee, v060, v061, integration-tests, tdd]

# Dependency graph
requires:
  - phase: 35-01
    provides: VcKind::OpaqueCallee, VcKind::OpaqueCalleeUnsafe, generate_call_site_vcs None-arm, diagnostics.rs/callbacks.rs wiring
provides:
  - Five integration-level unit tests in vcgen.rs covering V060/V061 end-to-end: safe warning, unsafe fn error, unsafe block error, contracted no-diagnostic, and dedup
  - Regression guard preventing silent-skip from being re-introduced
  - OPAQUE-01 and OPAQUE-02 requirements demonstrably satisfied by test suite
affects:
  - 36-infer-summary (callee contract inference will reduce OpaqueCallee emission)

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "Integration test pattern: make_caller_* helpers build minimal Function with Terminator::Call to named callee"
    - "ContractDatabase::new() (empty) triggers OpaqueCallee path; insert entry triggers contracted path"
    - "Dedup assertion: two Call terminators to same callee must yield exactly one OpaqueCallee VC"

key-files:
  created: []
  modified:
    - crates/analysis/src/vcgen.rs

key-decisions:
  - "Five integration tests added with exact names specified in plan (test_opaque_callee_safe_warning, etc.) alongside existing 5 unit tests — total 10 OpaqueCallee tests"
  - "test_opaque_callee_safe_warning uses exact count assertion (== 1) and string assertions ('uncontracted_fn', 'no verification contract') to be maximally specific"
  - "test_opaque_callee_dedup_same_callee asserts exactly 1 VC (not >= 1) to lock in dedup behavior"
  - "Three helper functions added: make_caller_calling_uncontracted_fn, make_caller_with_unsafe_block_calling_uncontracted_fn, make_caller_with_two_calls_to_uncontracted_fn"

# Metrics
duration: 5min
completed: 2026-02-28
---

# Phase 35 Plan 02: Opaque Callee Integration Tests (V060/V061) Summary

**Five integration-level unit tests in vcgen.rs exercise the full generate_vcs -> generate_call_site_vcs -> OpaqueCallee/OpaqueCalleeUnsafe path end-to-end, proving V060/V061 diagnostics fire correctly with exact assertion specificity**

## Performance

- **Duration:** 5 min
- **Completed:** 2026-02-28
- **Tasks:** 2 (TDD integration tests + quality gate verification)
- **Files modified:** 1

## Accomplishments

- Added 5 integration test functions with plan-specified names:
  - `test_opaque_callee_safe_warning`: exactly 1 OpaqueCallee VC, description contains "uncontracted_fn" and "no verification contract"
  - `test_opaque_callee_unsafe_error`: OpaqueCalleeUnsafe VC for unsafe fn calling uncontracted callee
  - `test_opaque_callee_unsafe_block_error`: OpaqueCalleeUnsafe VC when call is inside unsafe block
  - `test_opaque_callee_no_diagnostic_for_contracted`: zero OpaqueCallee VCs when callee has a ContractDatabase entry
  - `test_opaque_callee_dedup_same_callee`: exactly 1 OpaqueCallee VC for two calls to same uncontracted callee (dedup)
- Added 3 helper functions: `make_caller_calling_uncontracted_fn`, `make_caller_with_unsafe_block_calling_uncontracted_fn`, `make_caller_with_two_calls_to_uncontracted_fn`
- All 10 OpaqueCallee tests (5 unit + 5 integration) pass GREEN
- Full test suite (1225 analysis + driver tests) GREEN, clippy -D warnings clean, rustfmt clean

## Task Commits

1. **Task 1 (integration tests):** `684614b` — test(35-02): add five integration tests for V060/V061 opaque callee diagnostics

## Files Created/Modified

- `crates/analysis/src/vcgen.rs` — Added 5 integration tests and 3 helper functions in `#[cfg(test)] mod tests`

## Decisions Made

- Tests use exact callee name "uncontracted_fn" as specified in plan (distinct from the 35-01 "uncontracted_callee" helpers — separate test scaffolding for integration level)
- `test_opaque_callee_safe_warning` uses `assert_eq!(opaque_vcs.len(), 1)` — maximum specificity to catch any VC duplication regression
- `test_opaque_callee_dedup_same_callee` asserts exactly `== 1` (not `>= 1`) to lock in the dedup guarantee from 35-01

## Deviations from Plan

None — plan executed exactly as written. All 5 test functions implemented with exact names, all assertions match plan specification.

## End-to-End Verification Gate Results

1. `cargo test -p rust-fv-analysis` — 1225 tests GREEN, including all 10 opaque_callee tests
2. `cargo test -p rust-fv-driver` — all tests GREEN
3. `VcKind::OpaqueCallee` present in vcgen.rs — confirmed (line 2391)
4. `VcKind::OpaqueCalleeUnsafe` present in vcgen.rs — confirmed (line 2389)
5. diagnostics.rs contains "OpaqueCallee" in warning branch and vc_kind_description — confirmed
6. callbacks.rs contains "opaque_callee" in vc_kind_to_string — confirmed (lines 1206-1207)
7. Silent-skip `tracing::debug!.*treating as opaque.*continue` pattern gone from generate_call_site_vcs — confirmed (no matches)

## Phase 35 Requirements

- **OPAQUE-01**: VcKind::OpaqueCallee (V060 warning) emitted for safe-context uncontracted callees — satisfied and regression-guarded
- **OPAQUE-02**: VcKind::OpaqueCalleeUnsafe (V061 error) emitted for unsafe-context uncontracted callees — satisfied and regression-guarded

## Self-Check: PASSED

- `crates/analysis/src/vcgen.rs` — FOUND
- Commit `684614b` — FOUND

---
*Phase: 35-opaque-callee-diagnostics*
*Completed: 2026-02-28*
