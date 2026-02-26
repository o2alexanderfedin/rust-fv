---
phase: 30-set-discriminant-vcgen
plan: "01"
subsystem: vcgen
tags: [tdd, vcgen, set-discriminant, red-tests]
dependency_graph:
  requires: []
  provides: [vcgen_06_set_discriminant_unit, vcgen_06_set_discriminant_assertion]
  affects: [crates/analysis/tests/vcgen_completeness29.rs]
tech_stack:
  added: []
  patterns: [TDD RED scaffold, assertion-based failure, script_to_text helper]
key_files:
  modified:
    - crates/analysis/tests/vcgen_completeness29.rs
decisions:
  - "vcgen_06_set_discriminant_unit uses variant index 1; vcgen_06_set_discriminant_assertion uses variant index 2 — distinct to prove index specificity in SMT output"
  - "contains('1') assertion is sound for index 1 since any SMT output from a VC for variant 1 will contain the literal '1'"
  - "No #[should_panic] — tests fail via assertion as required by plan"
metrics:
  duration: 87
  completed_date: "2026-02-26"
  tasks_completed: 1
  files_modified: 1
---

# Phase 30 Plan 01: TDD RED Scaffold for VCGEN-06 SetDiscriminant VC Emission Summary

TDD RED tests asserting VCGen emits ≥1 VC with 'discriminant' and variant index in SMT for Statement::SetDiscriminant — both tests fail because VCGen currently treats SetDiscriminant as a no-op (0 VCs).

## What Was Done

Added two RED TDD tests to `crates/analysis/tests/vcgen_completeness29.rs`:

1. **`vcgen_06_set_discriminant_unit`** (new test after `mirconv_02_set_discriminant`):
   - Builds a Function IR with `Statement::SetDiscriminant(Place::local("_1"), 1)`
   - Calls `vcgen::generate_vcs(&func, None)`
   - Asserts `!vcs.conditions.is_empty()` — FAILS (0 VCs)
   - Asserts SMT output contains `"discriminant"` — FAILS
   - Asserts SMT output contains `'1'` — FAILS

2. **`vcgen_06_set_discriminant_assertion`** (replaced existing `#[ignore]` stub):
   - Removed `#[ignore = "TODO Plan 03/05: ..."]` attribute entirely
   - Replaced `todo!("Plan 03/05: implement after Statement::SetDiscriminant exists")` with real assertions
   - Uses variant index 2 to distinguish from test 1
   - Same assertion pattern — FAILS (0 VCs)

## Test Results

| Test | Status | Failure message |
|------|--------|----------------|
| `vcgen_06_set_discriminant_unit` | RED (FAILED) | "VCGEN-06: expected VC for SetDiscriminant, got 0" |
| `vcgen_06_set_discriminant_assertion` | RED (FAILED) | "VCGEN-06: expected VC for SetDiscriminant, got 0" |
| `mirconv_02_set_discriminant` | GREEN (regression guard) | N/A |
| All other 9 tests | GREEN | N/A |

Full suite: 9 passed, 2 failed, 0 ignored — only the two new vcgen_06 tests are FAILED.

## Deviations from Plan

None - plan executed exactly as written.

## Self-Check: PASSED

- FOUND: crates/analysis/tests/vcgen_completeness29.rs
- FOUND: commit 56a5d2c
