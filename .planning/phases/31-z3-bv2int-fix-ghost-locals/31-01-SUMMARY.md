---
phase: 31-z3-bv2int-fix-ghost-locals
plan: "01"
subsystem: testing
tags: [tdd, vcgen, smt, bv2int, ghost-locals, red-tests]

requires:
  - phase: 30-set-discriminant-vcgen
    provides: "vcgen_completeness29.rs test file with 11 GREEN tests (VCGEN-06 closed)"
  - phase: 04
    provides: "IR Local.is_ghost field; vcgen uses_spec_int_types(); encode_assignment()"

provides:
  - "TDD RED test phase04_bv2int_logic_selection: asserts (set-logic ALL) for 'as int' in ensures with QF_BV IR types"
  - "TDD RED test phase04_ghost_local_leaks_into_vc: asserts __ghost_x absent from SMT when is_ghost=true"

affects:
  - 31-02
  - 31-03

tech-stack:
  added: []
  patterns:
    - "Tautological postcondition (ensures: [SpecExpr { raw: 'true' }]) forces VC generation when no user contracts needed"
    - "Full Function struct literal in tests (not make_func helper) when contracts or non-default fields are required"

key-files:
  created: []
  modified:
    - crates/analysis/tests/vcgen_completeness29.rs

key-decisions:
  - "Ghost test uses ensures:true to force VC generation — without contracts no VCs are emitted and ghost leak is unobservable (plan specified Contracts::default() but behavior requires VCs to be RED)"
  - "Both tests use full Function struct literals instead of make_func() helper because make_func() does not accept contracts parameter"

patterns-established:
  - "RED test pattern: construct minimal Function with just enough IR to trigger the failing path, assert the desired post-fix behavior"

requirements-completed:
  - Phase-04-bv2int
  - Phase-04-ghost

duration: 3min
completed: 2026-02-26
---

# Phase 31 Plan 01: Z3 bv2int + Ghost Locals TDD RED Scaffold Summary

**Two TDD RED tests added to vcgen_completeness29.rs: phase04_bv2int_logic_selection (set-logic ALL assertion) and phase04_ghost_local_leaks_into_vc (ghost variable exclusion assertion)**

## Performance

- **Duration:** 3 min
- **Started:** 2026-02-26T21:02:34Z
- **Completed:** 2026-02-26T21:05:54Z
- **Tasks:** 1
- **Files modified:** 1

## Accomplishments

- `phase04_bv2int_logic_selection` test: RED — I32 function with `"(result as int) > 0"` in ensures produces `(set-logic QF_BV)` instead of `(set-logic ALL)`. SMT output confirms `uses_spec_int_types()` does not scan spec expression strings.
- `phase04_ghost_local_leaks_into_vc` test: RED — function with `__ghost_x` (is_ghost=true) leaks both a `(declare-const __ghost_x ...)` and `(assert (= __ghost_x ...))` into VCs. Confirms `encode_assignment()` does not filter ghost locals.
- All 11 Phase 29/30 tests remain GREEN (no regression).
- `cargo clippy --tests` passes with 0 errors.

## Task Commits

1. **TDD RED scaffold: Phase 04 bv2int + ghost locals** - `9aa6bc6` (test)

## Files Created/Modified

- `crates/analysis/tests/vcgen_completeness29.rs` - Added 165 lines: two new RED test functions with full Function struct literals and Phase 04 gap comments

## Decisions Made

- Ghost test uses `ensures: vec![SpecExpr { raw: "true".to_string() }]` to force VC generation. The plan specified `Contracts::default()` but that produces 0 VCs — the ghost leak is unobservable without at least one postcondition VC. Tautological ensures is the minimal change.
- Both tests use full Function struct literals (not `make_func()` helper) because the helper uses `Contracts::default()` and does not accept a contracts parameter.

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 2 - Missing Critical] Ghost test requires tautological ensures for observability**
- **Found during:** Task 1 (writing ghost test)
- **Issue:** Plan specified `Contracts::default()` but with no contracts, `generate_vcs()` returns 0 VCs and `all_smt` is empty — the assertion `!all_smt.contains("__ghost_x")` passes trivially (GREEN not RED)
- **Fix:** Added `ensures: vec![SpecExpr { raw: "true".to_string() }]` to force VC generation; added assertion `!vcs.conditions.is_empty()` to guard the observable leak
- **Files modified:** crates/analysis/tests/vcgen_completeness29.rs
- **Verification:** Test now FAILs with clear message showing `__ghost_x` in SMT output
- **Committed in:** 9aa6bc6

---

**Total deviations:** 1 auto-fixed (1 missing critical — observability requirement)
**Impact on plan:** Essential fix; without it the ghost test would be silently GREEN and fail to characterize the gap for plan 31-03.

## Issues Encountered

- rustfmt required struct field expansion (single-line `Local { ... }` → multi-line). Pre-commit hook caught and rejected first commit; fixed with `cargo fmt`.

## Next Phase Readiness

- `phase04_bv2int_logic_selection` is RED and ready for plan 31-02 (fix `uses_spec_int_types()` to scan spec expressions)
- `phase04_ghost_local_leaks_into_vc` is RED and ready for plan 31-03 (fix `encode_assignment()` to skip `is_ghost` locals)
- SMT output captured in test failure messages serves as implementation specification for both fixes

---
*Phase: 31-z3-bv2int-fix-ghost-locals*
*Completed: 2026-02-26*

## Self-Check: PASSED

- FOUND: crates/analysis/tests/vcgen_completeness29.rs
- FOUND: .planning/phases/31-z3-bv2int-fix-ghost-locals/31-01-SUMMARY.md
- FOUND: 9aa6bc6
