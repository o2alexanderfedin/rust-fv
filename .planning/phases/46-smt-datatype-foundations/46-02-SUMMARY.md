---
phase: 46-smt-datatype-foundations
plan: 02
subsystem: verification
tags: [smt, datatype, struct, enum, functional-update, z3, vcgen]

# Dependency graph
requires:
  - phase: 46-smt-datatype-foundations plan 01
    provides: Int sort encoding and Repeat rvalue support
provides:
  - Struct/enum types verified as first-class SMT datatypes (no Uninterpreted fallback)
  - Nested field projection functional update (s.inner.field = val)
  - Downcast+Field projection for enum variant field updates
  - All rvalue types supported on projected LHS places
  - Discriminant encoding soundness documented
affects: [phase-47-mir-coverage, phase-48-ownership, phase-54-stdlib-contracts]

# Tech tracking
tech-stack:
  added: []
  patterns: [nested-functional-update, downcast-projection, datatype-sort-enforcement]

key-files:
  created: []
  modified:
    - crates/analysis/src/encode_sort.rs
    - crates/analysis/src/vcgen.rs
    - crates/analysis/tests/e2e_verification.rs

key-decisions:
  - "Discriminant encoding kept as uninterpreted function (not native testers) - sound because SwitchInt correctly constrains paths; native testers deferred as optimization"
  - "Nested spec parsing (result.inner.a) out of scope for COMPL-05 - E2E tests verify structural correctness via SMT output inspection"

patterns-established:
  - "Struct/enum types always encode as Sort::Datatype, never Sort::Uninterpreted"
  - "Nested field projections handled via build_nested_functional_update with chained mk- constructors"

requirements-completed: [COMPL-01, COMPL-05]

# Metrics
duration: 1775s
completed: 2026-03-05
---

# Phase 46 Plan 02: SMT Datatype Wiring & Functional Update Hardening Summary

**Struct/enum types verified as first-class SMT datatypes with native constructors/selectors; functional update hardened for nested projections, Downcast, and all rvalue types**

## Performance

- **Duration:** 29 min
- **Started:** 2026-03-05T08:06:58Z
- **Completed:** 2026-03-05T08:36:33Z
- **Tasks:** 2
- **Files modified:** 3

## Accomplishments
- Verified struct/enum types produce Sort::Datatype (not Sort::Uninterpreted) with comprehensive tests
- Added unit tests for nested field projection, Downcast+Field, and projected BinaryOp functional updates
- Added E2E tests confirming nested struct updates produce correct mk-Inner/mk-Outer constructors
- Added E2E test for functional update with BinaryOp on projected place (s.x = s.x + 1)
- Updated outdated doc comments in encode_sort.rs reflecting current datatype implementation
- Fixed clippy collapsible_if warning in encode_assignment

## Task Commits

Each task was committed atomically:

1. **Task 1+2: Datatype wiring + Functional update hardening** - `50d267e` (feat)
   Combined commit since both tasks modify the same files and all implementation was already in place.

**Plan metadata:** (pending)

## Files Created/Modified
- `crates/analysis/src/encode_sort.rs` - Updated doc comments; added 4 tests verifying no Uninterpreted fallback for struct/enum
- `crates/analysis/src/vcgen.rs` - Fixed clippy warning; added 3 unit tests for nested/Downcast/projected-binop functional updates; added test helper functions
- `crates/analysis/tests/e2e_verification.rs` - Added e2e_nested_struct_update and e2e_functional_update_binop tests

## Decisions Made
- Discriminant encoding kept as uninterpreted function rather than native Z3 testers. The current approach is sound because SwitchInt correctly constrains discriminant values, Aggregate uses correct constructors, and SwitchInt generates disjoint path conditions. Native testers would require significant restructuring of the SwitchInt terminator encoding and are deferred as a future optimization.
- E2E tests for nested struct update use `result.c == 3` postcondition instead of `result.inner.a == 10` because nested field spec parsing is not yet implemented. Structural correctness verified via SMT output inspection.

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Fixed clippy collapsible_if warning**
- **Found during:** Task 1
- **Issue:** Nested `if all_field_or_downcast { if let Some(base_ty) = ... }` flagged by clippy
- **Fix:** Collapsed into single `if all_field_or_downcast && let Some(base_ty) = ...`
- **Files modified:** crates/analysis/src/vcgen.rs
- **Verification:** `cargo clippy` passes with no warnings
- **Committed in:** 50d267e

---

**Total deviations:** 1 auto-fixed (1 bug)
**Impact on plan:** Minor code cleanup. No scope creep.

## Issues Encountered
- Implementation for both tasks was already in place from prior work. The TDD RED phase did not produce failing tests since build_nested_functional_update, Downcast handling, and the fallback path were already implemented. Tests serve as regression guards and documentation.
- Constant::Aggregate variant does not exist in the IR, requiring the nested struct E2E test to use a two-step approach (create Inner, then create Outer using the Inner local).

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- Phase 46 complete: all 4 requirements (COMPL-01, COMPL-05, COMPL-07, COMPL-11) implemented
- Phase 47 (MIR Coverage Hardening) can proceed independently
- Phase 54 (Stdlib Contracts) unblocked by struct/enum datatype foundations

---
*Phase: 46-smt-datatype-foundations*
*Completed: 2026-03-05*
