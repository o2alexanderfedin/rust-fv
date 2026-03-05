---
phase: 46-smt-datatype-foundations
plan: 03
subsystem: analysis
tags: [smt, datatype, enum, istester, discriminant, vcgen]

# Dependency graph
requires:
  - phase: 46-02
    provides: "SMT datatype declarations for struct/enum, Term::IsTester variant, formatter"
provides:
  - "Native IsTester-based discriminant branch conditions in SwitchInt encoding"
  - "SetDiscriminant VCs use datatype testers instead of uninterpreted functions"
  - "E2E verification that enum SMT output uses tester syntax"
affects: [47-mir-coverage-hardening, 54-stdlib-contracts-batch-i]

# Tech tracking
tech-stack:
  added: []
  patterns: ["IsTester SwitchInt encoding pattern: variant index -> mk-{name} tester", "EnumDiscriminantSource type alias for complex return"]

key-files:
  created: []
  modified:
    - crates/analysis/src/vcgen.rs
    - crates/analysis/tests/e2e_verification.rs

key-decisions:
  - "Non-enum discriminant fallback preserved: uninterpreted discriminant-{local} function kept for non-enum Rvalue::Discriminant"
  - "Enum Rvalue::Discriminant returns None: SwitchInt IsTester handles branch conditions directly"

patterns-established:
  - "IsTester encoding: SwitchInt maps variant index to mk-{variant_name} constructor tester"
  - "Graceful fallback: enum paths use IsTester, non-enum paths keep uninterpreted function"

requirements-completed: [COMPL-01]

# Metrics
duration: 27min
completed: 2026-03-05
---

# Phase 46 Plan 03: Gap Closure Summary

**Native IsTester discriminant encoding replacing uninterpreted functions for enum SwitchInt branch conditions and SetDiscriminant VCs**

## Performance

- **Duration:** 27 min
- **Started:** 2026-03-05T09:34:42Z
- **Completed:** 2026-03-05T10:01:41Z
- **Tasks:** 2
- **Files modified:** 2

## Accomplishments
- SwitchInt on enum discriminant generates `Term::IsTester("mk-{variant}", expr)` branch conditions instead of `Eq(discr, BitVecLit)`
- SetDiscriminant VCs use native datatype testers instead of uninterpreted `discriminant-{local}` functions
- E2E test `e2e_enum_datatype_match` verifies IsTester syntax `(_ is mk-` appears and `discriminant-` does not
- All 1273+ analysis unit tests pass, full workspace tests pass with zero failures

## Task Commits

Each task was committed atomically:

1. **Task 1: Add Term::IsTester variant with formatter and Z3 native support** - `6db26af` (feat)
2. **Task 2: Wire IsTester into SwitchInt discriminant encoding and update E2E tests** - `4e1816b` (feat)

## Files Created/Modified
- `crates/analysis/src/vcgen.rs` - SwitchInt uses IsTester for enum discriminants, SetDiscriminant VCs use testers, Rvalue::Discriminant returns None for enums, added find_discriminant_enum_source helper
- `crates/analysis/tests/e2e_verification.rs` - E2E test asserts IsTester syntax and absence of discriminant- functions

## Decisions Made
- Non-enum discriminant encoding preserved as uninterpreted function fallback (only enum types get IsTester)
- Rvalue::Discriminant returns None for enum types since SwitchInt handles branching via IsTester directly
- Added `EnumDiscriminantSource` type alias to address clippy type_complexity warning

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Fixed clippy warnings in new code**
- **Found during:** Task 2
- **Issue:** Unnecessary `ref` pattern on `variants` binding, and complex return type on `find_discriminant_enum_source`
- **Fix:** Removed `ref` keyword, added `EnumDiscriminantSource` type alias
- **Files modified:** crates/analysis/src/vcgen.rs
- **Verification:** `cargo clippy --all-targets` produces zero warnings (excluding pre-existing Cargo.toml notice)
- **Committed in:** 4e1816b (Task 2 commit)

---

**Total deviations:** 1 auto-fixed (1 bug)
**Impact on plan:** Minor code quality fix, no scope creep.

## Issues Encountered
None

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- Phase 46 fully complete: all 3 plans done, COMPL-01 fully satisfied with native datatype testers
- Ready for Phase 47 (MIR Coverage Hardening)
- IsTester encoding pattern available for any future enum-related verification work

---
*Phase: 46-smt-datatype-foundations*
*Completed: 2026-03-05*

## Self-Check: PASSED
