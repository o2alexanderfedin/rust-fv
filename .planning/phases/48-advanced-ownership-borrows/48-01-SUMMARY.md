---
phase: 48-advanced-ownership-borrows
plan: 01
subsystem: analysis
tags: [trigger-inference, datatype-symbol, borrow-phase, refcell, vcgen, diagnostics]

# Dependency graph
requires:
  - phase: 46-smt-datatype-foundations
    provides: SMT datatype encoding (selectors, constructors, testers)
provides:
  - is_datatype_symbol filter preventing unsound quantifier instantiation from datatype symbols
  - BorrowPhase enum (Active/Reserved/Activated) for two-phase borrow modeling
  - RefCellGhostState struct for interior mutability VC generation
  - VcKind::BorrowConflict (V090) and VcKind::UseAfterPartialMove (V091)
  - Synthetic __trigger_wrap fallback when all trigger candidates are datatype symbols
affects: [48-02, 48-03, 48-04]

# Tech tracking
tech-stack:
  added: []
  patterns: [datatype-symbol-structural-recognition, synthetic-trigger-wrapper, two-phase-borrow-enum]

key-files:
  created:
    - crates/analysis/tests/trigger_filter_tests.rs
  modified:
    - crates/analysis/src/encode_quantifier.rs
    - crates/analysis/src/ir.rs
    - crates/analysis/src/vcgen.rs
    - crates/driver/src/callbacks.rs
    - crates/driver/src/diagnostics.rs

key-decisions:
  - "Structural recognition for datatype symbols (mk-/is-/UpperCase-field patterns) instead of manual blocklist"
  - "Synthetic __trigger_wrap only generated when datatype apps were filtered, not when no candidates exist"
  - "BorrowPhase defaults to Active for all existing BorrowInfo constructions"

patterns-established:
  - "Datatype symbol filtering: is_datatype_symbol() check before trigger candidate acceptance"
  - "Synthetic trigger fallback: __trigger_wrap wraps body when all candidates filtered"

requirements-completed: [COMPL-08]

# Metrics
duration: 2406s
completed: 2026-03-06
---

# Phase 48 Plan 01: Trigger Filter & IR Type Foundations Summary

**Datatype symbol filter (COMPL-08) preventing unsound quantifier instantiation, plus BorrowPhase/RefCellGhostState/BorrowConflict/UseAfterPartialMove IR foundations for plans 02-03**

## Performance

- **Duration:** 2406s (~40 min)
- **Started:** 2026-03-06T00:25:25Z
- **Completed:** 2026-03-06T01:05:31Z
- **Tasks:** 2
- **Files modified:** 70

## Accomplishments
- Trigger inference now filters SMT datatype selectors (`Point-x`), constructors (`mk-Point`), and testers (`is-Some`) from candidate lists, preventing unsound quantifier instantiation loops
- Synthetic `__trigger_wrap` fallback ensures quantifiers are never left without triggers when all candidates are datatype symbols
- BorrowPhase enum establishes the two-phase borrow lifecycle contract for plan 02
- RefCellGhostState struct provides the interior mutability tracking contract for plan 03
- VcKind::BorrowConflict (V090) and UseAfterPartialMove (V091) wired through diagnostics pipeline

## Task Commits

Each task was committed atomically:

1. **Task 1: Datatype symbol filter in trigger inference (COMPL-08)** - `4127baf` (feat, TDD)
2. **Task 2: IR type foundations for ownership VCs** - `97330ce` (feat)

## Files Created/Modified
- `crates/analysis/src/encode_quantifier.rs` - is_datatype_symbol filter, has_filtered_datatype_apps, synthetic wrapper logic
- `crates/analysis/tests/trigger_filter_tests.rs` - 7 tests for datatype symbol filtering
- `crates/analysis/src/ir.rs` - BorrowPhase enum, RefCellGhostState struct, phase field on BorrowInfo, refcell_ghost_states on Function
- `crates/analysis/src/vcgen.rs` - BorrowConflict and UseAfterPartialMove VcKind variants
- `crates/driver/src/callbacks.rs` - vc_kind_to_string mappings
- `crates/driver/src/diagnostics.rs` - V090/V091 descriptions and suggest_fix entries
- 64 additional files updated with `phase: BorrowPhase::Active` and `refcell_ghost_states: vec![]`

## Decisions Made
- Used structural recognition (prefix/pattern matching) for datatype symbols rather than maintaining a manual blocklist -- scales automatically with new datatypes
- Refined synthetic trigger to only fire when datatype apps were filtered (not when no candidates exist at all) -- preserves existing behavior for non-datatype-symbol cases
- BorrowPhase defaults to Active for all existing BorrowInfo constructions -- preserves existing semantics while enabling two-phase borrow support in plan 02

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Refined synthetic trigger condition to avoid breaking existing tests**
- **Found during:** Task 2 (verification step)
- **Issue:** Original `has_app_nodes` condition in synthetic trigger generation was too broad, triggering on zero-arg apps and bodies with user functions that don't cover all bound vars
- **Fix:** Replaced with `has_filtered_datatype_apps` that only returns true when the body contains non-empty-arg datatype symbol apps
- **Files modified:** crates/analysis/src/encode_quantifier.rs
- **Verification:** All 1273+ existing tests pass, plus 7 new trigger filter tests
- **Committed in:** 97330ce (Task 2 commit)

**2. [Rule 3 - Blocking] Fixed misplaced refcell_ghost_states in CoroutineInfo structs**
- **Found during:** Task 2 (compilation check)
- **Issue:** Automated script inserted `refcell_ghost_states: vec![]` inside `CoroutineInfo` struct literals that contained the string "coroutine_info:" in their parent `Some(CoroutineInfo { ... })` pattern
- **Fix:** Moved the field to the correct position after the `coroutine_info:` field closing in the parent `Function` struct
- **Files modified:** crates/analysis/src/async_vcgen.rs, crates/analysis/tests/async_verification.rs, crates/driver/tests/async_cex_e2e.rs
- **Verification:** Clean compilation, all tests pass
- **Committed in:** 97330ce (Task 2 commit)

---

**Total deviations:** 2 auto-fixed (1 bug, 1 blocking)
**Impact on plan:** Both fixes necessary for correctness. No scope creep.

## Issues Encountered
None beyond the auto-fixed deviations above.

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- BorrowPhase enum ready for plan 02 (two-phase borrow VC generation)
- RefCellGhostState ready for plan 03 (RefCell interior mutability VCs)
- VcKind::BorrowConflict and UseAfterPartialMove ready for plans 02-03 to generate VCs against
- V090/V091 diagnostics fully wired and ready for use

---
*Phase: 48-advanced-ownership-borrows*
*Completed: 2026-03-06*
