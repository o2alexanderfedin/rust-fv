---
phase: 48-advanced-ownership-borrows
plan: 03
subsystem: analysis
tags: [ownership, partial-move, borrow-splitting, field-disjointness, vcgen]

# Dependency graph
requires:
  - phase: 48-advanced-ownership-borrows (plans 01-02)
    provides: "VcKind::UseAfterPartialMove + BorrowConflict variants, Projection::Field, BorrowPhase"
provides:
  - "Per-field partial struct move tracking with UseAfterPartialMove VCs"
  - "Field-level borrow disjointness checking (borrow splitting)"
  - "Place::field_indices() helper for field path extraction"
affects: [49-cross-crate, 51-core-language-features]

# Tech tracking
tech-stack:
  added: []
  patterns: ["FieldMoveTracker for per-field move state", "extract_borrow_place for Rvalue::Ref origin lookup"]

key-files:
  created:
    - crates/analysis/tests/partial_move_tests.rs
    - crates/analysis/tests/borrow_splitting_tests.rs
  modified:
    - crates/analysis/src/vcgen.rs
    - crates/analysis/src/ir.rs
    - crates/analysis/src/borrow_conflict.rs
    - crates/analysis/tests/lifetime_verification.rs
    - crates/analysis/tests/two_phase_borrow_tests.rs

key-decisions:
  - "FieldMoveTracker uses HashMap<(String, Vec<usize>), bool> for moved_fields plus HashSet for whole-struct moves"
  - "detect_borrow_conflicts takes Option<&Function> for backward-compatible field disjointness"
  - "Field disjointness compares projection paths level-by-level; prefix paths are NOT disjoint"

patterns-established:
  - "FieldMoveTracker pattern: linear block walk with per-field move state tracking"
  - "extract_borrow_place pattern: walk statements to find Rvalue::Ref origin for a borrow local"

requirements-completed: [COMPL-14, COMPL-16]

# Metrics
duration: 2621s
completed: 2026-03-06
---

# Phase 48 Plan 03: Partial Struct Moves and Borrow Splitting Summary

**Per-field partial struct move tracking with UseAfterPartialMove VCs and disjoint field borrow splitting for conflict elimination**

## Performance

- **Duration:** 2621s (~44 min)
- **Started:** 2026-03-06T01:53:35Z
- **Completed:** 2026-03-06T02:37:16Z
- **Tasks:** 2
- **Files modified:** 7

## Accomplishments
- FieldMoveTracker tracks per-field move state at arbitrary nesting depth (s.inner.x)
- UseAfterPartialMove VCs generated for reads of moved fields; re-assignment clears moved state
- Field-level borrow disjointness checking prevents false BorrowConflict VCs on disjoint fields
- 12 new tests (6 partial move + 6 borrow splitting) all passing

## Task Commits

Each task was committed atomically:

1. **Task 1: Per-field partial struct move tracking** - `43042eb` (test) + `4731c88` (feat)
2. **Task 2: Disjoint field borrow splitting** - `150a612` (test) + `d72c467` (feat)

_Note: TDD tasks have separate test (RED) and implementation (GREEN) commits_

## Files Created/Modified
- `crates/analysis/src/vcgen.rs` - FieldMoveTracker + generate_partial_move_vcs + pipeline integration
- `crates/analysis/src/ir.rs` - Place::field_indices() helper method
- `crates/analysis/src/borrow_conflict.rs` - extract_borrow_place + are_borrows_field_disjoint + detect_borrow_conflicts updated
- `crates/analysis/tests/partial_move_tests.rs` - 6 tests for partial move tracking
- `crates/analysis/tests/borrow_splitting_tests.rs` - 6 tests for borrow splitting
- `crates/analysis/tests/lifetime_verification.rs` - Updated caller for new signature
- `crates/analysis/tests/two_phase_borrow_tests.rs` - Updated caller for new signature

## Decisions Made
- FieldMoveTracker uses HashMap<(String, Vec<usize>), bool> for field paths plus HashSet<String> for whole-struct moves
- detect_borrow_conflicts takes Option<&Function> to preserve backward compatibility with existing callers (None disables field disjointness)
- Field disjointness compares projection paths level-by-level; prefix paths (s.inner vs s.inner.x) are NOT disjoint
- Whole-struct borrows (no field projections) always conflict with any field borrow

## Deviations from Plan

None - plan executed exactly as written.

## Issues Encountered
None

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- Partial move tracking and borrow splitting complete
- Ready for Phase 48 Plan 04 (next in phase)
- All 1273+ analysis tests passing with 0 failures

---
*Phase: 48-advanced-ownership-borrows*
*Completed: 2026-03-06*
