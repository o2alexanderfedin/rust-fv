---
phase: 48-advanced-ownership-borrows
plan: 04
subsystem: verification
tags: [two-phase-borrow, mir-converter, borrow-checking, ownership]

requires:
  - phase: 48-02
    provides: BorrowPhase enum and BorrowInfo struct with Reserved/Activated variants
provides:
  - MIR converter TwoPhaseBorrow detection populating BorrowPhase::Reserved
  - Reserved-to-Activated transition at call site terminators
  - E2E integration test for two-phase borrow pattern
affects: [cross-crate-verification, stdlib-contracts]

tech-stack:
  added: []
  patterns: [two-phase-borrow-detection, call-site-activation]

key-files:
  created:
    - crates/driver/tests/two_phase_borrow_e2e.rs
  modified:
    - crates/driver/src/mir_converter.rs

key-decisions:
  - "Region names derived from basic block index (format!('_{}', bb_idx)) for borrow info collection"
  - "Reserved borrows activated when local appears in any Call terminator argument position"

patterns-established:
  - "MIR statement scanning: iterate body.basic_blocks for Assign/Ref patterns to extract borrow metadata"
  - "Call-site activation: scan terminators for Call args referencing Reserved borrow locals"

requirements-completed: [COMPL-13]

duration: 9min
completed: 2026-03-06
---

# Phase 48 Plan 04: Two-Phase Borrow MIR Detection Summary

**MIR converter detects TwoPhaseBorrow flag and populates BorrowPhase::Reserved, closing the COMPL-13 end-to-end pipeline**

## Performance

- **Duration:** 9 min (544s)
- **Started:** 2026-03-06T03:26:25Z
- **Completed:** 2026-03-06T03:35:29Z
- **Tasks:** 1
- **Files modified:** 2

## Accomplishments
- MIR converter now scans basic block statements for Rvalue::Ref with BorrowKind::Mut { kind: TwoPhaseBorrow } and sets BorrowPhase::Reserved
- Reserved borrows transition to Activated when their destination local appears as a Call terminator argument
- E2E integration test confirms no false-positive BorrowConflict for overlapping Reserved+Shared borrows
- Control test confirms Active borrows still produce conflicts as expected
- All 14 existing borrow-related tests remain green (5 two_phase + 6 splitting + 3 new E2E)

## Task Commits

Each task was committed atomically:

1. **Task 1: Populate BorrowInfo from MIR borrow statements with TwoPhaseBorrow detection** - `bab0b76` (feat)

## Files Created/Modified
- `crates/driver/src/mir_converter.rs` - Added borrow_info collection from MIR statements with TwoPhaseBorrow detection and call-site activation
- `crates/driver/tests/two_phase_borrow_e2e.rs` - E2E integration tests for two-phase borrow pattern (3 tests)

## Decisions Made
- Region names use basic block index (`'_0`, `'_1`, etc.) since exact MIR region info is not easily accessible from statement context
- Reserved borrows are activated by scanning all Call terminators' arguments -- any Reserved borrow whose local appears as a Move/Copy arg gets Activated

## Deviations from Plan

None - plan executed exactly as written.

## Issues Encountered
None

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- COMPL-13 gap fully closed: end-to-end two-phase borrow pipeline working
- Phase 48 complete (all 4 plans: COMPL-08, COMPL-09, COMPL-13, COMPL-14, COMPL-16)
- Ready for Phase 49 (Cross-Crate & Interop Completeness)

---
*Phase: 48-advanced-ownership-borrows*
*Completed: 2026-03-06*
