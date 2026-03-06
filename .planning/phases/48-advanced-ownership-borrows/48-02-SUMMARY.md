---
phase: 48-advanced-ownership-borrows
plan: 02
subsystem: analysis
tags: [refcell, interior-mutability, two-phase-borrow, ghost-state, vcgen, borrow-conflict]

# Dependency graph
requires:
  - phase: 48-advanced-ownership-borrows (plan 01)
    provides: BorrowPhase enum, RefCellGhostState struct, VcKind::BorrowConflict, refcell_ghost_states field
provides:
  - generate_refcell_vcs() function for RefCell ghost state VC generation
  - Two-phase borrow skip logic in detect_borrow_conflicts
  - Function::has_refcell_locals() helper
affects: [48-advanced-ownership-borrows, stdlib-contracts, cross-crate]

# Tech tracking
tech-stack:
  added: []
  patterns: [ghost-state-tracking, two-phase-borrow-reservation]

key-files:
  created:
    - crates/analysis/tests/refcell_ghost_tests.rs
    - crates/analysis/tests/two_phase_borrow_tests.rs
  modified:
    - crates/analysis/src/vcgen.rs
    - crates/analysis/src/ir.rs
    - crates/analysis/src/borrow_conflict.rs

key-decisions:
  - "Linear block walk for RefCell ghost state tracking (sufficient for straight-line code; branch join analysis is future work)"
  - "Reserved borrows skip conflict check entirely via early continue in detect_borrow_conflicts"

patterns-established:
  - "Ghost state tracking: walk basic blocks linearly, track state per RefCellGhostState, generate BorrowConflict VCs on precondition violation"
  - "Two-phase borrow: Reserved phase skips shared-mutable conflict; Active/Activated conflict normally"

requirements-completed: [COMPL-09, COMPL-13]

# Metrics
duration: 1566s
completed: 2026-03-06
---

# Phase 48 Plan 02: RefCell Ghost State VCs and Two-Phase Borrow Modeling Summary

**RefCell borrow/borrow_mut ghost state tracking with BorrowConflict VCs for 7 API methods, plus two-phase borrow reservation skip in conflict detection**

## Performance

- **Duration:** 1566s (~26 min)
- **Started:** 2026-03-06T01:17:59Z
- **Completed:** 2026-03-06T01:43:55Z
- **Tasks:** 2
- **Files modified:** 5

## Accomplishments
- RefCell ghost state VCs generated for borrow, borrow_mut, try_borrow, try_borrow_mut, into_inner, replace, swap
- Ghost state (borrow_count, is_mut_borrowed) tracked across basic blocks with drop handling
- Two-phase borrows with Reserved phase skip shared borrow conflict detection
- 16 tests total (11 RefCell + 5 two-phase), all passing

## Task Commits

Each task was committed atomically:

1. **Task 1: RefCell ghost state VC generation (COMPL-09)** - `f263664` (feat)
2. **Task 2: Two-phase borrow modeling (COMPL-13)** - `d311eca` (feat)

## Files Created/Modified
- `crates/analysis/src/vcgen.rs` - Added generate_refcell_vcs(), extract_refcell_method(), extract_refcell_drop(); wired into generate_vcs_with_db
- `crates/analysis/src/ir.rs` - Added Function::has_refcell_locals() helper
- `crates/analysis/src/borrow_conflict.rs` - Added BorrowPhase::Reserved skip in detect_borrow_conflicts
- `crates/analysis/tests/refcell_ghost_tests.rs` - 11 unit tests for RefCell ghost state VCs
- `crates/analysis/tests/two_phase_borrow_tests.rs` - 5 unit tests for two-phase borrow conflict detection

## Decisions Made
- Linear block walk for RefCell ghost state tracking (sufficient for straight-line code; branch join analysis is future work)
- Reserved borrows skip conflict check entirely via early `continue` in detect_borrow_conflicts
- Use SMT `App("=", ...)` for equality assertions in RefCell VCs (consistent with existing VC encoding)

## Deviations from Plan

None - plan executed exactly as written.

## Issues Encountered
- Compilation errors in initial generate_refcell_vcs due to using `Term::Var` (correct: `Term::Const`) and `rust_fv_smtlib::term::Sort` (correct: `rust_fv_smtlib::sort::Sort`). Fixed by inspecting the actual smtlib crate types.

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- RefCell ghost state and two-phase borrow foundations ready
- Plan 03-05 can build on these for partial move tracking, reborrow tracking, and integration
- MIR converter detection of TwoPhaseBorrow flag not yet implemented (would require rustc MIR integration, deferred to when MIR converter is extended)

---
*Phase: 48-advanced-ownership-borrows*
*Completed: 2026-03-06*
