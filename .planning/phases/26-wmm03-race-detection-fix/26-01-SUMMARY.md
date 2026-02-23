---
phase: 26-wmm03-race-detection-fix
plan: "01"
subsystem: concurrency
tags: [rc11, weak-memory, race-detection, z3, tdd, smt]

requires:
  - phase: 21-rc11-weak-memory
    provides: generate_rc11_vcs() function with WeakMemoryRace VC skeleton in rc11.rs

provides:
  - WeakMemoryRace VC emits preamble+mo_cmds+rf_cmds+Assert(BoolLit(true)) — SAT-returning formula
  - test_relaxed_data_race_detected calls Z3 and asserts SolverResult::Sat to close the WMM-03 soundness gap

affects: [parallel.rs SAT→verified:false→callbacks.rs error pipeline, any consumer of WeakMemoryRace VcKind]

tech-stack:
  added: []
  patterns:
    - "Violation-detection semantics for race VCs: Assert(BoolLit(true)) means constraints are satisfiable = race exists (mirrors WeakMemoryCoherence pattern with Assert(hb∧eco))"
    - "TDD RED→GREEN: write failing Z3 SAT assertion first, then fix the VC body"

key-files:
  created: []
  modified:
    - crates/analysis/src/concurrency/rc11.rs
    - crates/analysis/tests/weak_memory_litmus.rs

key-decisions:
  - "WeakMemoryRace VC uses Assert(BoolLit(true)) not a semantic violation term — the preamble+mo+rf constraints are the real content; BoolLit(true) confirms the combined constraint set is SAT (race structurally exists)"
  - "mo_cmds and rf_cmds included in WeakMemoryRace script to mirror WeakMemoryCoherence pattern and give Z3 full context"

patterns-established:
  - "Race VC SAT = race detected = driver reports error (verified:false) — symmetric to coherence UNSAT = coherence holds (verified:true)"

requirements-completed:
  - WMM-03

duration: 3min
completed: 2026-02-23
---

# Phase 26 Plan 01: WeakMemoryRace VC Fix Summary

**WeakMemoryRace VC in rc11.rs fixed from Assert(BoolLit(false)) stub to preamble+mo_cmds+rf_cmds+Assert(BoolLit(true)), closing the WMM-03 soundness gap where Relaxed data races were silently hidden**

## Performance

- **Duration:** 3 min
- **Started:** 2026-02-23T06:35:22Z
- **Completed:** 2026-02-23T06:38:22Z
- **Tasks:** 2
- **Files modified:** 2

## Accomplishments

- Fixed Step J in `generate_rc11_vcs()`: WeakMemoryRace VC now includes `mo_cmds`, `rf_cmds`, and `Assert(BoolLit(true))` instead of `Assert(BoolLit(false))`
- Updated `test_relaxed_data_race_detected` to call `solver_or_skip()` and assert `SolverResult::Sat(_)` on the WeakMemoryRace VC
- All 9 litmus tests pass (CoRR, CoRW, CoWR, CoWW, SB, LB, MP, IRIW, Race); 0 clippy errors

## Task Commits

Each task was committed atomically:

1. **Tasks 1+2: Fix rc11.rs Step J + update test to assert SAT (TDD RED→GREEN)** - `cf9a02a` (fix)

## Files Created/Modified

- `crates/analysis/src/concurrency/rc11.rs` - Step J WeakMemoryRace VC: replaced `Assert(BoolLit(false))` with `mo_cmds + rf_cmds + Assert(BoolLit(true))`
- `crates/analysis/tests/weak_memory_litmus.rs` - `test_relaxed_data_race_detected`: added `solver_or_skip()` + Z3 SAT assertion

## Decisions Made

- WeakMemoryRace VC uses `Assert(BoolLit(true))` to confirm the combined preamble+mo+rf constraint set is satisfiable, meaning a race execution exists. This mirrors the violation-detection semantics pattern from WeakMemoryCoherence (SAT = issue found).
- Including `mo_cmds` and `rf_cmds` in the WeakMemoryRace script gives Z3 the full structural context (total order + rf functional constraints), consistent with the WeakMemoryCoherence VC construction.

## Deviations from Plan

None - plan executed exactly as written.

## Issues Encountered

None. RED phase confirmed UNSAT (buggy BoolLit(false)); GREEN phase confirmed SAT after fix. Surgical one-line change to rc11.rs.

## User Setup Required

None - no external service configuration required.

## Next Phase Readiness

- WMM-03 soundness gap closed: WeakMemoryRace VCs now correctly return SAT, enabling the downstream pipeline (parallel.rs SAT → verified:false → callbacks.rs error push) to surface race errors
- No further work needed for Phase 26 Plan 01

---
*Phase: 26-wmm03-race-detection-fix*
*Completed: 2026-02-23*
