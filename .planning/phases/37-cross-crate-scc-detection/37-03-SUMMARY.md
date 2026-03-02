---
phase: 37-cross-crate-scc-detection
plan: 03
subsystem: analysis
tags: [recursion, termination, vcgen, cross-crate, scc, integration-tests, z3]

# Dependency graph
requires:
  - phase: 37-02
    provides: generate_termination_vcs activated for cross-crate callees; vcgen.rs wired to from_functions_with_cross_crate_db
  - phase: 37-01
    provides: CallGraph::from_functions_with_cross_crate_db with virtual node injection and back-edge heuristic
provides:
  - "4 end-to-end integration tests in recursion_verification.rs covering cross-crate SCC detection"
  - "Bug fix: generate_termination_vcs now correctly matches cross-crate callees stored as full paths in RecursiveGroup"
  - "XCREC-01 and XCREC-02 demonstrated end-to-end via Z3 UNSAT/SAT verification"
affects:
  - recursion-verification
  - vcgen-termination
  - cross-crate-scc-detection

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "Cross-crate SCC integration test pattern: ContractDatabase with back-edge heuristic -> generate_vcs -> filter Termination VCs -> Z3 check"
    - "normalize_callee fallback: check group.contains(raw_name) in addition to group.contains(normalized_name) for cross-crate paths"

key-files:
  created: []
  modified:
    - "crates/analysis/tests/recursion_verification.rs"
    - "crates/analysis/src/recursion.rs"

key-decisions:
  - "generate_termination_vcs group membership check extended: || !group.contains(callee_name) added as fallback for cross-crate full-path callee names stored in RecursiveGroup"
  - "Integration test helpers make_cross_crate_local_foo and make_cross_crate_local_foo_decremented reuse the same IR construction pattern as recursion.rs unit tests"
  - "back-edge heuristic dependency: test DB entry has decreases.raw='foo' (substring of normalized in-crate fn name) to trigger cross-crate SCC detection"

patterns-established:
  - "Cross-crate callee name duality: RecursiveGroup stores full paths from name_map; normalize_callee strips to last segment — check both forms"

requirements-completed:
  - XCREC-01
  - XCREC-02

# Metrics
duration: ~12min
completed: 2026-03-02
---

# Phase 37 Plan 03: Cross-Crate SCC Integration Tests Summary

**4 end-to-end integration tests validate cross-crate SCC detection + Z3 termination verification, plus bug fix for cross-crate callee group membership check in generate_termination_vcs**

## Performance

- **Duration:** ~12 min
- **Started:** 2026-03-02T00:00:14Z
- **Completed:** 2026-03-02T00:12:57Z
- **Tasks:** 2
- **Files modified:** 2

## Accomplishments

- Added 4 integration tests to `recursion_verification.rs` exercising the full cross-crate SCC pipeline
- Fixed bug in `generate_termination_vcs`: cross-crate callees stored as full paths (`dep_crate::bar`) in `RecursiveGroup` were not found via normalized short name (`bar`) — added `|| !group.contains(callee_name)` fallback
- All 4 new tests pass with Z3: XCREC-01 (SCC member reporting), XCREC-02 (UNSAT), XCREC-02 (SAT counterexample), regression
- All 1243+ pre-existing tests remain GREEN
- `cargo clippy -D warnings` clean on both analysis and driver crates

## Task Commits

Each task was committed atomically:

1. **Task 1+2: Integration tests + normalize_callee bug fix + validation** - `53bf3f2` (feat)

**Plan metadata:** (docs commit follows)

## Files Created/Modified

- `crates/analysis/tests/recursion_verification.rs` - Added 4 cross-crate SCC integration tests and 2 IR construction helpers (`make_cross_crate_local_foo`, `make_cross_crate_local_foo_decremented`, `make_cross_crate_db_with_back_edge`)
- `crates/analysis/src/recursion.rs` - Fixed `generate_termination_vcs` group membership check to also match cross-crate full-path callee names

## Decisions Made

- **normalize_callee fallback:** The fix `&& !group.contains(callee_name)` is minimal-invasive — it handles the cross-crate case where RecursiveGroup stores full names from `name_map` (e.g., `dep_crate::bar`) while `normalize_callee` strips to last segment (`bar`). The check first tries the normalized name (single-crate path), then the raw callee name (cross-crate path).
- **Integration test placement:** Tests appended to existing `recursion_verification.rs` with dedicated IR helper functions — consistent with the established pattern of make_factorial, make_even, make_odd helpers in the same file.
- **DB back-edge trigger:** Test DB entry uses `decreases.raw = "foo"` which contains the normalized in-crate function name, triggering the back-edge heuristic in `from_functions_with_cross_crate_db` to form the cross-crate SCC.

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Fixed cross-crate callee group membership check in generate_termination_vcs**
- **Found during:** Task 1 (running integration tests for the first time)
- **Issue:** `RecursiveGroup` stores full callee paths from `name_map` (e.g., `"dep_crate::bar"`), but `normalize_callee("dep_crate::bar")` returns `"bar"`. The check `group.contains("bar")` returned false for `"dep_crate::bar"` in the group, causing cross-crate termination VCs to never be generated.
- **Fix:** Changed condition from `if !group.contains(&normalized) { continue; }` to `if !group.contains(&normalized) && !group.contains(callee_name) { continue; }`
- **Files modified:** `crates/analysis/src/recursion.rs`
- **Verification:** All 4 new integration tests pass; all pre-existing tests remain GREEN; clippy clean
- **Committed in:** `53bf3f2` (Task 1+2 combined commit)

---

**Total deviations:** 1 auto-fixed (1 bug — cross-crate callee name normalization mismatch)
**Impact on plan:** The bug fix was required for cross-crate termination VCs to be generated at all. Without it, the pipeline silently skipped cross-crate recursive calls. The fix is minimal-invasive (1 line change) and does not affect single-crate path.

## Issues Encountered

- Task 1 tests were failing on first run because the RecursiveGroup full-name vs. normalized short-name mismatch had not been caught during Phase 37-01 and 37-02 (those tests used a different setup where normalize_callee produced a match). Fixed via Rule 1 auto-fix.

## User Setup Required

None - no external service configuration required.

## Next Phase Readiness

- XCREC-01 and XCREC-02 both satisfied end-to-end
- Phase 37 complete (3/3 plans: 37-01 SCC detection, 37-02 VC generation wiring, 37-03 integration tests)
- v0.6 milestone Cross-Crate Verification: all XCREC requirements demonstrated end-to-end with Z3
- The normalize_callee bug fix makes the cross-crate termination VC pipeline fully functional

---
*Phase: 37-cross-crate-scc-detection*
*Completed: 2026-03-02*
