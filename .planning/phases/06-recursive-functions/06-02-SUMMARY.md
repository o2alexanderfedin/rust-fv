---
phase: 06-recursive-functions
plan: 02
subsystem: analysis
tags: [recursion, termination, uninterpreted-functions, smt-axioms, vcgen, decreases]

# Dependency graph
requires:
  - phase: 06-recursive-functions (plan 01)
    provides: "#[decreases(expr)] proc macro, Contracts.decreases field, VcKind::Termination, RecursiveGroup, CallGraph::detect_recursion()"
provides:
  - "recursion.rs module: check_missing_decreases(), generate_termination_vcs(), encode_recursive_function()"
  - "VCGen integration: recursive functions detected and handled during generate_vcs()"
  - "Missing #[decreases] diagnostic: always-SAT VC with helpful suggestion"
  - "Uninterpreted function encoding: declare-fun + forall axioms for base/recursive cases"
affects: [06-03, driver-diagnostics, verification-pipeline]

# Tech tracking
tech-stack:
  added: []
  patterns: [termination VC generation via measure comparison, uninterpreted function axiomatization, diagnostic VC for missing annotations]

key-files:
  created:
    - crates/analysis/src/recursion.rs
  modified:
    - crates/analysis/src/lib.rs
    - crates/analysis/src/vcgen.rs

key-decisions:
  - "Termination VCs use bitvector signed less-than (BvSLt) based on first parameter type"
  - "Missing-decreases produces always-SAT diagnostic VC through normal VC pipeline (not separate error path)"
  - "Uninterpreted function encoding uses quantified forall axioms with implicit triggers"
  - "Recursion detection in generate_vcs uses single-function call graph (sufficient for self-recursion)"

patterns-established:
  - "Termination VC: NOT(call_measure < entry_measure) negated for UNSAT=valid check"
  - "Diagnostic VC pattern: assert(true) + check-sat = always SAT to report errors through VC pipeline"
  - "Uninterpreted function: (declare-fun name_uninterp (param_sorts) return_sort) + forall axioms per case"
  - "Argument substitution: map formal param names to actual call-site operands via substitute_term()"

# Metrics
duration: 10min
completed: 2026-02-12
---

# Phase 6 Plan 2: Recursion Verification Core Summary

**Termination VC generation with measure comparison at recursive call sites, uninterpreted function encoding with quantified axioms, and missing-decreases diagnostic VCs integrated into VCGen pipeline**

## Performance

- **Duration:** 10 min
- **Started:** 2026-02-12T08:14:31Z
- **Completed:** 2026-02-12T08:24:50Z
- **Tasks:** 2 (TDD)
- **Files modified:** 3

## Accomplishments
- Created `recursion.rs` module with `MissingDecreasesError`, `check_missing_decreases()`, `generate_termination_vcs()`, and `encode_recursive_function()` -- the core of Phase 6
- Integrated recursion detection into `generate_vcs()`: builds call graph, detects SCCs, generates termination VCs for each recursive call site with `VcKind::Termination`
- Missing `#[decreases]` on recursive functions produces always-SAT diagnostic VC through normal verification pipeline (not a separate error path)
- `encode_recursive_function()` generates uninterpreted SMT function declaration with universally quantified axioms for base and recursive cases
- 13 new tests (7 unit + 3 encode + 3 integration), all 1768 tests passing, 0 warnings

## Task Commits

Each task was committed atomically:

1. **Task 1: Create recursion.rs with termination VC generation and missing-decreases detection** - `2ec784b` (feat)
2. **Task 2: Integrate recursion module into VCGen and add uninterpreted function encoding** - `62a7627` (feat)

_Note: TDD tasks -- tests written first (RED), then implementation (GREEN), then refactor._

## Files Created/Modified
- `crates/analysis/src/recursion.rs` - NEW: Core recursion analysis module (890 lines) with check_missing_decreases, generate_termination_vcs, encode_recursive_function + 10 unit tests
- `crates/analysis/src/lib.rs` - Added `pub mod recursion` export
- `crates/analysis/src/vcgen.rs` - Integrated recursion detection into generate_vcs() + 3 integration tests with make_recursive_factorial helper

## Decisions Made
- Termination VCs use bitvector signed less-than (`BvSLt`) when parameter type is signed, unsigned less-than (`BvULt`) otherwise -- matches Z3's bitvector theory
- Missing-decreases errors flow through the normal VC pipeline as always-SAT diagnostic VCs, rather than a separate error reporting mechanism -- simpler architecture, consistent UX
- Uninterpreted function encoding uses quantified `forall` axioms (Dafny/F* pattern) rather than Z3's `define-fun-rec` -- better control over instantiation depth and error reporting
- Single-function call graph in generate_vcs is sufficient for self-recursion detection; mutual recursion across contract_db deferred to Plan 03

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 3 - Blocking] CallGraph import moved from module-level to test-only**
- **Found during:** Task 1 (clippy check)
- **Issue:** `CallGraph` imported at module level in recursion.rs but only used in tests; clippy flagged unused import
- **Fix:** Removed from module imports, added to `#[cfg(test)]` test module imports
- **Files modified:** crates/analysis/src/recursion.rs
- **Verification:** `cargo clippy --workspace -- -D warnings` passes
- **Committed in:** 2ec784b (Task 1 commit)

**2. [Rule 1 - Bug] Fixed 3 collapsible-if patterns flagged by clippy**
- **Found during:** Task 1 (clippy check)
- **Issue:** Nested `if let` + `if` patterns in check_missing_decreases, extract_return_value, extract_recursive_return
- **Fix:** Collapsed into `if let ... && ...` let-chain syntax
- **Files modified:** crates/analysis/src/recursion.rs
- **Verification:** `cargo clippy --workspace -- -D warnings` passes
- **Committed in:** 2ec784b (Task 1 commit)

---

**Total deviations:** 2 auto-fixed (1 Rule 3 blocking, 1 Rule 1 bug/lint)
**Impact on plan:** Mechanical fixes for clippy compliance. No scope creep.

## Issues Encountered
None -- plan executed smoothly.

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- All recursion verification infrastructure is complete
- Plan 06-03 can proceed with full integration testing, diagnostics improvements, and end-to-end verification
- Termination VCs are generated and can be dispatched to Z3 via the existing solver pipeline
- Missing-decreases errors flow through the standard VC result pathway

## Self-Check: PASSED

- File `crates/analysis/src/recursion.rs` verified present
- File `crates/analysis/src/lib.rs` contains `pub mod recursion`
- File `crates/analysis/src/vcgen.rs` contains recursion integration
- Commit 2ec784b verified in git history
- Commit 62a7627 verified in git history
- 1768 tests pass, 0 failures, 0 warnings

---
*Phase: 06-recursive-functions, Plan: 02*
*Completed: 2026-02-12*
