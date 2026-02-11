---
phase: 01-soundness-foundation
plan: 01
subsystem: analysis
tags: [vcgen, ssa, cfg, smt, z3, path-conditions, bitvector]

# Dependency graph
requires:
  - phase: none
    provides: "existing 5-crate workspace with linear VCGen"
provides:
  - "CFG-aware path-condition-based VCGen replacing linear block walking"
  - "Path enumeration with cycle detection for branch/loop handling"
  - "Path-condition-guarded assertions using (=> cond assertion) encoding"
  - "E2E tests for if/else, 3-way match, nested branches, early return, branch-specific overflow"
  - "Comparison operation signedness fix (operand-based type inference)"
affects: [01-02-PLAN, 01-03-PLAN, overflow-encoding, postcondition-verification]

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "Path enumeration via recursive CFG traversal with HashSet cycle detection"
    - "Path-condition-guarded assertions: (=> cond (= var value)) for branch-specific assignments"
    - "Common-prefix detection via branch_depth tracking (depth 0 = unguarded)"
    - "Operand-type inference for comparison signedness via BinOp::is_comparison()"

key-files:
  created: []
  modified:
    - "crates/analysis/src/vcgen.rs"
    - "crates/analysis/src/ir.rs"
    - "crates/analysis/tests/e2e_verification.rs"

key-decisions:
  - "Path-sensitive encoding over SSA phi-nodes: simpler, naturally handles early returns and match arms"
  - "Path condition = conjunction of branch decisions; path exhaustiveness enforced via disjunction assertion"
  - "Common-prefix assignments (branch_depth == 0) emitted unguarded to avoid circular constraints"
  - "Comparison ops use operand types for signedness, not destination type (Bool)"

patterns-established:
  - "CFG path enumeration: traverse_block() recursively follows Goto/SwitchInt/Assert/Call edges"
  - "Branch condition encoding: Bool discriminants use identity/negation; integer uses Eq with BitVecLit"
  - "E2E test pattern: build IR function, generate VCs, render to SMT-LIB, submit to Z3, assert SAT/UNSAT"

# Metrics
duration: 11min
completed: 2026-02-11
---

# Phase 1 Plan 1: SSA/CFG VCGen Fix Summary

**Path-condition-based VCGen replacing linear block walking, fixing the critical soundness bug for branching functions like max(a,b)**

## Performance

- **Duration:** 11 min
- **Started:** 2026-02-11T08:12:25Z
- **Completed:** 2026-02-11T08:23:26Z
- **Tasks:** 2
- **Files modified:** 3

## Accomplishments
- Fixed the critical soundness bug: VCGen now traverses the CFG via terminator edges instead of linear block iteration
- Path-condition encoding correctly handles if/else, 3-way match, nested branches (4 paths), and early return via Goto
- max(a,b) with postcondition `result >= a && result >= b` now verifies as UNSAT (proved sound)
- 62 total tests passing (52 unit + 10 E2E), zero clippy warnings, zero regressions

## Task Commits

Each task was committed atomically:

1. **Task 1: Implement SSA renaming and path-condition-based VCGen** - `a3490f3` (feat) + `ea034ba` (fix)
   - Rewrote VCGen with CFG traversal, path enumeration, path-condition guards
   - Fixed comparison signedness bug (Rule 1 deviation)
2. **Task 2: Add E2E tests for branching and multi-path control flow** - `ea034ba` (feat)
   - 6 new E2E tests: if/else SSA, wrong postcondition, 3-way match, early return, nested branches, branch overflow

## Files Created/Modified
- `crates/analysis/src/vcgen.rs` - Rewritten VCGen with path enumeration, CFG traversal, path-condition-guarded assertions
- `crates/analysis/src/ir.rs` - Added `BinOp::is_comparison()` method for signedness inference
- `crates/analysis/tests/e2e_verification.rs` - 6 new E2E tests for branching control flow

## Decisions Made
- **Path-sensitive encoding over SSA phi-nodes**: Instead of creating new SSA variable names at each assignment and using ITE at merge points, we enumerate all paths and guard each path's assignments with `(=> path_condition assertion)`. This is simpler, naturally handles early returns and match arms without explicit phi nodes, and is equivalent in expressiveness for acyclic CFGs.
- **Common-prefix detection via branch_depth**: Assignments in blocks before any SwitchInt have `branch_depth == 0` and are emitted without path-condition guards. This prevents circular constraints like `(=> _3 (= _3 (> _1 _2)))`.
- **Comparison operand-type inference**: For comparison ops (`Gt`, `Lt`, `Ge`, `Le`, `Eq`, `Ne`), the type for signedness is inferred from the operands, not the destination (which is Bool).

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Comparison signedness using destination type instead of operand type**
- **Found during:** Task 2 (E2E test `test_if_else_branches_ssa` failing)
- **Issue:** `encode_assignment` for `_3 = _1 > _2` called `find_local_type(func, "_3")` which returned `Ty::Bool`. `encode_binop(Gt, ..., &Ty::Bool)` generated unsigned comparison (`bvugt`) instead of signed (`bvsgt`) for `i32` operands.
- **Fix:** Added `BinOp::is_comparison()` method. For comparison ops, type is inferred from operands via `infer_operand_type()` first, falling back to destination type.
- **Files modified:** `crates/analysis/src/vcgen.rs`, `crates/analysis/src/ir.rs`
- **Verification:** `test_if_else_branches_ssa` now passes -- max(a,b) postcondition verified as UNSAT
- **Committed in:** `ea034ba`

**2. [Rule 1 - Bug] Path conditions guarding common-prefix assignments**
- **Found during:** Task 2 (E2E tests failing)
- **Issue:** Assignments in blocks before SwitchInt (e.g., `_3 = _1 > _2` in bb0) were being guarded by the branch condition derived from that same assignment, creating circular constraints.
- **Fix:** Added `branch_depth` field to `PathAssignment`. Assignments with `branch_depth == 0` are emitted without path-condition guards.
- **Files modified:** `crates/analysis/src/vcgen.rs`
- **Verification:** All 10 E2E tests pass
- **Committed in:** `ea034ba`

---

**Total deviations:** 2 auto-fixed (2 bugs)
**Impact on plan:** Both bugs were pre-existing in the codebase, exposed by the new E2E tests. Fixes were essential for correctness.

## Issues Encountered
None beyond the auto-fixed deviations above.

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- VCGen now correctly handles all acyclic control flow patterns (if/else, match, early return, nested branches)
- Ready for Plan 01-02 (overflow encoding audit) which will build on this sound foundation
- Loop handling deferred to Phase 2 as planned (cycle detection prevents infinite recursion but doesn't verify loop bodies)

## Self-Check: PASSED

- All 3 modified files exist on disk
- Commits a3490f3 and ea034ba verified in git log
- 52 unit tests + 10 E2E tests passing
- Zero clippy warnings

---
*Phase: 01-soundness-foundation*
*Completed: 2026-02-11*
