---
phase: 02-table-stakes-completion
plan: 02
subsystem: analysis
tags: [loop-invariant, vcgen, smt, z3, back-edge, cfg, dfs]

# Dependency graph
requires:
  - phase: 02-01
    provides: "SolverBackend trait, structured tracing, Z3 native backend"
  - phase: 01-01
    provides: "Path-sensitive VCGen with CFG traversal and SSA encoding"
provides:
  - "LoopInfo struct in IR for loop representation"
  - "detect_loops() via DFS back-edge detection"
  - "3-VC loop invariant verification (initialization, preservation, sufficiency)"
  - "Next-state variable encoding for preservation VC"
  - "#[invariant] attribute extraction in driver"
affects: [02-03, 02-05, Phase 3]

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "Classical 3-VC loop invariant verification (Hoare logic)"
    - "Next-state variable encoding for inductive step"
    - "DFS back-edge detection for loop discovery"

key-files:
  created:
    - crates/analysis/tests/loop_verification.rs
  modified:
    - crates/analysis/src/ir.rs
    - crates/analysis/src/vcgen.rs
    - crates/driver/src/callbacks.rs
    - crates/driver/src/mir_converter.rs

key-decisions:
  - "Next-state variables (_var_next) for preservation VC to avoid SMT constant reuse conflicts"
  - "Body-only assignments (exclude header stmts) in preservation VC with header stmts encoded separately"
  - "Header statement encoding in exit VC to establish condition variable relationship"
  - "Loops without invariants skip verification with tracing::warn (no partial verification)"

patterns-established:
  - "3-VC pattern: initialization, preservation, sufficiency with labeled descriptions"
  - "Next-state encoding: declare x_next constants, encode body with _next LHS, substitute in invariant check"
  - "Loop test pattern: manual IR construction with LoopInfo, 4-block CFG (init, header, body, exit)"

# Metrics
duration: 16min
completed: 2026-02-11
---

# Phase 2 Plan 2: Loop Invariant Verification Summary

**Classical 3-VC loop invariant verification with DFS back-edge detection, next-state variable encoding, and 10 E2E tests proving correct/incorrect invariant handling**

## Performance

- **Duration:** 16 min
- **Started:** 2026-02-11T11:38:14Z
- **Completed:** 2026-02-11T11:54:42Z
- **Tasks:** 2
- **Files modified:** 5 core + ~15 test/bench files (field additions)

## Accomplishments
- Loop representation in IR with LoopInfo struct (header_block, back_edge_blocks, invariants)
- DFS back-edge detection for automatic loop discovery from CFG
- 3-VC generation: initialization (precondition => invariant), preservation (invariant + condition + body => invariant'), sufficiency (invariant + NOT condition => postcondition)
- Next-state variable encoding solving the SMT constant reuse problem in preservation VCs
- 10 E2E tests covering correct loops, wrong invariants, edge cases, and auto-detection
- Driver support for extracting #[invariant] annotations from HIR attributes

## Task Commits

Each task was committed atomically:

1. **Task 1: Add loop representation to IR and detect loops in VCGen** - `f2a83ec` (feat)
2. **Task 2: E2E loop verification tests with Z3** - `1421c1f` (test)

## Files Created/Modified
- `crates/analysis/src/ir.rs` - Added LoopInfo struct, loops field on Function, invariants on Contracts
- `crates/analysis/src/vcgen.rs` - detect_loops(), generate_loop_invariant_vcs(), next-state encoding, substitute_next_state()
- `crates/analysis/tests/loop_verification.rs` - 10 E2E tests (~1250 lines) with Z3 integration
- `crates/driver/src/callbacks.rs` - invariant extraction from rust_fv::invariant:: doc attributes
- `crates/driver/src/mir_converter.rs` - loops: vec![] field in Function construction

## Decisions Made
1. **Next-state variables for preservation VC**: The naive approach of encoding `_3 = 0` (invariant) and `_3 = _3 + 1` (body) creates contradictory SMT assertions on the same constant. Solution: declare `_3_next` constants, encode body assignments with `_next` LHS, check invariant with substituted variable names.
2. **Header statement encoding**: The exit VC needs header block statements encoded (e.g., `_4 = _3 < _1`) to establish the relationship between the condition variable and loop variables. Without this, `NOT _4` is unconstrained and Z3 finds trivial counterexamples.
3. **Body-only assignments in preservation**: The preservation VC encodes header statements separately (to establish condition), then uses collect_body_only_assignments() to get only the body block statements for next-state encoding.
4. **Two-variable loop test instead of sum loop**: The original sum loop (`sum += i`) requires a non-linear inductive invariant not expressible in our spec language. Replaced with a two-variable loop (`count += 1; i += 1`) with relational invariant `_5 == _3` that IS inductively provable.

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Exit VC missing header statement encoding**
- **Found during:** Task 2 (E2E tests)
- **Issue:** Exit VC did not encode header block statements, so the condition variable (e.g., `_4`) was unconstrained. `NOT _4` didn't constrain loop variables, causing false counterexamples.
- **Fix:** Added header statement encoding before asserting NOT condition in exit VC
- **Files modified:** crates/analysis/src/vcgen.rs
- **Verification:** test_simple_counter_loop, test_countdown_loop, test_zero_iteration_loop all UNSAT
- **Committed in:** 1421c1f (Task 2 commit)

**2. [Rule 1 - Bug] Preservation VC SSA constant conflict**
- **Found during:** Task 2 (E2E tests)
- **Issue:** Encoding invariant `_3 = 0` and body `_3 = _3 + 1` creates contradictory assertions on the same SMT constant `_3`. Z3 returns UNSAT trivially (from contradiction, not from correctness).
- **Fix:** Implemented next-state variable approach: declare `_var_next` constants, encode body with `_next` LHS, substitute in invariant check
- **Files modified:** crates/analysis/src/vcgen.rs (substitute_next_state, collect_body_only_assignments)
- **Verification:** test_wrong_preservation_invariant correctly returns SAT
- **Committed in:** 1421c1f (Task 2 commit)

**3. [Rule 1 - Bug] Sum loop test invariant not inductively provable under bitvector semantics**
- **Found during:** Task 2 (E2E tests)
- **Issue:** The invariant `_5 >= 0` for `sum += i` is not inductively provable because Z3 can pick `_5 = 0x7FFFFFF0` (satisfies `_5 >= 0` signed) and `_3 = 1`, making `_5 + _3` overflow to negative. No simple linear invariant works for the sum loop.
- **Fix:** Replaced sum loop test with a two-variable loop (`count += 1; i += 1`) where `_5 == _3` is a correct relational invariant provable under bitvector semantics.
- **Files modified:** crates/analysis/tests/loop_verification.rs
- **Verification:** test_two_variable_loop passes all 3 VCs as UNSAT
- **Committed in:** 1421c1f (Task 2 commit)

---

**Total deviations:** 3 auto-fixed (3 bugs)
**Impact on plan:** All auto-fixes were necessary for correctness. The sum loop replacement maintains test coverage of multi-variable loops while being mathematically sound.

## Issues Encountered
- Mass field updates across ~80 struct constructions (tests, benches) needed for new `loops` and `invariants` fields -- resolved with scripted updates and `cargo fmt`
- Bitvector semantics fundamentally limit which loop invariants are inductively provable without non-linear arithmetic support in the spec parser

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- Loop invariant infrastructure ready for use by assertion/panic verification (02-03)
- Spec parser needs multiplication/division support for expressing complex loop invariants (future work)
- All 363+ tests passing across workspace

---
*Phase: 02-table-stakes-completion*
*Completed: 2026-02-11*

## Self-Check: PASSED

All key files verified present. All task commits verified in git log.
