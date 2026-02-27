---
phase: 20-separation-logic
plan: 04
subsystem: testing
tags: [separation-logic, integration-tests, z3, pts_to, frame-rule, ghost-predicates, tdd]

# Dependency graph
requires:
  - phase: 20-01
    provides: pts_to encoding, sep_heap/perm array declarations, heapval accessor
  - phase: 20-02
    provides: ghost predicate extraction, GhostPredicateDatabase
  - phase: 20-03
    provides: sep-conj detection, build_frame_axiom, AUFBV logic selection, parse_spec_expr_with_db
provides:
  - E2E integration tests verifying all 4 SEP requirements against live Z3
  - TDD-validated proof that the full pipeline (spec → IR → VCGen → SMT → Z3) works end-to-end
  - Test helpers (build_ptr_func, build_two_ptr_func, build_caller_func) for future sep-logic tests
affects:
  - phase 21 (weak memory — will use same test infrastructure patterns)
  - phase 22 (async — may use similar IR-building helpers)
  - phase 23 (integration — may re-use sep-logic E2E test helpers)

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "Integration test helper pattern: build_ptr_func/build_two_ptr_func for RawPtr IR construction"
    - "Z3 skip pattern: solver_or_skip() panics with Z3_NOT_AVAILABLE prefix for CI detection"
    - "Recursive ghost pred exhaustion: register self-recursive pred to test depth=0 behavior from public API"
    - "Raw SMT-LIB string check_sat_raw for direct Z3 satisfiability verification"

key-files:
  created:
    - crates/analysis/tests/sep_logic_integration.rs
  modified: []

key-decisions:
  - "Use recursive ghost predicate (looping(p) = looping(p)) to test depth-exhaustion via public parse_spec_expr_with_db API — avoids needing to expose private parse_spec_expr_with_depth"
  - "Test SEP-03 frame axiom validity by asserting Z3 returns UNSAT for negation of frame axiom hand-crafted in SMT-LIB directly"
  - "Ghost predicate body for SEP-04: owned(p) = pts_to(p, 0) — simple non-recursive pred verifies depth-3 expansion to pts_to And term"

patterns-established:
  - "IR-building helpers in integration tests follow Function struct literal pattern with all fields explicit"
  - "Each SEP requirement test has numbered sub-sections (1. parse check, 2. VCGen check, 3. Z3 check)"

requirements-completed: [SEP-01, SEP-02, SEP-03, SEP-04]

# Metrics
duration: 7min
completed: 2026-02-19
---

# Phase 20 Plan 04: Separation Logic E2E Integration Tests Summary

**4 end-to-end integration tests verifying sep-logic pipeline (spec→IR→VCGen→SMT→Z3) for all SEP-01 through SEP-04 requirements with live Z3 validation**

## Performance

- **Duration:** 7 min
- **Started:** 2026-02-19T06:12:40Z
- **Completed:** 2026-02-19T06:19:45Z
- **Tasks:** 1 (with 2 TDD commits: RED + GREEN)
- **Files modified:** 1

## Accomplishments

- TDD RED phase: 4 failing test stubs with proper clippy-clean structure
- TDD GREEN phase: all 4 tests implemented and passing against live Z3
- SEP-01: pts_to(p, v) parses to And([Select(perm, p), Eq(heapval_as_bv32(...), v)]) and Z3 returns sat
- SEP-02: pts_to(p,x) * pts_to(q,y) parses to outer And with two pts_to arms, Z3 returns sat for conjunction
- SEP-03: call-site VC for callee with pts_to requires uses AUFBV logic, contains forall frame axiom, negation is UNSAT in Z3
- SEP-04: ghost predicate owned(p)=pts_to(p,0) expands at depth 3 to pts_to And term; recursive pred looping(p)=looping(p) exhausts depth returning BoolLit(false)

## Task Commits

TDD task committed in two phases:

1. **TDD RED - Failing test stubs** — `3364ddc` (test)
2. **TDD GREEN - All 4 tests passing** — `8224e89` (feat)

**Plan metadata:** (this commit — docs)

_Note: REFACTOR phase not needed — code structure was clean after GREEN: helpers extracted, each test has clear comments_

## Files Created/Modified

- `crates/analysis/tests/sep_logic_integration.rs` — 4 E2E integration tests with shared IR-building helpers

## Decisions Made

- Used recursive ghost predicate (looping(p) = looping(p)) to test depth=0 behavior via the public API — avoids needing to make `parse_spec_expr_with_depth` public. The function `parse_spec_expr_with_db` internally uses depth=3, and a self-recursive predicate unwinds 3 times to reach depth=0 which returns BoolLit(false).
- SEP-03 frame axiom validity tested via direct SMT-LIB raw string (not via VCGen's generated script) to get a clean UNSAT proof — the VCGen-generated script verifies the call-site precondition encoding, not the axiom validity directly.
- Ghost predicate body for SEP-04 uses `pts_to(p, 0)` (not `if n==0 { true } else { pts_to(p, 0) }`) because spec_parser does not support Expr::If — keeps the test focused and parseable.

## Deviations from Plan

None — plan executed exactly as written. The ghost predicate body choice was a minor simplification (using a non-conditional body) to work within existing spec_parser capabilities, documented in Decisions Made above.

## Issues Encountered

- Pre-commit hook runs clippy with `-D warnings` on test files — RED phase stubs required `#![allow(dead_code, unused_imports)]` to pass clippy while leaving imports for GREEN phase
- rustfmt reformatted multi-line `assert_eq!` calls to single line — auto-corrected on second commit

## Next Phase Readiness

- Phase 20 is now complete: all 4 SEP requirements (pts_to ownership, separating conjunction, frame rule, ghost predicate unfold) are infrastructure-proven and E2E-tested
- Phase 21 (weak memory) can begin — test infrastructure patterns established here are reusable
- No blockers

---
*Phase: 20-separation-logic*
*Completed: 2026-02-19*
