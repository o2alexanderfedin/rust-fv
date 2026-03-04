---
phase: 39-fnmut-prophecy-variable-encoding-for-mutable-closure-capture-verification-implement-prophecy-pre-post-state-tracking-in-closure-analysis-rs-vcgen-rs-so-fnmut-closures-with-contracts-on-mutated-captured-state-can-be-verified
plan: 02
subsystem: verification
tags: [vcgen, prophecy, closure, fnmut, smt-lib, capture-mode]

# Dependency graph
requires:
  - phase: 39-01
    provides: "detect_closure_prophecies() in encode_prophecy.rs, CaptureMode enum in ir.rs, ProphecyInfo.closure_name field"
provides:
  - "Closure prophecy integration in generate_vcs declaration phase"
  - "FnMut closures with ByMutRef captures emit declare-const {field}_initial and declare-const {field}_prophecy in VC scripts"
  - "4 vcgen tests: upgraded placeholder + Fn/ByRef + FnMut/ByMove + two-ByMutRef integration tests"
affects:
  - vcgen
  - closure_analysis
  - encode_prophecy

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "detect_closure_prophecies wired after encode_closure_as_uninterpreted in declarations phase — mirrors detect_prophecies/prophecy_declarations pattern for &mut params"
    - "closure prophecy declarations extend same declarations vec used by all VC scripts — consistent SMT preamble"
    - "make_fn_closure_func test helper pattern for parameterized closure VC tests"

key-files:
  created: []
  modified:
    - crates/analysis/src/vcgen.rs

key-decisions:
  - "Closure prophecy wiring inserted at declarations collection site (lines 277-299) rather than inside the separate closure analysis block (lines 439-489) — avoids re-extracting closure_infos and ensures declarations are available"
  - "Reuse prophecy_declarations() function for closure prophecies unchanged — ProphecyInfo struct is shared between &mut param prophecies and closure capture prophecies"
  - "Test with ensures contract to trigger VC generation — functions without contracts produce no VCs so script assertions would never execute"

patterns-established:
  - "Wiring new declaration types: add after existing closure declarations loop using closure_infos already extracted"
  - "TDD for VC script content: use format!('{}', vc.script) then contains() assertions on SMT-LIB text"

requirements-completed: []

# Metrics
duration: 11min
completed: 2026-03-02
---

# Phase 39 Plan 02: FnMut Closure Prophecy Integration in generate_vcs Summary

**detect_closure_prophecies wired into generate_vcs so FnMut closures with ByMutRef captures emit declare-const {field}_initial and declare-const {field}_prophecy in every VC script**

## Performance

- **Duration:** 11 min
- **Started:** 2026-03-02T22:00:13Z
- **Completed:** 2026-03-02T22:11:06Z
- **Tasks:** 2
- **Files modified:** 1

## Accomplishments
- Wired `detect_closure_prophecies` + `prophecy_declarations` into `generate_vcs` closure declarations phase — FnMut/ByMutRef captures now produce SMT `declare-const` for initial and prophecy variables
- Upgraded placeholder test `test_vcgen_fnmut_closure_prophecy` with assertions verifying `declare-const count_initial` and `declare-const count_prophecy` appear in VC scripts
- Added 3 additional integration tests: Fn/ByRef (no prophecy), FnMut/ByMove (no prophecy), two-ByMutRef (both count and total declared)
- Full test suite passes with zero regressions (1258+ tests)

## Task Commits

Each task was committed atomically:

1. **Task 1: Wire detect_closure_prophecies into generate_vcs closure analysis block** - `23ed5fc` (feat)
2. **Task 2: Add non-regression and additional FnMut prophecy integration tests** - `a495ac9` (test)

**Plan metadata:** (this commit)

_Note: TDD tasks — RED phase confirmed test failures before GREEN implementation_

## Files Created/Modified
- `crates/analysis/src/vcgen.rs` - Added closure prophecy declaration wiring + 4 upgraded/new tests + make_fn_closure_func helper

## Decisions Made
- Inserted closure prophecy wiring at the declarations collection site (after `encode_closure_as_uninterpreted` loop, lines ~277-299) rather than inside the later closure analysis block — `closure_infos` was already extracted and `declarations` was mutable in scope, avoiding redundant extraction
- Reused existing `prophecy_declarations()` without modification — `ProphecyInfo` struct works identically for closure captures vs. `&mut` params; closure_name field disambiguates origin
- Used `ensures: vec![SpecExpr { raw: "true".to_string() }]` in tests to trigger VC generation — functions without contracts produce no VCs, making script content assertions unreachable

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] SpecExpr::BoolLit does not exist — SpecExpr is a plain struct**
- **Found during:** Task 1 (upgrading test_vcgen_fnmut_closure_prophecy)
- **Issue:** Plan template used `crate::ir::SpecExpr::BoolLit(true)` but `SpecExpr` is `pub struct SpecExpr { pub raw: String }` (no enum variants)
- **Fix:** Used `crate::ir::SpecExpr { raw: "true".to_string() }` instead
- **Files modified:** crates/analysis/src/vcgen.rs
- **Verification:** Compilation succeeded, test passed
- **Committed in:** 23ed5fc (Task 1 commit)

---

**Total deviations:** 1 auto-fixed (Rule 1 - Bug: incorrect type usage in plan template)
**Impact on plan:** Minor fix, no scope change. SpecExpr { raw: "true" } is semantically identical to plan's intent.

## Issues Encountered
- `cargo fmt` failed pre-commit hook on first Task 1 commit attempt — inline struct `SpecExpr { raw: "true".to_string() }` needed multi-line formatting. Fixed by running `cargo fmt` before re-committing.

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- FnMut prophecy encoding loop is now complete: IR (Plan 01) + detection (Plan 01) + vcgen integration (Plan 02)
- `count_initial` and `count_prophecy` SMT variables are declared in VC scripts for `#[ensures(count == old(count) + 1)]` style contracts on FnMut closures
- Ready for Phase 39 Plan 03 (if any) or next milestone work

---
*Phase: 39*
*Completed: 2026-03-02*
