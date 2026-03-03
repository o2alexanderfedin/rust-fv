---
phase: 40-generics-verification-completion
plan: 01
subsystem: analysis
tags: [rust, generics, smtlib, vcgen, monomorphize, trait-bounds, z3]

# Dependency graph
requires:
  - phase: 39-fnmut-closure-prophecy
    provides: vcgen.rs declarations collection pattern and closure prophecy injection
provides:
  - trait_bounds_as_smt_assumptions returns Vec<Command> with real DeclareSort/DeclareFun/Assert axioms for Ord
  - vcgen.rs parametric axiom injection uses declarations.extend(assumptions) directly
  - Unit and integration tests confirming real axiom emission for T: Ord bounds
affects:
  - 40-02-PLAN.md (GENERICS-02 gap closure)
  - any phase using generic function verification

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "Parameter-scoped Ord axioms: DeclareSort(T,0) + DeclareFun(T_le,[T,T],Bool) + Assert reflexivity/totality for _1/_2 - avoids Z3 quantifier instantiation issues"
    - "declarations.extend(assumptions) pattern: returning Vec<Command> from trait_bounds_as_smt_assumptions allows direct extension without Assert-wrapping"

key-files:
  created: []
  modified:
    - crates/analysis/src/monomorphize.rs
    - crates/analysis/src/vcgen.rs
    - crates/analysis/tests/generics_e2e.rs

key-decisions:
  - "trait_bounds_as_smt_assumptions returns Vec<Command> not Vec<Term> — callers use declarations.extend() directly"
  - "Ord/PartialOrd: emit DeclareSort(T,0) + DeclareFun(T_le,[T,T],Bool) + parameter-scoped reflexivity/totality axioms for _1/_2"
  - "Eq/PartialEq: emit BoolLit(true) — SMT equality is built-in, no axioms needed"
  - "Unknown bounds: emit BoolLit(true) — conservative soundness, no false premises"
  - "Parameter-scoped axioms instead of universal quantifiers — avoids Z3 quantifier instantiation issues"

patterns-established:
  - "Trait bound axiom injection: return Vec<Command> from helper, caller uses declarations.extend()"
  - "Uninterpreted sort pattern for generic types: DeclareSort(name,0) + DeclareFun(pred) + Assert axioms"

requirements-completed: [GENERICS-01]

# Metrics
duration: 15min
completed: 2026-03-03
---

# Phase 40 Plan 01: Generics Verification — Real Ord/PartialOrd SMT Axiom Emission Summary

**trait_bounds_as_smt_assumptions changed from Vec<Term> BoolLit no-ops to Vec<Command> with DeclareSort/DeclareFun/Assert axioms for Ord bounds, closing GENERICS-01 gap**

## Performance

- **Duration:** ~15 min
- **Started:** 2026-03-03T01:55:00Z
- **Completed:** 2026-03-03T02:10:53Z
- **Tasks:** 3 (RED + GREEN + REFACTOR)
- **Files modified:** 3

## Accomplishments

- Fixed trait_bounds_as_smt_assumptions to return Vec<Command> with real SMT commands for Ord/PartialOrd bounds — DeclareSort(T,0) + DeclareFun(T_le,[T,T],Bool) + reflexivity/totality axioms
- Updated vcgen.rs parametric axiom injection from Assert-wrapping loop to declarations.extend(assumptions)
- Added integration test ord_generic_smt_script_contains_declare_sort in generics_e2e.rs confirming DeclareSort and DeclareFun appear in VC scripts for T: Ord generic functions
- Full workspace test suite (all packages) passes with zero regressions

## Task Commits

Each task was committed atomically:

1. **Task 1: RED — Add failing tests** - `7498fb6` (pre-existing, tests added in this plan)
   - Unit tests test_trait_bounds_as_smt_assumptions_ord_emits_real_commands and test_trait_bounds_as_smt_assumptions_eq_is_noop already existed in monomorphize.rs
   - Added integration test ord_generic_smt_script_contains_declare_sort to generics_e2e.rs
   - Note: The RED commit includes the Task 1 test additions plus formatting

2. **Task 2+3: GREEN + REFACTOR** - `a7b117a` (feat)
   - Changed monomorphize.rs trait_bounds_as_smt_assumptions return type from Vec<Term> to Vec<Command>
   - Added Command and Sort imports to monomorphize.rs
   - Implemented Ord/PartialOrd axiom emission: DeclareSort + DeclareFun + Assert axioms
   - Updated vcgen.rs: declarations.extend(assumptions) replacing for-loop with Command::Assert wrapping
   - All 3 unit + integration tests pass (GREEN confirmed)
   - Full workspace tests pass (REFACTOR confirmed)

## Files Created/Modified

- `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/analysis/src/monomorphize.rs` - Changed return type of trait_bounds_as_smt_assumptions (lines 295-355): Vec<Term> -> Vec<Command> with real Ord axioms; added Command and Sort imports (lines 13-14)
- `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/analysis/src/vcgen.rs` - Updated parametric axiom injection (lines 299-313): declarations.extend(assumptions) replacing for-loop
- `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/analysis/tests/generics_e2e.rs` - Added ord_generic_smt_script_contains_declare_sort integration test (lines 118-162)

## Decisions Made

- Parameter-scoped axioms rather than universally quantified: avoids Z3 quantifier instantiation issues while still providing useful T_le constraints for _1 and _2 (the function parameters)
- Eq/PartialEq emit BoolLit(true): SMT equality is built-in via = operator, no sort declarations needed
- Unknown bounds emit BoolLit(true): conservative soundness ensures no false premises
- Return Vec<Command> not Vec<Term>: natural fit since DeclareSort/DeclareFun are top-level commands, not Term-level assertions

## GENERICS-01 Closure Evidence

- Return type: `pub fn trait_bounds_as_smt_assumptions(...) -> Vec<Command>` at monomorphize.rs:312
- DeclareSort emitted: `cmds.push(Command::DeclareSort(sort_name.clone(), 0))` at monomorphize.rs:321
- DeclareFun emitted: `cmds.push(Command::DeclareFun(...))` at monomorphize.rs:322-326
- vcgen.rs caller: `declarations.extend(assumptions)` at vcgen.rs:309
- Unit test PASSES: test_trait_bounds_as_smt_assumptions_ord_emits_real_commands
- Integration test PASSES: ord_generic_smt_script_contains_declare_sort
- Full workspace: cargo test --workspace exits 0

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 2 - Missing Critical] Fixed script.commands access: private field vs method**
- **Found during:** Task 1 (integration test authoring)
- **Issue:** Plan spec used `script.commands` as field access, but Script struct exposes commands() as a method (private field)
- **Fix:** Changed `first_vc.script.commands` to `first_vc.script.commands()` in generics_e2e.rs
- **Files modified:** crates/analysis/tests/generics_e2e.rs
- **Verification:** Compilation succeeded, integration test passed
- **Committed in:** a7b117a (Task 2+3 commit)

---

**Total deviations:** 1 auto-fixed (Rule 2 - missing critical access pattern)
**Impact on plan:** Trivial deviation - plan spec used field access pattern, actual API is method call. No scope creep.

## Issues Encountered

- The unit tests (test_trait_bounds_as_smt_assumptions_ord_emits_real_commands, test_trait_bounds_as_smt_assumptions_eq_is_noop) were already present in monomorphize.rs from a prior planning step. RED state was confirmed by compile errors (type mismatch Vec<Term> vs Vec<Command>).

## Next Phase Readiness

- GENERICS-01 closed: generic functions now verified against real trait bound SMT constraints
- Ready for 40-02: GENERICS-02 gap closure (whichever remaining generics gap is next)
- No blockers

## Self-Check

- [ ] crates/analysis/src/monomorphize.rs — modified (trait_bounds_as_smt_assumptions)
- [ ] crates/analysis/src/vcgen.rs — modified (declarations.extend)
- [ ] crates/analysis/tests/generics_e2e.rs — modified (new integration test)
- [ ] Commits: a7b117a (feat), 7498fb6 (test setup exists)

---
*Phase: 40-generics-verification-completion*
*Completed: 2026-03-03*
