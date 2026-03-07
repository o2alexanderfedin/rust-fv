---
phase: 51-core-language-features-i
plan: 02
subsystem: analysis
tags: [hrtb, union, ghost-state, smt, lifetime, bitvector]

requires:
  - phase: 51-core-language-features-i (plan 01)
    provides: Ty::Union, Ty::ConstGeneric, VcKind::UnionAccess IR scaffolding
provides:
  - HRTB universally quantified lifetime encoding in SMT preamble
  - Union ghost state active field tracking with UnionAccess VCs
  - generate_union_vcs function for linear block walk field tracking
  - extract_hrtb_bounds MIR converter for HRTB detection
affects: [52-advanced-type-system, 53-operator-smart-pointer]

tech-stack:
  added: []
  patterns: [linear-block-walk-ghost-state, universally-quantified-lifetime-encoding]

key-files:
  created:
    - crates/analysis/tests/hrtb_tests.rs
    - crates/analysis/tests/union_tests.rs
  modified:
    - crates/analysis/src/ir.rs
    - crates/analysis/src/vcgen.rs
    - crates/analysis/src/trait_analysis.rs
    - crates/driver/src/mir_converter.rs

key-decisions:
  - "HRTB lifetimes encoded as Int SMT constants with non-negative constraints (region identifiers)"
  - "Union ghost state follows MaybeUninit/RefCell linear block walk pattern for active field tracking"
  - "Active field read produces UNSAT VC (safe); inactive field read produces SAT VC (violation)"
  - "extract_hrtb_bounds detects for<'a> via bound_vars() on trait clauses in rustc predicates"

patterns-established:
  - "HRTB encoding: declare quantified lifetimes as Int constants in SMT preamble"
  - "Union VC generation: linear block walk tracking active_field ghost variable per union local"

requirements-completed: [LANG-02, LANG-03]

duration: 1906s
completed: 2026-03-07
---

# Phase 51 Plan 02: HRTB Lifetime Encoding & Union Type Verification Summary

**HRTB for<'a> bounds encoded as universally quantified SMT Int constants; union active field ghost state tracking with UnionAccess VCs for inactive field reads**

## Performance

- **Duration:** 1906s (~32 min)
- **Started:** 2026-03-07T04:24:23Z
- **Completed:** 2026-03-07T04:56:09Z
- **Tasks:** 2
- **Files modified:** 82 (80 for hrtb_bounds field propagation + 2 new test files)

## Accomplishments
- HRTB `for<'a>` bounds detected from rustc bound regions and encoded as universally quantified SMT Int constants
- Union ghost state tracking with active_field variable updated on field writes, checked on field reads
- Reading inactive union field generates UnionAccess VC (V130) -- SAT indicates violation
- Fixed pre-existing trait_analysis.rs issues from plan 51-01 scaffolding (Ty::Union match arms, Mutability::Shared)

## Task Commits

Each task was committed atomically:

1. **Task 1: HRTB universally quantified lifetime encoding** - `ba87935` (feat)
2. **Task 2: Union ghost state, reinterpretation VCs, MIR detection** - `e209503` (feat)

## Files Created/Modified
- `crates/analysis/src/ir.rs` - Added HrtbBound struct, hrtb_bounds field on Function
- `crates/analysis/src/vcgen.rs` - HRTB preamble encoding, generate_union_vcs function
- `crates/analysis/src/trait_analysis.rs` - Fixed Ty::Union match arms, Mutability::Shared
- `crates/driver/src/mir_converter.rs` - extract_hrtb_bounds for HRTB MIR detection
- `crates/analysis/tests/hrtb_tests.rs` - 5 HRTB tests
- `crates/analysis/tests/union_tests.rs` - 7 union tests

## Decisions Made
- HRTB lifetimes encoded as Int (region identifiers) in SMT -- universal quantification is implicit via constant declarations with non-negative constraints
- Union ghost state uses linear block walk (same pattern as MaybeUninit/RefCell) -- branch join analysis deferred
- Active field read = UNSAT (safe), inactive field read = SAT (violation) -- follows existing VcKind pattern
- extract_hrtb_bounds filters to Fn/FnMut/FnOnce traits only -- other HRTB bounds not relevant for verification

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 3 - Blocking] Fixed pre-existing trait_analysis.rs compilation errors**
- **Found during:** Task 1 (adding hrtb_bounds field)
- **Issue:** Plan 51-01 scaffolding left Ty::Union unmatched in has_drop_impl/is_unpin/has_copy_impl, and used non-existent Mutability::Immutable
- **Fix:** Added Ty::Union arms to all three functions, fixed Mutability::Immutable to Mutability::Shared
- **Files modified:** crates/analysis/src/trait_analysis.rs
- **Committed in:** ba87935

---

**Total deviations:** 1 auto-fixed (1 blocking)
**Impact on plan:** Fix was necessary for compilation. No scope creep.

## Issues Encountered
- rustc BoundRegionKind::Named API takes DefId (not symbol) in nightly-2026-02-11; fixed with tcx.item_name()

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- HRTB and union verification complete, ready for plan 51-03 (remaining LANG features)
- Union reinterpretation encoding reuses transmute bitvector pattern from Phase 50
- repr(C) layout assertions use offset-0 property of unions

---
*Phase: 51-core-language-features-i*
*Completed: 2026-03-07*
