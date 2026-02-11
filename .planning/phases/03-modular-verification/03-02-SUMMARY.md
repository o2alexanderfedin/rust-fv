---
phase: 03-modular-verification
plan: 02
subsystem: analysis
tags: [ownership, move-semantics, borrow-checker, shared-borrow, mutable-borrow, interprocedural, z3]

# Dependency graph
requires:
  - phase: 03-modular-verification
    plan: 01
    provides: "ContractDatabase, call-site encoding (assert-pre/havoc/assume-post), substitute_term"
provides:
  - "OwnershipKind enum classifying arguments as Moved/Copied/SharedBorrow/MutableBorrow"
  - "classify_argument deriving ownership from IR operand and parameter type"
  - "generate_ownership_constraints producing preservation/havoc/consumed constraints"
  - "Value-preservation constraints for SharedBorrow and Copied arguments at call sites"
  - "Mutable borrow havoc: no preservation constraint for &mut arguments"
affects: [trait-verification, higher-order-functions, lifetime-analysis]

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "Ownership classification from IR operand kind and parameter type"
    - "Pre-call snapshot variables for value preservation after calls"
    - "Constraint encoding: SharedBorrow/Copied -> preserve, MutableBorrow -> havoc, Moved -> consume"

key-files:
  created:
    - "crates/analysis/src/ownership.rs"
    - "crates/analysis/tests/ownership_tests.rs"
  modified:
    - "crates/analysis/src/vcgen.rs"
    - "crates/analysis/src/lib.rs"

key-decisions:
  - "Param type takes precedence over operand kind for ownership classification (Ref types override Move/Copy)"
  - "Pre-call snapshot via DeclareConst + assertion pairs for value preservation"
  - "Bounded callee return contracts to prevent bitvector overflow in E2E tests"
  - "No driver changes needed: ownership analysis driven entirely by VCGen from ContractDatabase param types"

patterns-established:
  - "Ownership-aware call-site encoding: classify arguments, generate constraints, encode in SMT"
  - "Pre-call snapshot pattern: declare snapshot var, assert == before call, assert == after call"
  - "Bitvector-safe test design: bound all intermediate values to prevent signed overflow"

# Metrics
duration: 11min
completed: 2026-02-11
---

# Phase 3 Plan 2: Ownership-Aware Verification Summary

**Ownership classification (Moved/Copied/SharedBorrow/MutableBorrow) with pre-call snapshot constraints encoding Rust's move/borrow semantics into inter-procedural verification conditions**

## Performance

- **Duration:** ~11 min
- **Started:** 2026-02-11T12:52:23Z
- **Completed:** 2026-02-11T13:03:40Z
- **Tasks:** 2
- **Files modified:** 4 (2 created, 2 modified)

## Accomplishments
- OwnershipKind enum with 4 variants classifying call arguments by ownership semantics
- classify_argument function deriving ownership from IR operand and parameter type
- VCGen integration: SharedBorrow/Copied arguments get pre-call snapshot preservation constraints
- MutableBorrow arguments correctly havoced (no preservation constraint added)
- 12 new E2E tests verifying ownership-aware verification with Z3
- 243 total tests passing (12 new ownership + 231 existing), zero clippy warnings

## Task Commits

Each task was committed atomically:

1. **Task 1: Ownership classification and constraint generation** - `8ced451` (feat)
2. **Task 2: Driver integration and E2E ownership tests** - `8ffa8f4` (feat)

## Files Created/Modified
- `crates/analysis/src/ownership.rs` - OwnershipKind enum, classify_argument, generate_ownership_constraints, 11 unit tests
- `crates/analysis/src/lib.rs` - Added ownership module declaration
- `crates/analysis/src/vcgen.rs` - Integrated ownership constraints into encode_callee_postcondition_assumptions, added encode_ownership_constraints_at_call_site
- `crates/analysis/tests/ownership_tests.rs` - 12 E2E tests for ownership-aware verification

## Decisions Made
- Parameter type takes precedence over operand kind: `Ty::Ref(_, Shared)` always yields SharedBorrow, even with `Operand::Move` -- the ref type carries the true semantic meaning
- Pre-call snapshot mechanism for value preservation: declare `{var}_pre_call_{block}` constant, assert `snapshot == var` before call and `var == snapshot` after -- this is idempotent and composable across multiple calls
- Callee return contracts bounded in tests to prevent bitvector signed overflow -- necessary because BV32 addition wraps and makes signed comparisons unsound for large values
- No driver changes required: ownership analysis is entirely driven by the VCGen reading callee param types from ContractDatabase's FunctionSummary

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Fixed bitvector overflow in E2E test postconditions**
- **Found during:** Task 2 (E2E tests)
- **Issue:** Tests using `result >= _1` with unbounded callee returns failed because BV32 addition of large positive values wraps to negative
- **Fix:** Bounded callee return contracts to small ranges (e.g., `result >= 0 && result <= 100`) to prevent overflow
- **Files modified:** crates/analysis/tests/ownership_tests.rs
- **Verification:** All 12 E2E tests pass with correct SAT/UNSAT results
- **Committed in:** 8ffa8f4 (Task 2 commit)

---

**Total deviations:** 1 auto-fixed (1 bug in test design)
**Impact on plan:** Minor test adjustment for bitvector arithmetic soundness. No scope creep.

## Issues Encountered
None - plan executed smoothly after the bitvector overflow fix.

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- Phase 3 (Modular Verification) is complete
- Inter-procedural verification with ownership reasoning works end-to-end
- ContractDatabase + call-site encoding + ownership constraints provide a solid foundation for:
  - Trait method dispatch verification
  - Higher-order function contracts
  - Lifetime-aware verification
- Ready for Phase 4 (next milestone features)

## Self-Check: PASSED

- All 4 key files: FOUND
- Commit 8ced451 (Task 1): FOUND
- Commit 8ffa8f4 (Task 2): FOUND
- All test result lines: ok (22 test runners, 0 failures)
- Clippy warnings: 0

---
*Phase: 03-modular-verification*
*Completed: 2026-02-11*
