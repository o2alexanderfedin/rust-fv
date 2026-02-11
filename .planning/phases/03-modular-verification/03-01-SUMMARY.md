---
phase: 03-modular-verification
plan: 01
subsystem: analysis
tags: [interprocedural, modular-verification, contract-database, call-site-encoding, z3]

# Dependency graph
requires:
  - phase: 02-table-stakes-completion
    provides: "Full VCGen pipeline with path-sensitive encoding, spec parser, SMT solver backend"
provides:
  - "ContractDatabase mapping function names to contracts with param metadata"
  - "Call-site VC encoding: assert-precondition, havoc-return, assume-postcondition"
  - "substitute_term for recursive term substitution at call sites"
  - "normalize_callee_name for MIR debug output parsing"
  - "Driver integration constructing ContractDatabase from HIR contracts"
affects: [03-02, trait-verification, higher-order-functions]

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "Modular call-site encoding via contract summaries"
    - "Term substitution for argument mapping at call sites"
    - "build_callee_func_context for parsing callee specs in caller context"

key-files:
  created:
    - "crates/analysis/src/contract_db.rs"
    - "crates/analysis/tests/interprocedural_tests.rs"
  modified:
    - "crates/analysis/src/vcgen.rs"
    - "crates/analysis/src/lib.rs"
    - "crates/driver/src/callbacks.rs"
    - "crates/driver/src/mir_converter.rs"

key-decisions:
  - "Optional ContractDatabase parameter for backward compatibility -- None preserves existing behavior"
  - "CallSiteInfo recorded during path traversal, not a separate pass"
  - "Callee postconditions asserted as positive assumptions (not negated) in caller postcondition VCs"
  - "build_callee_func_context constructs minimal Function for spec parsing from FunctionSummary"
  - "normalize_callee_name trims then strips 'const ' prefix then takes last :: segment"

patterns-established:
  - "Modular verification: each function checked independently using callee contracts as summaries"
  - "Call-site encoding: assert-precondition / havoc-return / assume-postcondition"
  - "Term substitution: callee param names mapped to actual argument terms recursively"

# Metrics
duration: 10min
completed: 2026-02-11
---

# Phase 3 Plan 1: Inter-procedural Contract Database and Call-Site Encoding Summary

**ContractDatabase with modular call-site VC encoding: assert callee preconditions, havoc return, assume postconditions for compositional verification of function call chains**

## Performance

- **Duration:** ~10 min
- **Started:** 2026-02-11T12:39:49Z
- **Completed:** 2026-02-11T12:49:25Z
- **Tasks:** 2
- **Files modified:** 14 (6 source + 8 test/bench files updated for new signature)

## Accomplishments
- ContractDatabase type with insert/get/contains for mapping function names to contracts
- Full call-site VC encoding in VCGen: precondition checking and postcondition assumption
- Driver constructs ContractDatabase from HIR-extracted contracts and passes to generate_vcs
- 10 new E2E inter-procedural tests all passing with Z3
- 231 total tests passing (10 new + 221 existing), zero clippy warnings

## Task Commits

Each task was committed atomically:

1. **Task 1: ContractDatabase and call-site encoding in VCGen** - `8574be4` (feat)
2. **Task 2: Driver integration and E2E inter-procedural tests** - `b7adf43` (feat)

## Files Created/Modified
- `crates/analysis/src/contract_db.rs` - ContractDatabase and FunctionSummary types with unit tests
- `crates/analysis/src/vcgen.rs` - generate_vcs accepts optional ContractDatabase, CallSiteInfo tracking, generate_call_site_vcs, encode_callee_postcondition_assumptions, substitute_term, normalize_callee_name
- `crates/analysis/src/lib.rs` - Added contract_db module declaration
- `crates/driver/src/callbacks.rs` - Constructs ContractDatabase from HIR and passes to generate_vcs
- `crates/driver/src/mir_converter.rs` - Made convert_ty public for driver callback access
- `crates/analysis/tests/interprocedural_tests.rs` - 10 E2E tests for inter-procedural verification
- `crates/analysis/tests/*.rs` (6 files) - Updated generate_vcs calls to pass None for backward compat
- `crates/analysis/benches/vcgen_bench.rs` - Updated generate_vcs calls to pass None

## Decisions Made
- Optional ContractDatabase parameter (None = backward compatible, Some = inter-procedural): ensures all 221 existing tests pass unchanged
- CallSiteInfo recorded inline during traverse_block rather than a separate CFG pass: simpler and captures path context
- Callee postconditions asserted positively in caller's postcondition VC: Z3 uses them as known facts
- build_callee_func_context creates minimal Function from FunctionSummary for spec parsing: avoids passing full callee IR
- normalize_callee_name handles MIR formatting variations: "const ", "::" paths, whitespace

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Fixed normalize_callee_name whitespace handling**
- **Found during:** Task 2 (E2E tests)
- **Issue:** Leading whitespace before "const " prefix was not handled (trim after strip_prefix missed the case)
- **Fix:** Trim input first, then strip "const " prefix
- **Files modified:** crates/analysis/src/vcgen.rs
- **Verification:** test_normalize_callee_name passes for all variants including "  const foo  "
- **Committed in:** b7adf43 (Task 2 commit)

---

**Total deviations:** 1 auto-fixed (1 bug)
**Impact on plan:** Minor fix for edge case. No scope creep.

## Issues Encountered
None - plan executed smoothly.

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- Inter-procedural verification infrastructure is complete
- Ready for Phase 3 Plan 2 (trait/generic verification or additional modular features)
- ContractDatabase and call-site encoding patterns can be extended for trait method dispatch

## Self-Check: PASSED

- All 6 key files: FOUND
- Commit 8574be4 (Task 1): FOUND
- Commit b7adf43 (Task 2): FOUND
- Total tests: 231 (all passing)
- Clippy warnings: 0

---
*Phase: 03-modular-verification*
*Completed: 2026-02-11*
