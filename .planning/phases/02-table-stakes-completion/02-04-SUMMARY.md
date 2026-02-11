---
phase: 02-table-stakes-completion
plan: 04
subsystem: analysis
tags: [smt, datatypes, structs, tuples, enums, arrays, z3, bitvectors, vcgen]

# Dependency graph
requires:
  - phase: 02-01
    provides: "Z3 native backend, tracing, DeclareDatatype command infrastructure"
provides:
  - "SMT datatype declarations for structs, tuples, and enums"
  - "Field selector encoding (Term::App with selector name)"
  - "Aggregate constructor encoding (Term::App with constructor name)"
  - "Type-aware projection resolution in VCGen (encode_place_with_type)"
  - "Spec parser support for result.field syntax"
  - "Signedness inference from struct/tuple field types in comparisons"
  - "8 E2E tests for aggregate encoding with Z3"
affects: [02-05, 03-driver, 03-generics]

# Tech tracking
tech-stack:
  added: []
  patterns: ["QF_UFBVDT logic for datatypes+bitvectors", "selector/constructor naming convention", "type-aware spec operand parsing"]

key-files:
  created:
    - "crates/analysis/tests/aggregate_encoding.rs"
  modified:
    - "crates/smtlib/src/command.rs"
    - "crates/smtlib/src/formatter.rs"
    - "crates/analysis/src/encode_sort.rs"
    - "crates/analysis/src/encode_term.rs"
    - "crates/analysis/src/vcgen.rs"
    - "crates/solver/src/solver.rs"
    - "crates/analysis/tests/soundness_suite.rs"
    - "crates/analysis/tests/completeness_suite.rs"
    - "crates/analysis/tests/e2e_verification.rs"

key-decisions:
  - "QF_UFBVDT logic when datatypes present (QF_UFDT lacks bitvectors, QF_BV lacks datatypes)"
  - "Selector naming: {TypeName}-{field_name} for structs, Tuple{N}-_{idx} for tuples, {VariantName}-{idx} for enums"
  - "Constructor naming: mk-{TypeName} for structs/tuples, mk-{VariantName} for enum variants"
  - "Signedness inferred from field types for struct/tuple field comparisons in specs"

patterns-established:
  - "Aggregate E2E test pattern: build IR with Rvalue::Aggregate, generate VCs, verify with Z3"
  - "DeclareDatatype before DeclareConst in SMT scripts (sort declarations before use)"
  - "Type-aware operand encoding via encode_operand_for_vcgen helper"

# Metrics
duration: ~30min
completed: 2026-02-11
---

# Phase 2 Plan 4: Aggregate Encoding Summary

**SMT datatype declarations for structs/tuples/enums with constructor/selector encoding, field-aware spec parsing, and 8 E2E Z3 tests**

## Performance

- **Duration:** ~30 min
- **Started:** 2026-02-11T11:00:00Z
- **Completed:** 2026-02-11T11:33:42Z
- **Tasks:** 2
- **Files modified:** 10 (3 created, 7 modified)

## Accomplishments
- Structs, tuples, and enums produce DeclareDatatype commands with correct SMT-LIB 2.6 syntax accepted by Z3
- Field access in specifications (`result.x > 0`) correctly encodes as selector application on the return value
- Aggregate construction (`Point { x: 1, y: 2 }`) correctly encodes as constructor application
- Signed/unsigned comparison inference works with struct field types (e.g., `result.x` on `Ty::Int(IntTy::I32)` uses `bvsgt` not `bvugt`)
- 353 tests passing across the workspace (345 pre-existing + 8 new), zero clippy warnings

## Task Commits

Each task was committed atomically:

1. **Task 1: SMT datatype declarations for structs, tuples, and enums** - `6110a09` (feat)
2. **Task 2: Aggregate construction, field access in VCGen, and E2E tests** - `991069d` (feat)

## Files Created/Modified
- `crates/smtlib/src/command.rs` - Added DatatypeVariant struct and DeclareDatatype command variant
- `crates/smtlib/src/formatter.rs` - Display impl for DeclareDatatype with multi-variant and field support
- `crates/analysis/src/encode_sort.rs` - Sort::Datatype for structs/tuples/enums, collect_datatype_declarations function
- `crates/analysis/src/encode_term.rs` - encode_place_with_type, encode_field_access, encode_aggregate, encode_aggregate_with_type
- `crates/analysis/src/vcgen.rs` - Datatype-aware base_script, aggregate Rvalue handling, result.field spec parsing, signedness inference
- `crates/solver/src/solver.rs` - DeclareDatatype handling in format_command
- `crates/analysis/tests/aggregate_encoding.rs` - 8 E2E tests (struct/tuple/array/enum encoding)
- `crates/analysis/tests/soundness_suite.rs` - DeclareDatatype in test formatter
- `crates/analysis/tests/completeness_suite.rs` - DeclareDatatype in test formatter
- `crates/analysis/tests/e2e_verification.rs` - DeclareDatatype in test formatter

## Decisions Made
- **QF_UFBVDT logic:** Z3's QF_UFDT logic does not support bitvectors, and QF_BV does not support user-defined datatypes. The combined QF_UFBVDT logic supports both. This was discovered during E2E testing when Z3 rejected "unknown sort 'BitVec'" under QF_UFDT.
- **Selector naming convention:** `{TypeName}-{field_name}` ensures global uniqueness in the SMT script. This matches the SMT-LIB 2.6 convention for algebraic datatype selectors.
- **Field-aware signedness inference:** When comparing `result.x > 0` where the return type is a struct, the comparison signedness is inferred from the field type (i32 = signed) rather than the struct type itself. Implemented via `infer_signedness_from_context` which resolves selector names to field types.

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Fixed QF_UFDT logic to QF_UFBVDT**
- **Found during:** Task 2 (E2E testing)
- **Issue:** Z3 rejected DeclareDatatype scripts under QF_UFDT with "unknown sort 'BitVec'" because QF_UFDT does not include bitvector theory
- **Fix:** Changed logic from QF_UFDT to QF_UFBVDT which combines uninterpreted functions, bitvectors, and datatypes
- **Files modified:** crates/analysis/src/vcgen.rs
- **Verification:** All 8 E2E tests pass with Z3
- **Committed in:** 991069d (Task 2 commit)

**2. [Rule 1 - Bug] Fixed signedness inference for struct field comparisons in specs**
- **Found during:** Task 2 (test_struct_field_postcondition_negative)
- **Issue:** `result.x > 0` on a Point struct used unsigned comparison (`bvugt`) because `make_comparison` only checked the return type (struct, not signed) and first param. With x = -1 (0xFFFFFFFF unsigned), unsigned comparison made -1 > 0 true, producing wrong UNSAT result
- **Fix:** Added `infer_signedness_from_context` that resolves selector application terms to their field types, enabling correct signed comparison for struct/tuple field accesses
- **Files modified:** crates/analysis/src/vcgen.rs
- **Verification:** test_struct_field_postcondition_negative correctly returns SAT (counterexample found)
- **Committed in:** 991069d (Task 2 commit)

---

**Total deviations:** 2 auto-fixed (2 bugs)
**Impact on plan:** Both auto-fixes necessary for correctness. The QF_UFBVDT fix was required for Z3 to accept any script combining datatypes and bitvectors. The signedness fix was required for correct verification of specifications on aggregate fields.

## Issues Encountered
None beyond the auto-fixed issues documented above.

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- Aggregate type encoding complete: structs, tuples, enums, arrays all work with Z3
- Success Criterion 5 verified: `#[ensures(result.x > 0)]` style specs work end-to-end
- Ready for Phase 2 remaining plans (02-02 loops, 02-03 enums, 02-05 error messages)

## Self-Check: PASSED

All key files verified present. Both task commits (6110a09, 991069d) verified in git log.

---
*Phase: 02-table-stakes-completion*
*Completed: 2026-02-11*
