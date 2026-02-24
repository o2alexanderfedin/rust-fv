---
phase: 28-smt-vcgen-completeness
plan: "01"
subsystem: testing
tags: [tdd, vcgen, smt, rust, formal-verification, vcgen-completeness]

# Dependency graph
requires: []
provides:
  - "TDD scaffold: 10 test functions for VCGEN-01..04 (array bounds, discriminant, casts, generics)"
  - "RED-phase baseline: 9 tests fail with logic assertions, 1 passes as regression guard"
affects:
  - 28-02-PLAN.md
  - 28-03-PLAN.md
  - 28-04-PLAN.md
  - 28-05-PLAN.md

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "build_*_function() helpers: construct minimal Function IR for specific test scenarios"
    - "make_func() base helper: all IR fields defaulted, only required fields specified"
    - "script_to_text() local utility: SMT script to string for assertion-based checking"
    - "Contract-forced VCs: add minimal postcondition to force VC generation in no-assertion functions"

key-files:
  created:
    - crates/analysis/tests/vcgen_completeness28.rs
  modified: []

key-decisions:
  - "vcgen_01_array_index tests VCGen auto-generation of bounds VCs for Projection::Index (not Assert terminator), matching VCGEN-01 spec intent"
  - "vcgen_01_field_projection kept as regression guard (field selection already works via encode_place_with_type)"
  - "vcgen_01_slice_len checks for assignment form '(assert (= _0 <len>))' not postcondition form to properly distinguish Len encoding from postcondition references"
  - "Cast tests add tautological postcondition 'true' to force VC generation without requiring non-trivial contract"
  - "VCGEN-04 generic tests fail with encode_sort panic 'Cannot encode generic type parameter T' — valid RED failure mode (missing implementation)"

patterns-established:
  - "RED test pattern: assert specific SMT text patterns, NOT just VC count, to properly distinguish implemented vs stub behavior"

requirements-completed:
  - VCGEN-01
  - VCGEN-02
  - VCGEN-03
  - VCGEN-04

# Metrics
duration: 14min
completed: 2026-02-24
---

# Phase 28 Plan 01: VCGEN-01..04 TDD Test Scaffold Summary

**10-test RED scaffold for VCGen completeness: bounds check, discriminant, int cast, generic trait bound — all failing before implementation**

## Performance

- **Duration:** 14 min
- **Started:** 2026-02-24T09:22:46Z
- **Completed:** 2026-02-24T09:36:37Z
- **Tasks:** 1
- **Files modified:** 1

## Accomplishments

- Created `crates/analysis/tests/vcgen_completeness28.rs` with all 10 required test functions
- 9 tests fail RED with clear assertion messages documenting what is missing
- 1 test (`vcgen_01_field_projection`) passes as regression guard for working field selector encoding
- File auto-discovered by `cargo test -p rust-fv-analysis --test vcgen_completeness28`
- Cargo fmt + clippy pass with no warnings

## Task Commits

1. **Task 1: TDD test scaffold (RED phase)** - `d900436` (test)

## Files Created/Modified

- `crates/analysis/tests/vcgen_completeness28.rs` - 10 test functions for VCGEN-01..04 with builder helpers and SMT text utilities

## Decisions Made

- `vcgen_01_array_index` tests VCGen auto-generation for `Projection::Index` (not `Assert(BoundsCheck)` terminator), matching the VCGEN-01 spec: "no bounds VC generated for Index projections"
- `vcgen_01_field_projection` kept as passing regression guard since `encode_place_with_type` + field projection already works
- `vcgen_01_slice_len` assertion distinguishes assignment form `(assert (= _0 ...))` from postcondition form `(assert (not ...))` to properly detect whether Len is encoded
- `build_cast_function` adds tautological postcondition `true` to force VC generation; cast encoding tests then check specific SMT patterns (sign_extend, extract, non-identity)
- VCGEN-04 generic tests fail via `encode_sort` panic for Generic("T") type — accepted as valid RED failure mode

## Deviations from Plan

None — plan executed exactly as written. The `vcgen_01_field_projection` test was noted as "may already pass" in the plan, and it does pass as intended.

## Issues Encountered

- Initial test for `vcgen_01_slice_len` passed falsely because `all_smt.contains("5")` matched the postcondition text `(assert (not (= _0 5)))`. Fixed by checking for assignment form specifically.
- `vcgen_01_array_index` initially used `Assert(BoundsCheck)` terminator (which passes); reverted to bare Projection::Index without Assert to properly test auto-generation.

## Next Phase Readiness

- All 10 test contracts established as behavioral spec for Plans 02-05
- Plan 02: implement `encode_int_to_int_cast` (VCGEN-03) — tests vcgen_03_cast_sign_extend, vcgen_03_cast_truncate, vcgen_03_transmute
- Plan 03: implement `Rvalue::Discriminant` encoding + `Rvalue::Len` encoding (VCGEN-01, VCGEN-02)
- Plan 04: implement `trait_bounds_as_smt_assumptions` and generic param handling (VCGEN-04)
- Plan 05: implement auto-generated bounds VCs for `Projection::Index` (VCGEN-01)

---
*Phase: 28-smt-vcgen-completeness*
*Completed: 2026-02-24*
