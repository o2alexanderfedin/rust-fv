---
phase: 29-to-fix-the-identified-gaps
plan: 02
subsystem: vcgen
tags: [smt, encode_term, float-to-int, fp.to_sbv, fp.to_ubv, RTZ, soundness]

# Dependency graph
requires:
  - phase: 29-01
    provides: CastKind exhaustive match in mir_converter, Phase 29 TDD scaffold (10 RED tests)
  - phase: 28-02
    provides: encode_cast() dispatcher and Rvalue::Cast wiring in vcgen.rs
provides:
  - encode_float_to_int_cast using fp.to_sbv/fp.to_ubv with RTZ rounding mode
  - encode_cast signature with to_signed: bool parameter
  - VCGEN-05 satisfied — soundness hole from Term::Extract on Float sort eliminated
  - mirconv_01_float_to_int_cast_kind test now GREEN (bonus)
affects:
  - 29-03 (aggregate conversion)
  - 29-04 (assumed correctness of float cast SMT encoding)

# Tech tracking
tech-stack:
  added: []
  patterns:
    - fp.to_sbv/fp.to_ubv with RTZ rounding mode for float-to-int casts (matching Rust as-cast semantics)
    - to_signed parameter threading from target type through encode_cast to encode_float_to_int_cast

key-files:
  created: []
  modified:
    - crates/analysis/src/encode_term.rs
    - crates/analysis/src/vcgen.rs
    - crates/analysis/src/monomorphize.rs

key-decisions:
  - "encode_cast adds to_signed: bool parameter — cleaner than passing full target Ty; for non-FloatToInt casts to_signed is unused"
  - "RTZ (round toward zero) rounding mode matches Rust's float-as-integer truncation semantics for as-casts"
  - "Term::Extract on Float sort was a type error in SMT-LIB2; fp.to_sbv/fp.to_ubv is the type-correct FPA-to-BV operator"

patterns-established:
  - "Pattern: encode_float_to_int_cast uses Term::App with indexed operator string '(_ fp.to_sbv N)' or '(_ fp.to_ubv N)' and RTZ rounding mode term as first argument"

requirements-completed: [VCGEN-05]

# Metrics
duration: 13min
completed: 2026-02-25
---

# Phase 29 Plan 02: Fix Float-to-Int SMT Encoding Summary

**Float-to-int cast encoding fixed from type-erroneous Term::Extract to type-correct SMT-LIB2 fp.to_sbv/fp.to_ubv with RTZ rounding, eliminating soundness hole and turning VCGEN-05 tests GREEN.**

## Performance

- **Duration:** 13 min
- **Started:** 2026-02-25T04:16:31Z
- **Completed:** 2026-02-25T04:29:00Z
- **Tasks:** 1
- **Files modified:** 3 (encode_term.rs, vcgen.rs, monomorphize.rs)

## Accomplishments

- Replaced `Term::Extract(to_bits - 1, 0, Box::new(src))` with proper FPA-to-BV operators `fp.to_sbv`/`fp.to_ubv` with RTZ rounding mode
- Added `to_signed: bool` parameter to `encode_cast` and `encode_float_to_int_cast`; vcgen.rs call site passes `ty_is_signed(target_ty)`
- vcgen_05_float_to_int_signed and vcgen_05_float_to_int_unsigned both GREEN
- mirconv_01_float_to_int_cast_kind also turned GREEN (same fix path)
- All 10 Phase 28 regression tests remain GREEN; full clippy + fmt clean

## Task Commits

1. **Task 1: Fix encode_float_to_int_cast to use fp.to_sbv/fp.to_ubv** - `9bd0740` (fix)

**Plan metadata:** (docs commit pending)

## Files Created/Modified

- `crates/analysis/src/encode_term.rs` - encode_float_to_int_cast replaced; encode_cast signature updated with to_signed
- `crates/analysis/src/vcgen.rs` - encode_cast call site updated to pass to_signed from target_ty
- `crates/analysis/src/monomorphize.rs` - auto-fix: added SetDiscriminant and Assume arms to exhaustive match

## Decisions Made

- `encode_cast` adds `to_signed: bool` rather than passing full `Ty` — cleaner API, non-FloatToInt arms ignore it
- RTZ rounding mode chosen to match Rust's truncation-toward-zero semantics for `f64 as i32`
- Soundness fix: `Term::Extract` on Float sort is a type error in SMT-LIB2 (extract requires BitVec); fp.to_sbv/fp.to_ubv is the correct FPA conversion operator

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 3 - Blocking] Non-exhaustive match in monomorphize.rs after Phase 29-01 added Statement variants**
- **Found during:** Task 1 (pre-commit hook ran clippy)
- **Issue:** `monomorphize.rs:138` had match on `Statement` missing `SetDiscriminant` and `Assume` arms — these were added in Phase 29-01 but the exhaustive match was not updated
- **Fix:** Added `Statement::SetDiscriminant(place, idx) => Statement::SetDiscriminant(place.clone(), *idx)` and `Statement::Assume(op) => Statement::Assume(op.clone())` arms
- **Files modified:** `crates/analysis/src/monomorphize.rs`
- **Verification:** cargo clippy passes clean
- **Committed in:** `9bd0740` (part of Task 1 commit)

**2. [Rule 3 - Blocking] Rustfmt formatting in mir_converter.rs (pre-existing)**
- **Found during:** Task 1 (pre-commit hook ran rustfmt)
- **Issue:** `mir_converter.rs:181` SetDiscriminant match arm had formatting style rustfmt preferred to reformat
- **Fix:** `cargo fmt` applied
- **Files modified:** `crates/driver/src/mir_converter.rs`
- **Verification:** rustfmt check passes
- **Committed in:** `9bd0740` (part of Task 1 commit)

---

**Total deviations:** 2 auto-fixed (both Rule 3 - blocking pre-commit issues)
**Impact on plan:** Both auto-fixes required to pass pre-commit hooks. No scope creep.

## Issues Encountered

None — straightforward implementation of plan steps.

## Next Phase Readiness

- Plan 03 (MIRCONV-02 aggregate conversion) can proceed; vcgen float-to-int is now sound
- mirconv_01 and vcgen_05 tests GREEN; 8 remaining Phase 29 tests still need their respective plans

---
*Phase: 29-to-fix-the-identified-gaps*
*Completed: 2026-02-25*
