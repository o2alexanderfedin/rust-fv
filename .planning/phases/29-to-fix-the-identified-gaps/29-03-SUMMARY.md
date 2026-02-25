---
phase: 29-to-fix-the-identified-gaps
plan: 03
subsystem: formal-verification
tags: [rust, mir, ir, aggregate, struct, enum, closure, set-discriminant, assume, vcgen]

# Dependency graph
requires:
  - phase: 29-to-fix-the-identified-gaps/29-01
    provides: CastKind exhaustive match + Phase 29 TDD scaffold with 10 RED tests
  - phase: 28-smt-vcgen-completeness
    provides: AggregateKind::Struct/Enum/Closure in ir.rs and encode_aggregate in encode_term.rs
provides:
  - ir::Statement::SetDiscriminant(Place, usize) variant in ir.rs
  - ir::Statement::Assume(Operand) variant in ir.rs
  - convert_rvalue handles AggregateKind::Adt and Closure in mir_converter.rs
  - convert_statement handles SetDiscriminant and Assume intrinsic in mir_converter.rs
affects:
  - 29-05 (VCGEN-06 SetDiscriminant assertion encoding — depends on IR variant existing)
  - vcgen.rs (SetDiscriminant/Assume appear in Statement enum, no-op for now)

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "AggregateKind::Adt maps to ir::AggregateKind::Enum for both structs (variant_idx=0) and enums"
    - "NonDivergingIntrinsic is Box-wrapped in StatementKind::Intrinsic — pattern as `box mir::NonDivergingIntrinsic::Assume(op)`"
    - "New Statement variants use if-let patterns in vcgen.rs (no exhaustive match required)"

key-files:
  created: []
  modified:
    - crates/analysis/src/ir.rs
    - crates/driver/src/mir_converter.rs
    - crates/analysis/tests/vcgen_completeness29.rs

key-decisions:
  - "AggregateKind::Adt used for both structs and enums — map to ir::AggregateKind::Enum with variant_idx (0 for structs)"
  - "NonDivergingIntrinsic is Box-wrapped in nightly MIR; pattern requires `box` binding"
  - "SetDiscriminant and Assume are no-ops in vcgen for now — IR representation is the goal; VCGen encoding deferred to Plan 05"
  - "mirconv_02_set_discriminant test un-ignored as IR round-trip test (vcgen must not panic)"

patterns-established:
  - "Aggregate: compute ir_ops before ir_kind match (avoids borrow issues with operands moved into closure)"

requirements-completed: [MIRCONV-02]

# Metrics
duration: 16min
completed: 2026-02-25
---

# Phase 29 Plan 03: MIRCONV-02 Aggregate Conversion + SetDiscriminant/Assume IR Variants Summary

**ir::Statement extended with SetDiscriminant and Assume variants; mir_converter Aggregate arm now handles Adt/Closure kinds (not just Tuple), closing the silent-skip gap for struct/enum construction in MIR-to-IR translation**

## Performance

- **Duration:** 16 min
- **Started:** 2026-02-25T04:18:54Z
- **Completed:** 2026-02-25T04:34:42Z
- **Tasks:** 1
- **Files modified:** 3

## Accomplishments
- Added `Statement::SetDiscriminant(Place, usize)` and `Statement::Assume(Operand)` to `ir::Statement` enum
- Fixed `convert_rvalue` Aggregate arm: `AggregateKind::Adt` now maps to `ir::AggregateKind::Enum`, `Closure` maps to `ir::AggregateKind::Closure` (previously both returned `None`)
- Wired `StatementKind::SetDiscriminant` and `StatementKind::Intrinsic(Assume)` in `convert_statement`
- Un-ignored and implemented `mirconv_02_set_discriminant` test as IR round-trip test
- All 3 `mirconv_02` tests GREEN; Phase 28 regression suite 10/10 GREEN; clean clippy

## Task Commits

1. **Task 1: Add SetDiscriminant+Assume variants; wire Adt/Closure aggregates** - `65b7368` (feat)

## Files Created/Modified
- `crates/analysis/src/ir.rs` - Added `SetDiscriminant(Place, usize)` and `Assume(Operand)` to `Statement` enum
- `crates/driver/src/mir_converter.rs` - Fixed Aggregate arm; added SetDiscriminant/Assume arms in `convert_statement`
- `crates/analysis/tests/vcgen_completeness29.rs` - Un-ignored and implemented `mirconv_02_set_discriminant` test

## Decisions Made
- `AggregateKind::Adt` maps to `ir::AggregateKind::Enum(name, variant_idx)` for both structs (variant_idx=0) and enums — the IR Enum variant handles both uniformly
- `NonDivergingIntrinsic` is `Box`-wrapped in `StatementKind::Intrinsic`; discovered during compilation that the pattern requires `box` binding
- VCGen treats `SetDiscriminant` and `Assume` as no-ops (fall through via `if let Statement::Assign(...)` pattern in vcgen.rs) — correct since VCGen encoding is deferred to Plan 05
- mirconv_02_set_discriminant re-implemented as a no-panic IR round-trip test (confirms variant exists and vcgen handles it gracefully)

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Box-wrapped NonDivergingIntrinsic pattern**
- **Found during:** Task 1 (wiring Assume in convert_statement)
- **Issue:** Plan showed `mir::StatementKind::Intrinsic(mir::NonDivergingIntrinsic::Assume(op))` but actual rustc type has `Box<NonDivergingIntrinsic<'_>>`
- **Fix:** Changed pattern to `mir::StatementKind::Intrinsic(box mir::NonDivergingIntrinsic::Assume(op))`
- **Files modified:** crates/driver/src/mir_converter.rs
- **Verification:** `cargo build -p rust-fv-driver` clean; no errors
- **Committed in:** 65b7368

---

**Total deviations:** 1 auto-fixed (Rule 1 - Bug, Box-wrapped intrinsic pattern)
**Impact on plan:** Necessary correctness fix; no scope creep.

## Issues Encountered
None beyond the Box-wrapping deviation noted above (auto-fixed).

## Next Phase Readiness
- MIRCONV-02 satisfied: struct/enum/closure aggregates now produce IR `Rvalue::Aggregate` (not `None`)
- `ir::Statement::SetDiscriminant` exists for Plan 05 (VCGEN-06 SetDiscriminant assertion encoding)
- Plan 04 (VCGEN-05 float-to-int fp.to_sbv/fp.to_ubv encoding) can proceed independently

---
*Phase: 29-to-fix-the-identified-gaps*
*Completed: 2026-02-25*
