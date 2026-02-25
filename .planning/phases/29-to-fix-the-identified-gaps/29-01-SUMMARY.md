---
phase: 29-to-fix-the-identified-gaps
plan: 01
subsystem: mir-converter, vcgen-tdd
tags: [tdd, cast-kinds, mir-conversion, regression-guard]
dependency_graph:
  requires: []
  provides: [MIRCONV-01, vcgen_completeness29_scaffold]
  affects: [mir_converter.rs, vcgen.rs, encode_term.rs]
tech_stack:
  added: []
  patterns: [tdd-red-green, exhaustive-match, cast-kind-preservation]
key_files:
  created:
    - crates/analysis/tests/vcgen_completeness29.rs
  modified:
    - crates/driver/src/mir_converter.rs
decisions:
  - "CastKind fix uses exhaustive match (not wildcard) so compiler enforces completeness on MIR API changes"
  - "mirconv_01_int_to_float_cast_kind is GREEN immediately — encode_term already handles IntToFloat correctly"
  - "mirconv_02 aggregate tests are GREEN as regression guards — vcgen handles Struct/Enum aggregates at IR level"
  - "VCGEN-05 tests assert fp.to_sbv/fp.to_ubv — RED until Plan 02 fixes encode_float_to_int_cast"
  - "VCGEN-06 field mutation tests are RED until Plan 05 adds projected LHS functional update"
  - "SetDiscriminant tests are #[ignore] — ir::Statement::SetDiscriminant does not exist (Plan 03)"
metrics:
  duration: 342
  completed: 2026-02-24
  tasks_completed: 2
  files_changed: 2
---

# Phase 29 Plan 01: TDD Scaffold + CastKind Preservation (MIRCONV-01) Summary

Established Phase 29 TDD scaffold with 10 tests covering MIRCONV-01/02 and VCGEN-05/06, then fixed the soundness hole in mir_converter.rs: all float casts were previously collapsed to IntToInt; now FloatToInt/IntToFloat/FloatToFloat/Pointer kinds are correctly preserved through MIR→IR conversion.

## Tasks Completed

| Task | Name | Commit | Files |
|------|------|--------|-------|
| 1 | RED: Add 10 tests in vcgen_completeness29.rs | 806982d | crates/analysis/tests/vcgen_completeness29.rs |
| 2 | GREEN: Fix CastKind mapping in mir_converter.rs | e00c3ee | crates/driver/src/mir_converter.rs |

## Test Status After Plan 01

| Test | Status | Fixed by |
|------|--------|----------|
| mirconv_01_float_to_int_cast_kind | RED | Plan 02 (fp.to_sbv encoding) |
| mirconv_01_int_to_float_cast_kind | GREEN | Already correct (encode_term) |
| mirconv_02_struct_aggregate | GREEN | Already correct (vcgen IR layer) |
| mirconv_02_enum_aggregate | GREEN | Already correct (vcgen IR layer) |
| mirconv_02_set_discriminant | IGNORED | Plan 03 (ir::Statement::SetDiscriminant) |
| vcgen_05_float_to_int_signed | RED | Plan 02 (fp.to_sbv) |
| vcgen_05_float_to_int_unsigned | RED | Plan 02 (fp.to_ubv) |
| vcgen_06_struct_field_mutation | RED | Plan 05 (projected LHS) |
| vcgen_06_field_mutation_use | RED | Plan 05 (projected LHS) |
| vcgen_06_set_discriminant_assertion | IGNORED | Plan 03/05 |

## Changes Made

### crates/analysis/tests/vcgen_completeness29.rs (CREATED)

Phase 29 TDD scaffold with 10 test functions. Mirrors vcgen_completeness28.rs structure with `make_func`, `build_cast_function`, and `script_to_text` helpers. Tests directly exercise the IR layer (bypassing mir_converter) to isolate vcgen behavior.

### crates/driver/src/mir_converter.rs (MODIFIED)

Fixed `convert_rvalue` Cast arm:

**Before (BUG):**
```rust
mir::Rvalue::Cast(_, op, ty) => {
    let ir_ty = convert_ty(*ty);
    Some(ir::Rvalue::Cast(
        ir::CastKind::IntToInt,   // hardcoded — ALL casts treated as integer
        convert_operand(op),
        ir_ty,
    ))
}
```

**After (FIXED):**
```rust
mir::Rvalue::Cast(kind, op, ty) => {
    let ir_ty = convert_ty(*ty);
    let ir_kind = match kind {
        mir::CastKind::IntToInt     => ir::CastKind::IntToInt,
        mir::CastKind::FloatToInt   => ir::CastKind::FloatToInt,
        mir::CastKind::IntToFloat   => ir::CastKind::IntToFloat,
        mir::CastKind::FloatToFloat => ir::CastKind::FloatToFloat,
        mir::CastKind::PtrToPtr
        | mir::CastKind::FnPtrToPtr
        | mir::CastKind::PointerCoercion(..)
        | mir::CastKind::PointerExposeProvenance
        | mir::CastKind::PointerWithExposedProvenance => ir::CastKind::Pointer,
        mir::CastKind::Transmute => ir::CastKind::IntToInt,
        mir::CastKind::Subtype   => ir::CastKind::IntToInt,
    };
    Some(ir::Rvalue::Cast(ir_kind, convert_operand(op), ir_ty))
}
```

The match is exhaustive — no wildcard. Rust compiler will flag missing variants if the MIR API changes.

## Verification Results

```
vcgen_completeness29: 3 passed, 5 failed (correct RED), 2 ignored
vcgen_completeness28: 10 passed, 0 failed (no regression)
cargo build -p rust-fv-driver: clean build, no warnings
cargo clippy -p rust-fv-driver: no warnings
grep CastKind::IntToInt: 3 lines (explicit Transmute/Subtype/IntToInt mappings, no wildcard)
```

## Deviations from Plan

### Behavior Differences (Documented)

**1. MIRCONV-02 tests are GREEN (not RED as predicted)**
- **Found during:** Task 1
- **Issue:** Plan predicted mirconv_02_struct_aggregate and mirconv_02_enum_aggregate would be RED. They are GREEN because the tests work at the IR level — vcgen already handles `AggregateKind::Struct` and `AggregateKind::Enum`. The MIRCONV-02 gap exists only in the MIR→IR conversion path in mir_converter.rs (which returns None for non-Tuple aggregates), not in vcgen.
- **Resolution:** Tests kept GREEN as regression guards. The real fix (Plan 03) will fix mir_converter.rs aggregate conversion, not vcgen.
- **Impact:** Net positive — confirmed vcgen already handles these kinds at IR level.

**2. mirconv_01_int_to_float_cast_kind is GREEN immediately**
- **Found during:** Task 1
- **Issue:** Plan said "Should be GREEN after Plan 01" — confirmed correct. encode_term already has encode_int_to_float_cast() emitting to_fp. The cast is GREEN from the start.
- **Resolution:** Test is a regression guard as intended.

## Self-Check: PASSED

- FOUND: crates/analysis/tests/vcgen_completeness29.rs
- FOUND: crates/driver/src/mir_converter.rs
- FOUND commit: 806982d (test(29-01): add 10 RED tests for MIRCONV-01..02 + VCGEN-05..06)
- FOUND commit: e00c3ee (fix(29-01): preserve CastKind in mir_converter — MIRCONV-01)
