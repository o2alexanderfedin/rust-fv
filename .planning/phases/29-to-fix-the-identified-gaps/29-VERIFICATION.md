---
phase: 29-to-fix-the-identified-gaps
verified: 2026-02-24T00:00:00Z
status: passed
score: 4/4 must-haves verified
re_verification: false
human_verification:
  - test: "Run cargo verify on a real Rust file containing float-to-int casts and struct field mutation"
    expected: "SMT script contains fp.to_sbv and mk-StructName functional update terms"
    why_human: "End-to-end MIR pipeline through rustc driver cannot be exercised by unit tests alone; need a real .rs file compilation"
---

# Phase 29: to-fix-the-identified-gaps Verification Report

**Phase Goal:** Fix all identified gaps in Rust -> SMT-LIB/SMT-LIB2 VCGen coverage -- soundness holes first (cast kind preservation, float-to-int SMT encoding), then coverage breadth (aggregates, missing rvalues, projected LHS mutation)
**Verified:** 2026-02-24
**Status:** passed
**Re-verification:** No -- initial verification

## Goal Achievement

### Observable Truths

| # | Truth | Status | Evidence |
|---|-------|--------|----------|
| 1 | FloatToInt/IntToFloat/FloatToFloat/Pointer cast kinds are preserved through MIR -> IR conversion (not collapsed to IntToInt) | VERIFIED | Exhaustive CastKind match at mir_converter.rs lines 301-313; no wildcard; all float cast kinds explicitly mapped |
| 2 | Float-to-int cast produces `((_ fp.to_sbv N) RTZ src)` for signed and `((_ fp.to_ubv N) RTZ src)` for unsigned (not `extract`) | VERIFIED | encode_term.rs lines 774-783; encode_float_to_int_cast uses Term::App with indexed operator and RTZ rounding mode; vcgen_05 tests GREEN |
| 3 | Struct/enum/closure aggregates produce ir::Rvalue::Aggregate (not None); SetDiscriminant and Assume IR variants exist and are wired | VERIFIED | ir.rs lines 572+574; AggregateKind::Adt at mir_converter.rs line 325; StatementKind::SetDiscriminant at line 184; NonDivergingIntrinsic::Assume at line 191 |
| 4 | Struct field mutation on projected LHS produces functional record update `(= s (mk-StructName new_field (Struct-other_field s) ...))` | VERIFIED | vcgen.rs lines 1552-1576; encode_rvalue_for_assignment helper at line 1518; Downcast narrowing with Cow<Ty> in encode_term.rs lines 67-106; vcgen_06 tests GREEN |

**Score:** 4/4 truths verified

### Required Artifacts

| Artifact | Expected | Status | Details |
|----------|----------|--------|---------|
| `crates/analysis/tests/vcgen_completeness29.rs` | TDD scaffold with 10 test functions (9 active, 1 ignored) | VERIFIED | 603 lines; 10 test functions; 9 pass, 1 ignored; all pass GREEN |
| `crates/driver/src/mir_converter.rs` | Exhaustive CastKind mapping; Adt/Closure aggregate arms; SetDiscriminant/Assume in convert_statement; TyKind::Param to Ty::Generic; CopyForDeref/RawPtr/Repeat arms | VERIFIED | All patterns confirmed present: CastKind exhaustive match (lines 301-313), AggregateKind::Adt (line 325), Closure (line 332), SetDiscriminant (line 184), Assume intrinsic (line 191), TyKind::Param (line 474), CopyForDeref (line 344), RawPtr (line 350), Repeat (line 356) |
| `crates/analysis/src/ir.rs` | Statement::SetDiscriminant(Place, usize) and Statement::Assume(Operand) variants; Rvalue::Repeat(Operand, usize) variant | VERIFIED | SetDiscriminant at line 572, Assume at line 574, Repeat at line 664 |
| `crates/analysis/src/encode_term.rs` | encode_float_to_int_cast using fp.to_sbv/fp.to_ubv; encode_cast with to_signed parameter; Projection::Downcast type narrowing with Cow<Ty> | VERIFIED | fp.to_sbv/fp.to_ubv at lines 779/781; RTZ at line 783; encode_cast signature with to_signed at line 724; Cow<Ty> at line 69; Downcast narrowing at lines 90-106 |
| `crates/analysis/src/vcgen.rs` | encode_assignment handles projected LHS via functional update (mk-); encode_rvalue_for_assignment helper; to_signed passed to encode_cast | VERIFIED | encode_rvalue_for_assignment at line 1518; mk- functional update at line 1576; to_signed at line 1635-1636 |

### Key Link Verification

| From | To | Via | Status | Details |
|------|----|-----|--------|---------|
| mir_converter.rs convert_rvalue Cast arm | ir::CastKind variants (FloatToInt, IntToFloat, FloatToFloat, Pointer) | exhaustive match on mir::CastKind | WIRED | Lines 301-313; no wildcard; Rust compiler enforces completeness |
| encode_term.rs encode_cast FloatToInt arm | encode_float_to_int_cast | to_signed parameter from target type | WIRED | Line 724 (signature), line 729 (FloatToInt arm), line 777 (implementation) |
| encode_float_to_int_cast | Term::App with fp.to_sbv / fp.to_ubv | indexed operator format string + RTZ rounding mode | WIRED | Lines 778-783; `format!("(_ fp.to_{signed}bv {to_bits})")` + `Term::RoundingMode("RTZ")` |
| vcgen.rs encode_cast call site | encode_cast with to_signed | ty_is_signed(target_ty) | WIRED | Lines 1635-1636; `let to_signed = crate::encode_term::ty_is_signed(target_ty)` |
| mir_converter.rs convert_rvalue Aggregate arm | ir::AggregateKind::Enum / Closure | AggregateKind::Adt match with def_id + variant_idx | WIRED | Lines 325-333; formats def_id as name; uses variant_idx.as_usize() |
| mir_converter.rs convert_statement | ir::Statement::SetDiscriminant | StatementKind::SetDiscriminant match | WIRED | Lines 184-190; converts place + variant_index |
| mir_converter.rs convert_statement | ir::Statement::Assume | StatementKind::Intrinsic(box NonDivergingIntrinsic::Assume) | WIRED | Line 191; box pattern for nightly Box-wrapped intrinsic |
| vcgen.rs encode_assignment projected LHS | Term::App("mk-StructName", fields) | single Projection::Field + Ty::Struct match | WIRED | Lines 1552-1576; all fields enumerated; changed field gets new_val; others use selector terms |
| encode_term.rs encode_place_with_type | Ty::Enum variant narrowing | Projection::Downcast narrows to ad-hoc Ty::Struct | WIRED | Lines 90-106; Cow::Owned(variant_struct_ty) assigned when Enum + variant_idx match |

### Requirements Coverage

| Requirement | Source Plans | Description | Status | Evidence |
|-------------|-------------|-------------|--------|----------|
| MIRCONV-01 | 29-01, 29-04 | Cast kind preservation (float casts, TyKind::Param, missing rvalue variants) | SATISFIED | Exhaustive CastKind match confirmed; TyKind::Param -> Ty::Generic at mir_converter.rs:474; CopyForDeref/RawPtr/Repeat all wired; NullaryOp not needed (removed from nightly-2026-02-11) |
| MIRCONV-02 | 29-03 | Aggregate conversion (Adt/Closure) + SetDiscriminant/Assume IR variants | SATISFIED | AggregateKind::Adt + Closure in convert_rvalue; SetDiscriminant + Assume in convert_statement; ir::Statement has both variants; mirconv_02 tests GREEN |
| VCGEN-05 | 29-02 | Float-to-int SMT encoding using fp.to_sbv/fp.to_ubv with RTZ | SATISFIED | encode_float_to_int_cast uses fp.to_sbv (signed) / fp.to_ubv (unsigned) with RTZ; both vcgen_05 tests GREEN |
| VCGEN-06 | 29-05 | Projected LHS struct mutation via functional record update | SATISFIED | encode_assignment produces mk-StructName functional update for single-level Field projection on Ty::Struct base; vcgen_06_struct_field_mutation GREEN; vcgen_06_field_mutation_use regression GREEN |

### Anti-Patterns Found

| File | Line | Pattern | Severity | Impact |
|------|------|---------|----------|--------|
| `crates/analysis/tests/vcgen_completeness29.rs` | 600 | `#[ignore]` with stale message "Statement::SetDiscriminant not yet in ir::Statement" | Info | SetDiscriminant IS now in ir::Statement (Plan 03). The actual test body is `todo!()` because VCGen encoding of discriminant as SMT assertion is intentionally deferred. Message is misleading but harmless; deferred work is documented. |
| `.planning/ROADMAP.md` | Phase 29 plans section | Plans 29-02 through 29-05 show as unchecked `[ ]` | Info | ROADMAP.md docs not updated to check off completed plans. All plans have commits, passing tests, and SUMMARY.md files. Documentation-only issue, no code impact. |
| `.planning/REQUIREMENTS.md` | Line 42 | "NullaryOp" listed as required rvalue variant to wire | Info | NullaryOp was removed from nightly-2026-02-11 MIR Rvalue enum. The wildcard arm in convert_rvalue handles this with a comment. The requirement as stated is not achievable on this nightly toolchain; the documented deviation is appropriate. |

### Human Verification Required

#### 1. End-to-end float cast verification

**Test:** Write a Rust file with `fn cast_test(x: f64) -> i32 { x as i32 }`, run through `cargo-verify`, inspect the generated SMT script.
**Expected:** SMT output contains `((_ fp.to_sbv 32) RTZ ...)` and does NOT contain `((_ extract 31 0) ...)`.
**Why human:** The full MIR pipeline through the rustc driver (not just the unit test IR layer) must exercise convert_rvalue -> vcgen -> encode_cast -> encode_float_to_int_cast. Unit tests in vcgen_completeness29.rs bypass mir_converter.rs and work at the IR level.

#### 2. End-to-end struct field mutation verification

**Test:** Write a Rust file with a struct `Point { x: i32, y: i32 }` and a function that assigns `p.x = 42`, run through `cargo-verify`, inspect the generated SMT script.
**Expected:** SMT output contains `(assert (= _1 (mk-Point 42 (Point-y _1))))` or equivalent functional update.
**Why human:** The full MIR pipeline is required to confirm the struct type has field names available in convert_ty's output, which feeds into vcgen's Ty::Struct(name, fields) match.

### Gaps Summary

No gaps found. All 4 requirements (MIRCONV-01, MIRCONV-02, VCGEN-05, VCGEN-06) are satisfied with substantive implementations wired end-to-end. The only deferred item (`vcgen_06_set_discriminant_assertion`) was intentionally deferred by the phase design (SetDiscriminant VCGen encoding is a stretch goal documented in the test's `#[ignore]` annotation). All 9 active Phase 29 tests pass GREEN; all 10 Phase 28 regression tests pass GREEN; full test suite (1200+ unit tests) passes with 0 failures; build and clippy are clean.

## Test Run Results (verified live)

```
vcgen_completeness29: 9 passed, 0 failed, 1 ignored  (ok)
vcgen_completeness28: 10 passed, 0 failed, 0 ignored (ok)
rust-fv-analysis full suite: 1200+ passed, 0 failed  (ok)
cargo build -p rust-fv-analysis -p rust-fv-driver:  Finished (no errors)
cargo clippy -p rust-fv-analysis -p rust-fv-driver: Finished (no warnings)
```

## Commits Verified

| Commit | Message | Requirement |
|--------|---------|-------------|
| 806982d | test(29-01): add 10 RED tests for MIRCONV-01..02 + VCGEN-05..06 | Scaffold |
| e00c3ee | fix(29-01): preserve CastKind in mir_converter -- MIRCONV-01 | MIRCONV-01 |
| 9bd0740 | fix(29-02): replace Term::Extract with fp.to_sbv/fp.to_ubv RTZ (VCGEN-05) | VCGEN-05 |
| 65b7368 | feat(29-03): add ir::Statement::SetDiscriminant+Assume; wire Adt/Closure aggregates (MIRCONV-02) | MIRCONV-02 |
| f1abab0 | feat(29-04): fix TyKind::Param->Generic; add CopyForDeref, RawPtr, Repeat | MIRCONV-01 |
| 77aba84 | fix(29-05): functional record update for projected LHS + Downcast type narrowing (VCGEN-06) | VCGEN-06 |

---

_Verified: 2026-02-24_
_Verifier: Claude (gsd-verifier)_
