---
phase: 47-mir-coverage-hardening
verified: 2026-03-05T22:27:18Z
status: human_needed
score: 4/4 must-haves verified (1 needs human confirmation for full Z3 solver invocation)
re_verification: false
human_verification:
  - test: "Run Z3 on aligned PtrToPtr cast VC and confirm UNSAT"
    expected: "Z3 returns UNSAT for a function casting *const u8 to *const u32 with addr % 4 == 0 precondition"
    why_human: "E2E tests verify SMT script structure but do not invoke Z3 solver; Success Criterion 1 explicitly requires Z3 UNSAT/SAT results"
  - test: "Run Z3 on unaligned PtrToPtr cast VC and confirm SAT with counterexample"
    expected: "Z3 returns SAT with a counterexample showing a misaligned address"
    why_human: "Same as above -- requires actual solver invocation to confirm counterexample generation"
---

# Phase 47: MIR Coverage Hardening Verification Report

**Phase Goal:** All pointer alignment casts generate safety VCs, CastKind variants are unambiguously encoded, ambiguous match arms are documented, and spec errors surface as rustc diagnostics
**Verified:** 2026-03-05T22:27:18Z
**Status:** human_needed
**Re-verification:** No -- initial verification

## Goal Achievement

### Observable Truths

| # | Truth | Status | Evidence |
|---|-------|--------|----------|
| 1 | A function casting `*const u8` to `*const u32` generates a `MemorySafety` VC asserting `addr % align_of::<u32>() == 0`; Z3 produces UNSAT for aligned case and SAT (counterexample) for unaligned case | VERIFIED (partial: Z3 invocation needs human) | `AlignmentSafety` VC generated with `bvsmod` in SMT script; 5 alignment E2E tests pass; 17 unit tests pass. SMT script contains `check-sat` and negation pattern. Z3 invocation not tested programmatically. |
| 2 | Each CastKind variant (IntToInt, FloatToInt, IntToFloat, PtrToPtr) follows a distinct encoding path in `mir_converter.rs`; no two variants share the same SMT output shape; unit tests cover all four variants | VERIFIED | `all_five_cast_kinds_produce_distinct_smt_output` test passes; 5 SMT snapshot tests confirm distinct shapes; `encode_ptr_to_ptr_cast` at line 754 of encode_term.rs |
| 3 | Every `match arm` path in `vcgen.rs` either generates a VC or has an explicit doc-comment explaining why it is intentionally skipped; no silent fallthrough remains undocumented | VERIFIED | 16 inline doc-comments in vcgen.rs, 3+ in encode_term.rs; centralized audit table at line 35 of vcgen.rs; AUDIT.md (68 lines) documents 44 match expressions audited |
| 4 | A function annotated with a syntactically invalid `#[requires(...)]` expression produces a rustc-style `error[V...]` diagnostic at the annotation source span instead of a logged warning that disappears silently | VERIFIED | `SpecValidationError` type at vcgen.rs:257; `error[V080]` formatting at diagnostics.rs:1147; thread-local error collection; 5 unit tests + 4 E2E tests pass |

**Score:** 4/4 truths verified (1 needs human confirmation for Z3 solver invocation)

### Required Artifacts

| Artifact | Expected | Status | Details |
|----------|----------|--------|---------|
| `crates/analysis/src/ir.rs` | CastKind::PtrToPtr variant | VERIFIED | Line 851: `PtrToPtr` variant with doc-comment |
| `crates/analysis/src/encode_term.rs` | PtrToPtr encoding with `encode_ptr_to_ptr_cast` | VERIFIED | Line 745: match arm; Line 754: helper function |
| `crates/analysis/src/vcgen.rs` | AlignmentSafety VcKind, SpecValidationError, audit table | VERIFIED | Line 235: AlignmentSafety; Line 257: SpecValidationError; Line 35: audit table |
| `crates/driver/src/diagnostics.rs` | V080 error formatting | VERIFIED | Line 1130+: `format_spec_validation_error` with `error[V080]` |
| `crates/driver/src/callbacks.rs` | AlignmentSafety wiring, spec error reporting | VERIFIED | Line 1695: `alignment_safety` string; Line 773-774: spec error reporting |
| `crates/analysis/tests/cast_kind_tests.rs` | Unit tests for CastKind variants (min 80 lines) | VERIFIED | 299 lines, 17 tests, all pass |
| `crates/driver/tests/alignment_e2e.rs` | E2E alignment tests (min 40 lines) | VERIFIED | 291 lines, 5 tests, all pass |
| `crates/analysis/tests/spec_validation_tests.rs` | Spec validation unit tests (min 40 lines) | VERIFIED | 155 lines, 5 tests, all pass |
| `crates/driver/tests/spec_diagnostic_e2e.rs` | Spec diagnostic E2E tests (min 30 lines) | VERIFIED | 162 lines, 4 tests, all pass |
| `.planning/phases/47-mir-coverage-hardening/AUDIT.md` | Formal audit record (min 30 lines) | VERIFIED | 68 lines with findings for both vcgen.rs and encode_term.rs |

### Key Link Verification

| From | To | Via | Status | Details |
|------|----|-----|--------|---------|
| `encode_term.rs` | `ir.rs` | `CastKind::PtrToPtr` match arm | WIRED | Line 745: `CastKind::PtrToPtr => encode_ptr_to_ptr_cast(src)` |
| `vcgen.rs` | `encode_term.rs` | `encode_cast` call | WIRED | encode_cast imported at line 74 and called in rvalue encoding |
| `callbacks.rs` | `VcKind::AlignmentSafety` | `vc_kind_to_string` | WIRED | Line 1695: `VcKind::AlignmentSafety => "alignment_safety"` |
| `vcgen.rs` | `spec_parser.rs` | `parse_spec` returning `Result<Term, Box<SpecValidationError>>` | WIRED | Line 4439: `parse_spec` returns Result; errors collected via thread-local |
| `callbacks.rs` | `diagnostics.rs` | V080 reporting | WIRED | Line 774: `diagnostics::report_spec_validation_error(spec_err)` |
| `vcgen.rs` | `SpecValidationError` | `spec_errors` on FunctionVCs | WIRED | Line 291: `spec_errors` field; Line 948-966: drain and attach |

### Requirements Coverage

| Requirement | Source Plan | Description | Status | Evidence |
|-------------|------------|-------------|--------|----------|
| COMPL-02 | 47-01 | Pointer cast alignment VCs (`addr % align_of::<T>() == 0`) | SATISFIED | AlignmentSafety VcKind with bvsmod encoding; 5 E2E tests + 17 unit tests |
| COMPL-03 | 47-01 | CastKind variants disambiguated and encoded correctly | SATISFIED | 5 distinct CastKind variants; `all_five_cast_kinds_produce_distinct_smt_output` test |
| COMPL-06 | 47-03 | Spec validation errors as driver diagnostics | SATISFIED | SpecValidationError type; V080 formatting; 4 E2E + 5 unit tests |
| COMPL-12 | 47-02 | Match arm fallthrough audit | SATISFIED | 44 match expressions audited; 16+ inline doc-comments; centralized audit table; AUDIT.md |

No orphaned requirements found -- all 4 requirement IDs from REQUIREMENTS.md Phase 47 mapping are covered by plans.

### Anti-Patterns Found

| File | Line | Pattern | Severity | Impact |
|------|------|---------|----------|--------|
| (none) | - | - | - | No TODOs, FIXMEs, placeholders, or stub implementations found in any modified file |

### Human Verification Required

### 1. Z3 UNSAT for Aligned PtrToPtr Cast

**Test:** Generate VCs for a function casting `*const u8` to `*const u32` with `addr % 4 == 0` precondition, then run the SMT script through Z3.
**Expected:** Z3 returns UNSAT (the alignment check passes).
**Why human:** E2E tests verify SMT script structure (contains `bvsmod`, `check-sat`, negation) but do not invoke Z3 -- unlike other E2E tests in the project (e.g., `async_cex_e2e.rs`) which do invoke Z3 with graceful skip.

### 2. Z3 SAT with Counterexample for Unaligned PtrToPtr Cast

**Test:** Generate VCs for a function casting `*const u8` to `*const u32` WITHOUT an alignment precondition, then run the SMT script through Z3.
**Expected:** Z3 returns SAT with a counterexample showing a misaligned address.
**Why human:** Same as above -- actual solver invocation not tested.

### Gaps Summary

No blocking gaps found. All artifacts exist, are substantive (well above minimum line counts), and are fully wired through the codebase. All 31 tests pass across 4 test files.

The only item requiring human verification is confirming Z3 actually produces UNSAT/SAT results when the generated SMT scripts are fed to it. The SMT script structure is verified programmatically (contains `bvsmod`, `check-sat`, negation pattern), so the implementation is sound -- the question is whether the generated SMT-LIB is valid and Z3-compatible. This follows the pattern of other E2E tests in the project that invoke Z3 with graceful skip, which the alignment tests do not do.

No `CastKind::Pointer` references remain in the codebase (fully renamed to `PtrToPtr`). Zero TODO/FIXME/HACK/PLACEHOLDER markers in any modified file.

---

_Verified: 2026-03-05T22:27:18Z_
_Verifier: Claude (gsd-verifier)_
