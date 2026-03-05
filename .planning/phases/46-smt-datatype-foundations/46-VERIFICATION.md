---
phase: 46-smt-datatype-foundations
verified: 2026-03-05T10:15:00Z
status: passed
score: 5/5 must-haves verified
re_verification:
  previous_status: gaps_found
  previous_score: 4/5
  gaps_closed:
    - "Enum discriminant VCs use native SMT testers (is-Variant) instead of uninterpreted functions"
  gaps_remaining: []
  regressions: []
---

# Phase 46: SMT Datatype Foundations Verification Report

**Phase Goal:** Structs and enums are encoded as first-class SMT datatypes with constructors and selectors, removing the uninterpreted-sort approximation that limits struct field reasoning
**Verified:** 2026-03-05T10:15:00Z
**Status:** passed
**Re-verification:** Yes -- after gap closure (plan 46-03)

## Goal Achievement

### Observable Truths (from ROADMAP Success Criteria)

| # | Truth | Status | Evidence |
|---|-------|--------|----------|
| 1 | Struct type generates `(declare-datatype StructName ...)` with constructor and selectors; field postconditions pass Z3 without uninterpreted-sort fallback | VERIFIED | `Ty::Struct` maps to `Sort::Datatype` in encode_sort.rs:63. `collect_datatype_declarations` generates DeclareDatatype commands. E2E test `e2e_struct_datatype_field_reasoning`. Tests confirm no Uninterpreted for struct/enum types. |
| 2 | Enum type generates `(declare-datatype EnumName ...)` with one constructor per variant, plus tester (`is-Variant`); discriminant VCs use these testers | VERIFIED | Enum DeclareDatatype generation correct (encode_sort.rs:67+). SwitchInt uses `Term::IsTester("mk-{variant}", expr)` at vcgen.rs:1271. SetDiscriminant uses IsTester at vcgen.rs:1511. Rvalue::Discriminant returns None for enums (vcgen.rs:2010-2012). E2E test asserts `(_ is mk-` present AND `discriminant-` absent in SMT output (e2e_verification.rs:3134-3144). Commits 6db26af, 4e1816b. |
| 3 | Functional update on any struct rvalue emits correct `mk-StructName` constructor term; COMPL-05 regression test GREEN | VERIFIED | `build_nested_functional_update` handles nested projections. Unit and E2E tests confirm (`e2e_nested_struct_update`, `e2e_functional_update_binop`). |
| 4 | Z3 native backend uses `Sort::int()` for SpecInt/SpecNat; no panics or uninterpreted fallback | VERIFIED | `Z3Value::Int(Int)` variant, `Sort::Int => Ok(Z3Value::Int(Int::new_const(...)))` at z3_native.rs:138. Full arithmetic, comparison, negation, model extraction. |
| 5 | `[expr; N]` (Rvalue::Repeat) encodes as forall-quantified equality; bounds-checked access passes verification | VERIFIED | `Term::Forall` at vcgen.rs:2038 with bounds and body. Unit tests confirm structure. |

**Score:** 5/5 truths verified

### Required Artifacts

| Artifact | Expected | Status | Details |
|----------|----------|--------|---------|
| `crates/smtlib/src/term.rs` | Term::IsTester variant | VERIFIED | Line 151: `IsTester(String, Box<Term>)` with doc comment |
| `crates/smtlib/src/formatter.rs` | IsTester formatting as `((_ is constructor) expr)` | VERIFIED | Line 244-246: correct SMT-LIB2 indexed identifier syntax. 6 formatter tests. |
| `crates/solver/src/z3_native.rs` | Int sort support + graceful IsTester handling | VERIFIED | Z3Value::Int variant with full arithmetic. IsTester returns unsupported error (correct -- text-based solver is primary path for enum VCs). |
| `crates/analysis/src/vcgen.rs` | SwitchInt IsTester, SetDiscriminant IsTester, Repeat forall, functional update | VERIFIED | All four features present and correctly wired. |
| `crates/analysis/src/encode_sort.rs` | No Uninterpreted fallback for struct/enum | VERIFIED | Ty::Struct -> Sort::Datatype, Ty::Enum -> Sort::Datatype. Tests at lines 981-1012 confirm. |
| `crates/analysis/tests/e2e_verification.rs` | E2E tests with IsTester assertions | VERIFIED | e2e_enum_datatype_match asserts IsTester syntax present, discriminant- absent (lines 3134-3144). |

### Key Link Verification

| From | To | Via | Status | Details |
|------|----|-----|--------|---------|
| vcgen.rs | term.rs | `Term::IsTester` constructor in SwitchInt | WIRED | Lines 1271, 1511: constructs IsTester terms |
| formatter.rs | term.rs | Display impl for IsTester | WIRED | Line 244: match arm formats `((_ is {constructor}) {expr})` |
| vcgen.rs | encode_sort.rs | `collect_datatype_declarations` | WIRED | Import and calls at vcgen.rs:256, 871 |
| vcgen.rs | ir.rs | `Ty::Enum` variant lookup for tester name | WIRED | Lines 1266, 1506, 2010: pattern matches on Ty::Enum to resolve variant names |
| z3_native.rs | z3::ast::Int | Sort::Int create_const | WIRED | Line 138 |

### Requirements Coverage

| Requirement | Source Plan | Description | Status | Evidence |
|-------------|------------|-------------|--------|----------|
| COMPL-01 | 46-02, 46-03 | Struct/enum types encoded as SMT declare-datatype with constructors, selectors, and testers | SATISFIED | Struct/enum produce DeclareDatatype. Native IsTester testers used in SwitchInt and SetDiscriminant. E2E confirms tester syntax in output. |
| COMPL-05 | 46-02 | Functional update on projected places generates correct mk-StructName for all rvalue types | SATISFIED | build_nested_functional_update handles multi-level Field, Downcast+Field. All rvalue types supported. Unit and E2E tests. |
| COMPL-07 | 46-01 | Z3 native backend supports Int sort via z3::Sort::int() | SATISFIED | Z3Value::Int variant, full arithmetic/comparison/negation, model extraction. 15+ tests. |
| COMPL-11 | 46-01 | Rvalue::Repeat encoded as universally quantified equality | SATISFIED | Forall-quantified encoding with bounds at vcgen.rs:2018-2038. Unit tests confirm Forall structure. |

### Anti-Patterns Found

| File | Line | Pattern | Severity | Impact |
|------|------|---------|----------|--------|
| vcgen.rs | 1517, 1524, 1742, 2015 | `discriminant-` fallback for non-enum types | Info | Correct design: non-enum types cannot use datatype testers; uninterpreted fallback is sound |

### Human Verification Required

None required. All truths verified programmatically with strong evidence.

### Gaps Summary

No gaps. All five success criteria verified. The single gap from the initial verification (native IsTester testers for enum discriminant VCs) has been fully closed by plan 46-03. COMPL-01 is now fully satisfied with constructors, selectors, AND testers.

---

_Verified: 2026-03-05T10:15:00Z_
_Verifier: Claude (gsd-verifier)_
