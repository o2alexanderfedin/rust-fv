---
phase: 39-fnmut-prophecy-variable-encoding-for-mutable-closure-capture-verification-implement-prophecy-pre-post-state-tracking-in-closure-analysis-rs-vcgen-rs-so-fnmut-closures-with-contracts-on-mutated-captured-state-can-be-verified
verified: 2026-03-02T22:30:00Z
status: passed
score: 9/9 must-haves verified
re_verification: false
---

# Phase 39: FnMut Prophecy Variable Encoding Verification Report

**Phase Goal:** Extend the IR and VCGen so that FnMut closures with mutable captured state emit SMT-LIB2 prophecy variable declarations (`{field}_initial`, `{field}_prophecy`) enabling contracts like `#[ensures(count == old(count) + 1)]` to be verified.
**Verified:** 2026-03-02T22:30:00Z
**Status:** passed
**Re-verification:** No — initial verification

## Goal Achievement

### Observable Truths (Plan 01)

| # | Truth | Status | Evidence |
|---|-------|--------|----------|
| 1 | ClosureInfo.env_fields carries CaptureMode per field (ByMove \| ByRef \| ByMutRef) | VERIFIED | `ir.rs` line 310: `pub env_fields: Vec<(String, Ty, CaptureMode)>` |
| 2 | ProphecyInfo has closure_name: Option<String> field | VERIFIED | `ir.rs` line 585: `pub closure_name: Option<String>` |
| 3 | detect_closure_prophecies returns one ProphecyInfo per ByMutRef env_field | VERIFIED | `encode_prophecy.rs` lines 185-196: filter on `CaptureMode::ByMutRef`, map to `ProphecyInfo` with `closure_name: Some(...)` |
| 4 | All existing ClosureInfo constructors compile with CaptureMode::ByMove default | VERIFIED | Full test suite 1258 tests pass; defunctionalize.rs migrated to 3-tuple destructure; integration test helpers updated |
| 5 | cargo test passes for encode_prophecy and ir modules | VERIFIED | All test result lines show `ok. N passed; 0 failed` |

### Observable Truths (Plan 02)

| # | Truth | Status | Evidence |
|---|-------|--------|----------|
| 6 | generate_vcs emits declare-const count_initial and declare-const count_prophecy for FnMut closure with ByMutRef env_field | VERIFIED | `vcgen.rs` lines 285-295: closure prophecy wiring block calls `detect_closure_prophecies` and extends declarations; test `test_vcgen_fnmut_closure_prophecy` asserts both strings in VC script |
| 7 | VC script contains both declarations when env_fields has a ByMutRef captured field | VERIFIED | `test_vcgen_fnmut_closure_two_by_mut_ref_both_declared` verifies `count_initial`, `count_prophecy`, `total_initial`, `total_prophecy` all appear |
| 8 | placeholder test test_vcgen_fnmut_closure_prophecy is upgraded to assert specific SMT output | VERIFIED | Test at line 7669 has explicit `assert!(script_str.contains("declare-const count_initial"))` and `assert!(script_str.contains("declare-const count_prophecy"))` |
| 9 | No regressions in any existing vcgen tests | VERIFIED | `test result: ok. 1258 passed; 0 failed; 0 ignored` |

**Score:** 9/9 truths verified

### Required Artifacts

| Artifact | Expected | Status | Details |
|----------|----------|--------|---------|
| `crates/analysis/src/ir.rs` | CaptureMode enum + updated ClosureInfo.env_fields + extended ProphecyInfo | VERIFIED | `pub enum CaptureMode` at line 29; `env_fields: Vec<(String, Ty, CaptureMode)>` at line 310; `closure_name: Option<String>` at line 585 |
| `crates/analysis/src/encode_prophecy.rs` | detect_closure_prophecies function | VERIFIED | `pub fn detect_closure_prophecies(closure_info: &ClosureInfo) -> Vec<ProphecyInfo>` at line 185; exported as `pub` |
| `crates/analysis/src/vcgen.rs` | Closure prophecy integration in generate_vcs declaration phase | VERIFIED | `detect_closure_prophecies` called at line 289 inside declarations wiring block |

### Key Link Verification

| From | To | Via | Status | Details |
|------|----|-----|--------|---------|
| `crates/analysis/src/encode_prophecy.rs` | `crates/analysis/src/ir.rs` | `CaptureMode` import + `ClosureInfo.env_fields` tuple index 2 | VERIFIED | `CaptureMode::ByMutRef` used in filter at line 189 |
| `crates/analysis/src/vcgen.rs` | `crates/analysis/src/encode_prophecy.rs` | `detect_closure_prophecies` call in closure analysis block | VERIFIED | `crate::encode_prophecy::detect_closure_prophecies(ci)` at line 289 |
| closure analysis block | declarations vec | `prophecy_declarations` appended after closure_infos loop | VERIFIED | `declarations.extend(closure_prophecy_decls)` at line 295; `closure_prophecy_decls` built from `prophecy_declarations(&cp)` at line 291 |

### Requirements Coverage

No requirement IDs declared in either plan's `requirements` field (both have `requirements: []`). No REQUIREMENTS.md mapping to verify against. Requirements coverage: N/A — no IDs to cross-reference.

### Anti-Patterns Found

No blockers or warnings found. Scanned modified files:
- `crates/analysis/src/ir.rs` — no TODO/FIXME/placeholder; no empty implementations; `CaptureMode` enum fully defined with three variants
- `crates/analysis/src/encode_prophecy.rs` — no TODO/FIXME/placeholder; `detect_closure_prophecies` has real logic (filter + map); no stub return
- `crates/analysis/src/vcgen.rs` — no TODO/FIXME/placeholder; wiring block is substantive (loop + conditional extend); upgraded test has concrete assertions

| File | Line | Pattern | Severity | Impact |
|------|------|---------|----------|--------|
| (none) | — | — | — | — |

### Human Verification Required

None. All goal behaviors are verifiable programmatically:
- SMT string assertions in vcgen tests directly confirm the declare-const declarations are present in generated VC scripts.
- Test results confirm zero regressions across all 1258 tests.

### Gaps Summary

No gaps. All must-have truths, artifacts, and key links are verified against the actual codebase. The phase goal is fully achieved:

- `CaptureMode` enum (ByMove | ByRef | ByMutRef) exists in `ir.rs`
- `ClosureInfo.env_fields` is `Vec<(String, Ty, CaptureMode)>`
- `ProphecyInfo.closure_name: Option<String>` field exists
- `detect_closure_prophecies` in `encode_prophecy.rs` produces `ProphecyInfo` entries only for `ByMutRef` captures
- `generate_vcs` in `vcgen.rs` wires closure prophecy declarations into every VC script preamble
- `test_vcgen_fnmut_closure_prophecy` asserts `declare-const count_initial` and `declare-const count_prophecy` appear in the SMT script
- 10 new tests (3 in ir.rs, 7 in encode_prophecy.rs) + 4 vcgen tests (1 upgraded + 3 new) = 14 total new tests
- Full test suite: 1258 passed, 0 failed — zero regressions
- `cargo clippy -p rust-fv-analysis` produces zero errors
- Commits: f906601, 86380ce (Plan 01), 23ed5fc, a495ac9 (Plan 02) all present in git log

---

_Verified: 2026-03-02T22:30:00Z_
_Verifier: Claude (gsd-verifier)_
