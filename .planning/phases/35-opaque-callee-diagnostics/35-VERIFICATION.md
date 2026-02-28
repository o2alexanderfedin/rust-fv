---
phase: 35-opaque-callee-diagnostics
verified: 2026-02-28T00:00:00Z
status: passed
score: 8/8 must-haves verified
re_verification: false
---

# Phase 35: Opaque Callee Diagnostics Verification Report

**Phase Goal:** Users receive actionable diagnostics when a verified function calls an uncontracted callee, replacing the current silent skip
**Verified:** 2026-02-28
**Status:** PASSED
**Re-verification:** No — initial verification

## Goal Achievement

### Observable Truths

| #  | Truth                                                                                                                               | Status     | Evidence                                                                                                   |
|----|-------------------------------------------------------------------------------------------------------------------------------------|------------|------------------------------------------------------------------------------------------------------------|
| 1  | cargo verify emits a V060 warning when a verified function calls a callee with no #[requires]/#[ensures] contract                   | VERIFIED   | vcgen.rs:2391 emits VcKind::OpaqueCallee; diagnostics.rs:83 routes OpaqueCallee to ReportKind::Warning     |
| 2  | cargo verify emits a V061 error when an uncontracted callee is called from within an unsafe block or unsafe fn                      | VERIFIED   | vcgen.rs:2383-2389 unsafe context check; OpaqueCalleeUnsafe falls through to ReportKind::Error             |
| 3  | The silent tracing::debug!() + continue at vcgen.rs:2375 is replaced with VcKind::OpaqueCallee or VcKind::OpaqueCalleeUnsafe VCs   | VERIFIED   | vcgen.rs:2377-2433 None-arm replaced; debug message now says "emitting opaque callee diagnostic"; no bare continue |
| 4  | cargo test (unit) passes: OpaqueCallee routes to warning severity, OpaqueCalleeUnsafe routes to error severity in diagnostics.rs    | VERIFIED   | 7 driver tests pass (test_vc_kind_to_string_opaque*, test_vc_kind_description_opaque*, test_severity_dispatch) |
| 5  | Integration test verifies V060 warning fires for safe verified caller calling uncontracted callee                                   | VERIFIED   | test_opaque_callee_safe_warning at vcgen.rs:9086 — asserts exactly 1 OpaqueCallee VC with name/message checks |
| 6  | Integration test verifies V061 error fires when uncontracted callee is called from unsafe block                                     | VERIFIED   | test_opaque_callee_unsafe_error (line 9127) and test_opaque_callee_unsafe_block_error (line 9154) both pass  |
| 7  | Integration test verifies zero OpaqueCallee VCs when all callees have contracts                                                     | VERIFIED   | test_opaque_callee_no_diagnostic_for_contracted at vcgen.rs:9181 — asserts zero OpaqueCallee/OpaqueCalleeUnsafe VCs |
| 8  | cargo test passes for all new integration and unit tests (10 total opaque callee tests)                                             | VERIFIED   | test run: 10 passed, 0 failed (vcgen filter test_opaque_callee); 7 passed, 0 failed (driver filter)         |

**Score:** 8/8 truths verified

### Required Artifacts

| Artifact                                     | Expected                                                                                       | Status     | Details                                                                                                 |
|----------------------------------------------|-----------------------------------------------------------------------------------------------|------------|---------------------------------------------------------------------------------------------------------|
| `crates/analysis/src/vcgen.rs`               | VcKind::OpaqueCallee and OpaqueCalleeUnsafe variants; None-arm emits always-SAT diagnostic VC | VERIFIED   | Lines 146-148: variants present. Lines 2377-2433: always-SAT VC emission with dedup + unsafe detection  |
| `crates/driver/src/diagnostics.rs`           | vc_kind_description + suggest_fix entries; OpaqueCallee routed to Warning                     | VERIFIED   | Lines 389-392: descriptions. Lines 542-546: suggest_fix. Lines 80-88: Warning branch includes OpaqueCallee |
| `crates/driver/src/callbacks.rs`             | vc_kind_to_string entries; OpaqueCallee excluded from failure push                            | VERIFIED   | Lines 1206-1207: "opaque_callee"/"opaque_callee_unsafe". Line 701: OpaqueCallee excluded from push      |

### Key Link Verification

| From                                                      | To                                               | Via                                                              | Status   | Details                                                             |
|-----------------------------------------------------------|--------------------------------------------------|------------------------------------------------------------------|----------|---------------------------------------------------------------------|
| vcgen.rs generate_call_site_vcs None-arm                  | VcKind::OpaqueCallee / VcKind::OpaqueCalleeUnsafe | func.is_unsafe_fn / unsafe_blocks.iter().any() check            | WIRED    | Lines 2383-2392: is_unsafe_context check selects vc_kind correctly  |
| diagnostics.rs report_kind dispatch                       | ReportKind::Warning for OpaqueCallee             | if condition on vc_kind matching OpaqueCallee                   | WIRED    | Lines 80-88: OpaqueCallee explicitly in Warning branch              |
| test_opaque_callee_safe_warning                           | VcKind::OpaqueCallee in result.conditions         | generate_vcs with ContractDatabase missing callee entry          | WIRED    | vcgen.rs:9086 — test passes, asserts exactly 1 OpaqueCallee VC      |
| test_opaque_callee_unsafe_error                           | VcKind::OpaqueCalleeUnsafe in result.conditions  | generate_vcs with func.is_unsafe_fn = true and missing contract | WIRED    | vcgen.rs:9127 — test passes, asserts OpaqueCalleeUnsafe VC          |

### Requirements Coverage

| Requirement | Source Plan   | Description                                                                                                                          | Status    | Evidence                                                                                  |
|-------------|---------------|--------------------------------------------------------------------------------------------------------------------------------------|-----------|-------------------------------------------------------------------------------------------|
| OPAQUE-01   | 35-01, 35-02  | User receives a diagnostic warning (V060-V069) when a verified function calls an uncontracted callee that affects verification soundness | SATISFIED | VcKind::OpaqueCallee variant exists; always-SAT VC emitted; routed to ReportKind::Warning; 10 tests guard it |
| OPAQUE-02   | 35-01, 35-02  | User receives a verification error (not warning) when unsafe code calls an uncontracted callee                                       | SATISFIED | VcKind::OpaqueCalleeUnsafe variant exists; unsafe context detection correct; routed to ReportKind::Error; test_opaque_callee_unsafe_error and test_opaque_callee_unsafe_block_error both pass |

REQUIREMENTS.md status column shows both OPAQUE-01 and OPAQUE-02 marked [x] Complete at Phase 35.

No orphaned requirements: both IDs declared in plan frontmatter are accounted for.

### Anti-Patterns Found

| File | Line | Pattern | Severity | Impact |
|------|------|---------|----------|--------|
| None | —    | —       | —        | No anti-patterns found in modified files |

**Anti-pattern scan notes:**
- Silent skip (`tracing::debug!(...); continue`) replaced at vcgen.rs:2377-2433 — confirmed removed
- None-arm now emits always-SAT VC before continuing — substantive implementation
- No bare `return null`, empty handlers, or placeholder comments found in modified files
- Deduplication via `seen_opaque: HashSet<String>` keyed on `"callee_name:vc_kind_debug"` — prevents noise

### Human Verification Required

None. All goal behaviors are mechanically testable:
- V060/V061 emission is verified by unit and integration tests in the test suite
- Severity routing (Warning vs Error) is verified by direct `report_kind` assertion tests
- SAT exclusion from failure push is verified by the callbacks.rs exclusion check and tests

All automated checks passed with zero failures.

## Commits Verified

| Commit   | Description                                                                  | Verified |
|----------|------------------------------------------------------------------------------|----------|
| `7a84c69` | feat(35-01): add OpaqueCallee/OpaqueCalleeUnsafe VcKind variants + vcgen None-arm emission | Yes |
| `82f6f3b` | feat(35-01): wire OpaqueCallee severity dispatch, vc_kind_to_string, and SAT exclusion in driver | Yes |
| `684614b` | test(35-02): add five integration tests for V060/V061 opaque callee diagnostics | Yes |

## Gaps Summary

No gaps. All must-haves from both plan frontmatter sections are satisfied:

**Plan 35-01 truths:** All 4 verified — variants exist, None-arm replaced, 13 unit tests GREEN.

**Plan 35-02 truths:** All 4 verified — 5 integration tests exist with exact plan-specified names and pass, full test suite GREEN.

The phase goal is fully achieved: users now receive actionable V060/V061 diagnostics instead of the former silent skip when a verified function calls an uncontracted callee.

---

_Verified: 2026-02-28_
_Verifier: Claude (gsd-verifier)_
