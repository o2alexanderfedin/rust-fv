---
phase: 19-counterexample-generation
verified: 2026-02-19T18:45:00Z
status: passed
score: 4/4 success criteria verified
re_verification:
  previous_status: gaps_found
  previous_score: 3/4
  gaps_closed:
    - "Developer sees Rust variable name (e.g. `x`) not SSA name (`_param_x_1`) at the failing line — JSON path now uses ir_func.source_names (commit 248fdc5)"
  gaps_remaining: []
  regressions: []
human_verification:
  - test: "Run cargo verify on a function with failing postcondition, compare --output-format=text vs --output-format=json output"
    expected: "Both text and JSON outputs show Rust source variable names (e.g. `x`, `result`) not SSA names (e.g. `_1`, `_2`)"
    why_human: "Requires a real SMT solver run with a failing verification condition producing a counterexample model"
  - test: "Run cargo verify on a function with failing postcondition and inspect ariadne terminal output"
    expected: "Source file is read, counterexample values appear as inline span labels at the failing spec line with format `x: i32 = 5`"
    why_human: "Requires real compiler+solver run; visual terminal output cannot be verified statically"
---

# Phase 19: Counterexample Generation Verification Report

**Phase Goal:** When verification fails, developers see Rust-typed counterexamples with source locations instead of SMT model dumps
**Verified:** 2026-02-19T18:45:00Z
**Status:** passed — all 4 success criteria verified
**Re-verification:** Yes — after gap closure (commit 248fdc5)

## Goal Achievement

### Observable Truths (Success Criteria)

| # | Truth | Status | Evidence |
|---|-------|--------|----------|
| 1 | Developer sees Rust variable name (e.g. `x`) not SSA name (`_param_x_1`) at the failing line | VERIFIED | Both paths now correct. Terminal (ariadne) path: `failure.source_names` at diagnostics.rs:112. JSON path: `build_counterexample_v2` passes `&ir_func.source_names` at parallel.rs:372 (fixed in commit 248fdc5, replacing the identity-map construct). |
| 2 | Developer sees typed Rust value (e.g. `i32: 5`, `bool: false`) not raw hex bitvector | VERIFIED | `cex_render.rs` implements `render_typed_value` dispatching on `ir::Ty` variants; bitvec hex parsing in `parse_bitvec`; display format `"i32: 5"` confirmed. 30 cex_render tests pass. |
| 3 | Developer sees counterexample values annotated inline at failing source line via ariadne span labels | VERIFIED | `diagnostics.rs` line 110 calls `render_counterexample`, line 181 uses `Source::from`, lines 123-166 add per-variable Labels. No unconditional fallback to `report_text_only`. |
| 4 | `--output-format=json` output includes a structured `counterexample` field on verification failure | VERIFIED | `JsonCounterexample`, `JsonCexVariable`, `JsonCexValue`, `JsonLocation` structs in json_output.rs lines 54-96. `JsonFailure.counterexample_v2` field at line 41. `build_counterexample_v2` now uses `&ir_func.source_names` (gap closed). TypeScript interfaces in verifier.ts match. |

**Score:** 4/4 success criteria fully verified

---

## Required Artifacts

| Artifact | Expected | Status | Details |
|----------|----------|--------|---------|
| `crates/analysis/src/ir.rs` | `Function.source_names: HashMap<String,String>` field | VERIFIED | Line 364: `pub source_names: std::collections::HashMap<String, String>`. |
| `crates/driver/src/mir_converter.rs` | `var_debug_info` harvest + ghost detection | VERIFIED | Lines 14, 24, 54 confirm `var_debug_info` iteration; `build_source_names` helper populates `source_names`. |
| `crates/driver/src/callbacks.rs` | Structured model pass-through, source location plumbing | VERIFIED | Line 693: `source_names: task_result.source_names.clone()` in VerificationFailure construction. |
| `crates/driver/src/cex_render.rs` | `render_counterexample`, `CexVariable`, `CexValue`, `render_typed_value` | VERIFIED | All public API present. 30 cex_render tests pass. |
| `crates/driver/src/lib.rs` | `mod cex_render` declaration | VERIFIED | Line 6: `pub mod cex_render;` |
| `crates/driver/src/diagnostics.rs` | Ariadne multi-label counterexample reporting | VERIFIED | Line 181: `Source::from`. Line 110: `render_counterexample`. `report_text_only` only in fallback branches. |
| `crates/driver/src/parallel.rs` | `build_counterexample_v2` uses `&ir_func.source_names` | VERIFIED | Line 372: `&ir_func.source_names` passed to `render_counterexample`. Identity map removed (commit 248fdc5). |
| `crates/driver/src/json_output.rs` | `JsonCounterexample`, `JsonCexVariable`, `JsonCexValue`, `JsonLocation` structs | VERIFIED | Lines 54-96 confirm all four structs. `JsonFailure.counterexample_v2: Option<JsonCounterexample>` at line 41. |
| `vscode-extension/src/verifier.ts` | `JsonCounterexample` and `JsonCexVariable` TypeScript interfaces | VERIFIED | Lines 29, 39 confirm `counterexample_v2?: JsonCounterexample` and `JsonCounterexample` interface present. |

---

## Key Link Verification

| From | To | Via | Status | Details |
|------|----|-----|--------|---------|
| `callbacks.rs` | `differential.rs` | `VcOutcome::Sat` carries `Vec<(String,String)>` | VERIFIED | Line 146 in differential.rs confirms type. |
| `mir_converter.rs` | `ir.rs` | `Function.source_names` populated from `body.var_debug_info` | VERIFIED | mir_converter.rs line 24 iterates `var_debug_info`. |
| `cex_render.rs` | `ir.rs` | `render_typed_value` dispatches on `ir::Ty` variants | VERIFIED | cex_render.rs line 11 imports `ir::{self, IntTy, Mutability, Ty, UintTy}`. |
| `cex_render.rs` | `differential.rs` | Takes `Vec<(String,String)>` model pairs | VERIFIED | `render_counterexample` signature at line 60 accepts `model: &[(String, String)]`. |
| `parallel.rs` | `ir.rs` | `build_counterexample_v2` uses `&ir_func.source_names` | VERIFIED | Line 372: `&ir_func.source_names` — identity map fully removed (commit 248fdc5). |
| `diagnostics.rs` | `cex_render.rs` | `report_with_ariadne` calls `render_counterexample` | VERIFIED | diagnostics.rs line 110: `crate::cex_render::render_counterexample(...)`. |
| `callbacks.rs` | `json_output.rs` | `JsonFailure.counterexample_v2` populated from `build_counterexample_v2` | VERIFIED | parallel.rs line 309: `build_counterexample_v2(...)` called with correct source_names. |
| `json_output.rs` | `verifier.ts` | TypeScript interface mirrors Rust struct field names | VERIFIED | verifier.ts lines 39-57 match json_output.rs struct definitions exactly. |

---

## Requirements Coverage

| Requirement | Source Plan | Description | Status | Evidence |
|-------------|------------|-------------|--------|---------|
| CEX-01 | 19-01-PLAN.md | User sees Rust variable names (not SSA names) in counterexample output | SATISFIED | Both terminal and JSON paths now use `ir_func.source_names`. Gap closure confirmed in commit 248fdc5. Full test suite (1134+ tests) passes. |
| CEX-02 | 19-02-PLAN.md | User sees typed Rust values (e.g. `i32: 5`, `bool: false`) not raw hex bitvectors | SATISFIED | `cex_render.rs` fully implements typed rendering. 30 cex_render tests pass. |
| CEX-03 | 19-03-PLAN.md | User sees counterexample values annotated at failing source line via ariadne labels | SATISFIED | diagnostics.rs: `Source::from` at line 181, `render_counterexample` at line 110, per-variable Labels at lines 123-166. |
| CEX-04 | 19-04-PLAN.md | Machine consumers receive structured `counterexample` field in `--output-format=json` output | SATISFIED | JsonCounterexample schema present and populated with correct Rust source names (CEX-01 gap now closed). |

---

## Anti-Patterns Found

| File | Line | Pattern | Severity | Impact |
|------|------|---------|----------|--------|
| _(none)_ | — | — | — | — |

The identity-map anti-pattern previously found in `parallel.rs` lines 369-374 has been removed (commit 248fdc5). No new anti-patterns introduced.

---

## Human Verification Required

### 1. Terminal Ariadne Output — Rust Names and Inline Span Labels

**Test:** Run `cargo verify` on a Rust function with a failing postcondition (e.g. `#[ensures(result >= 0)]` where result can be negative). Use text output format.
**Expected:** Terminal shows ariadne-formatted source span with per-variable labels like `x: i32 = -1` inline at the failing `#[ensures]` line. Variable names are Rust source names, not SSA names like `_1`.
**Why human:** Requires a real SMT solver run producing a SAT model; ariadne's terminal rendering cannot be statically verified.

### 2. JSON Output — Structured counterexample_v2 Field with Rust Names

**Test:** Run `cargo verify --output-format=json` on the same failing function and inspect the JSON output.
**Expected:** JSON contains `"counterexample_v2": { "variables": [{"name": "x", "type": "i32", "display": "i32: -1", ...}], "failing_location": {...}, "vc_kind": "...", "violated_spec": "..." }`. Variable names should now be Rust source names (`x`, `result`) not SSA names (`_1`, `_2`) — the gap has been closed.
**Why human:** Requires real solver run; JSON output needs end-to-end verification including SMT solving.

---

## Re-verification Summary

**Previous status:** gaps_found (3/4 success criteria, 1 gap)

**Gap that was closed:**

The sole gap was in `crates/driver/src/parallel.rs` `build_counterexample_v2()`. The function previously constructed a local `source_names` HashMap using an identity mapping (`local.name -> local.name`), bypassing the actual `ir_func.source_names` map harvested from `var_debug_info` in Plan 01.

**Fix applied (commit 248fdc5):**
- Removed the 7-line identity-map construction block (the old `let mut source_names = ...` loop)
- Replaced `&source_names` with `&ir_func.source_names` in the `render_counterexample` call at parallel.rs:372

**Verification of fix:**
- `git show 248fdc5` confirms the exact diff: `+        &ir_func.source_names,` replacing the identity map
- `cargo build -p rust-fv-driver` compiles cleanly (no errors)
- Full test suite: 1134+ tests, 0 failures, 0 regressions

All four success criteria are now fully satisfied. Phase 19 goal is achieved.

---

_Verified: 2026-02-19T18:45:00Z_
_Verifier: Claude (gsd-verifier)_
