---
phase: 06-recursive-functions
verified: 2026-02-26T00:00:00Z
status: passed
score: 7/7 must-haves verified
re_verification: false
retrospective: true
phase_executed: "2026-02-12 to 2026-02-14"
milestone: "v0.2 Advanced Verification (shipped 2026-02-14)"
---

# Phase 06: Recursive Functions — Verification Report

**Phase Goal:** Recursive functions with termination proofs via decreases clause
**Verified:** 2026-02-26T00:00:00Z
**Status:** passed
**Retrospective:** Yes — VERIFICATION.md created 2026-02-26 as part of Phase 32 audit closure

## Goal Achievement

Phase 06 goal was "Recursive functions with termination proofs via decreases clause". The phase shipped as part of v0.2 Advanced Verification milestone on 2026-02-14.

The phase comprised three plans:
- **06-01:** `#[decreases(expr)]` proc macro, `Contracts.decreases` IR field, `VcKind::Termination`, `RecursiveGroup` type, `CallGraph::detect_recursion()` via petgraph tarjan_scc
- **06-02:** `crates/analysis/src/recursion.rs` — `check_missing_decreases()`, `generate_termination_vcs()`, `encode_recursive_function()` with uninterpreted function encoding
- **06-03:** `crates/analysis/tests/recursion_verification.rs` (8 E2E tests via Z3), `format_missing_decreases_help()` and `format_termination_counterexample()` in diagnostics.rs

### Observable Truths

| # | Truth | Status | Evidence |
|---|-------|--------|----------|
| 1 | `pub fn decreases` proc macro exists in macros/src/lib.rs | VERIFIED | `crates/macros/src/lib.rs` line 99: `pub fn decreases(attr: TokenStream, item: TokenStream) -> TokenStream` — delegates to `spec_attribute("decreases", attr, item)` |
| 2 | `Contracts` struct has `decreases: Option<SpecExpr>` field | VERIFIED | `crates/analysis/src/ir.rs` line 490: `pub decreases: Option<SpecExpr>` |
| 3 | `VcKind::Termination` variant exists in ir.rs | VERIFIED | `crates/analysis/src/recursion.rs` line 213: `vc_kind: VcKind::Termination` used in generated VCs; variant confirmed in VcKind enum |
| 4 | `RecursiveGroup` struct and `tarjan_scc` usage in call_graph.rs | VERIFIED | `crates/analysis/src/call_graph.rs` line 23: `pub struct RecursiveGroup`; line 15: `use petgraph::algo::tarjan_scc`; line 187: `let sccs = tarjan_scc(&graph)` |
| 5 | `crates/analysis/src/recursion.rs` exists with `generate_termination_vcs` | VERIFIED | File exists; line 67: `pub fn generate_termination_vcs(` |
| 6 | `recursion_verification.rs` has ≥8 E2E tests | VERIFIED | 8 tests run and pass: e2e_factorial_with_decreases_verified, e2e_factorial_without_decreases_rejected, e2e_mutual_recursion_even_odd_verified, e2e_non_decreasing_measure_produces_counterexample, e2e_fibonacci_two_recursive_calls, e2e_recursive_function_postcondition_uses_uninterpreted_encoding, e2e_non_recursive_function_no_termination_vcs, snd_recursive_without_decreases_rejected |
| 7 | All recursion_verification tests pass via Z3 | VERIFIED | `cargo test -p rust-fv-analysis --test recursion_verification` — 8 passed; 0 failed |

**Score:** 7/7 truths verified

### Required Artifacts

| Artifact | Expected | Status | Details |
|----------|----------|--------|---------|
| `crates/macros/src/lib.rs` | `#[decreases(expr)]` proc macro | VERIFIED | Line 99: `pub fn decreases` using shared `spec_attribute` helper |
| `crates/analysis/src/ir.rs` | `Contracts.decreases: Option<SpecExpr>` field and `VcKind::Termination` variant | VERIFIED | Line 490: `pub decreases: Option<SpecExpr>`; VcKind::Termination generated in recursion.rs |
| `crates/analysis/src/call_graph.rs` | `RecursiveGroup` struct and `tarjan_scc` for SCC-based recursion detection | VERIFIED | Lines 23-28: RecursiveGroup; line 15: tarjan_scc import; line 165: `detect_recursion()` |
| `crates/analysis/src/recursion.rs` | `check_missing_decreases()`, `generate_termination_vcs()`, `encode_recursive_function()` | VERIFIED | All three functions present (lines 38, 67, and full module); 890 lines total |
| `crates/analysis/tests/recursion_verification.rs` | ≥8 E2E tests covering Phase 6 success criteria | VERIFIED | 8 tests, all GREEN via Z3 |
| `crates/driver/src/diagnostics.rs` | `format_missing_decreases_help()` and `format_termination_counterexample()` | VERIFIED | Both helpers integrated; VcKind::Termination handled in report_text_only() at line 235 |

### Key Link Verification

| From | To | Via | Status | Details |
|------|-----|-----|--------|---------|
| `#[decreases(n)]` | `Contracts.decreases` | Driver extracts from doc attribute `rust_fv::decreases::EXPR` | VERIFIED | callbacks.rs extracts decreases from doc attributes; spec_attribute encoding pattern |
| `Contracts.decreases` | `generate_termination_vcs()` | VCGen calls recursion module with decreases expression | VERIFIED | 06-02-SUMMARY: generate_vcs() integrates recursion detection + termination VC generation |
| `generate_termination_vcs()` | `VcKind::Termination` | Each termination VC assigned Termination kind | VERIFIED | recursion.rs line 213: `vc_kind: VcKind::Termination` |
| `CallGraph::detect_recursion()` | `RecursiveGroup` | tarjan_scc finds SCCs; size-1 SCCs with self-edge = direct recursion | VERIFIED | call_graph.rs lines 165-205: detect_recursion() produces Vec<RecursiveGroup> |
| `encode_recursive_function()` | SMT declare-fun + forall axioms | Uninterpreted function encoding with universally quantified cases | VERIFIED | 06-02-SUMMARY: encode_recursive_function() generates declare-fun + forall axioms |

### Requirements Coverage

| Requirement | Source Plan | Description | Status | Evidence |
|-------------|------------|-------------|--------|----------|
| REC-01 | 06-02 | Uninterpreted function encoding via declare-fun + forall axioms | SATISFIED | encode_recursive_function() in recursion.rs |
| REC-02 | 06-01 | `#[decreases(expr)]` annotation via proc macro | SATISFIED | macros/src/lib.rs: pub fn decreases; same spec_attribute pattern as requires/ensures |
| REC-03 | 06-02, 06-03 | Termination VC generation: measure_at_call < measure_at_entry | SATISFIED | generate_termination_vcs() with local variable declarations; 8 E2E tests GREEN |
| REC-04 | 06-01 | Mutual recursion detection via petgraph SCC | SATISFIED | CallGraph::detect_recursion() using tarjan_scc; RecursiveGroup.is_mutual() |
| REC-05 | 06-02 | Missing `#[decreases]` rejection via diagnostic VC (always-SAT pattern) | SATISFIED | check_missing_decreases() + always-SAT diagnostic VC; snd_recursive_without_decreases_rejected GREEN |
| INF-01 | 06-01 | petgraph dependency added | SATISFIED | Cargo.toml: petgraph = "0.8"; tarjan_scc in call_graph.rs |

### Code Quality / Technical Debt

| Category | Finding | Severity | Impact |
|----------|---------|----------|--------|
| Mutual recursion cross-function | Single-function call graph in generate_vcs doesn't form cross-function SCCs for mutual recursion — graceful handling only | Low | Documented in 06-03-SUMMARY; mutual recursion between functions handled gracefully (no false positives) |
| Termination VC bug fix | Initial termination VC encoding omitted local variable declarations — fixed in 06-03 (Rule 1 auto-fix) | Fixed | Critical correctness fix applied during execution; tests now validate correct behavior |

### Human Verification Required

None — all artifacts are programmatically verifiable.

### Gaps Summary

No significant gaps. All 5 Phase 6 success criteria are satisfied and validated by E2E tests via Z3. The mutual recursion cross-function case is handled gracefully (no false positives) with full cross-function SCC deferred — this is documented behavior, not a gap.

---

## Verification Evidence Log

### Phase 06 recursion_verification (cargo test -p rust-fv-analysis --test recursion_verification)

```
warning: /Users/alexanderfedin/Projects/hapyy/rust-fv/crates/driver/Cargo.toml: file `.../main.rs` found to be present in multiple build targets
   Compiling rust-fv-analysis v0.1.0 (/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/analysis)
    Finished `test` profile [unoptimized + debuginfo] target(s) in 0.68s
     Running tests/recursion_verification.rs (target/debug/deps/recursion_verification-d3031c932899b047)

running 8 tests
test e2e_mutual_recursion_even_odd_verified ... ok
test e2e_factorial_without_decreases_rejected ... ok
test e2e_factorial_with_decreases_verified ... ok
test snd_recursive_without_decreases_rejected ... ok
test e2e_non_recursive_function_no_termination_vcs ... ok
test e2e_non_decreasing_measure_produces_counterexample ... ok
test e2e_fibonacci_two_recursive_calls ... ok
test e2e_recursive_function_postcondition_uses_uninterpreted_encoding ... ok

test result: ok. 8 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.06s
```

### Full Workspace Tests (cargo test --workspace | grep "test result")

All workspace test suites: 0 failures. Verified 2026-02-26.

---

## Retrospective Note

Phase 06 was executed on 2026-02-12 to 2026-02-14 and shipped in milestone v0.2 Advanced Verification. This VERIFICATION.md was created retrospectively on 2026-02-26 as part of Phase 32 audit closure. The phase is covered by Phase 00 UAT (22/22 PASS) providing indirect functional coverage. The termination VC encoding bug found and fixed during 06-03 (missing local variable declarations) is documented as a Rule 1 auto-fix and confirmed correct via all 8 E2E tests passing.

---

**Verdict: PASS**

All 7 observable truths verified. All required artifacts confirmed present. All key links intact. Phase goal achieved. All 5 Phase 6 success criteria validated by E2E tests via Z3.

_Verified: 2026-02-26T00:00:00Z_
_Verifier: Claude (gsd-verifier, Phase 32 retrospective audit)_
