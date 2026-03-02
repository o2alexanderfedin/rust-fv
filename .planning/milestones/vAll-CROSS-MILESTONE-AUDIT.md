---
milestone: vAll
name: Cross-Milestone Comprehensive Audit (v0.1–v0.6)
audited: 2026-03-02T05:00:00Z
status: gaps_found
scores:
  requirements: 124/130
  phases: 38/38
  integration: 28/32
  flows: 7/9
gaps:
  requirements:
    - id: "TRT-01"
      status: "partial"
      phase: "08-trait-objects"
      claimed_by_plans: ["08-02-PLAN.md"]
      completed_by_plans: []
      verification_status: "passed (retrospective)"
      evidence: "generate_subtyping_vcs defined at behavioral_subtyping.rs:40 and unit-tested, but NEVER called from vcgen.rs or callbacks.rs production pipeline. Only called from trait_verification.rs test file. Behavioral subtyping VCs are NOT submitted to Z3 solver for user code."
    - id: "TRT-02"
      status: "partial"
      phase: "08-trait-objects"
      claimed_by_plans: ["08-02-PLAN.md"]
      completed_by_plans: []
      verification_status: "passed (retrospective)"
      evidence: "Same as TRT-01 — dynamic dispatch call sites use trait-level contracts only if generate_subtyping_vcs is wired. It is not."
    - id: "TRT-03"
      status: "partial"
      phase: "08-trait-objects"
      claimed_by_plans: ["08-02-PLAN.md"]
      completed_by_plans: []
      verification_status: "passed (retrospective)"
      evidence: "Same as TRT-01."
    - id: "TRT-04"
      status: "partial"
      phase: "08-trait-objects"
      claimed_by_plans: ["08-02-PLAN.md"]
      completed_by_plans: []
      verification_status: "passed (retrospective)"
      evidence: "Same as TRT-01."
    - id: "TRT-05"
      status: "partial"
      phase: "08-trait-objects"
      claimed_by_plans: ["08-02-PLAN.md"]
      completed_by_plans: []
      verification_status: "passed (retrospective)"
      evidence: "Same as TRT-01."
  integration:
    - "TRT-01..05: generate_subtyping_vcs (behavioral_subtyping.rs:40) is pub but never called from vcgen.rs or callbacks.rs — behavioral subtyping VCs not submitted to Z3 in production"
    - "CLO-01..06: defunctionalize_closure_call (defunctionalize.rs:53) is dead production code — live path uses encode_closure_as_uninterpreted (confirmed wired at vcgen.rs:281,872)"
  flows:
    - "Behavioral subtyping E2E flow: trait_analysis → behavioral_subtyping.rs → [BROKEN: no wiring to vcgen/driver] → Z3"
tech_debt:
  - phase: "04-differentiation"
    items:
      - "VERIFICATION.md still shows gaps_found — both gaps (bv2int, ghost filtering) closed by Phase 31 but file never updated"
  - phase: "08-trait-objects"
    items:
      - "generate_subtyping_vcs not wired into production vcgen pipeline — CRITICAL, not just tech debt"
  - phase: "27-async-cex-ide-fidelity"
    items:
      - "v0.4-MILESTONE-AUDIT.md still shows status: tech_debt — Phase 27 resolved it, audit file not updated"
  - phase: "v0.2-requirements"
    items:
      - "v0.2-REQUIREMENTS.md shows [ ] checkboxes and 'Pending' status for all 44 requirements despite being SHIPPED 2026-02-14"
  - phase: "v0.3-requirements"
    items:
      - "v0.3-REQUIREMENTS.md shows [ ] checkboxes and 'Pending' status for all 17 requirements despite being SHIPPED 2026-02-17"
  - phase: "audit-process"
    items:
      - "No MILESTONE-AUDIT.md for v0.2, v0.3, or v0.5 milestones"
      - "v0.5-audit-ROADMAP.md exists but no formal v0.5-MILESTONE-AUDIT.md"
  - phase: "34-cross-function-pointer-aliasing"
    items:
      - "DEBTLINE comments at unsafe_verification.rs:930,944 for alignment-check VC (pre-existing)"
  - phase: "37-cross-crate-scc-detection"
    items:
      - "vcgen.rs:3693 pre-existing TODO for error propagation in trigger-parsing handler"
      - "rustc_json.rs + cargo_verify.rs set inferred_summaries: None in alternative output paths"
  - phase: "36.1-alias-precondition-parsing"
    items:
      - "extract_alias_preconditions pub with no production callers — superseded by parse_alias_preconditions"
  - phase: "09-lifetime-reasoning"
    items:
      - "Conservative live ranges (0..num_blocks rather than precise intervals)"
  - phase: "07-closures"
    items:
      - "FnMut prophecy integration deferred (known scope boundary)"
---

# Cross-Milestone Comprehensive Audit: rust-fv v0.1–v0.6

**Audit Scope:** All 6 milestones (v0.1–v0.6), 38 active phases (1–33) + 6 archived v0.6 phases (34–37.1)
**Audited:** 2026-03-02T05:00:00Z
**Status:** ⚠ GAPS FOUND
**Score:** 124/130 requirements satisfied (TRT-01..05 partial — 6 reqs) | 38/38 phases verified | 7/9 E2E flows complete

---

## Source Code Truth

**`cargo test --workspace`:** 0 failures, exit code 0 (run 2026-03-02)

| Test Suite | Tests | Result |
|------------|-------|--------|
| rust_fv_analysis | 442 | ✅ 441 passed, 1 ignored |
| rust_fv_driver | 212 | ✅ 212 passed |
| smtlib | 165 | ✅ 165 passed |
| macros | 57 | ✅ 57 passed |
| Other suites | ~100+ | ✅ 0 failed |
| Doctests | ~45+ | ✅ 0 failed |
| **TOTAL** | **~1000+** | ✅ **0 failed** |

---

## Milestone Status Overview

| Milestone | Phases | Requirements | Audit Status | Audit Doc |
|-----------|--------|--------------|-------------|-----------|
| v0.1 POC | 1–5 | 37/37 | ✅ passed | v0.1-MILESTONE-AUDIT.md (updated Phase 33) |
| v0.2 Advanced | 6–12 | 44/44 (source truth) | ⚠ no audit file | MISSING |
| v0.3 Usability | 13–18 | 17/17 (source truth) | ⚠ no audit file | MISSING |
| v0.4 Full Rust | 19–27 | 16/16 | ⚡ tech_debt→resolved | v0.4-MILESTONE-AUDIT.md (Phase 27 fixed debt) |
| v0.5 SMT Complete | 28–33 | 9/9 | ⚠ no audit file | MISSING |
| v0.6 Cross-Crate | 34–37.1 | 7/7 | ✅ passed | v0.6-MILESTONE-AUDIT.md |

---

## Phase Verification Coverage

All 38 active phases have VERIFICATION.md files. All 6 archived v0.6 phases confirmed passed by v0.6 audit.

| Phase Range | Status | Notes |
|-------------|--------|-------|
| 01–03 | ✅ passed | Direct verification |
| 04 | ⚠ gaps_found (stale) | Gaps resolved by Phase 31; doc not updated |
| 05–08 | ✅ passed | Retrospective (Phase 32) |
| 09–03 | ✅ passed | Direct verification |
| 09–18 | ✅ passed | Mix of direct + retrospective |
| 19–27 | ✅ passed | Direct verification |
| 28–33 | ✅ passed | Direct verification |
| 34–37.1 | ✅ passed | Archived to milestones/v0.6-phases/ |
| 00-milestone-uat | ✅ passed | UAT 22/22 PASS |

---

## Requirements Coverage (3-Source Cross-Reference)

### v0.1 Requirements (37 total): 37/37 SATISFIED

All v0.1 requirements confirmed satisfied:
- SND-01..06: path-condition VCGen, overflow encoding, test suites, toolchain pinning ✅
- VER-01..05: loops, assert, panic, div-by-zero, shift overflow ✅
- TYP-01..04: struct, tuple, enum, array SMT encoding ✅
- SPEC-01..05: syn parser, quantifiers, ghost, int/nat, old() ✅
- MOD-01..04: contract summaries, call-site encoding, HIR contract map, ownership ✅
- BRW-01..03: prophecy variables, lifecycle, monomorphization ✅
- TOOL-01..05: cargo verify, colored output, Z3 bundled, tracing, error messages ✅
- PERF-01..05: sub-1s, sub-5s, VC caching, parallel, simplification ✅

### v0.2 Requirements (44 total): 44/44 SATISFIED (source truth)

Note: v0.2-REQUIREMENTS.md still shows `[ ]` — documentation inconsistency only.
Source code confirms all 44 implemented:
- REC-01..05: #[decreases], termination VCs, SCC mutual recursion, rejection ✅
- CLO-01..06: closure defunctionalization, Fn/FnMut/FnOnce, env encoding ✅
- **TRT-01..05: generate_subtyping_vcs implemented and unit-tested, VcKind::BehavioralSubtyping wired in diagnostics — ⚠ SEE CRITICAL GAP BELOW**
- LIF-01..06: NLL lifetime tracking, reborrow chains, outlives, borrow expiry ✅
- USF-01..06: unsafe detection, null/bounds checks, trusted annotation ✅
- FPV-01..06: IEEE 754 FPA theory, NaN/Inf VCs, perf warning ✅
- CON-01..06: happens-before, data race, lock invariants, deadlock, bounded ✅
- INF-01..04: petgraph, VcKind extensions, diagnostics, soundness tests ✅

### v0.3 Requirements (17 total): 17/17 SATISFIED (source truth)

Note: v0.3-REQUIREMENTS.md still shows `[ ]` — documentation inconsistency only.
- STDLIB-01..05: Vec/Option/Result/HashMap/Iterator contracts ✅
- PERF-01..06: <1s re-verify, push/pop, triggers, warnings, bv2int, differential ✅
- IDE-01..06: VSCode extension, rust-analyzer flycheck, marketplace ✅

### v0.4 Requirements (16 total): 16/16 SATISFIED

- CEX-01..04: typed counterexamples, ariadne labels, JSON output ✅
- SEP-01..04: pts_to, sep-conj, frame rule, ghost_predicate ✅
- WMM-01..04: RC11, 8 litmus tests, weak race detection, scope guard ✅
- HOF-01..02: fn_spec entailments, FnMut SSA environment ✅
- ASY-01..02: async functional props, state_invariant, **IDE fidelity CLOSED by Phase 27** ✅

### v0.5 Requirements (9 total): 9/9 SATISFIED

- VCGEN-01..06: memory ops, conditionals, casts, generics, float-to-int, projected LHS ✅
- MIRCONV-01..02: cast kind preservation, aggregate conversion ✅
Plus gap-closure requirements from phases 29.1–33 all satisfied.

### v0.6 Requirements (7 total): 7/7 SATISFIED

Per existing v0.6-MILESTONE-AUDIT.md (2026-03-02, status: passed):
- ALIAS-01..02: pointer aliasing, counterexample ✅
- OPAQUE-01..03: V060/V061, unsafe escalation, infer_summary ✅
- XCREC-01..02: cross-crate SCC, cross-crate #[decreases] ✅

---

## CRITICAL GAP: TRT-01..05 Behavioral Subtyping Production Wiring

### Finding

`generate_subtyping_vcs` at `crates/analysis/src/behavioral_subtyping.rs:40` is:

- **Fully implemented**: 500+ lines of logic, SMT encoding for behavioral subtyping
- **Thoroughly unit-tested**: 15+ tests in behavioral_subtyping.rs + 10 tests in trait_verification.rs
- **VcKind::BehavioralSubtyping**: Exists in vcgen.rs and diagnostics.rs for formatting
- **NOT CALLED FROM**: vcgen.rs production body, callbacks.rs, parallel.rs, or any driver code

**Grep evidence:**
```
# All callers of generate_subtyping_vcs:
crates/analysis/tests/trait_verification.rs:326,542,575,600,621,622,623  ← test-only
crates/analysis/src/behavioral_subtyping.rs:382,392,...                  ← self-tests only
```

No calls exist in: `crates/analysis/src/vcgen.rs`, `crates/driver/src/callbacks.rs`, `crates/driver/src/parallel.rs`

### Impact

When a developer annotates a trait with `#[requires]`/`#[ensures]` and writes an `impl Trait for Type`, the behavioral subtyping VCs are **NOT** generated and submitted to Z3. The function exists but is an island — unit-tested in isolation but never inserted into the live verification pipeline.

### Requirements Affected

TRT-01, TRT-02, TRT-03, TRT-04, TRT-05 (all 5 behavioral subtyping requirements from v0.2)

### Severity

⚠ **PARTIAL** — The infrastructure exists and is correct; the wiring is missing. A developer relying on trait contract verification would not receive VCs. This is a soundness gap for the advertised feature.

### Fix Required

In `crates/driver/src/callbacks.rs`, after collecting trait analysis data, identify `TraitImpl` functions and invoke `generate_subtyping_vcs` per impl, then submit VCs to the solver via the same path as other VC kinds.

---

## Closed Gaps (Previously Open, Now Resolved)

| Gap | Resolved By | Status |
|-----|-------------|--------|
| Phase 04 Z3 bv2int "unknown constant" | Phase 31 (uses_spec_int_types fix) | ✅ CLOSED |
| Phase 04 ghost locals filtering incomplete | Phase 31 (is_ghost_place guard) | ✅ CLOSED |
| Phase 23 async CEX TypeScript interface missing fields | Phase 27 (poll_iteration/await_side wired) | ✅ CLOSED |
| Phase 23 parallel.rs never populates async CEX fields | Phase 27 (build_counterexample_v2 fix) | ✅ CLOSED |
| Phase 11 float VCs use placeholder strings | Phase 33 (encode_operand wired) | ✅ CLOSED |
| Phase 04 VERIFICATION.md stale (gaps_found) | Resolved by Phase 31, **doc not updated** | ⚠ DOC ONLY |
| v0.4-MILESTONE-AUDIT.md shows tech_debt | Phase 27 resolved it, **audit not updated** | ⚠ DOC ONLY |
| v0.5 SetDiscriminant VCGen ignored test | Phase 30 (SetDiscriminant VCGen impl) | ✅ CLOSED |
| v0.5 for-loop VCGen partial (VCGEN-01) | Phase 29.1 (for_loop_vcgen.rs) | ✅ CLOSED |
| v0.5 prophecy test_prophecy_basic ignored | Phase 29.2 (convert_deref fix) | ✅ CLOSED |
| v0.5 generate_expiry_vcs stub | Phase 29.3 (statement scanning impl) | ✅ CLOSED |

---

## Integration Check Results

### Connected Exports (Wired Cross-Phase): 28/32

| Export | From | To | Status |
|--------|------|----|--------|
| generate_vcs_with_mode | vcgen.rs:837 | callbacks.rs:1111,1116 | ✅ WIRED |
| generate_vcs_with_db | vcgen.rs:246 | parallel.rs:264 | ✅ WIRED |
| from_functions_with_cross_crate_db | call_graph.rs:115 | vcgen.rs:373 | ✅ WIRED |
| ContractDatabase | contract_db.rs | callbacks.rs:133,174 | ✅ WIRED |
| FunctionSummary + is_inferred | contract_db.rs | callbacks.rs:456-457 | ✅ WIRED |
| AliasPrecondition | contract_db.rs | callbacks.rs → vcgen | ✅ WIRED |
| parse_alias_preconditions | callbacks.rs:937 | callbacks.rs:449 | ✅ WIRED |
| JsonCounterexample (poll_iteration, await_side) | json_output.rs | parallel.rs:414,427 | ✅ WIRED |
| load_default_contracts | stdlib_contracts/loader.rs | callbacks.rs:470 | ✅ WIRED |
| generate_termination_vcs | recursion.rs:67 | vcgen.rs:426 | ✅ WIRED |
| generate_float_vcs | float_verification.rs:91 | vcgen.rs:762 | ✅ WIRED |
| generate_async_vcs | async_vcgen.rs:47 | vcgen.rs:794 | ✅ WIRED |
| generate_rc11_vcs | concurrency/rc11.rs:255 | vcgen.rs:4130 | ✅ WIRED |
| generate_for_loop_vcs | for_loop_vcgen.rs | vcgen.rs:749 | ✅ WIRED |
| generate_expiry_vcs | borrow_conflict.rs | vcgen.rs:513 | ✅ WIRED |
| generate_alias_check_assertion | heap_model.rs | vcgen.rs (intra-crate) | ✅ WIRED |
| InferredSummary / inferred_summaries | json_output.rs | callbacks.rs:362-370 | ✅ WIRED |
| GhostPredicateDatabase | ghost_predicate_db.rs | callbacks.rs → VerificationTask | ✅ WIRED |
| VcKind::OpaqueCallee/Unsafe | vcgen.rs | diagnostics.rs:83, callbacks.rs:740 | ✅ WIRED |
| VcKind::InferredSummaryAlias (V062) | vcgen.rs:2446 | diagnostics.rs:85, callbacks.rs:742 | ✅ WIRED |
| encode_pts_to | sep_logic.rs | spec_parser.rs:836, vcgen.rs:2131-2172 | ✅ WIRED |
| hof_vcgen | hof_vcgen.rs | vcgen.rs:741-743 | ✅ WIRED |
| defunctionalize (live path) | defunctionalize.rs | vcgen.rs:281,872 | ✅ WIRED |
| trait_analysis | trait_analysis.rs | vcgen.rs (trait DB) | ✅ WIRED |
| bv2int + uses_spec_int_types | bv2int.rs | vcgen.rs:1532, 14 callsites | ✅ WIRED |
| mir_converter | mir_converter.rs | callbacks.rs pipeline | ✅ WIRED |
| simplify_term / simplify_script | simplify.rs | solver pipeline | ✅ WIRED |
| JsonVerificationReport | json_output.rs | rustc_json.rs, verifier.ts | ✅ WIRED |

### Orphaned / Missing Connections: 4

| Export | Issue | Requirements | Severity |
|--------|-------|--------------|---------|
| generate_subtyping_vcs | Test-only; not called from vcgen or driver | TRT-01..05 | 🔴 CRITICAL |
| defunctionalize_closure_call | Dead production code; live path uses encode_closure_as_uninterpreted | CLO-01..06 | ℹ INFO (not blocking — live path wired) |
| extract_alias_preconditions | Superseded by parse_alias_preconditions; pub but test-only | ALIAS-01..02 | ℹ INFO (per v0.6 audit) |
| v0.4-MILESTONE-AUDIT.md tech_debt status | Phase 27 resolved the debt; audit doc stale | ASY-01..02 | ⚠ DOC ONLY |

### E2E Flows: 7/9 Complete

| Flow | Requirements | Status |
|------|-------------|--------|
| Soundness VCGen → Z3 → diagnostics | SND-01..06, VER-01..05 | ✅ Complete |
| Modular contracts → call-site VCs → Z3 | MOD-01..04, BRW-01..03 | ✅ Complete |
| async fn → CoroutineInfo → VCs → Z3 → IDE (poll_iteration/await_side) | ASY-01..02, CEX-01..04 | ✅ Complete (Phase 27 fix) |
| WMM RC11 atomics → happens-before → Z3 | CON-01..06, WMM-01..04 | ✅ Complete |
| Cross-crate alias → alias_preconditions → VCs → Z3 | ALIAS-01..02, OPAQUE-01..03 | ✅ Complete |
| Cross-crate SCC → termination VCs → Z3 | XCREC-01..02, REC-01..05 | ✅ Complete |
| bv2int mode → differential testing → equivalence | PERF-05..06 (v0.3), VCGEN-01..06 | ✅ Complete |
| **Behavioral subtyping → generate_subtyping_vcs → Z3** | **TRT-01..05** | **⚠ BROKEN (not wired)** |
| defunctionalize_closure_call alternative path | CLO-01..06 | ⚠ Dead code (encode_closure_as_uninterpreted is live path; acceptable) |

---

## Tech Debt Summary (Non-Blocking Items)

| Item | Phase | Severity |
|------|-------|---------|
| v0.2-REQUIREMENTS.md: all [ ] unchecked despite SHIPPED | docs | Low |
| v0.3-REQUIREMENTS.md: all [ ] unchecked despite SHIPPED | docs | Low |
| Phase 04 VERIFICATION.md: gaps_found despite gaps closed | docs | Low |
| v0.4-MILESTONE-AUDIT.md: tech_debt despite Phase 27 fix | docs | Low |
| No MILESTONE-AUDIT.md for v0.2, v0.3, v0.5 | process | Low |
| extract_alias_preconditions: pub with no production callers | code | Low |
| rustc_json.rs + cargo_verify.rs: inferred_summaries: None | code | Low |
| vcgen.rs:3693 pre-existing trigger-parsing TODO | code | Info |
| defunctionalize_closure_call: dead production code | code | Info |
| Conservative live ranges in lifetime_analysis | code | Deferred |
| FnMut prophecy integration deferred | scope | Deferred |
| unsafe_verification.rs:930,944 DEBTLINE alignment check | code | Future |

---

## Milestone Definition of Done Assessment

| Milestone | Goal | Status |
|-----------|------|--------|
| v0.1: Sound verification POC | 248 tests, 5-crate workspace, E2E pipeline | ✅ ACHIEVED |
| v0.2: Advanced language features | Recursive, closures, traits, lifetimes, unsafe, FP, concurrency | ⚠ PARTIAL (TRT wiring gap) |
| v0.3: Production usability | Stdlib contracts, incremental, IDE, bv2int | ✅ ACHIEVED |
| v0.4: Full Rust verification | CEX, sep logic, WMM, HOF, async | ✅ ACHIEVED (Phase 27 closed tech debt) |
| v0.5: SMT completeness | All Rust expr categories generate VCs | ✅ ACHIEVED |
| v0.6: Cross-crate verification | Aliasing, opaque callees, cross-crate SCC | ✅ ACHIEVED |

---

## Audit Conclusion

The rust-fv project has delivered on 5 of 6 milestone goals. All 130 requirements are considered implemented at the unit-test level, and `cargo test --workspace` passes with 0 failures. However, one structural integration gap was discovered:

**`generate_subtyping_vcs` (behavioral_subtyping.rs:40) is never called from the live verification pipeline.** TRT-01..05 behavioral subtyping verification (v0.2 milestone requirement) is fully implemented and unit-tested but silently does not execute when a user runs `cargo verify` on Rust code with trait contracts. This is a soundness gap for the advertised v0.2 feature.

**Recommended next action:** Create a fix phase to wire `generate_subtyping_vcs` into the driver pipeline (callbacks.rs), identify trait impls with contracts, and submit behavioral subtyping VCs to Z3.

---

## Gap Closure Path

### Required Fix: TRT-01..05 Behavioral Subtyping Wiring

**File:** `crates/driver/src/callbacks.rs`
**Change:** After `after_analysis` collects `TraitDatabase`, identify trait impls with contracts and call `generate_subtyping_vcs` per impl, then submit VCs via the standard parallel.rs path.

```
New phase: 38-trait-subtyping-wiring
Goal: Wire generate_subtyping_vcs into callbacks.rs after_analysis for trait impls with contracts
Requirements: TRT-01..05
```

---

*Audited: 2026-03-02T05:00:00Z*
*Auditor: Claude (gsd-audit-milestone)*
*Source truth: cargo test --workspace → 0 failures*
