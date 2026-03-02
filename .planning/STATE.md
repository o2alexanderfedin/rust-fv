---
gsd_state_version: 1.0
milestone: v0.6
milestone_name: Cross-Crate Verification
status: unknown
last_updated: "2026-03-02T02:26:05.294Z"
progress:
  total_phases: 44
  completed_phases: 44
  total_plans: 125
  completed_plans: 126
---

# Project State

## Project Reference

See: .planning/PROJECT.md (updated 2026-02-28)

**Core value:** Sound, automated verification of Rust code properties with minimal developer burden -- if the tool says "verified", it must be mathematically correct; if a developer can write a spec, the tool should prove it automatically 80-90% of the time for safe Rust.

**Current focus:** v0.6 Cross-Crate Verification — Phase 37.1 Plan 01 COMPLETE (is_inferred+alias guard, V062 InferredSummaryAlias, driver wiring). ALIAS-01 and ALIAS-02 satisfied.

## Current Position

Phase: 37.1 of 44 (Inferred Summary Alias Guard) — COMPLETE (1/1 plans complete)
Plan: 37.1-01 complete
Status: Phase 37.1 complete
Last activity: 2026-03-02 — Completed 37.1-01: guard is_inferred early-continue for alias_preconditions co-occurrence, V062 InferredSummaryAlias VcKind, diagnostics.rs/callbacks.rs wiring (04852d9); ALIAS-01 and ALIAS-02 satisfied

Progress: [######░░░░] ~40% (v0.6 milestone, 7/~20 plans)

## Performance Metrics

**Velocity (historical):**
- Total plans completed: 53+ (v0.1: 17, v0.2: 21, v0.3: 13, v0.4+v0.5: ~40+, v0.6: 2)
- Average duration: 400-800s/plan (v0.5-audit baseline)
- Total execution time: ~8 days across v0.1-v0.5-audit

**By Milestone:**

| Milestone | Phases | Plans | Timeline |
|-----------|--------|-------|----------|
| v0.1 POC | 5 | 17 | 2 days |
| v0.2 Advanced | 7 | 21 | 3 days |
| v0.3 Usability | 6 | 13 | 1 day |
| v0.4 Full Rust | 9 | ~27 | 6 days |
| v0.5 + Audit | 11 | ~22 | 3 days |
| v0.6 (planned) | 4 | TBD | TBD |

**Recent Trend:**
- Phase 34: Plan 01 ~12min, Plan 02 ~9min
- Trend: Stable
| Phase 35 P02 | 5 | 2 tasks | 1 files |
| Phase 36-summary-contract-inference P01 | 35 | 3 tasks | 33 files |
| Phase 36-summary-contract-inference P02 | 0 | 2 tasks | 4 files |
| Phase 37-cross-crate-scc-detection P01 | 480 | 2 tasks | 1 files |
| Phase 37-cross-crate-scc-detection P02 | 900 | 2 tasks | 2 files |
| Phase 37-cross-crate-scc-detection P03 | 720 | 2 tasks | 2 files |
| Phase 37.1-inferred-summary-alias-guard P01 | 480 | 2 tasks | 3 files |

## Accumulated Context

### Decisions

Decisions are logged in PROJECT.md Key Decisions table.
Recent decisions relevant to v0.6:

- [Phase 33]: CallGraph bidirectional name_map normalization — normalize caller names internally, return full names via name_map
- [Phase 33]: encode_operand() wired directly into generate_float_vcs() — 3-line change pattern (minimal invasiveness)
- [Phase 33]: PtrCast alignment-check VC not yet generated — DEBTLINE in unsafe_verification.rs (v0.6 candidate)
- [v0.6 scope]: OPAQUE gap at vcgen.rs — silent skip replaced by V060-series diagnostics (Phase 35) then infer_summary (Phase 36)
- [v0.6 scope]: XCREC gap in recursion_verification.rs — Tarjan's SCC limited/untested for cross-crate SCCs (Phase 37)
- [Phase 34-01]: generate_alias_check_assertion mirrors generate_null_check_assertion — Term::Eq(Const(p), Const(q)) pattern
- [Phase 34-01]: AliasPrecondition stores parameter indices (not names) for call-site substitution in Plan 02
- [Phase 34-01]: alias(p,q) parse arm directly calls generate_alias_check_assertion_from_terms — no intermediate representation
- [Phase 34-01]: alias_preconditions defaults to vec![] on all FunctionSummary sites — zero-cost for non-alias callee functions
- [Phase 34-02]: Refactored early-return guard in generate_call_site_vcs — has_requires || has_alias_preconditions so alias VCs generated even when requires is empty
- [Phase 34-02]: Alias VC script mirrors precondition VC structure — base_script + prior assignments + caller preconditions + path condition, asserts p == q (SAT = violation)
- [Phase 34-02]: DEBTLINE test upgraded with ContractDatabase — null-check VC retained as regression guard alongside new alias VC assertion
- [Phase 34-02]: extract_alias_preconditions uses strip_prefix('!').map(str::trim) — idiomatic Rust per clippy::manual_strip
- [Phase 35-01]: OpaqueCallee always-SAT VC pattern — BoolLit(true) VC with vc_kind carrying diagnostic classification (mirrors DataRaceFreedom)
- [Phase 35-01]: Deduplication via seen_opaque HashSet — at most one OpaqueCallee per (callee_name, vc_kind) pair per function
- [Phase 35-01]: OpaqueCallee SAT excluded from failure push in callbacks.rs — SAT = diagnostic fired (warning only); OpaqueCalleeUnsafe SAT IS a failure
- [Phase 35-01]: None contract_db skips call-site processing entirely; Some(&empty_db) emits OpaqueCallee diagnostics
- [Phase 35]: Five integration tests added with exact names (test_opaque_callee_safe_warning, etc.) providing end-to-end regression guard for V060/V061
- [Phase 36-summary-contract-inference]: infer_summary suppression via is_inferred flag on FunctionSummary — early continue in generate_call_site_vcs before has_requires check
- [Phase 36-summary-contract-inference]: Synthetic DB entry guard: || contracts.is_inferred added to existing OR-chain — minimal invasiveness
- [Phase 36-summary-contract-inference]: is_inferred propagation via doc-attr pattern matching rust_fv::infer_summary in extract_contracts (mirrors is_pure arm)
- [Phase 36-summary-contract-inference]: inferred_summaries omitted entirely (None) when no infer_summary callees — skip_serializing_if ensures field absent rather than null or empty array
- [Phase 36-summary-contract-inference]: ContractDatabase::iter() added as public API enabling callbacks.rs to enumerate all entries for JSON report population
- [Phase 36.1-alias-precondition-parsing]: extract_contracts() return type changed from HashMap<LocalDefId, Contracts> to HashMap<LocalDefId, HirContracts> — preserves unsafe_requires across HIR->IR boundary; hir_contracts_to_ir() added as converter
- [Phase 36.1-alias-precondition-parsing]: UNSAT alias VC requires caller anti-alias precondition (_1 != _2) — alias VC is SAT-based (asserts equality = violation); distinct locals alone are insufficient without constraint
- [Phase 36.1-alias-precondition-parsing]: parse_alias_preconditions() uses source_to_idx (source param name -> zero-based index) built by inverting build_source_names() against args_iter()
- [Phase 37-cross-crate-scc-detection]: from_functions_with_cross_crate_db accepts ContractDatabase and injects virtual nodes for contracted callees; back-edge heuristic via decreases.raw substring match enables cross-crate SCC detection
- [Phase 37-02]: generate_termination_vcs uses caller-side VC for cross-crate calls (callee body unavailable); vcgen.rs uses match contract_db to select from_functions_with_cross_crate_db vs from_functions
- [Phase 37-03]: normalize_callee fallback — generate_termination_vcs group check uses || !group.contains(callee_name) to match full-path cross-crate callee names stored in RecursiveGroup
- [Phase 37-03]: Cross-crate SCC integration test pattern — ContractDatabase with back-edge heuristic (decreases.raw contains in-crate fn name) -> generate_vcs -> filter Termination VCs -> Z3 UNSAT/SAT check
- [Phase 37.1-inferred-summary-alias-guard]: V062 InferredSummaryAlias: hoist has_alias_preconditions before is_inferred guard; always-SAT warning VC; excluded from failure-push; Warning severity in diagnostics

### Pending Todos

0 pending.

### Blockers/Concerns

None current. Phase 37 complete (all 3 plans). XCREC-01 and XCREC-02 satisfied end-to-end. v0.6 milestone complete.

## Session Continuity

Last session: 2026-03-02
Stopped at: Completed 37.1-01-PLAN.md — guard is_inferred+alias co-occurrence, V062 InferredSummaryAlias (04852d9); ALIAS-01 and ALIAS-02 satisfied; Phase 37.1 complete
Resume file: None
Next step: Phase 37.1 complete. Next phase or milestone planning.

---

*Last updated: 2026-03-02 — 37.1-01 complete: guard is_inferred+alias co-occurrence, VcKind::InferredSummaryAlias (V062), diagnostics.rs/callbacks.rs wiring; ALIAS-01 and ALIAS-02 satisfied; Phase 37.1 fully complete*
