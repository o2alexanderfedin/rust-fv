---
gsd_state_version: 1.0
milestone: v0.6
milestone_name: Cross-Crate Verification
status: unknown
last_updated: "2026-02-28T21:02:27.906Z"
progress:
  total_phases: 41
  completed_phases: 40
  total_plans: 120
  completed_plans: 120
---

# Project State

## Project Reference

See: .planning/PROJECT.md (updated 2026-02-28)

**Core value:** Sound, automated verification of Rust code properties with minimal developer burden -- if the tool says "verified", it must be mathematically correct; if a developer can write a spec, the tool should prove it automatically 80-90% of the time for safe Rust.

**Current focus:** v0.6 Cross-Crate Verification — Phase 36 Plan 01 complete (infer_summary). Phase 37 (cross-crate recursion) is next.

## Current Position

Phase: 36 of 37 (Summary Contract Inference) — Plan 01 COMPLETE
Plan: 36-01 complete
Status: In progress
Last activity: 2026-02-28 — Completed 36-01 infer_summary proc-macro + OpaqueCallee suppression (5f0d7f6)

Progress: [####░░░░░░] ~20% (v0.6 milestone, 4/~20 plans)

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

### Pending Todos

0 pending.

### Blockers/Concerns

- [Phase 37] Cross-crate MIR availability: Tarjan's across crate boundaries requires exported symbol contract metadata — confirm nightly rustc metadata API at Phase 37 planning

## Session Continuity

Last session: 2026-02-28
Stopped at: Completed 36-01-PLAN.md — infer_summary proc-macro, is_inferred flag, OpaqueCallee suppression; OPAQUE-03 fulfilled (5f0d7f6)
Resume file: None
Next step: Execute Phase 37 — cross-crate recursion (XCREC)

---

*Last updated: 2026-02-28 — 36-01 complete: #[verifier::infer_summary] proc-macro with is_inferred propagation, OpaqueCallee suppression for annotated callees, OPAQUE-03 requirement fulfilled*
