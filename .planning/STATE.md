---
gsd_state_version: 1.0
milestone: v0.6
milestone_name: Cross-Crate Verification
status: in-progress
last_updated: "2026-02-28T11:04:10Z"
progress:
  total_phases: 4
  completed_phases: 0
  total_plans: 1
  completed_plans: 1
---

# Project State

## Project Reference

See: .planning/PROJECT.md (updated 2026-02-28)

**Core value:** Sound, automated verification of Rust code properties with minimal developer burden -- if the tool says "verified", it must be mathematically correct; if a developer can write a spec, the tool should prove it automatically 80-90% of the time for safe Rust.

**Current focus:** v0.6 Cross-Crate Verification — Phase 34 Plan 01 complete, Plan 02 (call-site alias VC injection) next.

## Current Position

Phase: 34 of 37 (Cross-Function Pointer Aliasing)
Plan: 34-01 complete, ready for 34-02
Status: In progress
Last activity: 2026-02-28 — Completed 34-01 cross-function pointer aliasing core infrastructure

Progress: [#░░░░░░░░░] ~5% (v0.6 milestone, 1/~20 plans)

## Performance Metrics

**Velocity (historical):**
- Total plans completed: 51+ (v0.1: 17, v0.2: 21, v0.3: 13, v0.4+v0.5: ~40+)
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
- v0.5-audit average: ~350s/plan, lean phases
- Trend: Stable

## Accumulated Context

### Decisions

Decisions are logged in PROJECT.md Key Decisions table.
Recent decisions relevant to v0.6:

- [Phase 33]: CallGraph bidirectional name_map normalization — normalize caller names internally, return full names via name_map
- [Phase 33]: encode_operand() wired directly into generate_float_vcs() — 3-line change pattern (minimal invasiveness)
- [Phase 33]: PtrCast alignment-check VC not yet generated — DEBTLINE in unsafe_verification.rs (v0.6 candidate)
- [v0.6 scope]: ALIAS gap at unsafe_verification.rs:1109-1135 — inter-procedural alias tracking via call-graph edges
- [v0.6 scope]: OPAQUE gap at vcgen.rs:2366-2376 — silent skip replaced by V060-series diagnostics (Phase 35) then infer_summary (Phase 36)
- [v0.6 scope]: XCREC gap in recursion_verification.rs — Tarjan's SCC limited/untested for cross-crate SCCs (Phase 37)
- [Phase 34-01]: generate_alias_check_assertion mirrors generate_null_check_assertion — Term::Eq(Const(p), Const(q)) pattern
- [Phase 34-01]: AliasPrecondition stores parameter indices (not names) for call-site substitution in Plan 02
- [Phase 34-01]: alias(p,q) parse arm directly calls generate_alias_check_assertion_from_terms — no intermediate representation
- [Phase 34-01]: alias_preconditions defaults to vec![] on all FunctionSummary sites — zero-cost for non-alias callee functions

### Pending Todos

0 pending.

### Blockers/Concerns

- [Phase 34] Call-graph edge aliasing propagation may require changes across unsafe_verification.rs and call_graph.rs — scope to be confirmed at planning
- [Phase 36] infer_summary inference strategy (read/write effects) needs research at Phase 36 planning — conservative pure-read default may be sufficient for v0.6
- [Phase 37] Cross-crate MIR availability: Tarjan's across crate boundaries requires exported symbol contract metadata — confirm nightly rustc metadata API at Phase 37 planning

## Session Continuity

Last session: 2026-02-28
Stopped at: Completed 34-01-PLAN.md — cross-function pointer aliasing core infrastructure (ed3aeb1)
Resume file: None
Next step: Execute 34-02-PLAN.md — call-site alias VC injection

---

*Last updated: 2026-02-28 — 34-01 complete: alias check assertion, VcKind::PointerAliasing, alias() spec_parser arm, AliasPrecondition/FunctionSummary extension*
