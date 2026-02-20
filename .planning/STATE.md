# Project State

## Project Reference

See: .planning/PROJECT.md (updated 2026-02-19)

**Core value:** Sound, automated verification of Rust code properties with minimal developer burden -- if the tool says "verified", it must be mathematically correct; if a developer can write a spec, the tool should prove it automatically 80-90% of the time for safe Rust.

**Current focus:** v0.4 Full Rust Verification — Phase 19 (Counterexample Generation) Plan 1 complete

## Current Position

Phase: 19 of 23 (Counterexample Generation)
Plan: 1 complete, advancing to Plan 2
Status: In progress
Last activity: 2026-02-20 — Plan 19-01 complete (structured counterexample data foundation)

Progress: [████████████████░░░░░░░░] 72% (18/23 phases complete, Phase 19 in progress — 1/4 plans done)

## Performance Metrics

**Velocity:**
- Total plans completed: 51 (v0.1: 17, v0.2: 21, v0.3: 13)
- Average duration: 800 seconds (v0.3 baseline)
- Total execution time: 5 days (v0.1: 2d, v0.2: 3d, v0.3: 1d)

**By Milestone:**

| Milestone | Phases | Plans | Timeline |
|-----------|--------|-------|----------|
| v0.1 POC | 5 | 17 | 2 days |
| v0.2 Advanced | 7 | 21 | 3 days |
| v0.3 Usability | 6 | 13 | 1 day |
| v0.4 Full Rust | 5 | TBD | In progress |

**Recent Trend:**
- v0.3 average: 800s/plan, 13 plans across 6 phases
- Trend: Stable

*Updated after each plan completion*

## Accumulated Context

### Decisions

Decisions are logged in PROJECT.md Key Decisions table.
Recent decisions relevant to v0.4:

- [Phase 18]: Post-hoc QF_BV→QF_LIA/QF_NIA replacement (minimally invasive)
- [Phase 18]: SolverInterface trait in differential.rs (self-contained, no binary dep)
- [v0.4 research]: Counterexample must be built first — force multiplier for all other features
- [v0.4 research]: Separation logic uses distinct heap domain (not byte-array model) to avoid conflict with heap_model.rs
- [v0.4 research]: Weak memory axioms scoped to WeakMemory* VcKind only — prevents SeqCst regressions
- [v0.4 research]: Z3 MBQI preferred for HOF spec entailment queries (heavy universal quantification)
- [v0.4 research]: Async coroutine detection in driver only — rustc internals must not leak into analysis crate
- [Phase 19-01]: Source location plumbing uses pre-built HashMap approach: build_source_location_map() during after_analysis while TyCtxt is live, then pass HashMap into parallel tasks — avoids TyCtxt lifetime issues in rayon threads
- [Phase 19-01]: Ghost detection via __ghost_ name prefix is simpler than HIR attribute scanning and sufficient for the proc macro convention used in the codebase
- [Phase 19-01]: source_column stored 1-based (col_display + 1) to match convention in source_line

### Pending Todos

0 pending.

### Blockers/Concerns

**v0.4 phase-specific risks (from research):**
- [Phase 20] Heap domain choice (Viper Ref sort vs bitvector-set permissions) — resolve at Phase 20 planning
- [Phase 21] RC11 AcqRel encoding — not equivalent to Release OR Acquire; derive from arXiv:2108.06944
- [Phase 23] Async coroutine MIR shape may have changed post-PR#145330 — validate with RUSTFLAGS="-Zunpretty=mir" before Phase 23

## Session Continuity

Last session: 2026-02-20
Stopped at: Completed 19-01-PLAN.md — structured counterexample data foundation
Resume file: None
Next step: /gsd:execute-phase 19-02 (typed value rendering module cex_render.rs)

---

*State initialized: 2026-02-14*
*Last updated: 2026-02-19 after v0.4 roadmap creation*
