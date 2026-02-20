# Project State

## Project Reference

See: .planning/PROJECT.md (updated 2026-02-19)

**Core value:** Sound, automated verification of Rust code properties with minimal developer burden -- if the tool says "verified", it must be mathematically correct; if a developer can write a spec, the tool should prove it automatically 80-90% of the time for safe Rust.

**Current focus:** v0.4 Full Rust Verification — Phase 20 (Separation Logic) Plan 3 complete

## Current Position

Phase: 20 of 23 (Separation Logic)
Plan: 3 complete
Status: In progress
Last activity: 2026-02-20 — Plan 20-03 complete (sep-conj detection, ghost predicate expansion, frame rule, AUFBV logic selection)

Progress: [████████████████░░░░░░░░] 72% (18/23 phases complete, Phase 19 in progress — 4/4 plans done)

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
| Phase 19 P02 | 624 | 1 tasks | 8 files |
| Phase 19 P04 | 155 | 2 tasks | 7 files |
| Phase 19 P03 | 484 | 2 tasks | 3 files |
| Phase 20 P03 | 893 | 2 tasks | 3 files |
| Phase 20 P02 | 34 | 2 tasks | 5 files |
| Phase 20 P01 | 10 | 2 tasks | 3 files |

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
- [Phase 19]: cex_render: collapsible-if clippy fixed with let-chain syntax; JsonCounterexample needs Debug+Clone derives for use in VerificationFailure/Result; counterexample_v2 field backfilled across 8 files
- [Phase 19-04]: counterexample_v2 populated via build_counterexample_v2() in parallel.rs (where IR func data is available) not callbacks.rs; additive schema with backward compat flat field preserved
- [Phase 19-04]: TypeScript interfaces in verifier.ts mirror Rust struct field names exactly (type: string maps to Rust ty: String via serde rename)
- [Phase 19]: ariadne multi-label wiring: source_names/locals/params threaded through VerificationTaskResult to VerificationFailure; report_with_ariadne uses Source::from with disk-read source text and render_counterexample for typed Labels
- [Phase 20-02]: extract_ghost_predicates() as separate function (not modifying extract_contracts return type); ghost_pred_db as pub field on VerificationCallbacks; let-chain collapsible-if pattern for doc attr matching
- [Phase 20]: Separate heap domain (not byte-array model) for sep_logic to avoid conflict with heap_model.rs
- [Phase 20]: Default pointee_bits to 64 when RawPtr inner type cannot be resolved — conservative fallback
- [Phase 20]: perm array uses Bool (not fractional permissions) — sufficient for Plan 01 pts_to ownership semantics
- [Phase 20-03]: Syntactic sep-conj detection at Expr::Binary level before operand conversion — must check raw syn::Expr not converted Term
- [Phase 20-03]: convert_expr_with_db() as core internal entry point; convert_expr_with_bounds() delegates to it with empty DB for backward compat
- [Phase 20-03]: Frame axiom trigger :pattern ((select sep_heap _sep_frame_addr)) — reuses post-call heap select term to guide Z3 E-matching
- [Phase 20-03]: has_sep_logic_spec() is cheap syntactic pts_to substring check; prepend_sep_heap_decls() inserts after SetLogic command

### Pending Todos

0 pending.

### Blockers/Concerns

**v0.4 phase-specific risks (from research):**
- [Phase 20] Heap domain choice (Viper Ref sort vs bitvector-set permissions) — resolve at Phase 20 planning
- [Phase 21] RC11 AcqRel encoding — not equivalent to Release OR Acquire; derive from arXiv:2108.06944
- [Phase 23] Async coroutine MIR shape may have changed post-PR#145330 — validate with RUSTFLAGS="-Zunpretty=mir" before Phase 23

## Session Continuity

Last session: 2026-02-20
Stopped at: Completed 20-03-PLAN.md — sep-conj, ghost predicate expansion, frame rule, AUFBV logic selection
Resume file: None
Next step: /gsd:execute-phase 20 (continue with plan 04)

---

*State initialized: 2026-02-14*
*Last updated: 2026-02-20 after 19-03 ariadne multi-label counterexample rendering*
