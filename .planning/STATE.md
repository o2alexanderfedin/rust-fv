# Project State

## Project Reference

See: .planning/PROJECT.md (updated 2026-02-19)

**Core value:** Sound, automated verification of Rust code properties with minimal developer burden -- if the tool says "verified", it must be mathematically correct; if a developer can write a spec, the tool should prove it automatically 80-90% of the time for safe Rust.

**Current focus:** v0.5 SMT Completeness — Phase 28 (SMT VCGen Completeness) — Planned (5/5 plans ready).

## Current Position

Phase: 28 (SMT VCGen completeness) — Ready to execute
Plan: 0 complete (5 plans ready, 5 waves)
Status: Phase 28 Planned — VCGEN-01..04 covered across 28-01..05-PLAN.md
Last activity: 2026-02-22 — Plan 23-04 complete (ASY-01/ASY-02 TDD integration: 6 Z3 tests, QF_LIA spec parser fix)

Progress: [█████████████████████░░░] 91% (20/25 phases complete, Phases 24-25 pending)

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
| Phase 20 P04 | 425 | 1 tasks | 1 files |
| Phase 20 P03 | 893 | 2 tasks | 3 files |
| Phase 20 P02 | 34 | 2 tasks | 5 files |
| Phase 20 P01 | 10 | 2 tasks | 3 files |
| Phase 21 P01 | 452 | 2 tasks | 6 files |
| Phase 21 P02 | 353 | 2 tasks | 2 files |
| Phase 21 P02 | 353 | 2 tasks | 2 files |
| Phase 21 P03 | 976 | 2 tasks | 2 files |
| Phase 22 P01 | 1719 | 2 tasks | 32 files |
| Phase 22 P02 | 916 | 2 tasks | 3 files |
| Phase 22 P03 | 104 | 2 tasks | 2 files |
| Phase 24-sep04-ghost-predicate-wiring P01 | 808 | 1 tasks | 3 files |
| Phase 24-sep04-ghost-predicate-wiring P02 | 662 | 1 tasks | 6 files |
| Phase 25 P01 | 53 | 2 tasks | 2 files |
| Phase 23 P01 | 25 | 1 tasks | 58 files |
| Phase 23 P02 | 283 | 1 tasks | 2 files |
| Phase 23 P03 | 384 | 1 tasks | 5 files |
| Phase 23 P04 | 716 | 1 tasks | 3 files |
| Phase 26-wmm03-race-detection-fix P01 | 180 | 2 tasks | 2 files |
| Phase 26 P02 | 317 | 2 tasks | 2 files |

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
- [Phase 20-04]: Recursive ghost pred (looping(p)=looping(p)) used to test depth=0 exhaustion via public parse_spec_expr_with_db API — avoids exposing private parse_spec_expr_with_depth
- [Phase 20-04]: SEP-03 frame axiom validity proven via hand-crafted UNSAT SMT check (negation of axiom); VCGen-generated script checks call-site precondition encoding separately
- [Phase 21-01]: Use Term::IntLt for QF_LIA mo comparison (not Term::BvSLt) — correct for integer mo positions
- [Phase 21-01]: encode_fr takes store_s2 as explicit parameter (not inside store_events) — cleaner API
- [Phase 21-01]: thread_id defaults to 0 at all existing construction sites — backward compatible
- [Phase 21]: generate_rc11_vcs uses closure-based hb_term/eco_term for bounded N event sets — avoids materializing full N×N matrix as Terms
- [Phase 21]: Step 2b in generate_concurrency_vcs is additive — existing DataRaceFreedom VCs from Step 2 are unchanged; RC11 VCs are purely additive
- [Phase 21]: Litmus tests use custom SMT scripts (not generate_rc11_vcs) to pin specific forbidden executions with fixed rf choices
- [Phase 21]: Violation-detection semantics for coherence VCs: assert hb∧eco (violation), UNSAT=RC11 holds, SAT=coherence issue
- [Phase 21]: Initial-store-first axiom added to rc11.rs: mo(init) < mo(store) for all real stores per location
- [Phase 22]: Token-level fat-arrow scanning (not syn::parse_str) to handle => in fn_spec clauses — syn rejects fat-arrow as binary op
- [Phase 22]: %% as pre/post separator in fn_spec doc attributes to avoid :: collisions in expression content
- [Phase 22-02]: AUFLIA logic (not QF_BV) for HOF VCs — universal quantification requires non-QF logic
- [Phase 22-02]: Best-effort HOF spec expression parser with BoolLit(true) stub fallback — no panic on unrecognized expressions
- [Phase 22-02]: FnOnce uses identical Fn path — no env_before/after, single-call VC per RESEARCH.md Pattern 6
- [Phase 22-02]: Sort::Uninterpreted for closure environment sort — opaque in fn_spec context
- [Phase 22-02]: substitute_result() does post-parse substitution of result -> closure_app term
- [Phase 22-03]: Axiom injection pattern: commands_without_check_sat() + push axiom Assert + push CheckSat — clean test augmentation without modifying generate_fn_spec_vcs() API
- [Phase 22-03]: encode_type_for_auflia() replaces encode_type() for AUFLIA safety — BitVec sorts are invalid in AUFLIA, all integers map to Sort::Int
- [Phase 24]: generate_vcs() made backward-compatible delegation shim to generate_vcs_with_db with empty GhostPredicateDatabase — 6+ test sites unchanged
- [Phase 24]: parse_spec() updated to call parse_spec_expr_with_db (not db-less parse_spec_expr) — ghost predicates expand at all 13 call sites in vcgen.rs
- [Phase 24]: encode_callee_postcondition_assumptions required ghost_pred_db threading (compiler-enforced; Rule 3 auto-fix)
- [Phase 24]: VcKind::Precondition is for call-site checks (caller satisfies callee requires); function's own requires is an assumption in postcondition VCs — E2E tests need requires+ensures pair
- [Phase 24]: VerificationResult moved to types.rs (rustc-free) to enable parallel module export from lib.rs for driver integration tests
- [Phase 25]: renderCounterexampleLines shared helper in diagnostics.ts consumed by both createDiagnostic() and outputPanel.ts — single source of truth for counterexample rendering
- [Phase 25]: v2 schema preferred over legacy flat assignments in both diagnostics and output panel; fallback preserved for older binaries
- [Phase 23-01]: state_invariant placed in Contracts (not Function) following requires/ensures precedent; coroutine_info placed in Function as structural metadata not a contract clause; AsyncPostcondition separate from Postcondition since async completion is Poll::Ready not direct return
- [Phase 23]: Post-transform MIR at after_analysis has no TerminatorKind::Yield — fallback to SwitchInt discriminant counting (bb0 targets >= 3)
- [Phase 23]: count_coroutine_await_points() counts discriminant >= 3 (values 0/1/2 are reserved initial/done/panicked)
- [Phase 23]: QF_LIA logic for async VCs — no quantifiers needed for bounded state enumeration
- [Phase 23]: poll_iteration + await_side on JsonCounterexample with skip_serializing_if for backward compat
- [Phase 23]: parse_spec_expr_qf_lia uses in_int_mode=true for QF_LIA-compatible integer encoding in async VCs
- [Phase 23]: convert_path allows free SMT constant references in int_mode (awaited_result_N), strict BV mode preserved
- [Phase 26-wmm03-race-detection-fix]: WeakMemoryRace VC uses Assert(BoolLit(true)) + mo_cmds + rf_cmds — SAT = race detected, mirrors WeakMemoryCoherence violation-detection semantics
- [Phase 26]: Follow ghost_predicate_e2e.rs VerificationTask pattern (name/ir_func/contract_db fields); Function.atomic_ops for RC11 VCs with ConcurrencyConfig.verify_concurrency=true

### Pending Todos

0 pending.

### Blockers/Concerns

**v0.4 phase-specific risks (from research):**
- [Phase 20] Heap domain choice (Viper Ref sort vs bitvector-set permissions) — resolve at Phase 20 planning
- [Phase 21] RC11 AcqRel encoding — not equivalent to Release OR Acquire; derive from arXiv:2108.06944
- [Phase 20] Heap domain choice (Viper Ref sort vs bitvector-set permissions) — RESOLVED (Separate heap domain)
- [Phase 21] RC11 AcqRel encoding — RESOLVED (Phase 21 complete)
- [Phase 23] Async coroutine MIR shape validated: nightly-2026-02-11 uses post-transform SwitchInt discriminant (no Yield terminators at after_analysis hook) — RESOLVED

## Session Continuity

Last session: 2026-02-23
Stopped at: Phase 28 planned — 5 PLAN.md files created (VCGEN-01..04), verification passed, docs committed.
Resume file: None
Next step: /gsd:execute-phase 28

---

*State initialized: 2026-02-14*
*Last updated: 2026-02-23 after Phase 28 planning — v0.5 milestone started*
*Last updated: 2026-02-23 after 26-02 — Phase 26 complete, WMM-03 fully satisfied*
