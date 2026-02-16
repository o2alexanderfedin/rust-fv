# Project State

## Project Reference

See: .planning/PROJECT.md (updated 2026-02-14)

**Core value:** Sound, automated verification of Rust code properties with minimal developer burden -- if the tool says "verified", it must be mathematically correct; if a developer can write a spec, the tool should prove it automatically 80-90% of the time for safe Rust.

**Current focus:** Phase 16 - VSCode Extension

## Current Position

Phase: 16 of 18 (VSCode Extension) -- IN PROGRESS
Plan: 2 of 3
Status: Output panels with structured failure reports, SMT-LIB viewer, and gutter decorations complete
Last activity: 2026-02-16 — Completed 16-02-PLAN.md (Output panels and gutter decorations)

Progress: [███████████████████░░░░░] 84% (15/18 phases complete, 2/3 plans in Phase 16)

## Performance Metrics

**Velocity:**
- Total plans completed: 51 (v0.1: 17 plans, v0.2: 21 plans, v0.3: 13 plans)
- Average duration: 800 seconds (v0.3)
- Total execution time: 5 days (v0.1: 2 days, v0.2: 3 days, v0.3: 1 day)

**By Milestone:**

| Milestone | Phases | Plans | Timeline |
|-----------|--------|-------|----------|
| v0.1 POC | 5 | 17 | 2 days |
| v0.2 Advanced | 7 | 21 | 3 days |
| v0.3 Usability | 6 | 13/TBD | In progress |

**Recent Trend:**
- v0.1 average: 8.5 plans/day
- v0.2 average: 7.0 plans/day
- v0.3 current: 13 plans (avg 800s duration)
- Trend: Accelerating (improved efficiency with integration testing patterns and focused implementations)

**Recent Executions:**

| Plan | Duration | Tasks | Files |
|------|----------|-------|-------|
| Phase 14 P01 | 738s | 2 | 8 |
| Phase 14 P02 | 478s | 2 | 4 |
| Phase 14 P03 | 71min | 2 | 4 |
| Phase 14 P04 | 326s | 2 | 3 |
| Phase 15 P01 | 751s | 2 | 6 |
| Phase 15 P02 | 814s | 1 | 2 |
| Phase 15 P03 | 530s | 2 | 4 |
| Phase 16 P01 | 145s | 2 | 5 |
| Phase 16 P02 | 427s | 2 | 5 |

*Updated after each plan completion*

## Accumulated Context

### Decisions

Decisions are logged in PROJECT.md Key Decisions table.
Recent decisions affecting current work:

- v0.2: Behavioral subtyping for traits (LSP enforcement; precondition weaker, postcondition stronger)
- v0.2: Heap-as-array memory model for unsafe (byte-addressable memory with allocation metadata)
- v0.2: Bounded concurrency with happens-before (state explosion mitigation; sequential consistency first)
- v0.3: Standard library contracts as external crate pattern (Prusti/Verus model for versioning independence)
- v0.3 (13-01): SMT Seq sort for Vec/String/slice modeling (native sequence operations vs array encoding)
- v0.3 (13-01): StdlibContractRegistry with enable/disable flag (supports --no-stdlib-contracts)
- v0.3 (13-02): Vec push has no capacity precondition (Rust allocator handles reallocation)
- v0.3 (13-02): Element-level precision via seq.nth for Vec indexing (proves vec[i] == value)
- v0.3 (13-02): Option/Result as SMT datatypes with ghost accessors (option_value, ok_value, err_value)
- [Phase 13]: HashMap modeled as mathematical map abstraction with Array(K, Option(V)) encoding and frame conditions
- [Phase 13]: Iterator adaptors model composable sequence transformations (map preserves length, filter reduces)
- [Phase 13]: Stdlib contracts auto-load by default - zero configuration needed
- [Phase 13]: CLI flag --no-stdlib-contracts provides opt-out via environment variable
- [Phase 13]: Proptest oracle testing validates all stdlib contract postconditions against real behavior (256 cases each)
- [Phase 13]: E2E tests prove full verification pipeline works with stdlib contracts (IR -> ContractDB -> VCGen -> Z3)
- [Phase 14 (14-01)]: Dual-hash cache model (mir_hash + contract_hash) enables precise invalidation granularity
- [Phase 14 (14-01)]: Age-based eviction (30-day TTL) with lazy cleanup on load (no periodic background task)
- [Phase 14 (14-01)]: Transitive invalidation via reverse call graph (contract changes cascade to callers)
- [Phase 14 (14-01)]: Timestamp zero means "keep" for backward compatibility with old cache format
- [Phase 14 (14-02)]: Invalidation reasons shown for all re-verified functions (not behind verbose flag)
- [Phase 14 (14-02)]: --verbose flag controls per-function timing only, not invalidation reasons
- [Phase 14 (14-02)]: [SKIP] status distinguishes cached results from verified results
- [Phase 14 (14-02)]: Total timing always shown in summary when any functions verified
- [Phase 14 (14-03)]: Synthetic IR-level benchmarking provides controlled, reproducible scenarios without rustc overhead
- [Phase 14 (14-03)]: Small-scale validation tests (10 functions) verify infrastructure, not performance targets
- [Phase 14 (14-03)]: 9 correctness tests collectively prove incremental verification soundness
- [Phase 14]: Standalone test fixture crate (not workspace member) for realistic E2E testing
- [Phase 14]: cfg_attr contract syntax for rustc compatibility in test fixture
- [Phase 14]: E2E tests marked #[ignore] - require full toolchain and solvers
- [Phase 15 (15-01)]: Self-instantiation detection via recursive function name matching (not symbolic substitution)
- [Phase 15 (15-01)]: Catch-all interpreted symbol detection for unrecognized Term variants
- [Phase 15 (15-01)]: format_trigger_error returns String for testability and composability
- [Phase 15 (15-02)]: TriggerHint stored as Vec<Term> in IR, separate from SMT Term layer
- [Phase 15 (15-02)]: Test bodies use bound variable expressions, not unresolved function calls
- [Phase 15 (15-03)]: Manual triggers fully replace auto-inference (not merge)
- [Phase 15 (15-03)]: Validation errors propagate through Result type
- [Phase 15 (15-03)]: describe_quantifier_triggers for verbose mode output
- [Phase 15 (15-03)]: extract_manual_triggers strips rust_fv_trigger_hint annotations
- [Phase 16 (16-01)]: Whole-crate verification scope (matches cargo check pattern, relies on incremental cache)
- [Phase 16 (16-01)]: Fresh spawn per save (simpler lifecycle than persistent background process)
- [Phase 16 (16-01)]: DiagnosticSeverity.Error for verification failures (not Warning - same visual weight as rustc)
- [Phase 16 (16-01)]: Counterexamples formatted inline in diagnostic tooltip (not separate related information yet)
- [Phase 16 (16-02)]: Structured output channel shown by default (not raw output - better UX)
- [Phase 16 (16-02)]: SMT-LIB viewer reads from target/verify/ filesystem (not embedded in JSON - keeps payloads small)
- [Phase 16 (16-02)]: Gutter decorations use regex function matching (JSON lacks source_line for passing functions)
- [Phase 16 (16-02)]: Decorations persist across editor tab switches (lastVerificationReport + onDidChangeActiveTextEditor)

### Pending Todos

None yet.

### Blockers/Concerns

**From research:**
- Stdlib contract completeness - Need Tier 1 coverage (Vec, Option, HashMap, Iterator basics) before v0.3 ships
- IDE performance boundary - Must maintain <1s re-verification or adoption suffers
- Quantifier trigger diagnostics - Manual triggers expose SMT expert concepts, need progressive disclosure

**Mitigation strategies:**
- Property-based oracle testing for stdlib contract soundness
- Incremental verification prerequisite for IDE integration
- Static termination analysis before exposing manual trigger API

## Session Continuity

Last session: 2026-02-16
Stopped at: Completed 16-02-PLAN.md (Output panels and gutter decorations)
Resume file: None
Next step: Continue Phase 16 - Plan 03 (Z3 bundling and publishing)

---

*State initialized: 2026-02-14*
*Last updated: 2026-02-16 after completing 16-02-PLAN.md (Phase 16 plan 02)*
