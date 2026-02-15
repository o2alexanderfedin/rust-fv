# Project State

## Project Reference

See: .planning/PROJECT.md (updated 2026-02-14)

**Core value:** Sound, automated verification of Rust code properties with minimal developer burden -- if the tool says "verified", it must be mathematically correct; if a developer can write a spec, the tool should prove it automatically 80-90% of the time for safe Rust.

**Current focus:** Phase 14 - Incremental Verification

## Current Position

Phase: 14 of 18 (Incremental Verification) -- IN PROGRESS
Plan: 2 of TBD (plans 01-02 complete)
Status: Plan 14-02 complete (per-function status output + cache management)
Last activity: 2026-02-15 — Completed 14-02-PLAN.md (user-visible incremental verification)

Progress: [█████████████████░░░░░░░] 72% (13/18 phases complete, 14 in progress)

## Performance Metrics

**Velocity:**
- Total plans completed: 43 (v0.1: 17 plans, v0.2: 21 plans, v0.3: 5 plans)
- Average duration: 408 seconds (v0.3)
- Total execution time: 5 days (v0.1: 2 days, v0.2: 3 days, v0.3: <1 day)

**By Milestone:**

| Milestone | Phases | Plans | Timeline |
|-----------|--------|-------|----------|
| v0.1 POC | 5 | 17 | 2 days |
| v0.2 Advanced | 7 | 21 | 3 days |
| v0.3 Usability | 6 | 5/TBD | In progress |

**Recent Trend:**
- v0.1 average: 8.5 plans/day
- v0.2 average: 7.0 plans/day
- v0.3 current: 5 plans (avg 1154s duration)
- Trend: Stable (complexity increasing with comprehensive stdlib contracts)

**Recent Executions:**

| Plan | Duration | Tasks | Files |
|------|----------|-------|-------|
| Phase 13 P02 | 703s | 2 | 6 |
| Phase 13 P03 | 107s | 2 | 10 |
| Phase 13 P04 | 50min | 2 | 8 |
| Phase 13 P05 | 83min | 2 | 8 |
| Phase 14 P01 | 738s | 2 | 8 |
| Phase 14 P02 | 478s | 2 | 4 |

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

Last session: 2026-02-15
Stopped at: Completed 14-02-PLAN.md (per-function status output + cache management)
Resume file: None
Next step: Continue Phase 14 (plan 03 and beyond)

---

*State initialized: 2026-02-14*
*Last updated: 2026-02-15 after completing 14-02-PLAN.md (Phase 14 plan 02)*
