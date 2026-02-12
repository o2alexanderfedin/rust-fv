# Project State: rust-fv

**Last updated:** 2026-02-12T08:08:03Z

## Project Reference

**Core Value:** Sound, automated verification of Rust code properties with minimal developer burden -- if the tool says "verified", it must be mathematically correct; if a developer can write a spec, the tool should prove it automatically 80-90% of the time for safe Rust.

**Current Milestone:** v0.2 Advanced Verification

**Current Focus:** Extend verification to cover all major Rust language features -- recursive functions, closures, traits, unsafe code, lifetimes, floating-point, and concurrency.

## Current Position

**Phase:** 6 - Recursive Functions
**Plan:** 1 of 3 complete
**Status:** In Progress
**Progress:** `[#         ] 0/7 phases` (v0.2 milestone, Phase 6: 1/3 plans)

### Active Work
- Completed Plan 06-01: Infrastructure (decreases macro, IR extensions, recursion detection)
- Next: Plan 06-02 (termination VC generation)

### Next Steps
1. Execute Plan 06-02: Termination VC generation using Contracts.decreases and detect_recursion()
2. Execute Plan 06-03: Encoding and diagnostics for termination VCs
3. Complete Phase 6 and move to Phase 7 (Closures)

## Performance Metrics

**v0.1 Baseline (shipped 2026-02-12):**
- Total LOC: 43,621 (5-crate workspace)
- Test count: 1,741
- Test coverage: 80.49%
- Warnings: 0
- Build time: ~15s (debug), ~45s (release)
- Single-function verification: <1s
- Loop/inter-procedural: <5s

**Phase 6-01 (2026-02-12):**
- Duration: 25 min
- Tasks: 2 (TDD)
- New tests: 14 (total: 1,755)
- Files modified: 18
- New LOC: ~589 (285 impl + 304 test updates)
- petgraph 0.8.3 added

**v0.2 Targets:**
- Target LOC: ~57,800 (+14,200 estimated for 7 features)
- Target test count: 2,000+ (add ~260 tests across features)
- Target coverage: maintain 80%+
- Warnings: 0 (non-negotiable)
- Performance: maintain v0.1 targets for existing features

## Accumulated Context

### Key Decisions (v0.2)

| Decision | Rationale | Phase |
|----------|-----------|-------|
| Implement ALL 7 advanced features in v0.2 | User wants comprehensive coverage; increases scope but matches vision | All |
| Phases 6-12 ordering (Recursion → Closures → Traits → Lifetimes → Unsafe → FP → Concurrency) | Dependency-driven: each builds on previous; FP/concurrency most isolated | All |
| Mandatory `#[decreases]` for recursive functions | Termination undecidable; unsound to assume termination without proof | Phase 6 |
| Bounded concurrency verification (max threads/context switches) | State explosion mitigation; document limitations clearly | Phase 12 |
| Sequential consistency only for atomics (v0.2) | Weak memory models deferred; SC first for foundational verification | Phase 12 |
| Reused spec_attribute helper for #[decreases] | Same doc attribute encoding pattern; zero code duplication | Phase 6 |
| petgraph 0.8 for SCC analysis | Mature, well-tested, minimal API surface | Phase 6 |
| Self-loop check for direct recursion in tarjan_scc | Size-1 SCCs include non-recursive nodes; only self-edge nodes are recursive | Phase 6 |

### In-Progress Todos

- Phase 6: Plans 02 and 03 remaining (termination VC generation, encoding/diagnostics).

### Blockers

None currently identified.

### Research Notes

**Phase 6 (Recursive Functions):**
- Well-documented pattern in F*/Dafny/Verus
- Uninterpreted function encoding with axioms for base/recursive cases
- petgraph 0.8.3 for Tarjan's SCC algorithm (mutual recursion detection)
- Estimated ~1,800 LOC

**Phase 7 (Closures):**
- Defunctionalization to first-order SMT datatypes
- Environment capture modes: Fn (immutable), FnMut (prophecy vars), FnOnce (move)
- Builds on v0.1 ownership reasoning
- Estimated ~2,200 LOC

**Phase 8 (Trait Objects):**
- Closed-world (sealed traits): sum types over known impls
- Open-world (public traits): uninterpreted functions
- Vtable verification following Kani 2022 approach
- Estimated ~1,800 LOC
- Research flag: open-world encoding needs design spike

**Phase 9 (Lifetime Reasoning):**
- Extends v0.1 prophecy variables
- NLL-based (not lexical) lifetime tracking
- SSA-based parameter encoding resolves prophecy limitation
- Optional polonius 0.3.0 (start without, add if needed)
- Estimated ~2,000 LOC

**Phase 10 (Unsafe Code Detection):**
- Heap-as-array memory model (Z3 array theory)
- Basic checks: null, bounds
- Explicit trust boundaries via `#[verifier::trusted]`
- Full separation logic deferred to v0.3+
- Estimated ~2,400 LOC

**Phase 11 (Floating-Point Verification):**
- SMT-LIB FPA theory (IEEE 754)
- Z3 QF_FP/QF_FPBV logics already available
- Performance warning: 2-10x slower than bitvectors
- Opt-in feature
- Estimated ~1,800 LOC

**Phase 12 (Concurrency Verification):**
- Bounded model checking (limit interleavings)
- Happens-before relations as partial order
- Sequential consistency only (no relaxed atomics)
- Highest complexity; research flag for interleaving strategy
- Estimated ~2,200 LOC

### Deferred Items (v0.3+)

From REQUIREMENTS.md v0.3+ section:
- Higher-order closures with specification entailments (ACLO-01, ACLO-02)
- Bounded model checking for unsafe (AUSF-01)
- Separation logic for heap reasoning (AUSF-02)
- Weak memory models (ACON-01)
- Async/await verification (ACON-02)
- Deadlock detection (ACON-03)
- Standard library contracts (ECO-01)
- Trigger customization (ECO-02)
- Z3 bv2int native integration (ECO-03)
- VSCode extension (ECO-04)
- rust-analyzer integration (ECO-05)

## Session Continuity

**Last session:** 2026-02-12 - Completed Plan 06-01 (infrastructure)
- Added #[decreases(expr)] proc macro, Contracts.decreases field, VcKind::Termination
- Added petgraph SCC-based recursion detection with RecursiveGroup type
- 14 new tests, 1755 total passing, 0 warnings

**Stopped at:** Completed 06-01-PLAN.md

**Next session expectations:**
- Execute Plan 06-02: Termination VC generation
- Execute Plan 06-03: Encoding and diagnostics
- Complete Phase 6

---
*STATE.md initialized: 2026-02-12 for v0.2 milestone*
