# Project State: rust-fv

**Last updated:** 2026-02-12T19:18:43Z

## Project Reference

**Core Value:** Sound, automated verification of Rust code properties with minimal developer burden -- if the tool says "verified", it must be mathematically correct; if a developer can write a spec, the tool should prove it automatically 80-90% of the time for safe Rust.

**Current Milestone:** v0.2 Advanced Verification

**Current Focus:** Extend verification to cover all major Rust language features -- recursive functions, closures, traits, unsafe code, lifetimes, floating-point, and concurrency.

## Current Position

**Phase:** 8 - Traits and Trait Objects
**Plan:** 1 of 3 complete
**Status:** In Progress
**Progress:** [███░░░░░░░] 33%

### Active Work
- Phase 8-01 COMPLETE: Trait IR and analysis infrastructure
- TraitDef, TraitMethod, TraitImpl, Ty::TraitObject types added
- VcKind::BehavioralSubtyping integrated
- TraitDatabase and analysis utilities implemented

### Next Steps
1. Continue Phase 8: Plan 02 (Behavioral Subtyping VCs)
2. Continue v0.2 Advanced Verification milestone

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

**Phase 6-02 (2026-02-12):**
- Duration: 10 min
- Tasks: 2 (TDD)
- New tests: 13 (total: 1,768)
- Files modified: 3
- New LOC: ~890 (recursion.rs) + ~325 (vcgen.rs integration + tests)

**Phase 6-03 (2026-02-12):**
- Duration: 15 min
- Tasks: 3
- New tests: 20 (8 e2e + 6 diagnostic + 6 unit) (total: 1,788)
- Files modified: 3 (1 created, 2 modified)
- New LOC: ~1,258 (recursion_verification.rs) + ~87 (diagnostics.rs) + ~111 (recursion.rs fixes)

**Phase 7-01 (2026-02-12):**
- Duration: 7 min
- Tasks: 2 (TDD)
- New tests: 19 (6 IR + 10 closure_analysis + 3 encode_sort) (total: 752 analysis crate)
- Files modified: 9 (1 created, 8 modified)
- New LOC: ~488 (closure_analysis.rs new + IR extensions + encode_sort extensions)

**Phase 7-02 (2026-02-12):**
- Duration: 87 min
- Tasks: 2 (TDD)
- New tests: 11 (7 defunctionalize + 2 spec_parser + 4 vcgen) (total: 765 analysis crate)
- Files modified: 4 (1 created, 3 modified)
- New LOC: ~659 (defunctionalize.rs 398 + spec_parser.rs 60 + vcgen.rs 261 - 60 minor refactors)

**Phase 7-03 (2026-02-12):**
- Duration: 36 min
- Tasks: 3
- New tests: 55 (6 diagnostic + 10 e2e closure + 39 analysis updates) (total: 1,843 workspace)
- Files modified: 2 (1 created, 1 modified)
- New LOC: ~1,260 (closure_verification.rs 1,145 + diagnostics.rs 115)

**Phase 8-01 (2026-02-12):**
- Duration: 11 min
- Tasks: 2 (TDD)
- New tests: 29 (9 IR/encode/vc + 20 trait_analysis) (total: 1,872 workspace)
- Files modified: 7 (1 created, 6 modified)
- New LOC: ~744 (trait_analysis.rs 453 + IR extensions 291)

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
| Termination VCs use BvSLt for signed params | Matches Z3 bitvector theory semantics for signed comparison | Phase 6 |
| Missing-decreases as diagnostic VC (always-SAT) | Flows through normal VC pipeline; simpler than separate error path | Phase 6 |
| Uninterpreted function encoding with forall axioms | Dafny/F* pattern; better control than Z3 define-fun-rec | Phase 6 |
| Closure environments as SMT datatypes | Follows struct encoding pattern (mk-{name} constructor, field selectors); environment is state, signature is metadata | Phase 7 |
| ClosureInfo boxed in Ty::Closure | Prevents recursive type size explosion (ClosureInfo contains Vec<Ty>) | Phase 7 |
| Closure classification via callee name parsing | Matches Rust's Fn/FnMut/FnOnce trait hierarchy; FnOnce most specific, Fn most general | Phase 7 |
| Defunctionalization for closure calls | Reynolds (1972) pattern: higher-order → first-order with explicit environment parameter | Phase 7 |
| Closure parameters as uninterpreted functions | Encoded as declare-fun in VCGen; enables modular verification | Phase 7 |
| FnOnce validation as diagnostic VCs | Always-SAT VCs for double-call violations; same pattern as missing-decreases | Phase 7 |
| Closure spec references via is_closure_param | Transforms predicate(x) → predicate_impl(env, x) in spec parser | Phase 7 |
| Uninterpreted closure encoding | Closures as declare-fun (sound but requires contracts); matches Rust verification tool patterns | Phase 7 |
| E2E test infrastructure validates pipeline correctness | Tests verify encoding, VC generation, Z3 processing rather than specific results | Phase 7 |
| Ty::TraitObject as Sort::Uninterpreted for open-world | Default open-world encoding; sealed traits switch to Sort::Datatype in closed-world analysis | Phase 8 |
| Sealed trait heuristics (visibility + super-trait) | Detects pub(crate), private, and sealed super-trait patterns without MIR visibility analysis | Phase 8 |
| Behavioral subtyping diagnostics explain LSP | Precondition WEAKER/postcondition STRONGER guidance for trait contract refinement | Phase 8 |

### In-Progress Todos

None - Phase 6 fully complete.

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

**Last session:** 2026-02-12 - Phase 8-01 (Trait IR and analysis infrastructure)
- Completed: TraitDef, TraitMethod, TraitImpl, Ty::TraitObject IR types
- Completed: VcKind::BehavioralSubtyping with full driver integration
- Completed: TraitDatabase, sealed detection, analysis utilities
- Status: 29 new tests (9 IR/VC + 20 trait_analysis), 1,872 total workspace tests passing, 0 warnings

**Stopped at:** Phase 8-01 COMPLETE (1 of 3)

**Next session expectations:**
- Continue Phase 8: Plan 02 (Behavioral Subtyping VCs)
- Continue v0.2 Advanced Verification milestone

---
*STATE.md initialized: 2026-02-12 for v0.2 milestone*
