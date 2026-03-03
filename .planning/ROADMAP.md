# Roadmap: rust-fv

## Milestones

- ✅ **v0.1 POC** - Phases 1-5 (shipped 2026-02-12)
- ✅ **v0.2 Advanced** - Phases 6-12 (shipped 2026-02-14)
- ✅ **v0.3 Usability** - Phases 13-18 (shipped 2026-02-17)
- ✅ **v0.4 Full Rust** - Phases 19-27 (shipped 2026-02-23)
- ✅ **v0.5 SMT Completeness** - Phases 28-29 (shipped 2026-02-25)
- ✅ **v0.5 Audit & Gap Closure** - Phases 29.1-29.4, 30-33 (shipped 2026-02-27)
- ✅ **v0.6 Cross-Crate Verification** - Phases 34-37, 37.1 (shipped 2026-03-02)

## Phases

<details>
<summary>✅ v0.1 POC (Phases 1-5) - SHIPPED 2026-02-12</summary>

Phases 1-5: proc macro annotations, SMT-LIB2 AST, bitvector theory, MIR-to-IR, VCGen, Z3 integration, end-to-end pipeline.

</details>

<details>
<summary>✅ v0.2 Advanced (Phases 6-12) - SHIPPED 2026-02-14</summary>

Phases 6-12: recursive functions, closures, trait objects, lifetimes, unsafe code, floating-point, bounded concurrency.

</details>

<details>
<summary>✅ v0.3 Usability (Phases 13-18) - SHIPPED 2026-02-17</summary>

Phases 13-18: stdlib contracts, incremental verification, trigger customization, VSCode extension, rust-analyzer integration, bv2int optimization.

</details>

<details>
<summary>✅ v0.4 Full Rust (Phases 19-27) - SHIPPED 2026-02-23</summary>

Phases 19-27: counterexample generation, separation logic, weak memory models, higher-order closures, async/await, gap closures.

</details>

<details>
<summary>✅ v0.5 SMT Completeness (Phases 28-29) - SHIPPED 2026-02-25</summary>

Phases 28-29: as-cast encoding, discriminant binding, array bounds VCs, generic trait bound premises, CastKind preservation, aggregate conversion, float-to-int soundness fix, missing rvalue variants, functional record update.

</details>

<details>
<summary>✅ v0.5 Audit & Gap Closure (Phases 29.1-29.4, 30-33) - SHIPPED 2026-02-27</summary>

Phases 29.1-33: for-loop VCGen, prophecy fix, borrow conflict detection, stdlib doc test fixes, SetDiscriminant VCGen, Z3/ghost fixes, retrospective verification docs, v0.1 tech debt closure, v0.1 milestone audit passed.

</details>


<details>
<summary>✅ v0.6 Cross-Crate Verification (Phases 34–37.1) — SHIPPED 2026-03-02</summary>

Phases 34–37.1: cross-function pointer aliasing, opaque callee diagnostics V060/V061, summary contract inference with `#[verifier::infer_summary]`, HIR-based alias precondition parsing, cross-crate Tarjan SCC detection, `#[decreases]` termination across crate boundaries, V062 InferredSummaryAlias guard.

- [x] Phase 34: Cross-Function Pointer Aliasing (2/2 plans) — completed 2026-02-28
- [x] Phase 35: Opaque Callee Diagnostics (2/2 plans) — completed 2026-02-28
- [x] Phase 36: Summary Contract Inference (2/2 plans) — completed 2026-02-28
- [x] Phase 36.1: Alias Precondition Parsing Fix (1/1 plans) — completed 2026-03-01
- [x] Phase 37: Cross-Crate SCC Detection (3/3 plans) — completed 2026-03-02
- [x] Phase 37.1: Inferred Summary + Alias Precondition Guard (1/1 plans) — completed 2026-03-02

</details>

### Phase 38: Trait Subtyping Wiring
**Goal:** Wire `generate_subtyping_vcs` into the driver's `after_analysis` pipeline so behavioral subtyping VCs are submitted to Z3 for every trait impl with contracts.
**Requirements:** TRT-01, TRT-02, TRT-03, TRT-04, TRT-05
**Gap Closure:** Closes gaps from vAll cross-milestone audit (TRT-01..05 partial, integration orphan, broken E2E flow)
**Plans:** 2/2 plans complete

Plans:
- [ ] 38-01-PLAN.md — Wire generate_subtyping_vcs into callbacks.rs after_analysis + unit tests
- [ ] 38-02-PLAN.md — E2E behavioral subtyping pipeline tests with Z3 UNSAT/SAT validation

## Progress

| Phase | Milestone | Plans Complete | Status | Completed |
|-------|-----------|----------------|--------|-----------|
| 34. Cross-Function Pointer Aliasing | v0.6 | 2/2 | Complete | 2026-02-28 |
| 35. Opaque Callee Diagnostics | v0.6 | 2/2 | Complete | 2026-02-28 |
| 36. Summary Contract Inference | v0.6 | 2/2 | Complete | 2026-02-28 |
| 36.1. Alias Precondition Parsing Fix | v0.6 | 1/1 | Complete | 2026-03-01 |
| 37. Cross-Crate SCC Detection | v0.6 | 3/3 | Complete | 2026-03-02 |
| 37.1. Inferred Summary + Alias Precondition Guard | v0.6 | 1/1 | Complete | 2026-03-02 |
| 38. Trait Subtyping Wiring | v0.7 | 2/2 | Complete | 2026-03-02 |
| 39. FnMut Prophecy Variable Encoding | v0.7 | 2/2 | Complete | 2026-03-02 |
| generics-fix. Generics Verification Fix | v0.7 | 1/1 | Complete (unverified) | 2026-03-02 |
| 40. Generics Verification Completion | 1/3 | In Progress|  | — |
| 41. Phase 38 Hardening | v0.7 | 0/— | Pending | — |
| 42. Phase 39 Production Wiring | v0.7 | 0/— | Pending | — |

### Phase 39: FnMut prophecy variable encoding for mutable closure capture verification — implement prophecy pre/post state tracking in closure_analysis.rs + vcgen.rs so FnMut closures with contracts on mutated captured state can be verified

**Goal:** Extend the IR and VCGen so that FnMut closures with mutable captured state emit SMT-LIB2 prophecy variable declarations (`{field}_initial`, `{field}_prophecy`) enabling contracts like `#[ensures(count == old(count) + 1)]` to be verified.
**Requirements**: TBD
**Depends on:** Phase 38
**Plans:** 2/2 plans complete

Plans:
- [ ] 39-01-PLAN.md — Add CaptureMode enum, update ClosureInfo.env_fields, extend ProphecyInfo, add detect_closure_prophecies
- [ ] 39-02-PLAN.md — Wire detect_closure_prophecies into vcgen.rs, upgrade fnmut_closure_prophecy test with SMT assertions

### Phase 40: Generics Verification Completion
**Goal:** Fix parametric axiom injection so generic functions are verified against real trait bound constraints (not trivially passed via `BoolLit(true)`), thread `MonomorphizationRegistry` through `VerificationTask` to activate `generate_vcs_monomorphized`, and write a VERIFICATION.md for the generics-fix phase to clear the audit blocker.
**Requirements:** GENERICS-01, GENERICS-02
**Gap Closure:** Closes gaps from v0.1 milestone audit — broken "Generic function trait-bound-aware verification" flow, unverified generics-fix phase, semantic no-op parametric axioms
**Depends on:** generics-fix
**Plans:** 1/3 plans executed

Plans:
- [ ] 40-01-PLAN.md — Fix trait_bounds_as_smt_assumptions: real Ord/PartialOrd SMT axioms (GENERICS-01)
- [ ] 40-02-PLAN.md — Thread MonomorphizationRegistry through VerificationTask; wire generate_vcs_monomorphized (GENERICS-02)
- [ ] 40-03-PLAN.md — Write generics-fix-VERIFICATION.md to clear audit blocker

### Phase 41: Phase 38 Hardening (Sealed Traits + Z3 Robustness + Dyn Dispatch)
**Goal:** Implement real sealed trait detection to replace the hardcoded `is_sealed: false`, fix `generate_subtyping_script` to emit proper SMT `declare-fun` statements so Z3 parse errors are no longer silently treated as verified, and wire dynamic dispatch call-site VCs to the behavioral subtyping pipeline.
**Requirements:** TRT-02, TRT-04
**Gap Closure:** Closes gaps from v0.1 milestone audit — TRT-02 partial (dyn dispatch not bridged), TRT-04 partial (sealed trait inactive), Z3 silent-pass integration gap
**Depends on:** Phase 38

### Phase 42: Phase 39 Production Wiring (Ty::Closure from Real MIR)
**Goal:** Wire `mir_converter.rs` to emit `Ty::Closure` variants from real rustc MIR closure lowering so the Phase 39 prophecy machinery is reachable from the production driver pipeline, and fix `CaptureMode` to detect real `ByMutRef` captures instead of always defaulting to `ByMove`.
**Requirements:** (none declared — integration gap closure)
**Gap Closure:** Closes gaps from v0.1 milestone audit — Phase 39 closure prophecy unreachable from real programs, broken "FnMut closure prophecy in production" flow
**Depends on:** Phase 39
