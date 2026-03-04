# Roadmap: rust-fv

## Milestones

- ✅ **v0.1 POC** - Phases 1-5 (shipped 2026-02-12)
- ✅ **v0.2 Advanced** - Phases 6-12 (shipped 2026-02-14)
- ✅ **v0.3 Usability** - Phases 13-18 (shipped 2026-02-17)
- ✅ **v0.4 Full Rust** - Phases 19-27 (shipped 2026-02-23)
- ✅ **v0.5 SMT Completeness** - Phases 28-29 (shipped 2026-02-25)
- ✅ **v0.5 Audit & Gap Closure** - Phases 29.1-29.4, 30-33 (shipped 2026-02-27)
- ✅ **v0.6 Cross-Crate Verification** - Phases 34-37, 37.1 (shipped 2026-03-02)
- ✅ **v0.7 Generics & Traits Hardening** - Phases 38-44, generics-fix (shipped 2026-03-04)

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

</details>

<details>
<summary>✅ v0.7 Generics & Traits Hardening (Phases 38–44, generics-fix) — SHIPPED 2026-03-04</summary>

Phases 38–44 + generics-fix: behavioral subtyping VCs with Liskov checks, FnMut prophecy variable encoding for mutable closure contracts, real trait bound SMT axioms (Ord/PartialOrd DeclareSort+DeclareFun), MonomorphizationRegistry population from call-site type analysis, sealed trait detection via HIR visibility, dyn dispatch call-site VC resolution, Nyquist validation coverage, closure production wiring (Ty::Closure from real MIR).

- [x] Phase 38: Trait Subtyping Wiring (2/2 plans) — completed 2026-03-02
- [x] Phase 39: FnMut Prophecy Variable Encoding (2/2 plans) — completed 2026-03-02
- [x] Phase generics-fix: Generics Verification Fix (1/1 plan) — completed 2026-03-02
- [x] Phase 40: Generics Verification Completion (3/3 plans) — completed 2026-03-03
- [x] Phase 41: Phase 38 Hardening (2/2 plans) — completed 2026-03-03
- [x] Phase 42: Phase 39 Production Wiring (1/1 plan) — completed 2026-03-03
- [x] Phase 43: Nyquist Validation Coverage (2/2 plans) — completed 2026-03-04
- [x] Phase 44: MonomorphizationRegistry Population (1/1 plan) — completed 2026-03-04

</details>

## Progress

| Phase | Milestone | Plans Complete | Status | Completed |
|-------|-----------|----------------|--------|-----------|
| 1-5 | v0.1 | 17/17 | Complete | 2026-02-12 |
| 6-12 | v0.2 | 21/21 | Complete | 2026-02-14 |
| 13-18 | v0.3 | 20/20 | Complete | 2026-02-17 |
| 19-27 | v0.4 | 27/27 | Complete | 2026-02-23 |
| 28-29 | v0.5 | 10/10 | Complete | 2026-02-25 |
| 29.1-33 | v0.5-audit | 22/22 | Complete | 2026-02-27 |
| 34-37.1 | v0.6 | 11/11 | Complete | 2026-03-02 |
| 38-44 + generics-fix | v0.7 | 14/14 | Complete | 2026-03-04 |
