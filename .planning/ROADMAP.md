# Roadmap: rust-fv

## Milestones

- ✅ **v0.1 POC** - Phases 1-5 (shipped 2026-02-12)
- ✅ **v0.2 Advanced** - Phases 6-12 (shipped 2026-02-14)
- ✅ **v0.3 Usability** - Phases 13-18 (shipped 2026-02-17)
- ✅ **v0.4 Full Rust** - Phases 19-27 (shipped 2026-02-23)
- ✅ **v0.5 SMT Completeness** - Phases 28-29 (shipped 2026-02-25)
- ✅ **v0.5 Audit & Gap Closure** - Phases 29.1-29.4, 30-33 (shipped 2026-02-27)
- 🚧 **v0.6 Cross-Crate Verification** - Phases 34-37 (in progress)

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

### 🚧 v0.6 Cross-Crate Verification (In Progress)

**Milestone Goal:** Break the "each crate is an island" barrier — cross-function pointer aliasing, opaque callee contract enforcement, and cross-crate mutual recursion detection.

**Phase Numbering:** Continues from v0.5-audit (last phase: 33)

- [ ] **Phase 34: Cross-Function Pointer Aliasing** - Inter-procedural aliasing analysis for unsafe code raw pointer arguments
- [ ] **Phase 35: Opaque Callee Diagnostics** - Warn/error when callee has no contract instead of silently skipping
- [ ] **Phase 36: Summary Contract Inference** - Auto-infer minimal read/write contracts for opaque callees via `#[verifier::infer_summary]`
- [ ] **Phase 37: Cross-Crate SCC Detection** - Tarjan's SCC extended across crate boundaries with termination measure verification

## Phase Details

### Phase 34: Cross-Function Pointer Aliasing
**Goal**: Users can verify that raw pointer arguments do not alias across function call boundaries in unsafe code
**Depends on**: Phase 33 (v0.5-audit complete)
**Requirements**: ALIAS-01, ALIAS-02
**Plans**: 2 plans
**Success Criteria** (what must be TRUE):
  1. User can write `#[unsafe_requires(!ptr_a.alias(ptr_b))]` on an unsafe function and `cargo verify` enforces the non-aliasing constraint across call boundaries
  2. User sees a counterexample identifying which specific pointer arguments alias when an aliasing violation is detected at a call site
  3. `unsafe_verification.rs` tracks aliasing via call-graph edges so that aliased pointer pairs from callers propagate into callee VCs
  4. The existing intra-procedural null/bounds checks in `unsafe_verification.rs:1109-1135` remain GREEN with no regressions

Plans:
- [ ] 34-01-PLAN.md — Core alias infrastructure (spec_parser alias arm, heap_model assertion, VcKind::PointerAliasing, contract_db AliasPrecondition)
- [ ] 34-02-PLAN.md — Call-site VC injection (unsafe_analysis extraction, vcgen injection loop, integration tests + DEBTLINE update)

### Phase 35: Opaque Callee Diagnostics
**Goal**: Users receive actionable diagnostics when a verified function calls an uncontracted callee, replacing the current silent skip
**Depends on**: Phase 34
**Requirements**: OPAQUE-01, OPAQUE-02
**Success Criteria** (what must be TRUE):
  1. User sees a V060-series warning diagnostic when `cargo verify` encounters a verified function calling a callee with no `#[requires]`/`#[ensures]` contract
  2. User sees a verification error (not just a warning) when the uncontracted callee is invoked from within an `unsafe` block
  3. The silent-skip path at `vcgen.rs:2366-2376` is replaced so that uncontracted callees produce observable output in `cargo verify` results
  4. Existing contracted callees continue to verify without new spurious diagnostics
**Plans**: TBD

### Phase 36: Summary Contract Inference
**Goal**: Users can opt into automatic minimal contract inference for opaque callees rather than manually writing contracts
**Depends on**: Phase 35
**Requirements**: OPAQUE-03
**Success Criteria** (what must be TRUE):
  1. User can annotate an uncontracted callee with `#[verifier::infer_summary]` and `cargo verify` auto-generates a minimal read/write effect contract for it
  2. The inferred contract suppresses the V060-series diagnostic for that callee (it is no longer "uncontracted")
  3. The inferred summary contract is visible in `--output-format=json` output so tools can inspect what was auto-generated
**Plans**: TBD

### Phase 37: Cross-Crate SCC Detection
**Goal**: Users can detect and verify mutually recursive call cycles that span multiple crates
**Depends on**: Phase 36
**Requirements**: XCREC-01, XCREC-02
**Success Criteria** (what must be TRUE):
  1. `cargo verify` detects a mutually recursive cycle between functions in two different crates and reports the SCC members by name
  2. User can attach `#[decreases(expr)]` to functions participating in a cross-crate recursive cycle and `cargo verify` checks that the termination measure decreases across crate boundaries
  3. The cross-crate SCC detection in `recursion_verification.rs` uses exported symbol contracts so that crate boundaries are transparent to Tarjan's algorithm
  4. Single-crate recursive function verification (existing) remains GREEN with no regressions
**Plans**: TBD

## Progress

**Execution Order:** 34 → 35 → 36 → 37

| Phase | Milestone | Plans Complete | Status | Completed |
|-------|-----------|----------------|--------|-----------|
| 34. Cross-Function Pointer Aliasing | 1/2 | In Progress|  | - |
| 35. Opaque Callee Diagnostics | v0.6 | 0/TBD | Not started | - |
| 36. Summary Contract Inference | v0.6 | 0/TBD | Not started | - |
| 37. Cross-Crate SCC Detection | v0.6 | 0/TBD | Not started | - |
