# Requirements: rust-fv v0.6

**Defined:** 2026-02-28
**Core Value:** Sound, automated verification of Rust code properties with minimal developer burden — if the tool says "verified", it must be mathematically correct; if a developer can write a spec, the tool should prove it automatically 80-90% of the time for safe Rust.

## v0.6 Requirements

Milestone goal: Break the "each crate is an island" barrier — cross-function pointer aliasing, opaque callee contract enforcement, and cross-crate mutual recursion detection.

### Pointer Aliasing (ALIAS)

- [x] **ALIAS-01**: User can verify that raw pointer arguments do not alias across function call boundaries in unsafe code (inter-procedural aliasing tracked via call-graph edges in `unsafe_verification.rs`)
- [x] **ALIAS-02**: User can see a counterexample identifying which pointer arguments alias when an aliasing violation is detected

### Opaque Callee Contracts (OPAQUE)

- [x] **OPAQUE-01**: User receives a diagnostic warning (V060–V069) when a verified function calls an uncontracted callee that affects verification soundness (closes the silent-skip gap at `vcgen.rs:2366–2376`)
- [x] **OPAQUE-02**: User receives a verification error (not warning) when unsafe code calls an uncontracted callee (escalated severity for unsafe context)
- [ ] **OPAQUE-03**: User can opt into summary contract inference for opaque callees via `#[verifier::infer_summary]`, which auto-generates minimal read/write contracts without manual annotation

### Cross-Crate Recursion (XCREC)

- [ ] **XCREC-01**: User can detect mutually recursive call cycles that span multiple crates (Tarjan's SCC extended across crate boundaries using exported symbol contracts in `recursion_verification.rs`)
- [ ] **XCREC-02**: User can verify `#[decreases]` termination measures for mutually recursive functions across crate boundaries (termination proof uses cross-crate SCC from XCREC-01)

## v2 Requirements

Deferred to future release. Tracked but not in current roadmap.

### Pointer Aliasing

- **ALIAS-03**: User can annotate pointer parameters with `#[alias_group(N)]` to declare intentional aliasing (explicit alias contracts)
- **ALIAS-04**: User can verify full Rust unsafe blocks (not just raw pointer calls) for aliasing via region-based alias analysis

### Cross-Crate Contracts

- **XCRATE-01**: User can load pre-compiled cross-crate contract summaries from `.rlib` metadata without re-verifying dependency crates
- **XCRATE-02**: User can publish contract summaries as part of crate releases so downstream crates benefit automatically

## Out of Scope

| Feature | Reason |
|---------|--------|
| Full pointer provenance analysis (LLVM Alias AA) | Too heavyweight for SMT encoding; defer to dedicated alias analysis milestone |
| Cross-crate verification of third-party crates without source | Cannot extract MIR from pre-compiled dependencies without nightly metadata |
| Sound inter-crate inlining of function bodies | Defeats modular verification — contract-based boundaries are intentional |
| Concurrency + aliasing interaction | Covered by v0.4 bounded concurrency; alias+concurrency interaction deferred |

## Traceability

Which phases cover which requirements. Updated during roadmap creation.

| Requirement | Phase | Status |
|-------------|-------|--------|
| ALIAS-01 | Phase 34 | Complete |
| ALIAS-02 | Phase 34 | Complete |
| OPAQUE-01 | Phase 35 | Complete |
| OPAQUE-02 | Phase 35 | Complete |
| OPAQUE-03 | Phase 36 | Pending |
| XCREC-01 | Phase 37 | Pending |
| XCREC-02 | Phase 37 | Pending |

**Coverage:**
- v0.6 requirements: 7 total
- Mapped to phases: 7
- Unmapped: 0 ✓

---
*Requirements defined: 2026-02-28*
*Last updated: 2026-02-28 after roadmap creation (phases 34-37 assigned)*
