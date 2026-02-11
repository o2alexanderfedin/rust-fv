# Requirements: rust-fv

**Defined:** 2026-02-10
**Core Value:** Sound, automated verification of Rust code properties with minimal developer burden

## v1 Requirements

Requirements for v0.2-v0.5 release cycle. Each maps to roadmap phases.

### Soundness (SND)

- [ ] **SND-01**: VCGen uses SSA variable renaming with phi functions at control-flow merge points
- [ ] **SND-02**: Multi-path control flow (if/else, match, early return) produces sound verification results
- [ ] **SND-03**: All arithmetic encoding verified against Rust overflow semantics (checked, wrapping, saturating)
- [ ] **SND-04**: Soundness test suite: programs with known bugs are rejected by the verifier
- [ ] **SND-05**: Completeness test suite: correct programs verify successfully
- [ ] **SND-06**: Nightly rustc version pinned in rust-toolchain.toml with compatibility documentation

### Verification Features (VER)

- [ ] **VER-01**: Loop invariants via `#[invariant(expr)]` attribute with 3 VCs (init, preservation, exit)
- [ ] **VER-02**: `assert!(expr)` statements verified statically from MIR
- [ ] **VER-03**: Panic detection for `unwrap()`, `expect()`, and array indexing
- [ ] **VER-04**: Division-by-zero verification for all integer division/remainder operations
- [ ] **VER-05**: Shift overflow verification for shift operations exceeding bit width

### Type Encoding (TYP)

- [ ] **TYP-01**: Structs encoded as SMT datatypes with constructors and field selectors
- [ ] **TYP-02**: Tuples encoded as SMT datatypes with positional selectors
- [ ] **TYP-03**: Enum variants encoded as SMT datatypes with discriminant and variant data
- [ ] **TYP-04**: Array/slice types encoded using SMT array theory

### Specification Language (SPEC)

- [ ] **SPEC-01**: Specification parser supports full Rust expression syntax via syn
- [ ] **SPEC-02**: Quantifiers (`forall`, `exists`) supported in specifications
- [ ] **SPEC-03**: Ghost code via `#[ghost]` attribute, erased at compile time
- [ ] **SPEC-04**: Unbounded mathematical integers (`int`, `nat`) for specification-only types
- [ ] **SPEC-05**: `old(expr)` operator for referring to pre-state values in postconditions

### Modular Verification (MOD)

- [ ] **MOD-01**: Inter-procedural verification using function contracts as summaries
- [ ] **MOD-02**: Call sites encoded as: assert precondition, havoc return, assume postcondition
- [ ] **MOD-03**: Function signature-to-contract map built from HIR
- [ ] **MOD-04**: Basic ownership reasoning leveraging Rust's borrow checker guarantees

### Borrow Reasoning (BRW)

- [ ] **BRW-01**: Mutable borrow reasoning via prophecy variables (Creusot-style)
- [ ] **BRW-02**: Prophecy lifecycle: creation at borrow, resolution at borrow expiration
- [ ] **BRW-03**: Trait/generic support via monomorphization-based verification

### Tooling (TOOL)

- [ ] **TOOL-01**: `cargo verify` command as cargo subcommand
- [ ] **TOOL-02**: Cargo-style output with colored status per function (OK/FAIL/TIMEOUT)
- [ ] **TOOL-03**: z3 crate with `bundled` feature as native solver backend
- [ ] **TOOL-04**: Structured tracing via `tracing` crate for debugging verification pipeline
- [ ] **TOOL-05**: Error messages show source location, failed property, and counterexample

### Performance (PERF)

- [ ] **PERF-01**: Sub-1s verification for single-function contracts (Phase 1 targets)
- [ ] **PERF-02**: Sub-5s verification for functions with loops and inter-procedural calls
- [ ] **PERF-03**: VC caching for unchanged functions (skip re-verification)
- [ ] **PERF-04**: Parallel verification of independent VCs across solver instances
- [ ] **PERF-05**: Formula simplification (constant folding, dead code elimination, CSE)

## v2 Requirements

Deferred to v1.0+ release. Tracked but not in current roadmap.

### Advanced Verification

- **ADV-01**: Trigger customization (`#[trigger]`) for SMT quantifier performance tuning
- **ADV-02**: Standard library contracts for Vec, HashMap, Option, Result
- **ADV-03**: Concurrency verification (atomics, locks, async/await)
- **ADV-04**: Unsafe code verification with conservative approximations
- **ADV-05**: AI-assisted proof generation (LLM-based invariant inference)
- **ADV-06**: Recursive function support with termination measures (`#[decreases]`)

### IDE Integration

- **IDE-01**: VSCode extension for real-time verification feedback
- **IDE-02**: rust-analyzer integration for inline diagnostics
- **IDE-03**: LSP-compatible verification status reporting

## Out of Scope

Explicitly excluded. Documented to prevent scope creep.

| Feature | Reason |
|---------|--------|
| Forked Rust compiler | Maintenance nightmare; zero-friction cargo workflow is key differentiator |
| Fully automatic verification (no annotations) | Undecidable for general programs; be honest about 80-90% automation |
| Full dependent types | Academic complexity; stick to refinement types |
| Custom SMT solver | Use Z3/CVC5 ecosystem; proven, maintained |
| Formal proof certificates | Too heavy for developer workflow |
| Windows support | Focus on macOS/Linux first; defer to community demand |
| One-size-fits-all proof automation | Different code needs different strategies; tunable automation |

## Traceability

Which phases cover which requirements. Updated during roadmap creation.

| Requirement | Phase | Status |
|-------------|-------|--------|
| SND-01 | Phase 1 | Pending |
| SND-02 | Phase 1 | Pending |
| SND-03 | Phase 1 | Pending |
| SND-04 | Phase 1 | Pending |
| SND-05 | Phase 1 | Pending |
| SND-06 | Phase 1 | Pending |
| VER-01 | Phase 2 | Pending |
| VER-02 | Phase 2 | Pending |
| VER-03 | Phase 2 | Pending |
| VER-04 | Phase 2 | Pending |
| VER-05 | Phase 2 | Pending |
| TYP-01 | Phase 2 | Pending |
| TYP-02 | Phase 2 | Pending |
| TYP-03 | Phase 2 | Pending |
| TYP-04 | Phase 2 | Pending |
| SPEC-01 | Phase 2 | Pending |
| SPEC-02 | Phase 4 | Pending |
| SPEC-03 | Phase 4 | Pending |
| SPEC-04 | Phase 4 | Pending |
| SPEC-05 | Phase 2 | Pending |
| MOD-01 | Phase 3 | Pending |
| MOD-02 | Phase 3 | Pending |
| MOD-03 | Phase 3 | Pending |
| MOD-04 | Phase 3 | Pending |
| BRW-01 | Phase 4 | Pending |
| BRW-02 | Phase 4 | Pending |
| BRW-03 | Phase 4 | Pending |
| TOOL-01 | Phase 2 | Pending |
| TOOL-02 | Phase 2 | Pending |
| TOOL-03 | Phase 2 | Pending |
| TOOL-04 | Phase 2 | Pending |
| TOOL-05 | Phase 5 | Pending |
| PERF-01 | Phase 1 | Pending |
| PERF-02 | Phase 5 | Pending |
| PERF-03 | Phase 5 | Pending |
| PERF-04 | Phase 5 | Pending |
| PERF-05 | Phase 5 | Pending |

**Coverage:**
- v1 requirements: 36 total
- Mapped to phases: 36
- Unmapped: 0

---
*Requirements defined: 2026-02-10*
*Last updated: 2026-02-10 after initial definition*
