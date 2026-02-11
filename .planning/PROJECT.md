# rust-fv: Formal Verification for Rust

## What This Is

A compiler-integrated formal verification tool that mathematically proves properties about Rust code. It hooks into `rustc` via `rustc_driver::Callbacks`, extracts MIR, translates it to SMT-LIB2, and verifies properties using Z3. Developers annotate functions with `#[requires]`, `#[ensures]`, `#[pure]`, and `#[invariant]` macros and get sub-second verification feedback during `cargo check`.

## Core Value

**Sound, automated verification of Rust code properties with minimal developer burden** — if the tool says "verified", it must be mathematically correct; if a developer can write a spec, the tool should prove it automatically 80-90% of the time for safe Rust.

## Requirements

### Validated

- ✓ Proc macro annotations (`#[requires]`, `#[ensures]`, `#[pure]`, `#[invariant]`) — v0.1.0
- ✓ SMT-LIB2 AST with strongly-typed sorts, terms, commands, scripts — v0.1.0
- ✓ Bitvector theory (QF_BV) encoding for all integer types (i8–i128, u8–u128, isize, usize) — v0.1.0
- ✓ Arithmetic overflow detection for add/sub/mul — v0.1.0
- ✓ MIR-to-IR conversion (basic blocks, statements, terminators, operands) — v0.1.0
- ✓ Verification condition generation from IR functions — v0.1.0
- ✓ Z3 solver integration via subprocess with auto-detection — v0.1.0
- ✓ End-to-end pipeline: annotation → MIR extraction → VC → SMT → Z3 → result — v0.1.0
- ✓ Rustc driver with `after_analysis` hook and `RUSTC` env var integration — v0.1.0
- ✓ Contract extraction from HIR doc attributes — v0.1.0
- ✓ Precondition and postcondition verification — v0.1.0
- ✓ Counterexample extraction from SAT results — v0.1.0

### Active

- [ ] Division-by-zero verification
- [ ] Shift overflow verification
- [ ] Array bounds checking
- [ ] Aggregate type encoding (tuples, structs, enums)
- [ ] Floating-point verification (IEEE 754)
- [ ] Full specification expression parser (beyond simple comparisons)
- [ ] Loop invariant support
- [ ] Mutable borrow reasoning (prophecy operators)
- [ ] Inter-procedural verification (function summaries)
- [ ] Recursive function support
- [ ] Proper SSA renaming for path-sensitive analysis
- [ ] Unreachable code elimination in VCGen
- [ ] Cargo subcommand (`cargo fv check`)
- [ ] IDE integration (rust-analyzer diagnostics)

### Out of Scope

- Unsafe code verification — Phase 3 feature, requires ghost state infrastructure
- Full dependent types — academic complexity; stick to refinement types
- Custom SMT solver — use Z3/CVC5 ecosystem
- Formal proof certificates — too heavy for developer workflow
- Windows support — focus on macOS/Linux first

## Context

- **Ecosystem:** Follows Verus model (SMT-based, Rust-native specs) but targets broader usability
- **Competitors:** Verus (academic, requires forked compiler), Prusti (Viper-based, heavy), Kani (bounded model checking, different niche)
- **Differentiator:** Zero-friction integration via standard `cargo` workflow, no forked compiler
- **Current state:** v0.1.0 released with 248 tests, zero warnings, 5-crate workspace
- **Tech debt:** Aggregate types uninterpreted, floats unsupported, spec parser limited to simple comparisons, SSA counter unused, mir_converter untested directly

## Constraints

- **Toolchain**: Nightly Rust required (`rustc_private` feature gate) — no stable alternative for MIR access
- **Solver**: Z3 must be installed on user's system — runtime dependency
- **Soundness**: Non-negotiable — false positives acceptable, false negatives are bugs
- **Performance**: Sub-1s for Phase 1 functions, sub-5s for Phase 2, sub-30s for Phase 3
- **Automation**: 80-90% for safe Rust, 60-70% for deductive, manual proof fallback accepted
- **API stability**: rustc internals change frequently — driver crate must absorb breakage

## Key Decisions

| Decision | Rationale | Outcome |
|----------|-----------|---------|
| SMT-based verification (Z3) | High automation (80-90%), mature ecosystem, bitvector theory for exact integer semantics | ✓ Good |
| Proc macros for specs | Stable API, no compiler fork needed, Rust-native syntax | ✓ Good |
| MIR-level analysis | Desugared, typed, borrow-checked — ideal for verification | ✓ Good |
| Bitvector theory (QF_BV) | Exact integer overflow semantics matching Rust | ✓ Good |
| Z3 as subprocess (not library) | Cross-platform, version flexibility, simpler build | ✓ Good |
| Hidden doc attributes for spec transport | Works with stable proc macros, survives compilation phases | ✓ Good |
| Verification by negation (assert NOT, check UNSAT) | Standard SMT approach, counterexamples come free | ✓ Good |
| 5-crate workspace separation | Clean boundaries, testable on stable (except driver) | ✓ Good |
| Conservative SMT encoding | Predictable performance over completeness | — Pending |

---
*Last updated: 2026-02-10 after initialization*
