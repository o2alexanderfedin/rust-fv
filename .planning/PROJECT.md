# rust-fv: Formal Verification for Rust

## What This Is

A compiler-integrated formal verification tool that mathematically proves properties about Rust code. It hooks into `rustc` via `rustc_driver::Callbacks`, extracts MIR, translates it to SMT-LIB2, and verifies properties using Z3. Developers annotate functions with `#[requires]`, `#[ensures]`, `#[pure]`, `#[invariant]`, `#[ghost]`, `#[decreases]`, `#[lock_invariant]`, `#[unsafe_requires]`, `#[unsafe_ensures]`, and `#[verifier::trusted]` macros and run `cargo verify` for automated verification with rustc-style diagnostics. Supports loops, structs, inter-procedural verification, ownership reasoning, quantifiers, prophecy variables, generics, recursive functions, closures, trait objects, lifetimes, unsafe code, floating-point, and concurrency.

## Core Value

**Sound, automated verification of Rust code properties with minimal developer burden** -- if the tool says "verified", it must be mathematically correct; if a developer can write a spec, the tool should prove it automatically 80-90% of the time for safe Rust.

## Requirements

### Validated

- ✓ Proc macro annotations (`#[requires]`, `#[ensures]`, `#[pure]`, `#[invariant]`) -- v0.1
- ✓ SMT-LIB2 AST with strongly-typed sorts, terms, commands, scripts -- v0.1
- ✓ Bitvector theory (QF_BV) encoding for all integer types -- v0.1
- ✓ Arithmetic overflow detection for add/sub/mul/div/rem/shl/shr -- v0.1
- ✓ MIR-to-IR conversion (basic blocks, statements, terminators, operands) -- v0.1
- ✓ Verification condition generation from IR functions -- v0.1
- ✓ Z3 solver integration via subprocess and native API -- v0.1
- ✓ End-to-end pipeline: annotation -> MIR -> VC -> SMT -> Z3 -> result -- v0.1
- ✓ Rustc driver with `after_analysis` hook -- v0.1
- ✓ Precondition/postcondition, counterexample, path-sensitive VCGen -- v0.1
- ✓ Soundness/completeness test suites (44 programs) -- v0.1
- ✓ Loops, assertions, aggregates, spec parser with old() -- v0.1
- ✓ `cargo verify`, native Z3, tracing, inter-procedural, ownership -- v0.1
- ✓ SpecInt/SpecNat, ghost code, quantifiers, prophecy, generics -- v0.1
- ✓ Simplification, caching, parallelism, Ariadne diagnostics, JSON output -- v0.1
- ✓ Recursive functions with `#[decreases]` termination measures and Tarjan's SCC -- v0.2
- ✓ Closure verification via defunctionalization (Fn/FnMut/FnOnce) -- v0.2
- ✓ Trait object verification with behavioral subtyping and sealed traits -- v0.2
- ✓ Lifetime reasoning with NLL tracking, outlives, reborrow chains, nested prophecy -- v0.2
- ✓ Unsafe code detection with heap-as-array model, null/bounds checks, `#[trusted]` -- v0.2
- ✓ IEEE 754 floating-point verification with SMT FPA theory -- v0.2
- ✓ Bounded concurrency verification with happens-before, data races, deadlock detection -- v0.2

### Active

- [ ] Standard library contracts (Vec, HashMap, Option, Result)
- [ ] Trigger customization (`#[trigger]`) for quantifier performance
- [ ] Z3 bv2int native integration
- [ ] Higher-order closures with specification entailments
- [ ] Weak memory models (Relaxed, Acquire, Release atomics beyond SeqCst)
- [ ] Async/await verification (Future trait, executor semantics)
- [ ] Separation logic for heap reasoning
- [ ] VSCode extension for real-time verification feedback
- [ ] rust-analyzer integration for inline diagnostics

### Out of Scope

- Forked Rust compiler -- zero-friction cargo workflow is key differentiator
- Full dependent types -- academic complexity; stick to refinement types
- Custom SMT solver -- use Z3/CVC5 ecosystem
- Formal proof certificates -- too heavy for developer workflow
- Windows support -- focus on macOS/Linux first
- Fully automatic verification (no annotations) -- undecidable for general programs

## Context

- **Ecosystem:** Follows Verus model (SMT-based, Rust-native specs) but targets broader usability
- **Competitors:** Verus (academic, requires forked compiler), Prusti (Viper-based, heavy), Kani (bounded model checking, different niche)
- **Differentiator:** Zero-friction integration via standard `cargo` workflow, no forked compiler
- **Current state:** v0.2 shipped with 2,264 tests, zero warnings, 5-crate workspace (macros/, smtlib/, solver/, analysis/, driver/), 66,133 LOC Rust
- **Known limitations:** Bounded concurrency (max threads/switches configurable), FPA theory 2-10x slower than bitvectors, sequential consistency only for atomics
- **Tech debt:** No standard library contracts, no weak memory models, no async/await support

## Constraints

- **Toolchain**: Nightly Rust required (`rustc_private` feature gate) -- no stable alternative for MIR access
- **Solver**: Z3 must be installed on user's system -- runtime dependency (native API via z3 crate also available)
- **Soundness**: Non-negotiable -- false positives acceptable, false negatives are bugs
- **Performance**: Sub-1s single-function, sub-5s with loops/inter-procedural, parallel verification for multi-function crates
- **Automation**: 80-90% for safe Rust, 60-70% for deductive, manual proof fallback accepted
- **API stability**: rustc internals change frequently -- driver crate must absorb breakage

## Key Decisions

| Decision | Rationale | Outcome |
|----------|-----------|---------|
| SMT-based verification (Z3) | High automation (80-90%), mature ecosystem, bitvector theory for exact integer semantics | ✓ Good |
| Proc macros for specs | Stable API, no compiler fork needed, Rust-native syntax | ✓ Good |
| MIR-level analysis | Desugared, typed, borrow-checked -- ideal for verification | ✓ Good |
| Bitvector theory (QF_BV) | Exact integer overflow semantics matching Rust | ✓ Good |
| SolverBackend trait (subprocess + native Z3) | Zero-cost abstraction, ~50ms overhead eliminated with native | ✓ Good |
| Hidden doc attributes for spec transport | Works with stable proc macros, survives compilation phases | ✓ Good |
| 5-crate workspace separation | Clean boundaries, testable on stable (except driver) | ✓ Good |
| Contract-based modular verification | Scalable (no callee inlining), standard technique | ✓ Good |
| Uninterpreted function encoding for recursion | Dafny/F* pattern; better control than Z3 define-fun-rec | ✓ Good |
| Defunctionalization for closures | Reynolds 1972; first-order SMT with explicit environment parameter | ✓ Good |
| Behavioral subtyping for traits | LSP enforcement; precondition weaker, postcondition stronger | ✓ Good |
| Heap-as-array memory model for unsafe | Byte-addressable memory with allocation metadata; null axiom | ✓ Good |
| IEEE 754 FPA theory for floats | Exact semantics; 2-10x slower but correct | ✓ Good |
| Bounded concurrency with happens-before | State explosion mitigation; sequential consistency first | ✓ Good |
| petgraph for SCC analysis | Mature Tarjan's algorithm; used for recursion and deadlock detection | ✓ Good |

---
*Last updated: 2026-02-14 after v0.2 milestone completion*
