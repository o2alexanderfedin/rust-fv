# rust-fv: Formal Verification for Rust

## What This Is

A compiler-integrated formal verification tool that mathematically proves properties about Rust code. It hooks into `rustc` via `rustc_driver::Callbacks`, extracts MIR, translates it to SMT-LIB2, and verifies properties using Z3. Developers annotate functions with `#[requires]`, `#[ensures]`, `#[pure]`, `#[invariant]`, and `#[ghost]` macros and run `cargo verify` for automated verification with rustc-style diagnostics. Supports loops, structs, inter-procedural verification, ownership reasoning, quantifiers, prophecy variables, and generics.

## Core Value

**Sound, automated verification of Rust code properties with minimal developer burden** -- if the tool says "verified", it must be mathematically correct; if a developer can write a spec, the tool should prove it automatically 80-90% of the time for safe Rust.

## Requirements

### Validated

- ✓ Proc macro annotations (`#[requires]`, `#[ensures]`, `#[pure]`, `#[invariant]`) -- v0.1.0
- ✓ SMT-LIB2 AST with strongly-typed sorts, terms, commands, scripts -- v0.1.0
- ✓ Bitvector theory (QF_BV) encoding for all integer types (i8-i128, u8-u128, isize, usize) -- v0.1.0
- ✓ Arithmetic overflow detection for add/sub/mul/div/rem/shl/shr -- v0.1
- ✓ MIR-to-IR conversion (basic blocks, statements, terminators, operands) -- v0.1.0
- ✓ Verification condition generation from IR functions -- v0.1.0
- ✓ Z3 solver integration via subprocess and native API -- v0.1
- ✓ End-to-end pipeline: annotation -> MIR extraction -> VC -> SMT -> Z3 -> result -- v0.1.0
- ✓ Rustc driver with `after_analysis` hook and `RUSTC` env var integration -- v0.1.0
- ✓ Contract extraction from HIR doc attributes -- v0.1.0
- ✓ Precondition and postcondition verification -- v0.1.0
- ✓ Counterexample extraction from SAT results -- v0.1.0
- ✓ Path-sensitive VCGen with sound control-flow handling -- v0.1
- ✓ Soundness test suite (22 programs) and completeness test suite (22 programs) -- v0.1
- ✓ Division-by-zero and shift overflow verification -- v0.1
- ✓ Loop invariant verification (3-VC: init/preserve/exit) -- v0.1
- ✓ Assertion and panic detection (unwrap, bounds, div-by-zero) -- v0.1
- ✓ Aggregate type encoding (structs, tuples, enums as SMT datatypes) -- v0.1
- ✓ Full syn-based specification parser with old() operator -- v0.1
- ✓ `cargo verify` subcommand with colored output -- v0.1
- ✓ Z3 native API backend via SolverBackend trait -- v0.1
- ✓ Structured tracing via tracing crate -- v0.1
- ✓ Inter-procedural verification with contract summaries -- v0.1
- ✓ Ownership-aware verification (move/copy/borrow classification) -- v0.1
- ✓ Unbounded mathematical integers (SpecInt/SpecNat, `as int` cast) -- v0.1
- ✓ Ghost code via `#[ghost]` attribute -- v0.1
- ✓ Quantifiers (forall/exists) with automatic trigger inference -- v0.1
- ✓ Prophecy variables for mutable borrow reasoning -- v0.1
- ✓ Generic function verification via monomorphization -- v0.1
- ✓ Formula simplification (8 algebraic rules, ~30% SMT size reduction) -- v0.1
- ✓ VC caching with SHA-256 invalidation -- v0.1
- ✓ Parallel verification with Rayon and topological ordering -- v0.1
- ✓ Ariadne-based rustc-style error diagnostics with fix suggestions -- v0.1
- ✓ JSON output for IDE integration -- v0.1

### Active

- [ ] Recursive function support with termination measures (`#[decreases]`)
- [ ] Closure verification (capture reasoning, Fn/FnMut/FnOnce contracts)
- [ ] Trait object and dynamic dispatch verification
- [ ] Unsafe code verification with conservative approximations
- [ ] Deeper reference/lifetime reasoning (reborrow tracking, lifetime-aware specs)
- [ ] SSA-based parameter encoding for prophecy variable resolution
- [ ] Floating-point verification (IEEE 754, QF_FP theory)
- [ ] Concurrency verification (atomics, Mutex/RwLock, Send/Sync, async/await)
- [ ] Standard library contracts (Vec, HashMap, Option, Result)
- [ ] Trigger customization (`#[trigger]`) for quantifier performance
- [ ] Z3 bv2int native integration (currently deferred)

## Current Milestone: v0.2 Advanced Verification

**Goal:** Extend verification to cover all major Rust language features -- recursive functions, closures, traits, unsafe code, lifetimes, floating-point, and concurrency.

**Target features:**
- Recursive functions with termination measures
- Closure and trait object verification
- Unsafe code with conservative approximations
- Deeper reference/lifetime reasoning with SSA fix
- Floating-point verification (IEEE 754)
- Concurrency verification (atomics, locks, async)

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
- **Current state:** v0.1 shipped with 1,741 tests, zero warnings, 5-crate workspace (macros/, smtlib/, solver/, analysis/, driver/), 43,621 LOC Rust
- **Known limitations:** Prophecy encoding limitation with direct &mut param reassignment (needs SSA for parameters), Z3 bv2int requires Z3 4.8.10+
- **Tech debt:** Floating-point types unsupported, recursive functions unsupported, no standard library contracts

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
| Verification by negation (assert NOT, check UNSAT) | Standard SMT approach, counterexamples come free | ✓ Good |
| 5-crate workspace separation | Clean boundaries, testable on stable (except driver) | ✓ Good |
| Path-condition encoding over SSA phi-nodes | Simpler handling of early returns, match arms | ✓ Good |
| Classical 3-VC loop verification | Proven Hoare-logic approach, clear failure diagnostics | ✓ Good |
| Contract-based modular verification | Scalable (no callee inlining), standard technique | ✓ Good |
| Monomorphization for generics | Mirrors Rust's own approach, concrete type safety | ✓ Good |
| Conservative trigger inference | Automatic benefit for all quantified specs | ✓ Good |
| AST-level formula simplification | Backend-agnostic, zero overhead, ~30% reduction | ✓ Good |
| Per-function SHA-256 caching | Conservative invalidation, correct by default | ✓ Good |
| Rayon parallel verification | Simple, effective, topological ordering for correctness | ✓ Good |
| Ariadne for diagnostics | Mature library, rustc-style output, good UX | ✓ Good |
| JSON output to stdout | IDE integration best practice, stderr for human output | ✓ Good |

---
*Last updated: 2026-02-12 after v0.2 milestone start*
