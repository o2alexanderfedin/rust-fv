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
- ✓ Standard library contracts (Vec, HashMap, Option, Result, Iterator) with SMT Seq theory, proptest oracle validation, zero-config loading -- v0.3
- ✓ Incremental verification with <1s re-verification via dual-hash MIR+contract cache, transitive invalidation, 20-30x speedup -- v0.3
- ✓ Manual trigger customization (`#[trigger(expr)]`) with self-instantiation detection and interpreted symbol warnings -- v0.3
- ✓ VSCode extension with inline diagnostics, status bar, output panel, SMT-LIB viewer, gutter decorations, Z3 bundling -- v0.3
- ✓ rust-analyzer integration with `--message-format=json`, flycheck via `overrideCommand`, diagnostic deduplication -- v0.3
- ✓ bv2int optimization with `--bv2int`/env activation, differential testing, `--bv2int-report` summary, slowdown warnings -- v0.3

### Active

#### Future (v0.4+)

- [ ] Higher-order closures with specification entailments
- [ ] Weak memory models (Relaxed, Acquire, Release atomics beyond SeqCst)
- [ ] Async/await verification (Future trait, executor semantics)
- [ ] Separation logic for heap reasoning
- [ ] Counterexample generation with concrete failure values
- [ ] Multiple SMT solver backends (CVC5, Yices)

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
- **Current state:** v0.3 shipped with 1,613 lib tests, zero warnings, 6-crate workspace + VSCode extension, 82,642 LOC Rust + TypeScript
- **Known limitations:** Bounded concurrency (max threads/switches configurable), FPA theory 2-10x slower than bitvectors, sequential consistency only for atomics; stdlib contracts cover Tier 1 only (Vec/HashMap/Option/Result/Iterator)
- **Tech debt:** Pre-existing doc test failures in stdlib_contracts/option.rs (26 doc tests, `self` parameter issue); no weak memory models; no async/await
- **v0.4 focus:** Advanced verification features — counterexample generation, higher-order closures, weak memory models, multiple SMT backends

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
| SMT Seq sort for stdlib (Phase 13) | Native sequence operations vs array encoding; Vec/String/slice modeling | ✓ Good |
| StdlibContractRegistry with enable flag (Phase 13) | Supports --no-stdlib-contracts opt-out; zero-config default | ✓ Good |
| Dual-hash cache (MIR+contract, Phase 14) | Precise invalidation granularity; age-based eviction (30-day TTL) | ✓ Good |
| Transitive invalidation via reverse call graph (Phase 14) | Contract changes cascade to callers; sound incremental verification | ✓ Good |
| Self-instantiation detection via name matching (Phase 15) | Catch-all for infinite trigger loops; conservative approach | ✓ Good |
| TriggerHint as Vec<Term> in IR (Phase 15) | Stored separately from SMT Term layer; clean layer separation | ✓ Good |
| Whole-crate verification scope in VSCode (Phase 16) | Matches cargo check pattern; relies on incremental cache for speed | ✓ Good |
| Fresh spawn per save (Phase 16) | Simpler lifecycle than persistent background process | ✓ Good |
| SMT-LIB viewer reads from filesystem (Phase 16) | Keeps JSON payloads small; files in target/verify/ | ✓ Good |
| --message-format=json separate from --output-format (Phase 17) | IDE rustc-compat vs machine-readable; orthogonal concerns | ✓ Good |
| Workspace-scoped overrideCommand (Phase 17) | Not global; workspace-aware RA mode | ✓ Good |
| Entire-function rejection for bitwise/shift (Phase 18) | Conservative bv2int applicability; avoids complex per-expression tracking | ✓ Good |
| SolverInterface trait in differential.rs (Phase 18) | Self-contained equivalence testing; no binary dependency for unit tests | ✓ Good |
| Post-hoc logic replacement for bv2int (Phase 18) | Swaps QF_BV to QF_LIA/QF_NIA; minimal invasiveness | ✓ Good |

---
*Last updated: 2026-02-17 after v0.3 milestone completion*
