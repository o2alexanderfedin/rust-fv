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
- ✓ Counterexample generation — typed Rust values (not SSA/hex), ariadne inline labels, JSON structured output -- v0.4
- ✓ Separation logic — `pts_to`, separating conjunction, frame rule, `#[ghost_predicate]` recursive heap predicates (depth-3 unfolding) -- v0.4
- ✓ Weak memory models — full RC11 (mo/rf/co), 8 canonical C11 litmus tests, data race detection for Relaxed/Acquire/Release atomics -- v0.4
- ✓ Higher-order closures — `fn_spec` specification entailments, stateful `FnMut` SSA-versioned environment tracking -- v0.4
- ✓ Async/await — `async fn` verification under sequential polling model, `#[state_invariant]` at suspension points, IDE rendering with poll_iteration/await_side -- v0.4

- ✓ Numeric `as`-cast encoding with correct sign-extension/truncation/FPA semantics — v0.5
- ✓ Match/if-let/while-let discriminant binding VCGen via `Rvalue::Discriminant` — v0.5
- ✓ Array index bounds VCs + `Rvalue::Len` as named SMT constant — v0.5 (partial: for loops deferred)
- ✓ Generic `where`-clause trait bound premises as SMT `Assert` in `generate_vcs_with_db` — v0.5
- ✓ CastKind preservation in MIR converter (FloatToInt/IntToFloat/FloatToFloat/Pointer) — v0.5
- ✓ Aggregate conversion: `AggregateKind::Adt/Closure` + `ir::Statement::SetDiscriminant/Assume` — v0.5
- ✓ Float-to-int SMT soundness fix: `fp.to_sbv/fp.to_ubv RTZ` — v0.5
- ✓ Missing rvalue variants: CopyForDeref, RawPtr, Repeat; TyKind::Param → Ty::Generic — v0.5
- ✓ Projected LHS struct field mutation via SMT functional record update — v0.5

### Active

#### Current Milestone: v0.6 (TBD)

(Next milestone requirements to be defined with `/gsd:new-milestone`)

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
- **Ecosystem:** Follows Verus model (SMT-based, Rust-native specs) but targets broader usability
- **Competitors:** Verus (academic, requires forked compiler), Prusti (Viper-based, heavy), Kani (bounded model checking, different niche)
- **Differentiator:** Zero-friction integration via standard `cargo` workflow, no forked compiler
- **Current state:** v0.5 shipped — 29 phases, 92 plans, 6-crate workspace + VSCode extension; complete SMT VCGen coverage for all major Rust expression categories
- **v0.5 achievements:** Cast encoding, discriminant binding, array bounds VCs, generic premises, CastKind preservation, aggregate wiring, float-to-int soundness fix, functional record update for struct mutation
- **Known limitations:** Bounded concurrency (max threads/switches configurable), FPA theory 2-10x slower than bitvectors; async closures (Rust 2024) deferred to v0.5
- **Tech debt:** Pre-existing doc test failures in stdlib_contracts/option.rs (26 doc tests, `self` parameter issue); v0.4 tech debt fully resolved

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
| VcOutcome structured pairs for CEX (Phase 19) | Source name + Z3 model value pairs extracted at Z3 SAT time; clean boundary | ✓ Good |
| AUFBV SMT for separation logic (Phase 20) | Array theory for heap; pts_to as uninterpreted function over byte array | ✓ Good |
| Bounded ghost predicate unfolding depth-3 (Phase 20) | Covers practical linked lists/trees without induction; avoids undecidability | ✓ Good |
| Arc<GhostPredicateDb> through VerificationTask (Phase 24) | Thread-safe sharing across parallel verifier; Arc over clone | ✓ Good |
| QF_LIA integer arithmetic for RC11 (Phase 21) | mo/rf/co as integer sequences; avoids QF_BV complexity for ordering | ✓ Good |
| fn_spec as AUFLIA uninterpreted predicate (Phase 22) | First-order SMT encoding of closure specs; Reynolds defunctionalization extended | ✓ Good |
| CoroutineInfo + polling model for async (Phase 23) | Sequential poll-based state machine; no executor complexity | ✓ Good |
| GetModel in async VC scripts (Phase 27) | check_sat_raw() doesn't auto-append get-model; must be explicit in script | ✓ Good |
| await_side inferred from VcKind (Phase 27) | Deterministic from VC type; no Z3 model query needed | ✓ Good |
| infer_operand_type() for cast source type (Phase 28) | Fallback to target_ty when unresolvable; avoids panics on opaque operands | ✓ Good |
| Rvalue::Discriminant as Term::App uninterpreted selector (Phase 28) | Z3 accepts without explicit declare-fun; no need for SMT DeclareFun preamble | ✓ Good |
| BoundsCheck VCs use VcKind::MemorySafety (Phase 28) | No new variant needed; MemorySafety semantics cover all bounds checks | ✓ Good |
| Ty::Generic → Sort::Uninterpreted (Phase 28) | Enables parametric VCGen without monomorphization; no panic on generic specs | ✓ Good |
| trait_bounds_as_smt_assumptions emits BoolLit(true) (Phase 28) | Sound (no false premises), documents contract, Z3 ignores harmlessly | ✓ Good |
| CastKind exhaustive match in mir_converter (Phase 29) | Compiler enforces completeness on MIR API changes; no wildcard catch-all | ✓ Good |
| AggregateKind::Adt maps to ir::AggregateKind::Enum (Phase 29) | Structs use variant_idx=0; unified enum+struct encoding in IR | ✓ Good |
| encode_cast to_signed: bool parameter (Phase 29) | Distinguishes fp.to_sbv vs fp.to_ubv at call site; RTZ matches Rust truncation | ✓ Good |
| Cow<Ty> in encode_place_with_type (Phase 29) | Downcast produces owned variant-struct Ty alongside borrowed Tys from find_local_type | ✓ Good |
| Functional update emits ALL fields in order (Phase 29) | Changed field gets new_val, others get selector(base); correct constructor arity guaranteed | ✓ Good |

## Shipped: v0.5 SMT Completeness

**Goal achieved:** Complete SMT VCGen coverage for all major Rust expression categories — casts, match/discriminants, array bounds, generics, aggregates, and struct mutation.

**Delivered:**
- Numeric `as`-cast VCGen with sign-extension/truncation/FPA semantics (`encode_cast()`)
- Match/if-let/while-let discriminant binding via `Rvalue::Discriminant` uninterpreted selector
- Array bounds VCs + Rvalue::Len encoding; generic trait bound premises in `generate_vcs_with_db`
- CastKind preservation in MIR converter; AggregateKind::Adt/Closure wiring; SetDiscriminant/Assume IR variants
- Float-to-int soundness fix (`fp.to_sbv/fp.to_ubv RTZ`); TyKind::Param→Generic; CopyForDeref/RawPtr/Repeat
- Projected LHS struct field mutation via SMT functional record update with correct constructor arity

**Known gaps (deferred to v0.6):**
- VCGEN-01 PARTIAL: for/iterator loops, range expressions, slice references
- vcgen_06_set_discriminant_assertion (Statement::SetDiscriminant VCGen encoding)

---
*Last updated: 2026-02-25 after v0.5 SMT Completeness milestone shipped*
