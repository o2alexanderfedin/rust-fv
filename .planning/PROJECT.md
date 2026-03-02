# rust-fv: Formal Verification for Rust

## What This Is

A compiler-integrated formal verification tool that mathematically proves properties about Rust code. It hooks into `rustc` via `rustc_driver::Callbacks`, extracts MIR, translates it to SMT-LIB2, and verifies properties using Z3. Developers annotate functions with `#[requires]`, `#[ensures]`, `#[pure]`, `#[invariant]`, `#[ghost]`, `#[decreases]`, `#[lock_invariant]`, `#[unsafe_requires]`, `#[unsafe_ensures]`, and `#[verifier::trusted]` macros and run `cargo verify` for automated verification with rustc-style diagnostics. Supports loops, structs, inter-procedural verification, ownership reasoning, quantifiers, prophecy variables, generics, recursive functions, closures, trait objects, lifetimes, unsafe code, floating-point, concurrency, for-loop iterator VCGen, borrow conflict detection, and heap separation logic.

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
- ✓ Array index bounds VCs + `Rvalue::Len` as named SMT constant — v0.5
- ✓ Generic `where`-clause trait bound premises as SMT `Assert` in `generate_vcs_with_db` — v0.5
- ✓ CastKind preservation in MIR converter (FloatToInt/IntToFloat/FloatToFloat/Pointer) — v0.5
- ✓ Aggregate conversion: `AggregateKind::Adt/Closure` + `ir::Statement::SetDiscriminant/Assume` — v0.5
- ✓ Float-to-int SMT soundness fix: `fp.to_sbv/fp.to_ubv RTZ` — v0.5
- ✓ Missing rvalue variants: CopyForDeref, RawPtr, Repeat; TyKind::Param → Ty::Generic — v0.5
- ✓ Projected LHS struct field mutation via SMT functional record update — v0.5

- ✓ For-loop iterator range VCGen — AUFLIA quantified VCs + QF_LIA bounded unrolling for `for x in 0..n` patterns — v0.5-audit
- ✓ Prophecy encoding for mutable references — `*_1` in postconditions resolves to `_1_prophecy` correctly — v0.5-audit
- ✓ Borrow conflict detection — `generate_expiry_vcs()` detects use-after-lifetime-end via statement scanning — v0.5-audit
- ✓ `Statement::SetDiscriminant` VCGen — discriminant assertion VCs fully implemented; VCGEN-06 closed — v0.5-audit
- ✓ Z3 bv2int fix — `uses_spec_int_types()` detects `as int`/`as nat`, enabling QF_LIA path for SpecInt/SpecNat — v0.5-audit
- ✓ Ghost locals filtering — `is_ghost_place()` guard prevents ghost variable leakage into executable VCs — v0.5-audit
- ✓ v0.1 tech debt fully resolved — E2E benchmarks, bv2int docs, pointer aliasing edge cases, trigger edge cases, float VC placeholders — v0.5-audit
- ✓ v0.1 Milestone Audit closed — status: passed, 37/37 phases pass, 0 human_needed — v0.5-audit

- ✓ Cross-function pointer aliasing — `#[unsafe_requires(!alias(p,q))]` generates Z3 SAT VCs detecting aliased pointer args at call sites — v0.6
- ✓ Opaque callee diagnostics V060/V061 — warning/error when verified function calls uncontracted callee; replaces silent skip — v0.6
- ✓ Summary contract inference — `#[verifier::infer_summary]` auto-generates minimal contracts for opaque callees; JSON output — v0.6
- ✓ HIR-based alias precondition parsing — `parse_alias_preconditions()` closes always-empty gap; full driver→vcgen→Z3 pipeline verified — v0.6
- ✓ Cross-crate Tarjan SCC detection — `from_functions_with_cross_crate_db` breaks crate island barrier via virtual node injection — v0.6
- ✓ Cross-crate `#[decreases]` termination verification — cross-crate mutual recursion termination proven with Z3 UNSAT/SAT — v0.6
- ✓ V062 InferredSummaryAlias guard — closes is_inferred + alias_preconditions co-occurrence; emits warning instead of silent drop — v0.6

### Active

*(Planning next milestone — see `/gsd:new-milestone`)*

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
- **Current state:** v0.6 complete — 44 phases, ~103,500 LOC Rust, 6-crate workspace + VSCode extension; cross-crate verification fully delivered, 1245+ tests passing
- **v0.6 achievements:** Cross-function pointer aliasing (ALIAS-01/02), opaque callee diagnostics V060/V061 (OPAQUE-01/02), summary contract inference (OPAQUE-03), HIR alias precondition parsing, cross-crate Tarjan SCC (XCREC-01), cross-crate termination measures (XCREC-02), V062 InferredSummaryAlias guard — all 7/7 requirements satisfied
- **Known limitations:** Bounded concurrency (max threads/switches configurable), FPA theory 2-10x slower than bitvectors; PtrCast alignment-check VC not yet generated (DEBTLINE); FnMut prophecy integration deferred; conservative live ranges in lifetime reasoning
- **Tech debt:** `extract_alias_preconditions` pub visibility with test-only callers; alternative output paths (rustc_json.rs, cargo_verify.rs) statically set `inferred_summaries: None`
- **Next:** v0.7 milestone — see `/gsd:new-milestone`

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
| Stub for_loop_vcgen with todo!() panic as TDD RED (Phase 29.1) | Pre-commit hook requires compile; runtime panic is valid TDD RED state | ✓ Good |
| in_postcondition threading through convert_expr_with_db (Phase 29.2) | `*_1` in ensures → `_1_prophecy`; inside old() resets to false; preconditions unchanged | ✓ Good |
| statement_references_local() exhaustive Rvalue match (Phase 29.3) | Checks both LHS and RHS; compiler-enforced completeness, no wildcard | ✓ Good |
| Term::IntLit takes i128 for SetDiscriminant (Phase 30) | Matches Term variant type; correct for i128 variant index cast | ✓ Good |
| Extended uses_spec_int_types() with substring scan (Phase 31) | Detects `as int`/`as nat` in spec strings; minimal change enabling QF_LIA path | ✓ Good |
| Ghost erasure from both encode_assignment and collect_declarations (Phase 31) | Complete SMT erasure; test contract takes precedence over plan prose | ✓ Good |
| Retrospective VERIFICATION.md with verbatim cargo test output (Phase 32) | Live test run during audit provides current evidence anchor | ✓ Good |
| Phase 11 float placeholder terms intentional PASS (Phase 32) | lhs/rhs/result placeholder VCs are correct design for float specs — not a gap | ✓ Good |
| encode_operand() wired directly into generate_float_vcs() (Phase 33) | 3-line change closes float VC placeholder tech debt; no abstraction layer needed | ✓ Good |
| CallGraph bidirectional name_map normalization (Phase 33) | Normalize caller names internally; return full names via name_map in all API methods | ✓ Good |
| AliasPrecondition stores parameter indices not names (Phase 34) | Enables call-site substitution — indices are stable across call boundaries; names vary | ✓ Good |
| OpaqueCallee always-SAT VC pattern (Phase 35) | BoolLit(true) VC with VcKind carrying diagnostic classification; mirrors DataRaceFreedom | ✓ Good |
| infer_summary suppression via is_inferred flag on FunctionSummary (Phase 36) | Early continue in generate_call_site_vcs before has_requires check; minimal invasiveness | ✓ Good |
| HirContracts return type for extract_contracts (Phase 36.1) | Preserves unsafe_requires across HIR→IR boundary; hir_contracts_to_ir() converter added | ✓ Good |
| from_functions_with_cross_crate_db back-edge heuristic (Phase 37) | Virtual node injection via ContractDatabase; decreases.raw substring match for cross-crate edges | ✓ Good |
| normalize_callee fallback for cross-crate callee names (Phase 37) | group.contains(callee) || !group.contains(callee_name) handles full-path cross-crate names | ✓ Good |
| V062 InferredSummaryAlias guard hoists alias check before is_inferred (Phase 37.1) | Alias VCs emitted regardless of is_inferred when alias_preconditions non-empty; warning-only | ✓ Good |

## Shipped: v0.6 Cross-Crate Verification (2026-03-02)

**Goal achieved:** Broke the "each crate is an island" barrier — cross-function pointer aliasing, opaque callee contract enforcement, and cross-crate mutual recursion detection all verified end-to-end.

**Delivered (phases 34–37.1):**
- Cross-function pointer aliasing: `#[unsafe_requires(!alias(p,q))]` → spec_parser → `AliasPrecondition` → vcgen alias VC loop → Z3 SAT
- Opaque callee diagnostics: V060 (warning) + V061 (error for unsafe context) replace silent skip at vcgen.rs:2366
- Summary contract inference: `#[verifier::infer_summary]` proc-macro → callbacks HIR scan → is_inferred flag → vcgen suppression → JSON `inferred_summaries`
- HIR alias precondition parsing: `parse_alias_preconditions()` in callbacks.rs closes always-empty alias_preconditions gap
- Cross-crate Tarjan SCC: `CallGraph::from_functions_with_cross_crate_db` injects virtual nodes for contracted callees
- Cross-crate termination: `generate_termination_vcs` uses caller-side VCs for cross-crate calls; Z3 UNSAT/SAT proof
- V062 InferredSummaryAlias guard: closes is_inferred + alias_preconditions co-occurrence; warning emitted instead of silent drop

---
*Last updated: 2026-03-02 after v0.6 Cross-Crate Verification milestone complete*
