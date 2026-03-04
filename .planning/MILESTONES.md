# Milestones

## v0.7 Generics & Traits Hardening (Shipped: 2026-03-04)

**Phases completed:** 8 phases (38–44 + generics-fix), 14 plans
**Tests:** 2,831 passing (0 failures), up from 1,245 in v0.6
**Lines of code:** ~107,173 Rust (+13,235 / -164 from v0.6)
**Timeline:** 3 days (2026-03-01 to 2026-03-03)
**Feature commits:** 75
**Requirements:** 7/7 (TRT-01..05, GENERICS-01, GENERICS-02) — all satisfied

**Key accomplishments:**
1. Behavioral subtyping VCs — `generate_subtyping_vcs` wired into `after_analysis` pipeline; trait impl postcondition/precondition Liskov checks submitted to Z3 for every impl with contracts (Phase 38)
2. FnMut prophecy variable encoding — `CaptureMode` enum, `detect_closure_prophecies`, and `ProphecyInfo.closure_name` enable mutable closure capture verification with pre/post state tracking (Phase 39)
3. Generic function verification with real trait bound constraints — `trait_bounds_as_smt_assumptions` emits real Ord/PartialOrd SMT axioms via `DeclareSort+DeclareFun+Assert`; replaces `BoolLit(true)` no-ops (Phase 40)
4. MonomorphizationRegistry population — `populate_monomorphization_registry` traverses MIR call sites for concrete type substitutions (T→i32); shared `Arc` wiring activates `generate_vcs_monomorphized` production path (Phase 44)
5. Sealed trait detection + dyn dispatch VCs — `detect_sealed_trait` via HIR visibility, `parse_dyn_dispatch_callee` resolves `<dyn Trait>::method` to behavioral subtyping VCs, Z3 pessimistic catch-all (Phase 41)
6. Closure production wiring — `convert_closure_ty` emits `Ty::Closure` from real rustc MIR; `ByMutRef` capture detection enables Phase 39 prophecy machinery from real programs (Phase 42)

**Delivered:** Complete generics and trait verification — behavioral subtyping with Liskov checks, FnMut prophecy variables for mutable closure contracts, real trait bound SMT axioms for generic functions, monomorphized verification from call-site type analysis, sealed trait detection, and dyn dispatch call-site resolution. All verified end-to-end with Z3.

---

## v0.6 Cross-Crate Verification (Shipped: 2026-03-02)

**Phases completed:** 6 phases (34–37.1), 11 plans
**Tests:** 1,245+ passing (0 failures), including 53 new v0.6 tests
**Lines of code:** ~103,500 Rust (+10,284 / -335 from v0.5-audit)
**Timeline:** 3 days (2026-02-27 to 2026-03-02)
**Feature commits:** 53
**Requirements:** 7/7 (ALIAS-01/02, OPAQUE-01/02/03, XCREC-01/02) — all satisfied

**Key accomplishments:**
1. Cross-function pointer aliasing — `#[unsafe_requires(!alias(p,q))]` generates Z3 SAT VCs that catch aliased pointer arguments at call sites with typed counterexamples (Phase 34)
2. Opaque callee diagnostics V060/V061 — warning/error when verified function calls uncontracted callee; replaces silent skip at `vcgen.rs:2366`; severity escalation for unsafe context (Phase 35)
3. Summary contract inference — `#[verifier::infer_summary]` auto-generates minimal read/write contracts for opaque callees; inferred summaries visible in JSON output (Phase 36)
4. HIR-based alias precondition parsing — `parse_alias_preconditions()` in callbacks.rs closes the always-empty `alias_preconditions` gap; full driver→HIR→vcgen→Z3 pipeline verified by 4 E2E tests (Phase 36.1)
5. Cross-crate Tarjan SCC detection — `CallGraph::from_functions_with_cross_crate_db` extends Tarjan's algorithm across crate boundaries using exported symbol contracts; breaks "each crate is an island" barrier (Phase 37)
6. Cross-crate `#[decreases]` termination verification — cross-crate mutual recursion termination measures verified with Z3 UNSAT/SAT proof; `generate_termination_vcs` activated for cross-crate callees (Phase 37)
7. V062 InferredSummaryAlias guard — closes is_inferred + alias_preconditions co-occurrence gap; emits warning instead of silently dropping alias VCs (Phase 37.1)

**Delivered:** Broke the "each crate is an island" barrier — inter-procedural pointer aliasing, opaque callee contract enforcement, and cross-crate mutual recursion detection all verified end-to-end with Z3 proofs.

---

## v0.1 Formal Verification POC (Shipped: 2026-02-12)

**Phases completed:** 5 phases, 17 plans
**Tests:** 1,741 passing (0 failures)
**Lines of code:** 43,621 Rust across 53 source files
**Timeline:** 2 days (2026-02-10 to 2026-02-11)
**Feature commits:** 33

**Key accomplishments:**
1. Path-sensitive VCGen with soundness/completeness test suites (44 regression tests proving both soundness and completeness)
2. Loop invariant verification with classical 3-VC approach (initialization, preservation, sufficiency)
3. Modular inter-procedural verification with Rust ownership-aware contract summaries
4. Quantified specifications (forall/exists) with automatic trigger inference for SMT instantiation
5. Generic function verification via monomorphization with per-instantiation VCs
6. Production-quality cargo verify with incremental caching, parallel verification, and rustc-style error diagnostics

**Delivered:** Sound, automated formal verification tool for Rust with 37/37 requirements shipped -- from soundness foundations through performance optimization, covering control flow, loops, assertions, structs, inter-procedural verification, ownership reasoning, quantifiers, ghost code, prophecy variables, generics, caching, parallelism, and IDE-ready diagnostics.

---


## v0.2 Advanced Verification (Shipped: 2026-02-14)

**Phases completed:** 7 phases (6-12), 21 plans
**Tests:** 2,264 passing (0 failures), up from 1,741 in v0.1
**Lines of code:** 66,133 Rust across 77 source files (up from 43,621)
**Timeline:** 3 days (2026-02-12 to 2026-02-14)
**New LOC:** ~22,500 (+52% over v0.1)

**Key accomplishments:**
1. Recursive function verification with `#[decreases]` termination measures and Tarjan's SCC mutual recursion detection via petgraph
2. Closure verification via defunctionalization (Reynolds 1972) with Fn/FnMut/FnOnce support and explicit environment encoding
3. Trait object verification with behavioral subtyping (LSP), sealed trait closed-world analysis, and open-world uninterpreted encoding
4. Lifetime and borrow reasoning with NLL-based tracking, transitive outlives resolution, reborrow chain detection, and nested prophecy variables
5. Unsafe code detection with heap-as-array memory model, null/bounds checks, `#[verifier::trusted]` trust boundaries, and provenance tracking
6. IEEE 754 floating-point verification with SMT FPA theory, NaN propagation and infinity overflow VCs, and one-time performance warning
7. Bounded concurrency verification with happens-before encoding for all 5 C11 atomic orderings, data race freedom VCs, lock invariant verification, Tarjan's SCC deadlock detection, and channel safety

**Delivered:** Extended formal verification to cover all major Rust language features -- recursive functions, closures, trait objects, lifetimes, unsafe code, floating-point arithmetic, and concurrent programs. All 44/44 v0.2 requirements implemented with 523 new tests and comprehensive E2E validation.

---


## v0.3 Production Usability (Shipped: 2026-02-17)

**Phases completed:** 6 phases (13-18), 20 plans
**Tests:** 1,613 lib tests passing (0 failures), plus TypeScript VSCode extension tests
**Lines of code:** 82,642 Rust + TypeScript VSCode extension (~145 files changed)
**Timeline:** 3 days (2026-02-14 to 2026-02-17)
**New LOC:** ~16,500 Rust (+25% over v0.2) + VSCode extension (TypeScript)

**Key accomplishments:**
1. Standard library contracts (Phase 13) — Vec<T>, Option<T>, Result<T,E>, HashMap<K,V>, Iterator preloaded contracts with SMT Seq theory; proptest oracle validation; zero-config loading with `--no-stdlib-contracts` opt-out
2. Incremental verification with <1s re-verification (Phase 14) — dual-hash MIR+contract cache, transitive invalidation via reverse call graph, 20-30x speedup benchmark suite; `cargo verify clean` support
3. Manual trigger customization (Phase 15) — `#[trigger(expr)]` annotation with static self-instantiation detection, interpreted symbol warnings (V015-V018 diagnostics), manual triggers override auto-inference
4. VSCode extension with real-time feedback (Phase 16) — inline red squiggles for failures, "Verifying..." status bar, output panel with SMT-LIB viewer, gutter decorations, Z3 bundling, marketplace packaging
5. rust-analyzer integration (Phase 17) — `--message-format=json` rustc-compatible output, flycheck integration via `overrideCommand`, deduplication of rustc+rust-fv diagnostics, RA mode detection
6. bv2int optimization with differential testing (Phase 18) — `--bv2int`/`RUST_FV_BV2INT=1` activation, conservative arithmetic-only eligibility (rejects bitwise/shift), differential testing proves equivalence, `--bv2int-report` summary table with timing and slowdown warnings

**Delivered:** Made rust-fv production-ready — real Rust code verifiable via Vec/HashMap/Option/Result contracts, sub-second re-verification via incremental caching, VSCode/rust-analyzer IDE integration with inline diagnostics, manual trigger control for quantifier performance, and arithmetic solver optimization via bv2int. All 17/17 v0.3 requirements implemented.

---


## v0.4 Full Rust Verification (Shipped: 2026-02-23)

**Phases completed:** 9 phases (19-27), 27 plans
**Timeline:** 2026-02-17 to 2026-02-23

**Key accomplishments:**
1. Counterexample generation — typed Rust values (not SSA/hex), ariadne inline labels at failing source line, JSON structured output, VSCode IDE wiring (CEX-01..04)
2. Separation logic — `pts_to` predicate with AUFBV encoding, separating conjunction, frame rule, `#[ghost_predicate]` recursive heap predicates with depth-3 unfolding (SEP-01..04)
3. Weak memory models — full RC11 (mo/rf/co primitives), 8 canonical C11 litmus tests (CoRR/CoWW/SB/LB/MP/IRIW), Relaxed/Acquire/Release data race detection (WMM-01..04)
4. Higher-order closures — `fn_spec` specification entailments via AUFLIA, stateful `FnMut` SSA-versioned environment tracking (HOF-01..02)
5. Async/await verification — sequential polling model, `#[state_invariant]` at suspension points, async counterexample extraction with poll_iteration/await_side IDE rendering (ASY-01..02)
6. Gap closure phases: SEP-04 ghost predicate production wiring, VSCode counterexample v2 integration, WMM-03 race detection fix, async counterexample IDE fidelity

**Delivered:** Complete Rust verification coverage — every major language feature verifiable with typed counterexamples, heap separation reasoning, weak memory model checking, higher-order closure specs, and async/await state invariants.

---


## v0.5 SMT Completeness (Shipped: 2026-02-25)

**Phases completed:** 2 phases (28-29), 10 plans
**Timeline:** 2026-02-23 to 2026-02-24
**Files changed:** 37 files, +6,539 / -48 lines

**Key accomplishments:**
1. TDD scaffold — 10 failing tests covering VCGEN-01..04 + MIRCONV-01/02 + VCGEN-05/06 requirements
2. Numeric `as`-cast encoding (`encode_cast()`) — sign-extension, zero-extension, truncation, FPA theory for float casts with correct SMT bitvector semantics (VCGEN-03)
3. Match/if-let discriminant binding — `Rvalue::Discriminant` → uninterpreted selector term in SMT; all `match`/`if let`/`while let` constructs generate VCs (VCGEN-02)
4. Array bounds VCs + `Rvalue::Len` — auto-generated `MemorySafety` VCs with index bounds checks; length encoded as named `{arr}_len` SMT constant (VCGEN-01 partial)
5. Generic trait bound premises — `trait_bounds_as_smt_assumptions()` injects `Assert` premises in `generate_vcs_with_db`; `Ty::Generic` encodes as `Sort::Uninterpreted` (VCGEN-04)
6. CastKind preservation in MIR converter — exhaustive match for FloatToInt/IntToFloat/FloatToFloat/Pointer kinds; compiler-enforced completeness (MIRCONV-01)
7. Aggregate conversion — `AggregateKind::Adt/Closure` wired; `ir::Statement::SetDiscriminant/Assume` variants added (MIRCONV-02)
8. Float-to-int SMT soundness fix — `fp.to_sbv/fp.to_ubv RTZ` rounding replaces erroneous `Term::Extract` on Float sort (VCGEN-05)
9. Missing rvalue variants — `CopyForDeref`, `RawPtr`, `Repeat` added to MIR converter; `TyKind::Param` → `ir::Ty::Generic` (MIRCONV-01 complete)
10. Projected LHS functional record update — struct field mutation (`s.x = expr`) generates `(assert (= s (mk-Struct new_x (Struct-y s))))` SMT assertions (VCGEN-06)

**Known Gaps:**
- VCGEN-01 PARTIAL: `for`/iterator loops over slices/ranges, range expressions (`1..10`), and slice references (`&[T]`) not yet covered — deferred to v0.6
- `vcgen_06_set_discriminant_assertion` test ignored: `Statement::SetDiscriminant` VCGen encoding deferred

**Delivered:** Complete SMT VCGen coverage for all major Rust expression categories — casts, match/discriminants, array bounds, generics, float-to-int soundness, aggregate construction, and struct mutation functional updates. All 9 previously-failing tests green; 1 test deferred.

**UAT Validation (2026-02-25):** Phase 00 v0.4+v0.5 UAT — 22/22 test items passed covering phases 19-29: counterexample generation, separation logic, weak memory models, higher-order closures, async/await, cast encoding, discriminant binding, array bounds VCs, generic premises, aggregate wiring, float-to-int soundness, and functional record update.

---


## v0.5 Audit & Gap Closure (Shipped: 2026-02-27)

**Phases completed:** 9 phases (00, 29.1–29.4, 30, 31, 32, 33), 22 plans
**Tests:** All passing (0 failures)
**Timeline:** 2026-02-25 to 2026-02-27
**Feature commits:** 18

**Key accomplishments:**
1. For-loop Iterator Range VCGen — AUFLIA quantified VCs + QF_LIA bounded unrolling for `for x in 0..n` patterns; closes VCGEN-01 partial gap (Phase 29.1)
2. Prophecy encoding for mutable references — `*_1` in postconditions resolves to `_1_prophecy` via `convert_deref` postcondition awareness; `test_prophecy_basic` GREEN (Phase 29.2)
3. Borrow conflict detection — `generate_expiry_vcs()` stub replaced with statement-scanning implementation, emits `BorrowValidity` VC for use-after-expiry (Phase 29.3)
4. Stdlib doc tests fixed — 26 `` ```text `` blocks changed to `` ```rust,ignore `` in option.rs/vec.rs/result.rs; syntax highlighting restored, tests visible to harness (Phase 29.4)
5. SetDiscriminant VCGen — `ir::Statement::SetDiscriminant` emits discriminant assertion VCs; `vcgen_06_set_discriminant_assertion` un-ignored; closes VCGEN-06 fully (Phase 30)
6. Z3 bv2int + ghost locals fix — `uses_spec_int_types()` detects `as int`/`as nat` enabling QF_LIA path; `is_ghost_place()` guard prevents ghost variables leaking into executable VCs (Phase 31)
7. Retrospective verification docs — VERIFICATION.md created for 7 early phases (05, 06, 07, 08, 11, 13, 17) missing them; all PASS (Phase 32)
8. v0.1 tech debt fully closed — E2E performance benchmarks run, bv2int user docs created, pointer aliasing edge case tests added, trigger/quantifier edge cases tested, float VC placeholders replaced with `encode_operand()` (Phase 33)
9. v0.1 Milestone Audit passed — status: passed, 37/37 phases pass, 0 human_needed items (Phase 33-06)

**Delivered:** Closed all known v0.5 gaps and v0.1 audit items — for-loop VCGen, prophecy fix, borrow conflict detection, SetDiscriminant VCGen, Z3/ghost fixes, comprehensive verification documentation, and all tech debt resolved. v0.1 milestone audit formally closed.

---

