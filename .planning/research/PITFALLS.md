# Pitfalls Research: v0.4 Full Rust Verification Features

**Domain:** Adding counterexample generation, async/await verification, weak memory models, higher-order closure spec entailments, and separation logic to an existing SMT-based Rust formal verifier (rust-fv)
**Researched:** 2026-02-19
**Confidence:** HIGH (codebase analysis + academic literature + domain-specific pitfall investigation)

## Executive Summary

This research identifies pitfalls specific to **adding** five advanced verification capabilities to the existing rust-fv tool. The key risk profile differs from building from scratch: all five features must **coexist** with an established verification pipeline (VCGen, SSA encoding, Z3/CVC5/Yices backends, existing `Model`/`SolverResult` types). The primary failure modes are:

1. **Integration regressions**: New encoding axioms break previously-verifying programs
2. **Silent unsoundness**: Feature appears to work but produces false negatives
3. **Nightly MIR instability**: Async coroutine state machine structure changes under the tool
4. **Theory combination conflicts**: Separation logic heap predicates clash with existing `heap_model.rs` array encoding
5. **Counterexample mapping loss**: SMT model variables do not map back to user-visible Rust names

The five features have a dependency order that determines safe phase sequencing: counterexample generation first (unblocks meaningful error output for all other features), then separation logic (changes heap theory baseline), then weak memory (axiom additions to concurrency layer), then async (MIR extension), then closure spec entailments (highest SMT complexity).

---

## Critical Pitfalls

### Pitfall 1: Counterexample Variable Names Lost in SSA Encoding

**What goes wrong:**
The VCGen in `crates/analysis/src/vcgen.rs` generates SSA-style names for SMT variables (e.g., `_0`, `_1`, `_param_x_0`, `_param_x_1`). When Z3 returns `(get-model)` output, the `Model` struct in `crates/solver/src/model.rs` stores raw SMT names as `Vec<(String, String)>`. When counterexample generation maps these back to user code, there is no registry linking `_param_x_1` to the Rust variable `x` at source line 42 with value 5. The user sees `_param_x_1 = #x00000005` instead of `x = 5 (at line 42)`.

**Why it happens:**
- SSA variable names are generated for solver efficiency, not human readability
- The existing `VcLocation` struct tracks block/statement index but not local-variable-to-SMT-name mappings
- `Model::assignments` is populated by parsing solver stdout; no reverse lookup table is built during VCGen
- Multiple SSA versions of the same variable (`x_0`, `x_1`, `x_2`) exist but only the version visible at the failing assertion matters

**How to avoid:**
Build a **variable provenance map** during VCGen that records `(smt_name -> (rust_name, source_line, block_idx))` for every declaration emitted. Store this map alongside the `VerificationCondition`. During model extraction, use the map to translate before presenting to users. SSA subscripts should be stripped for display; only the final assignment version at the assertion point is relevant.

- Data structure: `HashMap<String, RustVarInfo>` where `RustVarInfo = { rust_name, source_line, is_param }` built in parallel with `Script` generation
- Model filtering: suppress internal VCGen bookkeeping variables (e.g., path-condition helpers, quantifier witnesses) from the displayed counterexample
- Type recovery: preserve the `Ty` of each variable so counterexample values can be formatted correctly (e.g., `#x0000002a` shown as `42i32`, not as hex)

**Warning signs:**
- Counterexample output contains only underscore-prefixed names (`_0`, `_1`)
- Hex bitvector literals appear in counterexample without type context
- The same Rust variable appears multiple times under different SMT names
- `Model::get("x")` returns `None` for user variable `x` even when the counterexample is valid

**Phase to address:**
**Counterexample Generation Phase** — the provenance map must be built from day one of the VCGen extension. Retrofitting it later requires re-auditing every `Command::DeclareFun` emission site in `vcgen.rs`.

---

### Pitfall 2: Silent `Sat(None)` — Model Requested but Not Returned

**What goes wrong:**
`SolverResult::Sat(Option<Model>)` allows `Sat(None)` — a satisfiable result with no model. The existing `solver.rs` calls `ensure_check_sat_and_get_model` which appends `(get-model)` to the script. However, several conditions cause solvers to return `sat` on stdout with no model text: (1) the solver's `model` option was disabled, (2) quantifier-heavy formulas cause Z3 to return `sat` after approximation without a concrete model, (3) CVC5 and Yices have different model output formats that the current `parse_model()` parser may not handle correctly. The counterexample generation code receives `Sat(None)`, silently skips displaying anything, and the user sees "verification failed" with no explanation of why.

**Why it happens:**
- `parse_model()` in `parser.rs` handles Z3 4.15+ format and one legacy format, but CVC5 uses a different model syntax
- Quantifier-free linear arithmetic can sometimes produce `sat` without a grounding model
- The `(set-option :produce-models true)` command may be missing from scripts generated for new features
- Yices model output does not use s-expression format at all

**How to avoid:**
- Assert in CI that for every `sat` result from test cases, a non-empty model is produced
- Add solver-specific model parsers for CVC5 and Yices model output formats
- Ensure `(set-option :produce-models true)` is included at the top of every generated script (not just appended `(get-model)` at the end)
- Treat `Sat(None)` as a bug, not a legitimate state, in counterexample-mode: emit a warning "Solver returned SAT but no model — check solver configuration"
- For quantifier-heavy VCs (separation logic, weak memory axioms), test model retrievability explicitly in unit tests

**Warning signs:**
- Counterexample reports say "violation found" but show no variable assignments
- `Model::is_empty()` is true on returned models
- CVC5 or Yices backend produces different results than Z3 for the same VC
- `(get-model)` produces warning text instead of s-expression model

**Phase to address:**
**Counterexample Generation Phase** — must be hardened before any downstream feature adds axioms that complicate model extraction.

---

### Pitfall 3: Async Coroutine MIR Shape Changes Break Driver

**What goes wrong:**
Rust async functions desugar to coroutine state machines in MIR. The rustc nightly compiler (required by `rust-toolchain.toml`) transforms async MIR with `rustc_mir_transform::coroutine`. The state machine has three hardcoded states (not-yet-resumed=0, returned=1, poisoned=2), followed by suspension-point states. The field layout stores upvars first, then coroutine state field, then locals live across suspension points. This layout is **not stable** between nightly versions — the pull request to run MIR opts before coroutine state transform (August 2025, rust-lang/rust #145330) is one example of ongoing restructuring. The `crates/driver/src/callbacks.rs` MIR extraction code will silently misparse the new layout, extracting wrong IR for async functions.

**Why it happens:**
- The async MIR shape is an implementation detail of the coroutine transformation pass, not a stable API
- Rust nightly pins in `rust-toolchain.toml` keep the compiler stable per build, but milestone boundaries cause toolchain updates
- Async functions produce `CoroutineKind::Desugared(CoroutineDesugaring::Async, _)` in MIR, distinguishable from `gen` (sync generators) and `async gen` (async generators) — these three kinds have different MIR structures
- `poll()` is the primary entry point but a `drop()` shim also exists; the verifier must handle both

**How to avoid:**
- Inspect actual coroutine MIR shapes with `RUSTFLAGS="-Zunpretty=mir"` on real async functions before implementing extraction
- Add a **shape invariant test** that runs during CI: extract the MIR of a known async function and assert expected state count, field count, and suspension point indices
- When the invariant test fails after a toolchain update, it surfaces immediately rather than silently producing wrong IR
- Verify the `CoroutineKind` discriminant to select the correct extraction path
- Handle suspension points (`Yield` terminators in MIR) as explicit blocking points in the IR
- Do NOT attempt to inline across suspension points — model each suspension as a predicate boundary

**Warning signs:**
- Async function verification returns spurious results after a nightly toolchain update
- State count extracted from async MIR does not match expected `2 + N_suspension_points`
- The driver fails to find `poll()` entry in coroutine MIR
- CI fails with `panicked at 'unexpected MIR terminator: Yield in non-coroutine context'`

**Phase to address:**
**Async/Await Verification Phase** — shape invariant test must be the very first artifact of this phase. Any toolchain update during the phase should re-run the test.

---

### Pitfall 4: Weak Memory Axiom Set Unsoundness (C11 Relaxed Violation)

**What goes wrong:**
The existing `happens_before.rs` encodes `Relaxed` ordering as `Term::BoolLit(true)` — correct for the atomicity guarantee but incomplete for soundness under weak memory. The IRIW (Independent Reads of Independent Writes) litmus test is the canonical example: two threads reading two stores may see them in opposite orders under `Relaxed`. Encoding this requires a **modification order** (mo) relation per location, a **reads-from** (rf) map, and **coherence** (co) axioms. Adding only partial axioms (e.g., only `rf` but not `mo` or `co`) produces a model where programs appear safe under the verifier but can exhibit behaviors the C11 model forbids or allows incorrectly. The existing `happens_before.rs` encodes `SeqCst` correctly but the intermediate orderings (`Release`, `Acquire`, `AcqRel`) are collapsed to the same axiom — this is **unsound for AcqRel** which requires both a release fence on store and an acquire fence on load in the same operation.

**Why it happens:**
- C11 weak memory model requires four relations: `hb`, `rf`, `mo`, `co` — only `hb` (via timestamps) and `rf` exist in current code
- The existing sequential-consistency approach works correctly but cannot be extended to weaker orderings by partial axiom addition
- Research literature shows that the standard Owicki-Gries proof method is **unsound** for weak memory models (Vafeiadis et al., CPP2015) — the verifier's current concurrency encoding inherits this limitation
- "Relaxed = no synchronization" is only correct at the atomicity level; at the memory model level, relaxed accesses are still constrained by `co` and `rf` coherence axioms

**How to avoid:**
- Implement the full **RC11 fragment** (relaxed/release-acquire without load-buffering cycles) which is decidable and has correct SMT axioms. See "Verifying C11-Style Weak Memory Libraries via Refinement" (arXiv:2108.06944)
- Add the `mo` (modification order) as a per-location total order on stores: `(declare-fun mo_x (Int Int) Bool)` plus transitivity + totality axioms
- Add `co` (coherence) axioms relating `rf` and `mo`
- Test against the IRIW, LB (Load Buffering), SB (Store Buffering), and MP (Message Passing) litmus tests as a soundness check suite
- Separate `Relaxed` (only atomicity, no synchronization) from `Release`/`Acquire` (synchronization via `rf`+`hb`) — these are distinct encoding cases, not the same formula

**Warning signs:**
- The IRIW litmus test verifies as safe when it should be flagged as potentially unsafe under `Relaxed`
- AcqRel stores and loads produce the same SMT encoding as separate Acquire and Release operations
- Adding weak memory axioms causes existing `SeqCst`-only verification tests to fail (axiom conflict)
- Solver returns `unsat` on a program known to have a weak memory bug (false negative)

**Phase to address:**
**Weak Memory Model Phase** — start with a litmus test suite (IRIW, SB, LB, MP, CoRR, CoRW, CoWR, CoWW) as the specification for correctness. All eight should be correctly classified before declaring the phase complete.

---

### Pitfall 5: Separation Logic Conflicts with Existing `heap_model.rs` Array Encoding

**What goes wrong:**
`crates/analysis/src/heap_model.rs` declares a byte-addressable heap as `(Array (_ BitVec 64) (_ BitVec 8))` plus `allocated`, `alloc_base`, and `alloc_size` uninterpreted functions. Separation logic requires a **heap domain** — a partial function from locations to values — plus a separating conjunction (`*`) that requires disjoint domains. If separation logic is encoded on top of the existing flat array model, the two heap representations will conflict: separation logic needs to reason about heap *ownership* (which part of the heap a specification owns), but the array model treats the heap as a single global mutable object. Naive addition of separation logic axioms on top of the array model will either (a) be vacuously true because the global array satisfies all ownership predicates, or (b) create contradictory axioms that make every VC unsatisfiable.

**Why it happens:**
- The heap-as-array model is optimized for unsafe pointer verification, not ownership reasoning
- Separation logic's foundational operator `P * Q` means "heap splits into two disjoint parts satisfying P and Q respectively" — this does not compose with a single global array constant
- Research shows that integrating separation logic with SMT requires either (a) reduction to first-order logic with array axioms (decidable fragment), or (b) a separate heap domain theory with disjointness predicates
- The existing `alloc_base`/`alloc_size` functions can serve as an *allocation table* for separation logic's *emp* predicate but need axiom extensions

**How to avoid:**
- Adopt the **Viper/Carbon encoding**: model the heap as `(Array Ref Field Value)` where `Ref` is an abstract location sort, rather than a raw byte array. This is compatible with ownership reasoning.
- Alternatively, use the **bitvector-set encoding** for permission sets: represent the heap domain as a bitvector of allocated locations, with separating conjunction as bitwise-AND disjointness check. This encodes entirely within the existing `BitVec` theory.
- Add a separate `permissions` uninterpreted function `(permissions : Ref -> Bool)` layered on top of the existing `allocated` predicate, where `P * Q` becomes `disjoint(perm_P, perm_Q) /\ P /\ Q`
- Run all existing unsafe-pointer tests after adding separation logic axioms — if any existing test breaks, there is a theory conflict

**Warning signs:**
- Existing unsafe pointer verification tests fail after separation logic axioms are added
- Separation logic VCs are trivially UNSAT (contradictory axioms)
- `emp * P` does not simplify to `P` in the solver
- The frame rule generates incorrect results: adding more resources to context changes whether an assertion holds

**Phase to address:**
**Separation Logic Phase** — must be the first of the five features to establish the new heap theory baseline. If done after other features, heap-touching code in async and weak memory may need retroactive fixes.

---

### Pitfall 6: Closure Spec Entailments Break Existing Defunctionalization

**What goes wrong:**
`crates/analysis/src/defunctionalize.rs` encodes closures as first-order functions with explicit environment parameters (Reynolds 1972 pattern). Spec entailments for closures require expressing "closure `f` satisfies spec `S`" which means: for all inputs `x` and environments `env`, if `pre_S(x, env)` then `post_S(f_impl(env, x), x, env)`. This is a **universally quantified assertion** about the defunctionalized function. Adding this quantifier on top of the existing datatype encoding for closure environments causes Z3 to enter quantifier instantiation mode, which (a) can fail to instantiate when the trigger pattern is insufficiently tight, and (b) conflicts with the existing behavioral subtyping check in `behavioral_subtyping.rs` which uses a different schema for trait-level contracts.

**Why it happens:**
- Defunctionalization produces `(define-fun f_impl (...))` — a ground term, not a universally quantified formula. Spec entailments require `(forall (env ClosureEnv_f) (x T) ...)` layered on top.
- The existing `behavioral_subtyping.rs` generates `SubtypingVc` with precondition weakening (`trait_requires => impl_requires`) and postcondition strengthening (`impl_ensures => trait_ensures`). Closure spec entailments are a third category (spec-parametric verification) that does not fit either existing category.
- FnOnce closures can only be called once — the spec entailment must assert the property over the single call without allowing the quantifier to instantiate over multiple calls
- FnMut closures mutate their environment — the spec entailment must track the mutation across calls, requiring mutable environment state in the SMT encoding

**How to avoid:**
- Introduce a third `SubtypingKind` variant: `ClosureSpecEntailment` with its own VC generation path
- For spec entailments, use **defunctionalized witnesses** rather than universal quantification: instead of `forall env x. spec_holds(f_impl(env, x))`, use the calling context as a witness: at each concrete call site, generate a VC that the specific `env` and `x` at that call satisfy the spec
- For FnOnce: enforce single-call semantics by tracking consumption in the SMT encoding (add `called_once_f: Bool` constant, assert `(not called_once_f)` before call, `(assert called_once_f)` after)
- For FnMut: model environment mutation by using SSA versioning on environment fields: `env_v0`, `env_v1`, etc., matching the pattern already used for regular variables in VCGen

**Warning signs:**
- Existing closure verification tests fail after spec entailment axioms are added
- FnOnce closures verify correctly when called once but do not detect double-call violations
- Spec entailment VCs for closures are always `unsat` regardless of closure body (over-constrained)
- `behavioral_subtyping.rs` tests break — the subtyping logic and entailment logic are mutually interfering

**Phase to address:**
**Higher-Order Closure Spec Entailment Phase** — must explicitly audit interactions with `defunctionalize.rs` and `behavioral_subtyping.rs`. The three systems (defunctionalization, behavioral subtyping, spec entailments) must have non-overlapping VC domains.

---

### Pitfall 7: Regression in Existing Verification from Axiom Addition

**What goes wrong:**
Each of the five new features adds axioms to the SMT context: separation logic adds heap ownership axioms, weak memory adds `mo`/`rf`/`co` axioms, closure spec entailments add universal quantifiers. When these axioms are global (added to every VC's context), they can make previously-trivial proofs fail. Example: a separation logic disjointness axiom `(forall (p q Ref) (=> (points-to p v) (points-to q w) (= p q) (= v w)))` is a reasonable heap axiom but causes Z3's quantifier engine to instantiate the axiom against unrelated integer variables if the trigger pattern is too broad.

**Why it happens:**
- Adding globally-scoped axioms is the easiest implementation path (add to every generated `Script`) but the most dangerous
- Quantifier triggers that are too broad match terms from unrelated verification conditions
- Axiomatic theories added for one feature become inadvertently active in VCs for unrelated features
- The existing VCGen does not have a mechanism to scope axioms to specific VC types

**How to avoid:**
- **Scope axioms to the feature**: Only include weak memory axioms in VCs that involve `AtomicOp` or `SyncOp`. Only include separation logic axioms in VCs involving heap access. Use the `VcKind` enum (already in `vcgen.rs`) to gate axiom inclusion.
- **Regression test suite**: Run the full existing test suite (all tests in `crates/analysis/tests/`) after adding each new feature's axioms. Any newly-failing test is an axiom regression, not a user error.
- **Differential testing**: For each function verified before v0.4, verify it again with v0.4 features enabled. Results should not change unless the feature explicitly applies.
- **Axiom minimal principle**: Add only the axioms strictly necessary for soundness. Every axiom must be justified by a litmus test or specification that would be unsound without it.

**Warning signs:**
- Existing e2e tests in `e2e_verification.rs` or `e2e_stdlib.rs` fail after adding new feature axioms
- `completeness_suite.rs` tests regress (correct programs now fail to verify)
- `soundness_suite.rs` tests regress (incorrect programs now pass verification)
- Solver returns `unknown` for VCs that previously returned `unsat` quickly (quantifier instantiation overhead)

**Phase to address:**
**Every Phase** — regression suite must run as the final check of each phase's implementation. Any regression must be fixed before merging, not deferred.

---

### Pitfall 8: Async State Machine Verification Loops on Infinite Futures

**What goes wrong:**
Async functions that never complete (infinite loops with `yield` / `select!`) produce coroutine MIR with back-edges. Naively unrolling the state machine for verification creates a non-terminating VCGen loop. The existing loop handling in rust-fv uses invariant-based verification (loop invariants required). Async state machines are structurally different from ordinary loops: a suspension point (`poll` returning `Pending`) is semantically a loop back-edge but appears in MIR as a `Yield` terminator followed by a re-entry block. Without loop invariants specifically for suspension points, the verifier either (a) unrolls indefinitely, or (b) gives up immediately with `unknown`.

**Why it happens:**
- Async state machines in MIR are not syntactically loops — they are state transitions. The loop structure is implicit in the state enum transitions.
- Existing loop verification in rust-fv uses `#[invariant(...)]` annotations on loop head blocks. Async functions have no explicit loop head — the entire coroutine body is a loop across all states.
- `Future::poll` is typically called inside a runtime executor loop that the verifier cannot see
- Combining async verification with weak memory (e.g., `tokio::sync::Mutex`) requires reasoning about both suspension points and memory ordering

**How to avoid:**
- For async functions with potential non-termination: require `#[async_invariant(...)]` annotations placed at suspension points (analogous to loop invariants at loop heads)
- Model `Poll::Pending` returns as "function may be called again from state N" and generate VCs for each state transition `(state_i, input_j) -> state_k`
- Bound the verification depth: verify safety properties hold for the first N resume cycles, then require an invariant proof for the inductive step
- Do NOT attempt to verify liveness properties (eventual completion) in the first async phase — focus only on safety properties (no panic, no data race per resume step)

**Warning signs:**
- VCGen enters an infinite loop on async functions without `Yield` terminator detection
- `cargo test` hangs indefinitely on async verification tests
- Memory usage grows unbounded during async function processing
- Every async function returns `unknown` (bounded unrolling depth exceeded immediately)

**Phase to address:**
**Async/Await Verification Phase** — must define the bounded verification strategy for infinite futures before any async function is accepted as input. The bound must be explicit and user-configurable.

---

## Technical Debt Patterns

| Shortcut | Immediate Benefit | Long-term Cost | When Acceptable |
|----------|-------------------|----------------|-----------------|
| **Skip provenance map in counterexamples** (show raw SMT names) | Faster to ship; existing `Model` struct already works | Users cannot interpret counterexamples; adoption fails; every counterexample requires SMT knowledge to read | Never — counterexamples without source mapping are unusable |
| **Global axiom inclusion** (add all new axioms to every VC) | One code path; simpler VcGen | Axioms pollute unrelated VCs; existing tests regress; quantifier instantiation overhead on every proof | MVP only, with regression tests passing as acceptance criteria |
| **SeqCst-only as proxy for weak memory** (skip Relaxed/AcqRel axioms) | Much simpler encoding; existing `happens_before.rs` handles SeqCst | Unsound for programs using `Relaxed` or `AcqRel` orderings; false negatives on real concurrent programs | Acceptable as Phase 1 of weak memory if documented as "SeqCst only, Relaxed/AcqRel unsupported" |
| **Elide FnMut environment mutation** (treat FnMut as Fn for spec entailments) | Avoids SSA-on-environment complexity | Incorrect specs for any FnMut closure that mutates captured variables; soundness bug | Never — FnMut mutation is semantically critical |
| **Reuse existing heap-as-array for separation logic** (no new heap domain) | No theory change; backward compatible | Separation logic predicates are vacuously satisfiable; ownership reasoning does not work | Never — defeats the purpose of separation logic |
| **Unbounded async unrolling** (unroll until solver timeout) | No user annotations required | VCGen hangs on infinite futures; solver timeouts for long coroutines; non-deterministic results | Never — must bound explicitly |

---

## Integration Gotchas

| Integration | Common Mistake | Correct Approach |
|-------------|----------------|------------------|
| **`Model` + counterexample display** | Displaying `Model::assignments` directly to the user | Build provenance map in VCGen; translate SMT names to Rust names before display; filter internal bookkeeping variables |
| **CVC5 / Yices model parsing** | Assuming Z3 s-expression model format for all backends | Implement separate model parsers per solver; CVC5 uses `(model ...)` wrapper with different syntax; Yices uses flat assignment format |
| **Separation logic + `heap_model.rs`** | Adding SL predicates on top of byte-array heap | Use distinct heap domain (abstract `Ref` sort) for SL; keep byte-array model for unsafe pointer VCs; do not combine in same VC |
| **Weak memory + existing `thread_encoding.rs`** | Adding `mo`/`rf` relations to the existing timestamp-based HB encoding | Timestamp-based HB and event-based `mo`/`rf`/`co` are different formalisms; do not mix; choose one formalism for weak memory and rebuild |
| **Async + existing concurrency VCs** | Running async functions through `thread_encoding.rs` interleaving enumeration | Async is sequential coroutine semantics, not parallel thread interleaving; requires distinct extraction path in driver |
| **Closure spec entailments + `behavioral_subtyping.rs`** | Generating spec entailment VCs via existing `SubtypingVc` infrastructure | Spec entailments are a different VC class; add `ClosureSpecEntailment` variant to `SubtypingKind` rather than reusing existing variants |
| **Nightly rustc for async MIR** | Assuming coroutine MIR structure is stable across `rust-toolchain.toml` updates | Add shape invariant test; run it on every toolchain update; fail loudly with explicit error rather than producing wrong IR silently |

---

## Performance Traps

| Trap | Symptoms | Prevention | When It Breaks |
|------|----------|------------|----------------|
| **Separation logic quantifier explosion** | VCs with SL predicates time out; Z3 instantiates disjointness axioms against all ground terms | Use bitvector-set encoding (no quantifiers) or trigger-restricted axioms; test on heap-heavy programs | Any heap operation with >10 distinct allocation sites |
| **Weak memory `mo`+`rf`+`co` Cartesian product** | SMT formula size is O(N^3) in number of atomic operations N | Bound number of atomic events per VC; use partial-order reduction to prune equivalent interleavings | >10 atomic operations per thread; more than 3 threads |
| **Async state explosion** | Coroutine with K suspension points generates K^N VCs for N resumes | Bound resume count; use invariant-based proof for inductive step instead of explicit unrolling | >5 suspension points; any `loop { ... .await }` pattern |
| **Closure spec entailment with large environments** | Defunctionalized environment datatype with 20+ fields causes quadratic SMT encoding | Limit captured variable count; use abstract closure contract (pre/post only, not full body) for large closures | Closures capturing >10 variables; closures inside loops |
| **Cross-feature axiom interaction** | Each feature adds 5-10 axioms; combined VCs have 40+ axioms causing instantiation fog | Gate axioms on `VcKind`; profile solver statistics (`-st` flag) on combined VCs | Any VC that spans two or more new v0.4 features simultaneously |

---

## "Looks Done But Isn't" Checklist

- [ ] **Counterexample generation:** Every failing VC displays Rust variable names (not SMT names) with source line numbers — verified by running existing `soundness_suite.rs` and confirming human-readable output
- [ ] **Counterexample generation:** Model output is non-empty for all three backends (Z3, CVC5, Yices) — verified by a backend-specific model parser test
- [ ] **Async verification:** MIR shape invariant test passes on current nightly toolchain — verified by inspecting extracted state count matches `2 + N_suspension_points`
- [ ] **Async verification:** Infinite `loop { .await }` does not hang VCGen — verified by timeout test
- [ ] **Weak memory:** All eight C11 litmus tests (IRIW, SB, LB, MP, CoRR, CoRW, CoWR, CoWW) are correctly classified — verified by litmus test suite
- [ ] **Weak memory:** Existing `concurrency_verification.rs` tests still pass — regression verified
- [ ] **Separation logic:** `emp * P = P` frame rule holds in solver — verified by unit test
- [ ] **Separation logic:** Existing `heap_model.rs` unsafe pointer tests still pass after SL axioms added — regression verified
- [ ] **Closure spec entailments:** FnMut environment mutation is tracked across calls — verified by test with accumulating captured variable
- [ ] **Closure spec entailments:** FnOnce double-call violation is detected — verified by negative test
- [ ] **All features:** Running `cargo test` with all v0.4 features enabled does not regress any v0.3 test — full regression verified before any milestone release

---

## Recovery Strategies

| Pitfall | Recovery Cost | Recovery Steps |
|---------|---------------|----------------|
| **Counterexample shows SMT names** | LOW | Add provenance map retroactively; audit all `Command::DeclareFun` emission sites; add mapping layer before display |
| **`Sat(None)` in production** | MEDIUM | Emit explicit warning; add `(set-option :produce-models true)` to all scripts; implement solver-specific model parsers for CVC5/Yices |
| **Async MIR shape breaks after toolchain update** | MEDIUM | Shape invariant test surfaces the break immediately; fix extraction code for new MIR layout; pin toolchain version in CI until fixed |
| **Weak memory axiom set unsound** | HIGH | Disable weak memory feature flag; add litmus test suite to document correct behavior; rewrite axiom set against RC11 specification |
| **Separation logic conflicts with heap model** | HIGH | Isolate SL VCs from unsafe pointer VCs at `VcKind` level; implement separate heap domain; run regression suite |
| **Closure spec entailment breaks defunctionalization** | MEDIUM | Add `ClosureSpecEntailment` VC kind; generate entailment VCs in separate pass from defunctionalization; fix interaction test |
| **Global axiom regression** | MEDIUM | Gate axioms on `VcKind`; run regression suite to confirm fix; add axiom-scoping unit tests |
| **Async VCGen infinite loop** | HIGH | Add depth-limited recursion guard to coroutine state traversal; emit `unknown` at depth limit; require `#[async_invariant]` for unbounded futures |

---

## Pitfall-to-Phase Mapping

| Pitfall | Prevention Phase | Verification |
|---------|------------------|--------------|
| SSA variable names lost in counterexample | Counterexample Generation | Provenance map built; all failing VC outputs display Rust names |
| Silent `Sat(None)` with no model | Counterexample Generation | Backend-specific model parser tests pass for Z3, CVC5, Yices |
| Async coroutine MIR shape change | Async/Await Verification | MIR shape invariant test passes on current toolchain |
| Async infinite future VCGen hang | Async/Await Verification | Timeout test verifies bounded unrolling; `#[async_invariant]` required for loops |
| Weak memory axiom unsoundness | Weak Memory Model | All 8 C11 litmus tests correctly classified |
| Weak memory regression in SeqCst tests | Weak Memory Model | All existing `concurrency_verification.rs` tests still pass |
| Separation logic heap model conflict | Separation Logic | Frame rule test passes; unsafe pointer tests still pass |
| Closure spec entailment breaks defunctionalization | Higher-Order Closure Spec Entailments | FnMut mutation tracked; FnOnce double-call detected; `behavioral_subtyping.rs` tests unaffected |
| Global axiom regression | Every Phase | Full `cargo test` regression suite passes after each phase |

---

## Sources

**Counterexample Generation:**
- [SMT Models for Verification Debugging — Cédric Stoll, ETH Zürich (2019)](https://ethz.ch/content/dam/ethz/special-interest/infk/chair-program-method/pm/documents/Education/Theses/Cedric_Stoll_MA_report.pdf)
- [Z3 get-model returns not all variables — GitHub Issue #2502](https://github.com/Z3Prover/z3/issues/2502)
- [Programming Z3 — Nikolaj Bjørner, Stanford](https://theory.stanford.edu/~nikolaj/programmingz3.html)

**Async/Await MIR Coroutines:**
- [rustc_mir_transform::coroutine — nightly rustc docs](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_mir_transform/coroutine/index.html)
- [Run MIR opts before coroutine state transform — rust-lang/rust #145330 (2025)](https://github.com/rust-lang/rust/pull/145330)
- [Async function generates potentially panicking code — rust-lang/rust #147041](https://github.com/rust-lang/rust/issues/147041)
- [a-mir-formality — formal model of Rust MIR including async](https://github.com/rust-lang/a-mir-formality)

**Weak Memory Models:**
- [Verifying C11-Style Weak Memory Libraries via Refinement (arXiv:2108.06944)](https://arxiv.org/pdf/2108.06944)
- [Formal Reasoning about the C11 Weak Memory Model — Vafeiadis (CPP2015)](https://people.mpi-sws.org/~viktor/papers/cpp2015-invited.pdf)
- [Common Compiler Optimisations are Invalid in the C11 Memory Model — POPL 2015](https://plv.mpi-sws.org/c11comp/popl15.pdf)
- [Automating Deductive Verification for Weak-Memory Programs — Summers & Mueller (2018)](https://www.cs.ubc.ca/~alexsumm/papers/SummersMueller18.pdf)
- [Robustness against the C/C++11 Memory Model — ISSTA 2024](https://www.cs.tau.ac.il/research/roy.margalit/papers/issta24.pdf)

**Separation Logic + SMT:**
- [Automating Separation Logic Using SMT — Piskac, Wies, Zufferey (CAV 2013)](https://cs.nyu.edu/~wies/publ/tr_automating_separation_logic_using_smt.pdf)
- [Verification Algorithms for Automated Separation Logic Verifiers (arXiv:2405.10661)](https://arxiv.org/html/2405.10661v1)
- [Encoding Separation Logic in SMT-LIB v2.5 — SL-COMP](https://sl-comp.github.io/docs/smtlib-sl.pdf)
- [Formal Foundations for Translational Separation Logic Verifiers (arXiv:2407.20002)](https://arxiv.org/html/2407.20002)

**Higher-Order Closures and Spec Entailments:**
- [Compiling Higher-Order Specifications to SMT Solvers — Atkey](https://bentnib.org/hospec-smt.pdf)
- [Modular Specification and Verification of Delegation with SMT Solvers — ResearchGate](https://www.researchgate.net/publication/265073132_Modular_Specification_and_Verification_of_Delegation_with_SMT_Solvers)
- [Behavioral Subtyping, Specification Inheritance, and Modular Reasoning — ACM TOPLAS](https://dl.acm.org/doi/10.1145/2766446)

**Axiom Integration and Regression Prevention:**
- [Evaluating Soundness of a Gradual Verifier with Property Based Testing — POPL SRC 2023](https://popl23.sigplan.org/details/POPL-2023-student-research-competition/13/Evaluating-Soundness-of-a-Gradual-Verifier-with-Property-Based-Testing)
- [Identifying Overly Restrictive Matching Patterns in SMT-based Program Verifiers — ACM](https://dl.acm.org/doi/10.1145/3571748)
- [The Axiom Profiler — Becker et al., TACAS 2019](https://link.springer.com/chapter/10.1007/978-3-030-17462-0_6)

---

*Pitfalls research for: rust-fv v0.4 Full Rust Verification Features*
*Researched: 2026-02-19*
*Confidence: HIGH (codebase analysis of actual implementation + academic literature on each domain)*
