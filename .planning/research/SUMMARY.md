# Project Research Summary

**Project:** rust-fv v0.4 Full Rust Verification
**Domain:** SMT-based formal verification compiler plugin for Rust — advanced language features
**Researched:** 2026-02-19
**Confidence:** HIGH (codebase analysis + official docs + academic literature)

## Executive Summary

rust-fv v0.4 extends an existing, production-quality SMT-based Rust verifier (v0.3 baseline) with five advanced verification capabilities: counterexample generation, separation logic for heap reasoning, weak memory model (Relaxed/Acquire/Release atomics), higher-order closures with specification entailments, and async/await functional verification. The architecture is already well-designed for extension: all five features land exclusively in the `crates/analysis` layer, with zero new external crates required and zero changes to `crates/smtlib` or `crates/solver`. The existing SMT-LIB2 term vocabulary (Forall, Select, Store, App, Implies) is sufficient for all five encodings.

The recommended implementation approach treats each feature as an additive analysis-layer module with a well-defined integration point into `vcgen.rs`. Critically, each feature must scope its axioms to the relevant `VcKind` rather than injecting globally — global axiom pollution is the single most likely cause of regressions in an existing verification test suite. The separator between doable-v0.4 and deferred work is clear from research: magic wands, SeqCst memory fences as distinct from SeqCst stores, multi-threaded async, recursive SL predicates with full induction, and concurrent async verification are all explicitly out of scope.

The key risks in descending severity are: (1) separation logic conflicting with the existing `heap_model.rs` byte-array encoding — this requires establishing a new heap domain theory baseline before any other heap-touching features; (2) async coroutine MIR instability across nightly toolchain updates — requires a MIR shape invariant test as the first artifact of the async phase; (3) weak memory axiom unsoundness — requires validation against the 8 canonical C11 litmus tests (IRIW, SB, LB, MP, CoRR, CoRW, CoWR, CoWW) before declaring the weak memory phase complete. These risks directly determine phase ordering.

## Key Findings

### Recommended Stack

All v0.4 features require **zero new crates**. The existing infrastructure is sufficient: `z3` 0.19 for model extraction, `petgraph` 0.8 (already in `crates/analysis`) for happens-before graphs, `ariadne` (already in `crates/diagnostics`) for counterexample rendering, and `syn`/`quote` 2.x (already in `crates/macros`) for new proc macro attributes. The SMT theory map shows all five features are expressible in Z3/CVC5/Yices using existing LIA + Arrays + UF + quantifiers. One routing constraint: closure spec entailments use heavy universal quantification — Z3's MBQI handles this best, so the solver backend should prefer Z3 for `#[fn_spec]`-annotated HOF queries.

**Core technologies leveraged (all existing):**

- `z3` 0.19 (`Model::eval`, `get_const_interp`): counterexample extraction from SAT models
- `crates/smtlib` (`Term::Forall`, `Term::Select`, `Term::Store`, `Term::App`): sufficient for all five encodings without new variants
- `crates/analysis/concurrency/happens_before.rs`: existing skeleton for weak memory extension
- `crates/analysis/heap_model.rs`: existing heap-as-array baseline that separation logic extends with a new domain layer, not an in-place replacement
- `crates/analysis/defunctionalize.rs`: existing closure encoding that spec entailments build on
- `petgraph` 0.8: event graph construction for weak memory model

**Version constraints:**

- Rust nightly required (already the case) — async coroutine MIR uses `CoroutineKind::Desugared` which is nightly-only
- Z3 4.13+: `Model::eval` and `get_const_interp` APIs verified in `z3` 0.19.8
- SMT-LIB2 QF_ALIA: all three backends support the array + linear arithmetic theories used by all five features

### Expected Features

**Must have (table stakes — v0.4 is incomplete without these):**

- **Counterexample generation** — every mature verifier (Dafny, Kani, Why3) shows concrete variable values on failure; without this, debugging any v0.4 failure is blind; must be built first
- **Higher-order closure spec entailments** — closures were defunctionalized in v0.2 but HOF contracts are currently vacuously true or unprovable without spec entailment (`|=` syntax); completes the closure story

**Should have (competitive differentiators):**

- **Async/await verification (sequential polling model)** — no existing tool fully verifies async Rust functionally (Kani: "await: No"; Verus: draft PR not merged); first-mover advantage is significant
- **Weak memory model (Relaxed/Acquire/Release)** — needed to verify `Arc<T>`, `Mutex<T>`, `RwLock<T>`; SeqCst-only (v0.3) cannot reason about Acq/Rel synchronization patterns
- **Separation logic: `pts_to` + separating conjunction** — needed for custom allocators, linked lists, raw pointer contracts; existing heap-as-array model cannot prove aliasing freedom

**Defer to v0.5+:**

- Multi-threaded async (async + weak memory combined) — current research frontier, no practical tool exists
- Magic wands in separation logic — complex encoding, rarely needed, no tooling precedent in automated SMT
- SeqCst memory fences as distinct from SeqCst stores — vanishingly rare in real Rust code
- Recursive SL predicates with full induction — bounded unrolling to depth 3 covers practical cases
- Async liveness properties / termination — requires temporal logic or ranking functions, out of SMT scope
- Closure contract inference — undecidable in general; require explicit `#[fn_spec]` annotations

### Architecture Approach

All five features are analysis-layer additions with a uniform integration pattern: new module in `crates/analysis/src/`, new `VcKind` variants for precise diagnostic classification, and a dispatch call in `vcgen.rs` gated on the presence of the relevant IR nodes. The `crates/smtlib` and `crates/solver` crates require no changes because the existing `Term` AST (Forall, Exists, Implies, And, Or, Select, Store, App, Annotated) covers all encoding needs, and `SolverResult::Sat(Option<Model>)` already carries counterexample data. The driver crate changes only for features that require new MIR detection (async coroutine structure, counterexample variable name mapping).

**Major components (new in v0.4):**

1. `analysis/src/counterexample.rs` — `CounterexampleRenderer`: maps SMT variable names to Rust source names via provenance map built during VCGen; renders typed values via `ariadne` spans
2. `analysis/src/separation_logic.rs` — `SepLogicEncoder` + `FootprintAnalyzer`: shallow SL embedding over a distinct heap domain; `pts_to`, separating conjunction, frame rule; does not reuse the byte-array model
3. `analysis/src/concurrency/weak_memory.rs` — `WeakMemoryModel` encoding: C11 coherence axioms, modification order (`mo`), reads-from (`rf`), coherence (`co`) per location; extends `happens_before.rs`, does not replace it
4. `analysis/src/closure_spec.rs` — `ClosureSpecEncoder`: spec entailment as universally-quantified axiom over defunctionalized closure; `fn_spec(f, |y| pre => post)` syntax; new `ClosureSpecEntailment` VcKind
5. `analysis/src/async_encoding.rs` — `CoroutineFlattener`: detects coroutine MIR in driver, splits into `CoroutineState` segments at `Yield` terminators, generates per-state and cross-state invariant VCs

**Key architectural constraints:**

- Coroutine detection happens in `driver/src/mir_converter.rs` (uses rustc APIs); `analysis` only sees stable `CoroutineInfo` IR — never let rustc-internal types leak into the analysis crate
- Counterexample rendering belongs in `analysis/src/counterexample.rs` (has access to `ir::Function` variable names), not in `solver/src/model.rs` (pure SMT interface)
- Separation logic uses a distinct heap domain (abstract `Ref` sort or permission bitvector), not the existing byte-array model — the two coexist at different `VcKind` levels
- All new axioms must be scoped to the relevant `VcKind` — global axiom injection is an explicit anti-pattern that causes regression failures

### Critical Pitfalls

1. **Counterexample variable names lost in SSA encoding** — VCGen generates SSA names (`_param_x_1`); user sees `_param_x_1 = #x00000005` instead of `x = 5`. Avoid by building a `VarNameMap: HashMap<SmtName, RustVarInfo>` during VCGen from MIR `LocalDecls` source info; pass alongside the `VerificationCondition`; translate before display.

2. **Silent `Sat(None)` — model requested but not returned** — Z3, CVC5, and Yices have different model output formats; quantifier-heavy formulas sometimes yield `sat` without a grounding model. Avoid by treating `Sat(None)` as a bug in counterexample mode; adding solver-specific model parsers; asserting in CI that every `sat` result from test cases produces a non-empty model.

3. **Separation logic conflicts with existing `heap_model.rs` array encoding** — the byte-array heap model and SL's ownership-domain heap are incompatible theories; naive SL axioms on top of the array model either trivialize ownership or create contradictory UNSAT contexts. Avoid by using a distinct heap domain (Viper/Carbon `Ref` sort + permission sets) layered separately; run all existing unsafe pointer tests as a regression gate.

4. **Async coroutine MIR shape instability** — coroutine state machine layout is an implementation detail of `rustc_mir_transform::coroutine`, not a stable API; nightly toolchain updates silently misparse the new layout. Avoid by adding a MIR shape invariant test as the first artifact of the async phase; fail loudly rather than producing wrong IR silently.

5. **Weak memory axiom set unsoundness** — encoding only `hb` and `rf` without `mo` (modification order) and `co` (coherence) produces false negatives; the existing `Relaxed = BoolLit(true)` is sound for atomicity but unsound for memory model reasoning. Avoid by implementing the full RC11 fragment; validating against the 8 canonical C11 litmus tests before declaring the weak memory phase complete.

6. **Global axiom regression** — each feature adds 5-10 axioms; global inclusion (easiest implementation path) pollutes unrelated VCs and regresses existing proofs. Avoid by gating every new axiom on the relevant `VcKind`; running the full regression suite after each phase.

## Implications for Roadmap

Based on combined research findings, a 5-phase structure is recommended. **The key build-order conflict between research files has been resolved** (see conflict resolution table below). Counterexample generation is unanimously Phase 1. The remaining order is determined by the structural heap-theory dependency and toolchain fragility risk.

### Phase 1: Counterexample Generation

**Rationale:** Unanimous across all four research documents. All other v0.4 features produce complex verification failures. Without human-readable counterexamples (Rust variable names, typed values, source spans), developers cannot debug why any subsequent proof fails. This is the force multiplier for the entire milestone. Low risk, medium effort — the SMT infrastructure already returns models; the work is mechanical mapping and rendering.

**Delivers:** Every VC failure displays Rust variable names (not SSA names), typed values (not hex bitvectors), and source line numbers via `ariadne` inline labels; JSON output includes structured `counterexample` field; VSCode extension shows counterexample inline under the failing line.

**Addresses:** Counterexample generation feature; competitor gap vs Kani (byte-vector format) and Verus/Prusti (no CE).

**Avoids:** SSA name loss pitfall (Pitfall 1), Silent Sat(None) pitfall (Pitfall 2).

**Key implementation constraint:** Provenance map (`VarNameMap`) must be built from day one of the VCGen extension; retrofitting later requires re-auditing every `Command::DeclareFun` emission site in `vcgen.rs`. CVC5/Yices model parsers must be implemented alongside Z3.

### Phase 2: Separation Logic for Heap Reasoning

**Rationale:** This is the critical ordering decision that resolves the conflict between research files. PITFALLS (Pitfall 5) provides the definitive structural argument: separation logic "must be the first of the five features to establish the new heap theory baseline. If done after other features, heap-touching code in async and weak memory may need retroactive fixes." Async verification of `async fn` bodies that manipulate heap and weak memory verification of concurrent data structures both benefit from the SL heap domain being established first. Building SL last (as ARCHITECTURE and FEATURES suggest) optimizes for per-feature complexity but ignores the cross-feature heap domain dependency, resulting in higher total retrofit cost.

**Delivers:** `pts_to(p, v)` ownership predicate in spec language; separating conjunction (`*`) in `#[requires]`/`#[ensures]`; frame rule encoding; `#[ghost_predicate]` for user-defined recursive predicates (bounded unfolding depth 3); `SepConj` and `PointsTo` as IR-level `HeapPred` variants; `SepLogicEncoder` + `FootprintAnalyzer` modules.

**Addresses:** Separation logic feature; unsafe raw pointer contract verification; aliasing freedom proofs for linked lists and custom allocators.

**Avoids:** Heap model conflict pitfall (Pitfall 5); retroactive heap-model fixes in async and weak memory phases.

**Uses:** Existing `heap_model.rs` (`heap`, `allocated`, `alloc_base`, `alloc_size`), `Term::Forall`, `Term::Select`, `Term::Store`; no new crates.

**Key implementation constraint:** Do not encode SL predicates on top of the byte-array heap — use a distinct domain. No magic wands in v0.4. Run all existing `heap_model.rs` unsafe pointer tests as regression gate after adding SL axioms.

### Phase 3: Weak Memory Models (Relaxed/Acquire/Release)

**Rationale:** Builds on the existing `happens_before.rs` concurrency infrastructure — `AtomicOrdering` enum and `encode_atomic_ordering` function already exist. With separation logic's heap domain established in Phase 2, the weak memory phase can safely add memory-model axioms without retroactive heap changes. This is additive to the existing concurrency layer — the existing SeqCst encoding remains correct and is not replaced.

**Delivers:** C11 coherence axioms (`mo`, `rf`, `co` per-location); `Relaxed`, `Acquire`, `Release`, `AcqRel` correctly encoded (not collapsed to `BoolLit(true)` or timestamp-based HB); `WeakMemoryModel` enum in `ConcurrencyConfig`; new `weak_memory.rs` module; litmus test suite (8 canonical tests: IRIW, SB, LB, MP, CoRR, CoRW, CoWR, CoWW) as soundness specification.

**Addresses:** Weak memory model feature; `Arc<T>`, `Mutex<T>`, `RwLock<T>` verification; data race detection under weak ordering.

**Avoids:** Axiom unsoundness pitfall (Pitfall 4) — validated by litmus test suite; SeqCst regression pitfall (Pitfall 7).

**Key implementation constraint:** Do not mix timestamp-based HB encoding with event-based `mo`/`rf`/`co` formalisms. SeqCst must remain a special case of the new model. Scope axioms to `VcKind::WeakMemory*` variants only. `AcqRel` is not equivalent to `Release ∨ Acquire` — it requires both fence semantics simultaneously.

### Phase 4: Higher-Order Closures with Specification Entailments

**Rationale:** Builds directly on the existing `defunctionalize.rs` (v0.2) and `trigger customization` (v0.3) infrastructure. With counterexamples available (Phase 1), failed entailment VCs are debuggable. The spec entailment pattern uses heavy universal quantification — Z3's MBQI is tested and available. Positioned before async because the closure-capture-across-boundary pattern established here directly informs async's `persistent_fields` encoding across suspension points.

**Delivers:** `fn_spec(f, |y| pre => post)` spec expression; `#[fn_spec]` proc macro attribute; `ClosureSpec` IR type; `closure_spec.rs` module with `ClosureSpecEncoder`; `ClosureSpecEntailment` VcKind; correct FnOnce (single-call enforcement) and FnMut (SSA-versioned environment mutation) handling; Z3 MBQI routing preference for entailment queries.

**Addresses:** Higher-order closure spec entailment feature; HOF contracts (currently vacuously true); stdlib `Iterator::map`/`filter` verified closure composition.

**Avoids:** Defunctionalization breakage pitfall (Pitfall 6) — by introducing `ClosureSpecEntailment` as a distinct VcKind separate from `SubtypingVc`.

**Key implementation constraint:** FnMut environment mutation must use SSA versioning (`env_v0 → env_v1`), not a mutable environment variable. FnOnce must track consumption (`called_once_f: Bool`). Audit `behavioral_subtyping.rs` for interaction — spec entailments are a third VC category, not a subtype of existing subtyping VCs.

### Phase 5: Async/Await Verification

**Rationale:** Saved for last because it has the highest combination of risks: (1) nightly MIR instability — the coroutine state machine layout is not stable across toolchain updates; (2) highest implementation complexity — requires new MIR detection in driver, new `CoroutineInfo` IR, new VCGen dispatch path; (3) dependency on all prior features — benefits from counterexamples (Phase 1) for debugging state machine failures, from sep logic (Phase 2) for async functions that manipulate heap, and from closure patterns (Phase 4) for captured-variable reasoning across suspension points. Being last also means the async phase encounters a fully-hardened verification pipeline with working regression suites.

**Delivers:** Async fn functional verification under sequential polling model (single-threaded executor, no Tokio scheduler modeling); `CoroutineInfo` + `CoroutineState` IR types; `async_encoding.rs` `CoroutineFlattener`; `#[async_requires]`, `#[async_ensures]`, `#[state_invariant]` proc macro attributes; MIR shape invariant CI test; bounded unrolling (configurable, default 3 iterations) for infinite futures.

**Addresses:** Async/await verification feature; first SMT-based Rust verifier with async functional verification; competitor gap vs Kani ("await: No"), Verus (draft PR not merged), Prusti (no support).

**Avoids:** Async MIR instability pitfall (Pitfall 3) — shape invariant test; infinite future VCGen hang pitfall (Pitfall 8) — bounded unrolling + `#[async_invariant]` required for `loop { .await }` patterns.

**Key implementation constraint:** Coroutine detection must happen in `driver/src/mir_converter.rs` only — never let rustc-internal types leak into `crates/analysis`. Do not model Tokio/async-std executor. Do not attempt liveness properties. Async closures (Rust 2024 edition) are deferred.

### Phase Ordering Rationale (Build Order Conflict Resolution)

Four research documents proposed two conflicting build orders after the unanimously-agreed Phase 1:

| Source | Proposed Order (after Counterexample) |
|--------|--------------------------------------|
| ARCHITECTURE.md | Closures → Async → Weak Memory → Sep Logic |
| FEATURES.md | Closures → Async → Weak Memory → Sep Logic |
| STACK.md | Sep Logic → Weak Memory → Async → Closures |
| PITFALLS.md | Sep Logic → Weak Memory → Async → Closures |

**Resolved order: Sep Logic → Weak Memory → Closures → Async**

The resolution logic:

- **Sep Logic must come before Async and Weak Memory** (PITFALLS decisive): The separation logic heap domain is a theory baseline, not an isolated feature. Async functions that manipulate heap and weak-memory concurrent data structures will touch the heap domain. Building SL last requires retroactive changes to already-built encodings — a higher total cost. PITFALLS identifies this as "critical risk." ARCHITECTURE and FEATURES recommendations (SL last) optimize single-feature complexity but ignore cross-feature heap dependencies.

- **Closures moved before Async** (ARCHITECTURE argument retained, STACK overridden): Async state machines have closure-like capture semantics (persistent fields across suspension points). The closure spec entailment encoding patterns established in Phase 4 transfer directly to async's `persistent_fields` encoding. However, Async has higher toolchain fragility risk than Closures, so placing Async last (vs STACK's Async before Closures) reduces the risk of other features depending on an unstable async pathway.

- **Async is last** (risk-based): Highest toolchain fragility (nightly MIR instability), highest implementation complexity, highest benefit from all prior features being stable.

### Research Flags

**Phases requiring `/gsd:research-phase` during planning:**

- **Phase 2 (Sep Logic):** Heap domain choice (Viper/Carbon `Ref` sort vs bitvector-set permissions) needs prototype validation. The exact boundary between the new SL heap domain and the existing byte-array model (`heap_model.rs`) must be specified before implementation — this decision propagates to all subsequent heap-touching phases.
- **Phase 3 (Weak Memory):** RC11 axiom set completeness needs derivation from the specification paper (arXiv:2108.06944) before implementation. Specifically: the correct SMT encoding of `AcqRel` (which is not `Release ∨ Acquire`) and the full `mo`/`rf`/`co` coherence axiom set must be established before writing encoding code.
- **Phase 5 (Async):** MIR shape validation required on current nightly toolchain before implementation starts. Run `RUSTFLAGS="-Zunpretty=mir"` on representative async functions; document the exact state machine structure, field layout, and state count formula before writing a single line of extraction code.

**Phases with standard patterns (skip `/gsd:research-phase`):**

- **Phase 1 (Counterexample):** Z3 `get-model` is thoroughly documented; ariadne integration is established; variable provenance mapping is a well-understood compiler engineering pattern. Implement directly.
- **Phase 4 (Closures):** Wolff et al. OOPSLA 2021 and Prusti's `|=` implementation are direct, complete reference implementations. The defunctionalization infrastructure already exists. Implement with the papers as specification.

## Confidence Assessment

| Area | Confidence | Notes |
|------|------------|-------|
| Stack | HIGH | Zero new crates confirmed; all SMT theories verified against official Z3/CVC5 docs; z3 0.19.8 API verified against crate docs |
| Features | MEDIUM-HIGH | All 5 features have reference implementations in academic literature or competitor tools; async has no merged production reference (Verus PR not merged) — slight uncertainty on async edge cases |
| Architecture | HIGH | Based on direct codebase analysis of all 5 crates; component boundaries confirmed; integration points verified against actual code |
| Pitfalls | HIGH | Pitfalls derived from codebase analysis of actual implementation + academic literature on each domain; C11 litmus test validation approach is well-established |

**Overall confidence:** HIGH

### Gaps to Address

- **CVC5/Yices model parsing for counterexamples (Phase 1):** The existing `parser.rs` handles Z3 only. CVC5 uses a different model syntax; Yices uses flat assignment format (not s-expression). One source flags the CVC5 format difference as LOW confidence — needs direct CVC5 testing to confirm the exact format before implementing the Phase 1 CVC5 model parser.

- **RC11 axiom completeness for AcqRel (Phase 3):** The existing `happens_before.rs` collapses `AcqRel` to the same axiom as separate `Acquire` + `Release` — this is potentially unsound. The RC11 specification paper must be used as ground truth for Phase 3 axiom derivation; do not reconstruct from first principles.

- **Async coroutine MIR shape on current toolchain (Phase 5):** PR #145330 (August 2025) restructured when MIR opts run relative to the coroutine state transform. The coroutine field layout documented in the research may have changed. Must be validated with `RUSTFLAGS="-Zunpretty=mir"` on the current `rust-toolchain.toml` nightly version before Phase 5 implementation begins.

- **Sep logic heap domain boundary (Phase 2):** The research recommends a distinct heap domain for sep logic (not the byte-array model) but leaves the exact encoding (Viper-style `Ref` sort vs bitvector-set permissions) as a design decision. This must be resolved in Phase 2 planning with a prototype, because it determines all downstream heap-predicate encoding.

- **FnMut spec entailments with stateful closures (Phase 4):** Research acknowledges FnMut entailments requiring mutable environment tracking across calls are the hardest case. A concrete encoding example (SSA-versioned `env_v0 → env_v1` across calls) should be prototyped early in Phase 4 before committing to the full implementation.

## Sources

### Primary (HIGH confidence — official docs + codebase)

- `crates/analysis/src/ir.rs` — confirmed IR fields: `AtomicOrdering`, `ClosureInfo`, `UnsafeOperation`, `ConcurrencyConfig`
- `crates/solver/src/result.rs` — confirmed `SolverResult::Sat(Option<Model>)` + `Model::assignments`
- `crates/analysis/src/concurrency/happens_before.rs` — confirmed `encode_atomic_ordering()` with `Relaxed = BoolLit(true)` current limitation
- `crates/analysis/src/heap_model.rs` — confirmed byte-array heap encoding (`Array (BitVec 64) (BitVec 8)`)
- `crates/analysis/src/defunctionalize.rs` — confirmed defunctionalization pattern
- [z3 crate 0.19 docs](https://docs.rs/z3/latest/z3/struct.Model.html) — `Model::eval`, `get_const_interp`, `iter` verified
- [rustc_mir_transform::coroutine](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_mir_transform/coroutine/index.html) — `Yield` terminator, coroutine state machine transform
- [CVC5 SL theory docs](https://cvc5.github.io/docs/cvc5-1.0.2/theories/theories.html) — confirmed experimental status of native SL theory

### Secondary (MEDIUM confidence — academic literature + reference implementations)

- [Wolff et al. OOPSLA 2021 — Modular Specification and Verification of Closures in Rust](https://pm.inf.ethz.ch/publications/WolffBilyMathejaMuellerSummers21.pdf) — spec entailment FOL encoding reference
- [Dartagnan SV-COMP 2020](https://hernanponcedeleon.github.io/pdfs/svcomp20.pdf) — `ψ_prog ∧ ψ_assert ∧ ψ_mm` SMT encoding pattern for weak memory
- [XMM: Relaxed Memory Concurrency Re-executed, POPL 2025](https://www.st.ewi.tudelft.nl/sschakraborty/papers/popl2025-xmm.pdf) — Acq/Rel axiomatic model
- [Automating Separation Logic Using SMT (Piskac/Wies/Zufferey, CAV 2013)](https://cs.nyu.edu/~wies/publ/tr_automating_separation_logic_using_smt.pdf) — heap-as-array + ownership encoding approach
- [Formal Foundations for Translational SL Verifiers, POPL 2025](https://dardinier.me/papers/POPL25_CoreIVL.pdf) — sound basis for SL-based tools
- [Verifying C11-Style Weak Memory Libraries via Refinement (arXiv:2108.06944)](https://arxiv.org/pdf/2108.06944) — RC11 fragment axiom set
- [Prusti Specification Entailments docs](https://viperproject.github.io/prusti-dev/user-guide/verify/spec_ent.html) — `|=` syntax reference
- [Verus Async PR #1839](https://github.com/verus-lang/verus/pull/1839) — competitor async approach (draft, not merged)
- [Vafeiadis et al., CPP2015 — Owicki-Gries unsoundness for weak memory](https://people.mpi-sws.org/~viktor/papers/cpp2015-invited.pdf) — confirms existing HB encoding is unsound for Relaxed/AcqRel
- [Automating Deductive Verification for Weak-Memory, Summers/Mueller 2018](https://www.cs.ubc.ca/~alexsumm/papers/SummersMueller18.pdf) — Viper-based Acq/Rel encoding

### Tertiary (LOW confidence — single source or inference)

- CVC5 model format differs from Z3 s-expression format — inferred; needs direct testing to confirm exact format before implementing Phase 1 CVC5 model parser
- CVC5 SL no theory-mixing limitation — inferred from "safe-options disables SL" and absence of combined QF_SLIA in SL-COMP; needs direct CVC5 testing to confirm

---
*Research completed: 2026-02-19*
*Ready for roadmap: yes*
