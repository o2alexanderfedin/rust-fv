# Roadmap: rust-fv

## Milestones

- ✅ **v0.1 POC** - Phases 1-5 (shipped 2026-02-12)
- ✅ **v0.2 Advanced Verification** - Phases 6-12 (shipped 2026-02-14)
- ✅ **v0.3 Production Usability** - Phases 13-18 (shipped 2026-02-17)
- 🚧 **v0.4 Full Rust Verification** - Phases 19-23 (in progress)

## Phases

<details>
<summary>✅ v0.1 POC (Phases 1-5) - SHIPPED 2026-02-12</summary>

### Phase 1: Soundness Foundation
**Goal**: Core SMT pipeline is end-to-end functional
**Plans**: 3 plans

Plans:
- [x] 01-01: SMT-LIB2 AST and bitvector theory
- [x] 01-02: MIR-to-IR conversion and VCGen
- [x] 01-03: Z3 integration and E2E pipeline

### Phase 2: Table-Stakes Completion
**Goal**: Preconditions, postconditions, counterexamples, path-sensitivity
**Plans**: 5 plans

Plans:
- [x] 02-01: Precondition/postcondition encoding
- [x] 02-02: Path-sensitive VCGen
- [x] 02-03: Counterexample extraction (raw)
- [x] 02-04: Loops, assertions, aggregates
- [x] 02-05: Spec parser with old()

### Phase 3: Modular Verification
**Goal**: Inter-procedural verification with ownership reasoning
**Plans**: 2 plans

Plans:
- [x] 03-01: Contract summaries and inter-procedural VCGen
- [x] 03-02: Ownership reasoning

### Phase 4: Differentiation
**Goal**: Quantifiers, ghost code, prophecy, generics
**Plans**: 4 plans

Plans:
- [x] 04-01: SpecInt/SpecNat and ghost code
- [x] 04-02: Quantifiers with trigger inference
- [x] 04-03: Prophecy variables
- [x] 04-04: Generic function monomorphization

### Phase 5: Performance and Polish
**Goal**: Production-ready cargo verify with caching and diagnostics
**Plans**: 3 plans

Plans:
- [x] 05-01: Incremental caching and parallel verification
- [x] 05-02: Ariadne diagnostics and JSON output
- [x] 05-03: cargo verify CLI

</details>

<details>
<summary>✅ v0.2 Advanced Verification (Phases 6-12) - SHIPPED 2026-02-14</summary>

### Phase 6: Recursive Functions
**Goal**: Termination-verified recursive and mutually recursive functions
**Plans**: 3 plans

Plans:
- [x] 06-01: #[decreases] termination measures
- [x] 06-02: Tarjan's SCC for mutual recursion
- [x] 06-03: Uninterpreted function encoding

### Phase 7: Closures
**Goal**: Fn/FnMut/FnOnce closure verification via defunctionalization
**Plans**: 3 plans

Plans:
- [x] 07-01: Defunctionalization encoding
- [x] 07-02: FnMut environment mutation
- [x] 07-03: FnOnce single-call enforcement

### Phase 8: Trait Objects
**Goal**: Trait object verification with behavioral subtyping
**Plans**: 3 plans

Plans:
- [x] 08-01: Behavioral subtyping (LSP)
- [x] 08-02: Sealed trait closed-world analysis
- [x] 08-03: Open-world uninterpreted encoding

### Phase 9: Lifetime Reasoning
**Goal**: Borrow/lifetime verification with NLL and prophecy
**Plans**: 3 plans

Plans:
- [x] 09-01: NLL-based lifetime tracking
- [x] 09-02: Reborrow chain detection
- [x] 09-03: Nested prophecy variables

### Phase 10: Unsafe Code Detection
**Goal**: Raw pointer safety via heap-as-array model
**Plans**: 3 plans

Plans:
- [x] 10-01: Heap-as-array memory model
- [x] 10-02: Null/bounds checks
- [x] 10-03: #[verifier::trusted] boundaries

### Phase 11: Floating-Point Verification
**Goal**: IEEE 754 exact semantics via SMT FPA theory
**Plans**: 2 plans

Plans:
- [x] 11-01: FPA theory encoding
- [x] 11-02: NaN/infinity VCs and performance warning

### Phase 12: Bounded Concurrency
**Goal**: Data race freedom and deadlock detection for concurrent programs
**Plans**: 3 plans

Plans:
- [x] 12-01: Happens-before encoding (all 5 C11 orderings)
- [x] 12-02: Data race freedom VCs and lock invariants
- [x] 12-03: Deadlock detection via Tarjan's SCC

</details>

<details>
<summary>✅ v0.3 Production Usability (Phases 13-18) - SHIPPED 2026-02-17</summary>

### Phase 13: Standard Library Contracts
**Goal**: Developers can verify code using Vec, Option, Result, HashMap, Iterator without writing contracts
**Plans**: 3 plans

Plans:
- [x] 13-01: SMT Seq theory and StdlibContractRegistry
- [x] 13-02: Vec/Option/Result/HashMap contracts
- [x] 13-03: Iterator adaptor contracts and proptest oracle validation

### Phase 14: Incremental Verification
**Goal**: Re-verification after local edits completes in under 1 second
**Plans**: 4 plans

Plans:
- [x] 14-01: Dual-hash MIR+contract cache
- [x] 14-02: Transitive invalidation via reverse call graph
- [x] 14-03: Benchmark suite (20-30x speedup)
- [x] 14-04: cargo verify clean support

### Phase 15: Manual Trigger Customization
**Goal**: Developers can control quantifier instantiation with #[trigger(expr)]
**Plans**: 3 plans

Plans:
- [x] 15-01: Self-instantiation detection and interpreted symbol warnings
- [x] 15-02: TriggerHint IR type and storage
- [x] 15-03: Manual trigger override of auto-inference

### Phase 16: VSCode Extension
**Goal**: Developers see verification results inline in the editor as they type
**Plans**: 3 plans

Plans:
- [x] 16-01: Inline diagnostics and status bar
- [x] 16-02: Output panel, SMT-LIB viewer, gutter decorations
- [x] 16-03: Z3 bundling and marketplace packaging

### Phase 17: rust-analyzer Integration
**Goal**: rust-analyzer flycheck invokes cargo verify and shows verification diagnostics
**Plans**: 2 plans

Plans:
- [x] 17-01: --message-format=json rustc-compatible output
- [x] 17-02: overrideCommand flycheck integration and diagnostic deduplication

### Phase 18: bv2int Optimization
**Goal**: Arithmetic-only functions verify faster under QF_LIA without unsoundness risk
**Plans**: 3 plans

Plans:
- [x] 18-01: --bv2int activation and conservative eligibility filter
- [x] 18-02: Post-hoc QF_BV→QF_LIA/QF_NIA replacement and differential testing
- [x] 18-03: --bv2int-report summary and slowdown warnings

</details>

### 🚧 v0.4 Full Rust Verification (In Progress)

**Milestone Goal:** Complete Rust verification coverage — every major language feature verifiable with no exceptions and no compromises. Counterexample generation, separation logic, weak memory models, higher-order closure spec entailments, and async/await functional verification.

## Phase Details

### Phase 19: Counterexample Generation
**Goal**: When verification fails, developers see Rust-typed counterexamples with source locations instead of SMT model dumps
**Depends on**: Phase 18
**Requirements**: CEX-01, CEX-02, CEX-03, CEX-04
**Success Criteria** (what must be TRUE):
  1. Developer sees Rust variable name (e.g. `x`) not SSA name (`_param_x_1`) at the failing line when verification fails
  2. Developer sees typed Rust value (e.g. `i32: 5`, `bool: false`) not raw hex bitvector in the counterexample output
  3. Developer sees counterexample values annotated inline at the failing source line via ariadne span labels in terminal output
  4. `--output-format=json` output includes a structured `counterexample` field on verification failure consumable by machine tools
**Plans**: 4 plans

Plans:
- [x] 19-01-PLAN.md — Data foundation: VcOutcome structured pairs, IR source_names, ghost detection, source location plumbing (CEX-01)
- [ ] 19-02-PLAN.md — Typed value rendering module cex_render.rs: bitvec→decimal, struct/enum/ptr/array display (CEX-02)
- [ ] 19-03-PLAN.md — Ariadne multi-label wiring: source file read + per-variable span Labels at spec use sites (CEX-03)
- [ ] 19-04-PLAN.md — JSON schema extension: JsonCounterexample struct + VSCode TypeScript interface update (CEX-04)

### Phase 20: Separation Logic
**Goal**: Developers can prove aliasing freedom and heap ownership properties for raw pointer code using separation logic predicates
**Depends on**: Phase 19
**Requirements**: SEP-01, SEP-02, SEP-03, SEP-04
**Success Criteria** (what must be TRUE):
  1. Developer writes `pts_to(p, v)` in `#[requires]`/`#[ensures]` and the verifier proves raw pointer ownership is satisfied at the call site
  2. Developer writes separating conjunction (`H1 * H2`) in specs and the verifier proves the two heap regions do not alias
  3. Developer writes a function that modifies one heap region and the frame rule automatically propagates the unchanged remainder — no manual re-specification required
  4. Developer defines `#[ghost_predicate] fn linked_list(p, n)` recursively and the verifier unfolds it to depth 3 to prove list structure properties
**Plans**: 4 plans

Plans:
- [ ] 20-01-PLAN.md — Sep heap domain (sep_heap + perm arrays) + pts_to(p,v) encoding in sep_logic.rs and spec_parser.rs (SEP-01)
- [ ] 20-02-PLAN.md — #[ghost_predicate] proc-macro + GhostPredicateDatabase + callbacks.rs extraction (SEP-04 foundation)
- [ ] 20-03-PLAN.md — Separating conjunction (*) detection + ghost predicate expansion + frame rule in vcgen.rs + AUFBV logic selection (SEP-02, SEP-03, SEP-04)
- [ ] 20-04-PLAN.md — E2E integration tests for all 4 SEP requirements verified against Z3 (SEP-01, SEP-02, SEP-03, SEP-04)

### Phase 21: Weak Memory Models
**Goal**: Developers can verify programs using Relaxed/Acquire/Release/AcqRel atomic orderings with sound RC11 semantics
**Depends on**: Phase 20
**Requirements**: WMM-01, WMM-02, WMM-03, WMM-04
**Success Criteria** (what must be TRUE):
  1. Developer annotates atomic operations with `Relaxed`, `Acquire`, `Release`, or `AcqRel` ordering and the verifier applies full RC11 coherence axioms (`mo`, `rf`, `co`) rather than collapsing them to `BoolLit(true)`
  2. All 8 canonical C11 litmus tests (IRIW, SB, LB, MP, CoRR, CoRW, CoWR, CoWW) produce the correct allowed/forbidden verdicts, serving as the soundness regression suite
  3. Data race detection reports races under Relaxed orderings that the SeqCst-only path would miss
  4. Existing SeqCst proofs from v0.2/v0.3 continue to pass with zero regressions — weak memory axioms are scoped to `WeakMemory*` VcKind only
**Plans**: TBD

### Phase 22: Higher-Order Closures
**Goal**: Developers can specify and verify higher-order functions taking closure arguments with precise pre/postconditions
**Depends on**: Phase 21
**Requirements**: HOF-01, HOF-02
**Success Criteria** (what must be TRUE):
  1. Developer writes `fn_spec(f, |x| pre => post)` in a HOF spec and the verifier proves the closure satisfies the given pre/postcondition entailment at every call site
  2. Developer annotates a `FnMut` closure HOF and the verifier tracks environment mutation across calls via SSA-versioned environment (`env_v0 → env_v1`), proving postconditions that reference mutated captured variables
**Plans**: TBD

### Phase 23: Async/Await Verification
**Goal**: Developers can verify functional properties of async fn code under sequential polling model
**Depends on**: Phase 22
**Requirements**: ASY-01, ASY-02
**Success Criteria** (what must be TRUE):
  1. Developer annotates `async fn` with `#[requires]`/`#[ensures]` and `cargo verify` proves the functional postcondition holds when the future resolves under a sequential polling model
  2. Developer writes `#[state_invariant]` on an `async fn` and the verifier proves the invariant holds at every `.await` suspension point within the function body
**Plans**: TBD

## Progress

**Execution Order:**
Phases execute in numeric order: 19 → 20 → 21 → 22 → 23

| Phase | Milestone | Plans Complete | Status | Completed |
|-------|-----------|----------------|--------|-----------|
| 1-5. POC Phases | v0.1 | 17/17 | Complete | 2026-02-12 |
| 6-12. Advanced Phases | v0.2 | 21/21 | Complete | 2026-02-14 |
| 13-18. Usability Phases | v0.3 | 13/13 | Complete | 2026-02-17 |
| 19. Counterexample Generation | 4/4 | Complete    | 2026-02-20 | - |
| 20. Separation Logic | 2/4 | In Progress|  | - |
| 21. Weak Memory Models | v0.4 | 0/TBD | Not started | - |
| 22. Higher-Order Closures | v0.4 | 0/TBD | Not started | - |
| 23. Async/Await Verification | v0.4 | 0/TBD | Not started | - |
