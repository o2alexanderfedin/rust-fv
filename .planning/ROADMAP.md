# Roadmap: rust-fv

## Milestones

- ✅ **v0.1 POC** - Phases 1-5 (shipped 2026-02-12)
- ✅ **v0.2 Advanced Verification** - Phases 6-12 (shipped 2026-02-14)
- ✅ **v0.3 Production Usability** - Phases 13-18 (shipped 2026-02-17)
- ✅ **v0.4 Full Rust Verification** - Phases 19-27 (shipped 2026-02-23)
- ✅ **v0.5 SMT Completeness** - Phases 28-29 (shipped 2026-02-24) + UAT Phase 00 (validated 2026-02-25, 22/22 tests pass)

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
**Goal**: Recursive functions with termination proofs via decreases clause
**Plans**: 3 plans

Plans:
- [x] 06-01: Decreases clause and termination measures
- [x] 06-02: Recursive function summaries via UF encoding
- [x] 06-03: SCC-based call graph analysis

### Phase 7: Closures
**Goal**: Fn/FnMut/FnOnce closure verification via defunctionalization
**Plans**: 3 plans

Plans:
- [x] 07-01: Defunctionalization with explicit environment parameter
- [x] 07-02: FnMut SSA-versioned environment
- [x] 07-03: Higher-order contract propagation

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

<details>
<summary>✅ v0.4 Full Rust Verification (Phases 19-27) - SHIPPED 2026-02-23</summary>

### Phase 19: Counterexample Generation
**Goal**: When verification fails, developers see Rust-typed counterexamples with source locations
**Plans**: 4 plans

Plans:
- [x] 19-01: Data foundation: VcOutcome structured pairs, IR source_names, ghost detection, source location plumbing (CEX-01)
- [x] 19-02: Typed value rendering cex_render.rs: bitvec→decimal, struct/enum/ptr/array display (CEX-02)
- [x] 19-03: Ariadne inline counterexample labels at failing source line (CEX-03)
- [x] 19-04: JSON output structured counterexample field + VSCode extension wiring (CEX-04)

### Phase 20: Separation Logic
**Goal**: Heap ownership reasoning via pts_to, separating conjunction, frame rule, ghost predicates
**Plans**: 4 plans

Plans:
- [x] 20-01: pts_to predicate and AUFBV encoding (SEP-01)
- [x] 20-02: Separating conjunction and disjoint ownership (SEP-02)
- [x] 20-03: Frame rule for function calls (SEP-03)
- [x] 20-04: #[ghost_predicate] recursive heap predicates with depth-3 unfolding (SEP-04)

### Phase 21: Weak Memory Models
**Goal**: RC11 coherence axioms for Relaxed/Acquire/Release atomics and data race detection
**Plans**: 3 plans

Plans:
- [x] 21-01: RC11 foundation: mo/rf/co primitives, 8 litmus tests (WMM-01, WMM-02)
- [x] 21-02: Data race detection for weak memory orderings (WMM-03, WMM-04)
- [x] 21-03: Litmus test validation suite (CoRR, CoRW, CoWR, CoWW, SB, LB, MP, IRIW)

### Phase 22: Higher-Order Closures
**Goal**: fn_spec specification entailments and stateful FnMut environment tracking
**Plans**: 3 plans

Plans:
- [x] 22-01: fn_spec entailment encoding via AUFLIA (HOF-01)
- [x] 22-02: FnMut SSA-versioned environment capture (HOF-02)
- [x] 22-03: Higher-order closure contract propagation

### Phase 23: Async/Await Verification
**Goal**: async fn verification under sequential polling model with state invariants
**Plans**: 4 plans

Plans:
- [x] 23-01: CoroutineInfo IR and async VC generation foundation (ASY-01)
- [x] 23-02: state_invariant at await suspension points (ASY-02)
- [x] 23-03: Async counterexample extraction and JSON output
- [x] 23-04: Async diagnostics and driver integration

### Phase 24: SEP-04 Ghost Predicate Production Wiring
**Goal**: Close SEP-04 wiring gap — ghost_pred_db reaches generate_vcs_with_db in production path
**Plans**: 2 plans

Plans:
- [x] 24-01: Extract and Arc ghost predicates through VerificationTask (SEP-04 gap)
- [x] 24-02: Wire ghost_pred_db to generate_vcs_with_db and validate E2E

### Phase 25: VSCode Counterexample v2 Integration
**Goal**: Close CEX-02/CEX-04 IDE gap — VSCode shows typed Rust values from counterexample_v2
**Plans**: 1 plan

Plans:
- [x] 25-01: diagnostics.ts + outputPanel.ts consume counterexample_v2 typed schema

### Phase 26: WMM-03 Weak Memory Race Detection Fix
**Goal**: WeakMemoryRace VC emits SAT-returning formula so Relaxed data races are detected
**Plans**: 2 plans

Plans:
- [x] 26-01: Fix WeakMemoryRace VC body in rc11.rs (Assert(BoolLit(true)) + mo/rf constraints)
- [x] 26-02: WeakMemoryRace UX in diagnostics.rs + E2E driver integration test

### Phase 27: Async Counterexample IDE Fidelity
**Goal**: Async verification failures show poll iteration and await-side context in VSCode
**Plans**: 1 plan

Plans:
- [x] 27-01: Extract poll_iteration from Z3 model, infer await_side, update TypeScript interface + outputPanel rendering

</details>

## Progress

| Phase | Milestone | Plans Complete | Status | Completed |
|-------|-----------|----------------|--------|-----------|
| 1-5. POC Phases | v0.1 | 17/17 | Complete | 2026-02-12 |
| 6-12. Advanced Phases | v0.2 | 21/21 | Complete | 2026-02-14 |
| 13-18. Usability Phases | v0.3 | 13/13 | Complete | 2026-02-17 |
| 1-5. POC Phases | v0.1 | 17/17 | Complete | 2026-02-12 |
| 6-12. Advanced Phases | v0.2 | 21/21 | Complete | 2026-02-14 |
| 13-18. Usability Phases | v0.3 | 13/13 | Complete | 2026-02-17 |
| 19-27. Full Rust Verification | v0.4 | 27/27 | Complete | 2026-02-23 |
| 28-29. SMT Completeness Phases | v0.5 | 10/10 | Complete | 2026-02-24 |
| 00. v0.4+v0.5 Milestone UAT | v0.5 UAT | 1/1 | Complete | 2026-02-25 |

<details>
<summary>✅ v0.5 SMT Completeness (Phases 28-29) — SHIPPED 2026-02-24</summary>

### Phase 28: SMT VCGen Completeness
**Goal**: VCGen completeness — all major Rust expression categories generate correct SMT VCs
**Requirements**: VCGEN-01, VCGEN-02, VCGEN-03, VCGEN-04
**Plans**: 5 plans

Plans:
- [x] 28-01: TDD scaffold: 10 failing tests for VCGEN-01..04
- [x] 28-02: VCGEN-03: Numeric as-cast encoding (encode_cast + Rvalue::Cast)
- [x] 28-03: VCGEN-02: Discriminant binding for match/if-let/while-let (Rvalue::Discriminant)
- [x] 28-04: VCGEN-01: Array index bounds VCs and slice length encoding (Rvalue::Len)
- [x] 28-05: VCGEN-04: Generic where-clause premises as SMT Assert (trait_bounds_as_smt_assumptions)

### Phase 29: Fix Identified SMT VCGen Gaps
**Goal**: Fix soundness holes and coverage breadth gaps in Rust → SMT-LIB VCGen
**Requirements**: MIRCONV-01, MIRCONV-02, VCGEN-05, VCGEN-06
**Plans**: 5 plans

Plans:
- [x] 29-01: TDD scaffold (10 RED tests) + MIRCONV-01: CastKind preservation
- [x] 29-02: VCGEN-05: float-to-int SMT encoding fix (fp.to_sbv/fp.to_ubv RTZ)
- [x] 29-03: MIRCONV-02: AggregateKind::Adt/Closure + IR SetDiscriminant/Assume
- [x] 29-04: MIRCONV-01 (TyKind::Param→Generic) + CopyForDeref/RawPtr/Repeat rvalues
- [x] 29-05: VCGEN-06: projected LHS functional record update + Downcast narrowing

</details>

### Phase 29.4: Stdlib Contracts Option Doc Test Fixes (INSERTED)

**Goal:** [Urgent work - to be planned]
**Requirements**: TBD
**Depends on:** Phase 29
**Plans:** 0 plans

Plans:
- [ ] TBD (run /gsd:plan-phase 29.4 to break down)

### Phase 29.3: Borrow Conflict Detection Implementation (INSERTED)

**Goal:** [Urgent work - to be planned]
**Requirements**: TBD
**Depends on:** Phase 29
**Plans:** 0 plans

Plans:
- [ ] TBD (run /gsd:plan-phase 29.3 to break down)

### Phase 29.2: Prophecy Encoding for Mutable Reference Assignments (INSERTED)

**Goal:** [Urgent work - to be planned]
**Requirements**: TBD
**Depends on:** Phase 29
**Plans:** 0 plans

Plans:
- [ ] TBD (run /gsd:plan-phase 29.2 to break down)

### Phase 29.1: For-loop Iterator Range VCGen (INSERTED)

**Goal:** Add VCGen support for for-loops over ranges and iterators — AUFLIA quantified VCs + QF_LIA bounded unrolling VCs + MIR pattern detection
**Requirements**: VCGEN-01-FORLOOP
**Depends on:** Phase 29
**Plans:** 3 plans

Plans:
- [ ] 29.1-01-PLAN.md — TDD scaffold: 8 RED tests + IteratorKind IR extension
- [ ] 29.1-02-PLAN.md — for_loop_vcgen.rs module + wiring into generate_vcs_with_db (8 tests GREEN)
- [ ] 29.1-03-PLAN.md — MIR for-loop pattern detection + test 09 integration test

### Phase 00: v0.4+v0.5 Milestone UAT ✅
**Goal**: Combined UAT document validating v0.4 (phases 19-27) and v0.5 (phases 28-29) deliverables end-to-end
**Requirements**: UAT-01
**Plans**: 1 plan
**Completed**: 2026-02-25

Plans:
- [x] 00-01: Author and execute v0.4-v0.5-UAT.md (22 test items covering phases 19-29) — all 22 PASS
