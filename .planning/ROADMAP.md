# Roadmap: rust-fv

## Milestones

- **v0.1 Formal Verification POC** -- Phases 1-5 (shipped 2026-02-12)
- **v0.2 Advanced Verification** -- Phases 6-12 (active)

## Phases

<details>
<summary>v0.1 Formal Verification POC (Phases 1-5) -- SHIPPED 2026-02-12</summary>

- [x] Phase 1: Soundness Foundation (3/3 plans) -- completed 2026-02-11
- [x] Phase 2: Table Stakes Completion (5/5 plans) -- completed 2026-02-11
- [x] Phase 3: Modular Verification (2/2 plans) -- completed 2026-02-11
- [x] Phase 4: Differentiation (4/4 plans) -- completed 2026-02-11
- [x] Phase 5: Performance and Polish (3/3 plans) -- completed 2026-02-11

See `.planning/milestones/v0.1-ROADMAP.md` for full details.

</details>

### v0.2 Advanced Verification (Phases 6-12)

#### Phase 6: Recursive Functions

**Goal:** Developer can verify recursive functions with automatic termination checking

**Dependencies:** v0.1 complete (inter-procedural verification, contract summaries)

**Requirements:** REC-01, REC-02, REC-03, REC-04, REC-05, INF-01

**Plans:** 3 plans

Plans:
- [x] 06-01-PLAN.md -- Infrastructure: #[decreases] macro, IR/VcKind extensions, petgraph SCC detection
- [x] 06-02-PLAN.md -- Core: recursion.rs module with termination VCs and uninterpreted function encoding
- [x] 06-03-PLAN.md -- Integration: driver extraction, diagnostics, end-to-end Z3 verification tests

**Success Criteria:**
1. Developer annotates recursive function with `#[decreases(expr)]` and verifier proves termination measure decreases on each recursive call
2. Developer writes factorial/fibonacci function without `#[decreases]` and verifier rejects with "missing termination measure" diagnostic
3. Developer verifies mutually recursive functions (e.g., even/odd checkers) with shared decreases clause
4. Developer sees termination VC failure with counterexample showing non-decreasing measure between calls
5. Developer verifies recursive tree traversal with structural measure (e.g., `tree.size()`)

---

#### Phase 7: Closures

**Goal:** Developer can verify functions that accept and call closures with explicit contracts

**Dependencies:** Phase 6 (recursive closures may exist)

**Requirements:** CLO-01, CLO-02, CLO-03, CLO-04, CLO-05, CLO-06

**Plans:** 3 plans

Plans:
- [x] 07-01-PLAN.md -- Infrastructure: IR closure types (Ty::Closure, ClosureTrait, ClosureInfo), closure_analysis module, encode_sort extension
- [x] 07-02-PLAN.md -- Core: defunctionalize.rs module, VCGen closure integration, spec parser closure references
- [x] 07-03-PLAN.md -- Integration: closure diagnostics, end-to-end Z3 verification tests

**Success Criteria:**
1. Developer verifies function accepting `Fn` closure with immutable captures (e.g., `Vec::map` with `|x| x + 1`)
2. Developer verifies function accepting `FnMut` closure with mutable captures using prophecy variables (e.g., counter closure)
3. Developer verifies function accepting `FnOnce` closure with move semantics (e.g., thread spawn callback)
4. Developer specifies closure contract via `#[requires]`/`#[ensures]` on closure-accepting function parameter
5. Developer sees closure contract violation with diagnostic pointing to closure call site

---

#### Phase 8: Trait Objects

**Goal:** Developer can verify dynamic dispatch and trait implementations against trait-level contracts

**Dependencies:** Phase 7 (trait methods may accept closures)

**Requirements:** TRT-01, TRT-02, TRT-03, TRT-04, TRT-05

**Plans:** 3 plans

Plans:
- [x] 08-01-PLAN.md -- Infrastructure: IR trait types (TraitDef, TraitMethod, TraitImpl, Ty::TraitObject), trait_analysis module, VcKind::BehavioralSubtyping
- [x] 08-02-PLAN.md -- Core: behavioral_subtyping.rs module, VCGen dyn Trait dispatch, sealed trait sum type encoding
- [x] 08-03-PLAN.md -- Integration: trait diagnostics, end-to-end Z3 verification tests

**Success Criteria:**
1. Developer defines trait with `#[requires]`/`#[ensures]` annotations on trait methods
2. Developer verifies each `impl Trait for Type` satisfies trait-level contracts (behavioral subtyping)
3. Developer calls method on `Box<dyn Trait>` and verifier uses trait-level contract (not impl-specific)
4. Developer marks trait as `#[sealed]` and verifier enumerates all known impls for closed-world verification
5. Developer sees "impl does not satisfy trait contract" error when implementation violates trait postcondition

---

#### Phase 9: Lifetime Reasoning

**Goal:** Developer can verify programs with explicit lifetime annotations and non-lexical lifetime patterns

**Dependencies:** Phase 8 (trait objects have lifetime bounds)

**Requirements:** LIF-01, LIF-02, LIF-03, LIF-04, LIF-05, LIF-06, INF-02 (VcKind::BorrowValidity)

**Plans:** 3 plans

Plans:
- [x] 09-01-PLAN.md -- Infrastructure: IR lifetime types (LifetimeParam, BorrowInfo, ReborrowChain), lifetime_analysis module, VcKind::BorrowValidity, nested prophecy encoding
- [x] 09-02-PLAN.md -- Core: borrow_conflict.rs module, VCGen borrow validity integration, spec parser final(*x)/final(**x), #[borrow_ensures] macro
- [x] 09-03-PLAN.md -- Integration: borrow timeline diagnostics, end-to-end Z3 verification tests

**Success Criteria:**
1. Developer verifies function with lifetime parameters (`'a`, `'b`) and compiler-inferred outlives constraints (`T: 'a`)
2. Developer uses non-lexical lifetimes (NLL) pattern (borrow ends at last use, not scope end) and verifier accepts
3. Developer verifies borrow expiry using prophecy variables (final value after mutable borrow lifetime ends)
4. Developer sees borrow validity VC failure when attempting to use value after lifetime expiry
5. Developer verifies reborrow chain (e.g., `&mut &mut T`) with correct lifetime tracking

---

#### Phase 10: Unsafe Code Detection

**Goal:** Developer receives warnings and basic verification for unsafe code with explicit trust boundaries

**Dependencies:** Phase 9 (pointer validity requires lifetime reasoning)

**Requirements:** USF-01, USF-02, USF-03, USF-04, USF-05, USF-06, INF-02 (VcKind::MemorySafety)

**Success Criteria:**
1. Developer writes unsafe block and verifier flags it in output with source location and warning message
2. Developer dereferences raw pointer and verifier generates null-check VC (`ptr != null`)
3. Developer performs pointer arithmetic and verifier generates bounds-check VC (`offset < allocation_size`)
4. Developer annotates unsafe function with `#[unsafe_requires]`/`#[unsafe_ensures]` and verifier checks contract at call sites
5. Developer marks unsafe function as `#[verifier::trusted]` and verifier skips body verification but checks call-site contracts

---

#### Phase 11: Floating-Point Verification

**Goal:** Developer can verify floating-point arithmetic with IEEE 754 semantics (opt-in, performance trade-off documented)

**Dependencies:** Phase 10 (unsafe may contain FP operations)

**Requirements:** FPV-01, FPV-02, FPV-03, FPV-04, FPV-05, FPV-06, INF-02 (VcKind::FloatingPointNaN)

**Success Criteria:**
1. Developer enables floating-point verification and verifier encodes `f32`/`f64` as SMT FloatingPoint theory (IEEE 754)
2. Developer verifies FP operation and verifier generates NaN propagation VC (`!fp.isNaN(result)` unless NaN expected)
3. Developer sees Inf overflow check VC for operations that may overflow to infinity
4. Developer verifies FP comparison respecting IEEE 754 semantics (NaN != NaN, -0.0 == +0.0)
5. Developer receives performance warning when enabling FP verification ("FPA theory 2-10x slower than bitvectors")

---

#### Phase 12: Concurrency Verification

**Goal:** Developer can verify bounded concurrent programs with sequential consistency atomics

**Dependencies:** Phase 11 (concurrent code may use FP), Phase 9 (concurrent code requires lifetime reasoning for shared state)

**Requirements:** CON-01, CON-02, CON-03, CON-04, CON-05, CON-06, INF-02 (VcKind::DataRaceFreedom), INF-03, INF-04

**Success Criteria:**
1. Developer enables bounded concurrency verification (configurable max threads/context switches) and verifier enumerates thread interleavings
2. Developer verifies atomic operation (SeqCst) and verifier encodes total ordering constraints in happens-before relation
3. Developer sees data race VC failure when shared mutable state accessed without synchronization
4. Developer annotates Mutex with `#[lock_invariant(expr)]` and verifier checks invariant holds on lock acquire/release
5. Developer receives bounded verification warning ("limited to N threads, M context switches; may miss interleavings")

---

## Progress

| Phase | Milestone | Plans Complete | Status | Completed |
|-------|-----------|----------------|--------|-----------|
| 1. Soundness Foundation | v0.1 | 3/3 | Complete | 2026-02-11 |
| 2. Table Stakes Completion | v0.1 | 5/5 | Complete | 2026-02-11 |
| 3. Modular Verification | v0.1 | 2/2 | Complete | 2026-02-11 |
| 4. Differentiation | v0.1 | 4/4 | Complete | 2026-02-11 |
| 5. Performance and Polish | v0.1 | 3/3 | Complete | 2026-02-11 |
| 6. Recursive Functions | v0.2 | 3/3 | Complete | 2026-02-12 |
| 7. Closures | v0.2 | 3/3 | Complete | 2026-02-12 |
| 8. Trait Objects | v0.2 | 3/3 | Complete | 2026-02-12 |
| 9. Lifetime Reasoning | v0.2 | 3/3 | Complete | 2026-02-13 |
| 10. Unsafe Code Detection | v0.2 | 0/? | Pending | - |
| 11. Floating-Point Verification | v0.2 | 0/? | Pending | - |
| 12. Concurrency Verification | v0.2 | 0/? | Pending | - |

---
*Roadmap created: 2026-02-10*
*Last updated: 2026-02-13 (Phase 9 complete: 3/3 plans)*
