# Roadmap: rust-fv

## Milestones

- ✅ **v0.1 POC** - Phases 1-5 (shipped 2026-02-12)
- ✅ **v0.2 Advanced** - Phases 6-12 (shipped 2026-02-14)
- ✅ **v0.3 Usability** - Phases 13-18 (shipped 2026-02-17)
- ✅ **v0.4 Full Rust** - Phases 19-27 (shipped 2026-02-23)
- ✅ **v0.5 SMT Completeness** - Phases 28-29 (shipped 2026-02-25)
- ✅ **v0.5 Audit & Gap Closure** - Phases 29.1-29.4, 30-33 (shipped 2026-02-27)
- ✅ **v0.6 Cross-Crate Verification** - Phases 34-37, 37.1 (shipped 2026-03-02)
- ✅ **v0.7 Generics & Traits Hardening** - Phases 38-44, generics-fix (shipped 2026-03-04)
- 🔄 **v0.8 Completeness & Coverage** - Phases 45-56 (in progress)

## Phases

<details>
<summary>✅ v0.1 POC (Phases 1-5) - SHIPPED 2026-02-12</summary>

Phases 1-5: proc macro annotations, SMT-LIB2 AST, bitvector theory, MIR-to-IR, VCGen, Z3 integration, end-to-end pipeline.

</details>

<details>
<summary>✅ v0.2 Advanced (Phases 6-12) - SHIPPED 2026-02-14</summary>

Phases 6-12: recursive functions, closures, trait objects, lifetimes, unsafe code, floating-point, bounded concurrency.

</details>

<details>
<summary>✅ v0.3 Usability (Phases 13-18) - SHIPPED 2026-02-17</summary>

Phases 13-18: stdlib contracts, incremental verification, trigger customization, VSCode extension, rust-analyzer integration, bv2int optimization.

</details>

<details>
<summary>✅ v0.4 Full Rust (Phases 19-27) - SHIPPED 2026-02-23</summary>

Phases 19-27: counterexample generation, separation logic, weak memory models, higher-order closures, async/await, gap closures.

</details>

<details>
<summary>✅ v0.5 SMT Completeness (Phases 28-29) - SHIPPED 2026-02-25</summary>

Phases 28-29: as-cast encoding, discriminant binding, array bounds VCs, generic trait bound premises, CastKind preservation, aggregate conversion, float-to-int soundness fix, missing rvalue variants, functional record update.

</details>

<details>
<summary>✅ v0.5 Audit & Gap Closure (Phases 29.1-29.4, 30-33) - SHIPPED 2026-02-27</summary>

Phases 29.1-33: for-loop VCGen, prophecy fix, borrow conflict detection, stdlib doc test fixes, SetDiscriminant VCGen, Z3/ghost fixes, retrospective verification docs, v0.1 tech debt closure, v0.1 milestone audit passed.

</details>

<details>
<summary>✅ v0.6 Cross-Crate Verification (Phases 34–37.1) — SHIPPED 2026-03-02</summary>

Phases 34–37.1: cross-function pointer aliasing, opaque callee diagnostics V060/V061, summary contract inference with `#[verifier::infer_summary]`, HIR-based alias precondition parsing, cross-crate Tarjan SCC detection, `#[decreases]` termination across crate boundaries, V062 InferredSummaryAlias guard.

</details>

<details>
<summary>✅ v0.7 Generics & Traits Hardening (Phases 38–44, generics-fix) — SHIPPED 2026-03-04</summary>

Phases 38–44 + generics-fix: behavioral subtyping VCs with Liskov checks, FnMut prophecy variable encoding for mutable closure contracts, real trait bound SMT axioms (Ord/PartialOrd DeclareSort+DeclareFun), MonomorphizationRegistry population from call-site type analysis, sealed trait detection via HIR visibility, dyn dispatch call-site VC resolution, Nyquist validation coverage, closure production wiring (Ty::Closure from real MIR).

- [x] Phase 38: Trait Subtyping Wiring (2/2 plans) — completed 2026-03-02
- [x] Phase 39: FnMut Prophecy Variable Encoding (2/2 plans) — completed 2026-03-02
- [x] Phase generics-fix: Generics Verification Fix (1/1 plan) — completed 2026-03-02
- [x] Phase 40: Generics Verification Completion (3/3 plans) — completed 2026-03-03
- [x] Phase 41: Phase 38 Hardening (2/2 plans) — completed 2026-03-03
- [x] Phase 42: Phase 39 Production Wiring (1/1 plan) — completed 2026-03-03
- [x] Phase 43: Nyquist Validation Coverage (2/2 plans) — completed 2026-03-04
- [x] Phase 44: MonomorphizationRegistry Population (1/1 plan) — completed 2026-03-04

</details>

### v0.8 Completeness & Coverage (Phases 45–56)

- [x] **Phase 45: Quick Wins & Pattern Integration** - Verification item regression tests + pattern matching E2E tests (completed 2026-03-05)
- [x] **Phase 46: SMT Datatype Foundations** - struct/enum declare-datatype, Rvalue::Repeat, functional update hardening, Z3 Int sort (gap closure: native enum testers) (completed 2026-03-05)
- [x] **Phase 47: MIR Coverage Hardening** - Pointer alignment VCs, CastKind disambiguation, match arm fallthrough audit, spec validation diagnostics (completed 2026-03-05)
- [x] **Phase 48: Advanced Ownership & Borrows** - RefCell ghost state, two-phase borrowing, partial struct moves, borrow splitting, trigger inference fix (completed 2026-03-06)
- [x] **Phase 49: Cross-Crate & Interop Completeness** - Cross-crate generic registry, mutable static race VCs, NonNull encoding, From::from at ?, iterator adapter chaining (gap closure in progress) (completed 2026-03-06)
- [x] **Phase 50: Stdlib Ptr/Mem & Unsafe Boundary** - ptr::read/write contracts, mem::swap contracts, FFI extern "C" modeling, transmute/MaybeUninit, async limitation doc (completed 2026-03-07)
- [x] **Phase 51: Core Language Features I** - Const generics, HRTB, union types, Drop::drop modeling, Pin wrapper (completed 2026-03-07)
- [x] **Phase 52: Advanced Type System Features** - catch_unwind, impl Trait RPITIT, GATs, trait upcasting, negative impls (completed 2026-03-07)
- [ ] **Phase 53: Operator & Smart Pointer Verification** - Operator overloading, custom Deref, Index/IndexMut, unsafe Send/Sync
- [ ] **Phase 54: Stdlib Contracts Batch I** - HashSet, VecDeque, BTreeMap/BTreeSet, BinaryHeap, LinkedList, Weak, Cell, OnceCell
- [ ] **Phase 55: Stdlib Contracts Batch II & Iterators** - Path, DoubleEndedIterator, collect/FromIterator, custom Iterator contracts, format!, OsStr, inline asm
- [ ] **Phase 56: Async & Concurrency Extensions** - Async closures, async streams, cancellation safety, Condvar, Barrier, thread-local, fences

## Phase Details

### Phase 45: Quick Wins & Pattern Integration
**Goal**: All previously-identified VCGen regression items pass as green tests, and all four pattern matching constructs verified end-to-end
**Depends on**: Phase 44 (v0.7 complete)
**Requirements**: COMPL-19, COMPL-20, COMPL-21, COMPL-22, PAT-01, PAT-02, PAT-03, PAT-04
**Success Criteria** (what must be TRUE):
  1. `cargo verify` on a function using `for x in 0..n` produces the same VC result whether called via unit path or E2E path — 8 previously-RED unit tests are GREEN
  2. A test function annotated around `SetDiscriminant` produces a verified-or-counterexample result (not silent no-op) confirmed by E2E test
  3. A function with ghost variables does not produce spurious SMT failures — regression test is GREEN
  4. A function whose spec contains `as int` routes through QF_LIA solver path — regression test confirms correct solver selection
  5. Functions using `let`-`else`, slice patterns `[first, .., last]`, range patterns `1..=5`, and `@` bindings each produce correct VCs confirmed by integration tests
**Plans:** 2/2 plans complete
Plans:
- [ ] 45-01-PLAN.md — COMPL-19..22 regression validation suite + SetDiscriminant E2E
- [ ] 45-02-PLAN.md — Pattern matching E2E tests (PAT-01..04)

### Phase 46: SMT Datatype Foundations
**Goal**: Structs and enums are encoded as first-class SMT datatypes with constructors and selectors, removing the uninterpreted-sort approximation that limits struct field reasoning
**Depends on**: Phase 45
**Requirements**: COMPL-01, COMPL-05, COMPL-07, COMPL-11
**Success Criteria** (what must be TRUE):
  1. A struct type generates a `(declare-datatype StructName ...)` SMT command with one constructor and one selector per field; a function verified against struct field postconditions passes Z3 without uninterpreted-sort fallback
  2. An enum type generates a `(declare-datatype EnumName ...)` with one constructor per variant, plus a tester (`is-Variant`) per constructor; discriminant VCs use these testers
  3. Functional update on any struct rvalue (not just field-mutation) emits the correct `mk-StructName` constructor term using the new datatype; regression test from COMPL-05 remains GREEN
  4. `Z3::Sort::int()` is used in the native Z3 backend when encoding `SpecInt`/`SpecNat` sorts; no panics or fallback to uninterpreted sort for integer specs
  5. `[expr; N]` (`Rvalue::Repeat`) encodes as a universally quantified equality `(forall ((i Int)) (= (select arr i) val))` or a const-array store chain in SMT; bounds-checked access to repeated array passes verification
**Plans:** 3/3 plans complete
Plans:
- [x] 46-01-PLAN.md — Z3 native Int sort support + Rvalue::Repeat encoding (COMPL-07, COMPL-11)
- [x] 46-02-PLAN.md — Datatype wiring completion + functional update hardening (COMPL-01, COMPL-05)
- [ ] 46-03-PLAN.md — Gap closure: native enum IsTester discriminant encoding (COMPL-01)

### Phase 47: MIR Coverage Hardening
**Goal**: All pointer alignment casts generate safety VCs, CastKind variants are unambiguously encoded, ambiguous match arms are documented, and spec errors surface as rustc diagnostics
**Depends on**: Phase 46
**Requirements**: COMPL-02, COMPL-03, COMPL-06, COMPL-12
**Success Criteria** (what must be TRUE):
  1. A function casting `*const u8` to `*const u32` generates a `MemorySafety` VC asserting `addr % align_of::<u32>() == 0`; Z3 produces UNSAT for aligned case and SAT (counterexample) for unaligned case
  2. Each CastKind variant (IntToInt, FloatToInt, IntToFloat, PtrToPtr) follows a distinct encoding path in `mir_converter.rs`; no two variants share the same SMT output shape; unit tests cover all four variants
  3. Every `match arm` path in `vcgen.rs` either generates a VC or has an explicit doc-comment explaining why it is intentionally skipped; no silent fallthrough remains undocumented
  4. A function annotated with a syntactically invalid `#[requires(...)]` expression produces a rustc-style `error[V...]` diagnostic at the annotation source span instead of a logged warning that disappears silently
**Plans:** 3/3 plans complete
Plans:
- [x] 47-01-PLAN.md — CastKind PtrToPtr rename + AlignmentSafety VCs + E2E (COMPL-02, COMPL-03)
- [x] 47-02-PLAN.md — Match arm fallthrough audit for vcgen.rs + encode_term.rs (COMPL-12)
- [x] 47-03-PLAN.md — Spec validation V080 diagnostics (COMPL-06)

### Phase 48: Advanced Ownership & Borrows
**Goal**: RefCell interior mutability is tracked as ghost state, two-phase borrows and partial struct moves are modeled, disjoint field borrows are verified, and trigger inference no longer proposes datatype selector symbols
**Depends on**: Phase 47
**Requirements**: COMPL-08, COMPL-09, COMPL-13, COMPL-14, COMPL-16
**Success Criteria** (what must be TRUE):
  1. A function calling `cell.borrow()` when `borrow_mut()` is already outstanding generates a `BorrowConflict` VC that Z3 resolves as SAT (contract violation detected)
  2. A function using the two-phase borrow pattern `vec.push(vec.len())` verifies successfully — no false positive conflict VC
  3. A function that partially moves a struct field (`let x = s.field_a`) and then reads `s.field_b` verifies successfully; a subsequent read of `s.field_a` generates a use-after-move VC caught by Z3
  4. A function taking `&mut s.x` and `&s.y` simultaneously verifies successfully with disjointness confirmed in SMT; a function taking `&mut s.x` and `&s.x` produces a conflict VC
  5. Quantifier trigger inference never proposes a datatype selector symbol (e.g., `Struct-field`) as a trigger candidate; the filtered candidate list contains only user-defined or spec-level symbols
**Plans:** 4/4 plans complete
Plans:
- [ ] 48-01-PLAN.md — Trigger inference datatype filter (COMPL-08) + IR type foundations
- [ ] 48-02-PLAN.md — RefCell ghost state VCs + two-phase borrow modeling (COMPL-09, COMPL-13)
- [ ] 48-03-PLAN.md — Partial struct moves + borrow splitting (COMPL-14, COMPL-16)
- [ ] 48-04-PLAN.md — Gap closure: TwoPhaseBorrow MIR converter wiring (COMPL-13)

### Phase 49: Cross-Crate & Interop Completeness
**Goal**: Generic instantiations from cross-crate call sites populate the registry, mutable statics require synchronization proof, NonNull eliminates redundant null checks, From::from contracts propagate through ?, and iterator adapters compose contracts
**Depends on**: Phase 48
**Requirements**: COMPL-04, COMPL-10, COMPL-15, COMPL-17, COMPL-18
**Success Criteria** (what must be TRUE):
  1. A generic function `fn foo<T: Clone>()` called with `T=String` from an external crate appears in `MonomorphizationRegistry` and produces a monomorphized VC set; verified with a cross-crate test fixture
  2. A function reading a `static mut` variable without a lock generates a `DataRaceFreedom` VC that Z3 resolves as SAT; wrapping the access in a `Mutex` makes the VC UNSAT
  3. A function receiving `NonNull<u32>` does not generate a null-check VC for that pointer; a function receiving `*const u32` still generates one
  4. A function using `?` on a `Result<_, E>` where `From<E>` has a `#[ensures]` contract propagates that postcondition at the `?` call site; verified by Z3
  5. An iterator chain `iter.filter(|x| x > 0).map(|x| x * 2)` generates composed SMT contracts rather than `BoolLit(true)` fallbacks; the element-level postcondition flows from source through filter through map
**Plans:** 4/4 plans complete
Plans:
- [ ] 49-01-PLAN.md — Cross-crate generic registry population + V060 for uncontracted externals (COMPL-10)
- [ ] 49-02-PLAN.md — NonNull encoding + mutable static DataRaceFreedom VCs (COMPL-15, COMPL-17)
- [ ] 49-03-PLAN.md — From::from at ? operator + iterator adapter contract composition (COMPL-18, COMPL-04)
- [ ] 49-04-PLAN.md — Gap closure: From::from VCGen wiring + iterator adapter VCGen wiring (COMPL-18, COMPL-04)

### Phase 50: Stdlib Ptr/Mem & Unsafe Boundary
**Goal**: Low-level pointer and memory operation contracts are available, FFI functions are modeled as opaque callees, transmute is encoded with size/alignment checks, and the async multi-threaded limitation is formally documented
**Depends on**: Phase 49
**Requirements**: COMPL-23, COMPL-24, COMPL-25, LANG-15, LANG-16
**Success Criteria** (what must be TRUE):
  1. `std::ptr::copy_nonoverlapping(src, dst, n)` generates overlap and alignment VCs; calling it with known-overlapping pointers produces a Z3 SAT counterexample
  2. `std::mem::swap(&mut a, &mut b)` has a contract ensuring `a_post == b_pre && b_post == a_pre`; a function verified to use `swap` inherits this postcondition
  3. An `extern "C"` function without a user contract generates a V060 opaque-callee warning; adding `#[requires]`/`#[ensures]` to the extern item silences the warning and the contracts are used at call sites
  4. `std::mem::transmute::<u32, f32>(x)` generates a size-compatibility VC (both types are 4 bytes) and an alignment VC; `transmute::<u8, u32>` generates a SAT VC (size mismatch)
  5. Running `cargo verify` on an async function that spawns threads produces a documented warning `W080: async multi-threaded execution not modeled — sequential polling assumed`; the function still verifies under sequential model
**Plans:** 3/3 plans complete
Plans:
- [ ] 50-01-PLAN.md — Ptr/mem stdlib contracts with overlap, alignment, and exchange VCs (COMPL-23, COMPL-24)
- [ ] 50-02-PLAN.md — FFI V110 opaque callee + transmute VCs + MaybeUninit ghost state (LANG-15, LANG-16)
- [ ] 50-03-PLAN.md — W080 async multi-threaded sequential model warning (COMPL-25)

### Phase 51: Core Language Features I
**Goal**: Const generic parameters participate in verification, HRTB are encoded, union field access generates reinterpretation VCs, Drop invocations are modeled at scope exit, and Pin move-prevention is enforced
**Depends on**: Phase 50
**Requirements**: LANG-01, LANG-02, LANG-03, LANG-04, LANG-05
**Success Criteria** (what must be TRUE):
  1. A function `fn first<T, const N: usize>(arr: [T; N]) -> T` with `#[requires(N > 0)]` verifies with N encoded as an SMT integer constant; a call site with `N=0` produces a precondition violation counterexample
  2. A function `fn apply<F: for<'a> Fn(&'a i32) -> i32>(f: F)` with a `fn_spec` contract verifies; the `for<'a>` bound is encoded as a universally quantified SMT constraint
  3. A `union U { f: u32, g: f32 }` field read generates a reinterpretation-cast VC asserting bitwise equivalence; reading an uninitialized union variant generates a safety VC caught by Z3
  4. A function whose local variable implements `Drop` generates a drop-order model at scope exit; a type with `Drop` that also has `Copy` generates a compile-time diagnostic (sound rejection)
  5. A function calling `Pin::new_unchecked(&mut val)` on a non-`Unpin` type generates a move-prevention VC; code that subsequently moves the pinned value produces a Z3 SAT counterexample
**Plans:** 3/3 plans complete
Plans:
- [ ] 51-01-PLAN.md — IR type foundations + const generic verification (LANG-01)
- [ ] 51-02-PLAN.md — HRTB encoding + union type VCs (LANG-02, LANG-03)
- [ ] 51-03-PLAN.md — Drop scope-exit modeling + Pin move-prevention (LANG-04, LANG-05)
### Phase 52: Advanced Type System Features
**Goal**: catch_unwind is modeled, impl Trait return types are resolved for verification, GATs produce well-formedness constraints, trait upcasting preserves contracts, and negative impls strengthen assumptions
**Depends on**: Phase 51
**Requirements**: LANG-06, LANG-07, LANG-08, LANG-09, LANG-10
**Success Criteria** (what must be TRUE):
  1. A function calling `catch_unwind(|| { ... })` models the closure as an exception boundary; contracts on the closure body are checked; cleanup code after the closure is verified under both panic and non-panic paths
  2. A function returning `impl Iterator<Item=i32>` with `#[ensures(result.len() > 0)]` resolves the concrete type and verifies the postcondition; RPITIT contracts are inferred from the trait's spec
  3. A GAT `type Item<'a>` with a `where Self: 'a` bound generates a well-formedness SMT assertion at use sites; a violating instantiation produces a Z3 SAT counterexample
  4. Casting `dyn SubTrait` to `dyn SuperTrait` generates a vtable compatibility VC; contracts on `SuperTrait` methods are preserved and checked at call sites on the upcast reference
  5. A type with `impl !Send for MyType` recorded in the trait database causes any function that transfers `MyType` across a thread boundary to generate a `ThreadSafety` VC that Z3 resolves as SAT (violation)
**Plans:** 3/3 plans complete
Plans:
- [ ] 52-01-PLAN.md — impl Trait/RPITIT resolution + Ty::Opaque fallback (LANG-07)
- [ ] 52-02-PLAN.md — catch_unwind dual-path VCs + negative trait impls (LANG-06, LANG-10)
- [ ] 52-03-PLAN.md — GAT well-formedness + trait upcasting (LANG-08, LANG-09)

### Phase 53: Operator & Smart Pointer Verification
**Goal**: Operator overloads are verified for algebraic properties, custom Deref is checked for purity, Index/IndexMut contracts enforce panic-freedom, and unsafe Send/Sync impls are validated
**Depends on**: Phase 52
**Requirements**: LANG-11, LANG-12, LANG-13, LANG-14
**Success Criteria** (what must be TRUE):
  1. An `impl Add for Vector2D` with a `#[ensures(result.x == self.x + rhs.x)]` contract verifies; a commutativity property `a + b == b + a` can be stated as an `#[ensures]` and Z3 proves it for a commutative impl
  2. An `impl Deref for MyBox<T>` is verified as pure (no observable side effects); an impl that modifies state generates a purity-violation diagnostic
  3. An `impl Index<usize> for MyVec<T>` with `#[requires(index < self.len())]` is verified for panic-freedom; a call site that cannot prove the precondition produces a Z3 SAT counterexample naming the index value
  4. A type with `unsafe impl Send for MyType` generates a thread-safety VC; the verifier checks that all fields reachable from `MyType` are either `Send` themselves or guarded by synchronization primitives
**Plans:** 3 plans
Plans:
- [ ] 48-01-PLAN.md — Trigger inference datatype filter (COMPL-08) + IR type foundations
- [ ] 48-02-PLAN.md — RefCell ghost state VCs + two-phase borrow modeling (COMPL-09, COMPL-13)
- [ ] 48-03-PLAN.md — Partial struct moves + borrow splitting (COMPL-14, COMPL-16)

### Phase 54: Stdlib Contracts Batch I
**Goal**: Eight additional standard library collection types have SMT contracts available for verification, expanding zero-config coverage to all common collection types
**Depends on**: Phase 46 (depends on SMT datatype encoding for collection element modeling)
**Requirements**: STDLIB-01, STDLIB-02, STDLIB-03, STDLIB-04, STDLIB-05, STDLIB-06, STDLIB-07, STDLIB-08
**Success Criteria** (what must be TRUE):
  1. A function using `HashSet::insert` and `HashSet::contains` verifies with contracts asserting membership semantics — `contains(x)` is true after `insert(x)`, false after `remove(x)`
  2. A function using `VecDeque::push_front`/`pop_back` verifies with FIFO ordering contracts; element count postconditions are Z3-provable
  3. A function using `BTreeMap::insert` verifies with a sorted invariant contract; a postcondition asserting `k1 < k2 => map[k1]` appears before `map[k2]` is Z3-provable
  4. A function using `BinaryHeap::push` verifies with a heap invariant contract; `heap.peek()` is guaranteed to return the maximum element after insertion
  5. `Cell::get`/`set` and `OnceCell::get_or_init` each have contracts verifiable in zero-config mode; a function using `OnceCell` to lazily initialize a value verifies that the value is set exactly once
**Plans:** 3 plans
Plans:
- [ ] 48-01-PLAN.md — Trigger inference datatype filter (COMPL-08) + IR type foundations
- [ ] 48-02-PLAN.md — RefCell ghost state VCs + two-phase borrow modeling (COMPL-09, COMPL-13)
- [ ] 48-03-PLAN.md — Partial struct moves + borrow splitting (COMPL-14, COMPL-16)

### Phase 55: Stdlib Contracts Batch II & Iterators
**Goal**: Path/OsStr/format! are modeled, iterator protocol contracts enable for-loop verification over custom iterators, and inline asm is treatable as an opaque block with user contracts
**Depends on**: Phase 54
**Requirements**: STDLIB-09, STDLIB-10, STDLIB-11, STDLIB-12, STDLIB-13, STDLIB-14, STDLIB-15
**Success Criteria** (what must be TRUE):
  1. A function using `Path::join` verifies with a contract ensuring the result path contains the base path as a prefix; `canonicalize` is modeled as an opaque function returning an absolute path
  2. A custom struct implementing `DoubleEndedIterator` with `#[ensures]` on `next_back()` has those contracts checked during a `rev()` for-loop; element ordering postconditions are Z3-provable
  3. `collect::<Vec<_>>()` from an iterator preserves element-level contracts — if the source iterator has `#[ensures(item > 0)]` on `next()`, the collected `Vec` satisfies the corresponding `forall` postcondition
  4. A custom struct implementing `Iterator::next()` with `#[requires]`/`#[ensures]` contracts has those contracts used as the loop body spec during `for item in my_iter` VCGen; the for-loop verifies against the custom contracts
  5. An `unsafe { asm!(...) }` block with `#[unsafe_requires]`/`#[unsafe_ensures]` user-provided contracts generates VCs from those contracts at the asm call site; without contracts, it generates a V060 opaque warning
**Plans:** 3 plans
Plans:
- [ ] 48-01-PLAN.md — Trigger inference datatype filter (COMPL-08) + IR type foundations
- [ ] 48-02-PLAN.md — RefCell ghost state VCs + two-phase borrow modeling (COMPL-09, COMPL-13)
- [ ] 48-03-PLAN.md — Partial struct moves + borrow splitting (COMPL-14, COMPL-16)

### Phase 56: Async & Concurrency Extensions
**Goal**: Async closures are verified with combined capture and state machine specs, async streams are modeled as repeated polls, cancellation safety is checkable at each await point, and Condvar/Barrier/thread-local/fence concurrency primitives have SMT models
**Depends on**: Phase 50 (async foundation), Phase 53 (concurrency foundation)
**Requirements**: ASYNC-01, ASYNC-02, ASYNC-03, CONC-01, CONC-02, CONC-03, CONC-04
**Success Criteria** (what must be TRUE):
  1. An `async || { ... }` closure with `#[state_invariant]` verifies that the invariant holds at each `await` suspension point inside the closure body; captured mutable state is tracked via SSA versioning
  2. An async stream type with `poll_next()` implementing `Stream` trait verifies that each poll either produces `Some(item)` satisfying the item contract or `None` signaling termination; bounded unrolling covers N iterations
  3. A future dropped at any `.await` point inside `select!` leaves all guarded state satisfying the pre-drop invariant; a function annotated `#[cancellation_safe]` is verified to hold this property across all await points
  4. A function using `Condvar::wait` generates VCs asserting: (a) the predicate holds on wakeup (spurious wakeup handled), (b) the mutex is held on both entry and exit; `notify_one`/`notify_all` VCs assert the predicate is established before notification
  5. A `Barrier::wait()` usage verifies that all participating threads reach the barrier before any proceeds; `thread_local!` storage generates no cross-thread access VCs; `fence(Ordering::SeqCst)` appears as a synchronization edge in the RC11 execution graph
**Plans:** 3 plans
Plans:
- [ ] 48-01-PLAN.md — Trigger inference datatype filter (COMPL-08) + IR type foundations
- [ ] 48-02-PLAN.md — RefCell ghost state VCs + two-phase borrow modeling (COMPL-09, COMPL-13)
- [ ] 48-03-PLAN.md — Partial struct moves + borrow splitting (COMPL-14, COMPL-16)

## Progress

| Phase | Milestone | Plans Complete | Status | Completed |
|-------|-----------|----------------|--------|-----------|
| 1-5 | v0.1 | 17/17 | Complete | 2026-02-12 |
| 6-12 | v0.2 | 21/21 | Complete | 2026-02-14 |
| 13-18 | v0.3 | 20/20 | Complete | 2026-02-17 |
| 19-27 | v0.4 | 27/27 | Complete | 2026-02-23 |
| 28-29 | v0.5 | 10/10 | Complete | 2026-02-25 |
| 29.1-33 | v0.5-audit | 22/22 | Complete | 2026-02-27 |
| 34-37.1 | v0.6 | 11/11 | Complete | 2026-03-02 |
| 38-44 + generics-fix | v0.7 | 14/14 | Complete | 2026-03-04 |
| 45 | 2/2 | Complete    | 2026-03-05 | - |
| 46 | 3/3 | Complete    | 2026-03-05 | - |
| 47 | 3/3 | Complete    | 2026-03-05 | - |
| 48 | 4/4 | Complete    | 2026-03-06 | - |
| 49 | 4/4 | Complete    | 2026-03-06 | - |
| 50 | 3/3 | Complete    | 2026-03-07 | - |
| 51 | 3/3 | Complete   | 2026-03-07 | - |
| 52 | 3/3 | Complete   | 2026-03-07 | - |
| 53 | v0.8 | 0/? | Not started | - |
| 54 | v0.8 | 0/? | Not started | - |
| 55 | v0.8 | 0/? | Not started | - |
| 56 | v0.8 | 0/? | Not started | - |
