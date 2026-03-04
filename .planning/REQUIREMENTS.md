# Requirements: rust-fv

**Defined:** 2026-03-04
**Core Value:** Sound, automated verification of Rust code properties with minimal developer burden

## v0.8 Requirements

Requirements for v0.8 Completeness & Coverage milestone. Each maps to roadmap phases.

### Completeness — Partial → Complete (COMPL)

- [ ] **COMPL-01**: Struct/enum types encoded as SMT `declare-datatype` with constructors, selectors, and testers instead of uninterpreted sorts
- [ ] **COMPL-02**: Pointer cast alignment VCs generated (`addr % align_of::<T>() == 0`) for `*const u8 -> *const u32` style casts
- [ ] **COMPL-03**: CastKind variants (IntToInt, FloatToInt, IntToFloat, PtrToPtr) disambiguated and encoded correctly in MIR converter
- [ ] **COMPL-04**: Iterator adapter chaining (filter, map, etc.) composes contracts instead of falling back to `BoolLit(true)`
- [ ] **COMPL-05**: Functional update on projected places generates correct `mk-StructName` SMT terms for all rvalue types
- [ ] **COMPL-06**: Spec validation errors propagated as driver diagnostics instead of silently logged
- [ ] **COMPL-07**: Z3 native backend supports `Int` sort via `z3::Sort::int()`
- [ ] **COMPL-08**: Quantifier trigger inference filters out datatype selector symbols from candidate lists
- [ ] **COMPL-09**: `RefCell<T>` runtime borrow count tracked as ghost state with exclusivity VCs for `borrow()`/`borrow_mut()`
- [ ] **COMPL-10**: Cross-crate generic instantiations fully captured in MonomorphizationRegistry
- [ ] **COMPL-11**: `Rvalue::Repeat` (`[expr; N]`) encoded as universally quantified equality or const-array store chain
- [ ] **COMPL-12**: Silent match arm fallthrough cases in vcgen.rs audited and either handled or explicitly documented
- [ ] **COMPL-13**: Two-phase borrowing modeled for method calls like `vec.push(vec.len())`
- [ ] **COMPL-14**: Partial struct moves tracked per-field with use-after-partial-move VCs
- [ ] **COMPL-15**: Mutable static access generates data-race VCs requiring synchronization
- [ ] **COMPL-16**: Borrow splitting allows simultaneous `&mut s.x` and `&s.y` verified as disjoint
- [ ] **COMPL-17**: `NonNull<T>` encoded with non-null precondition, redundant null checks eliminated
- [ ] **COMPL-18**: `From::from()` conversion contracts verified at `?` operator usage sites
- [ ] **COMPL-19**: For-loop VCGen unit tests wired to match E2E behavior (8 RED tests → GREEN)
- [ ] **COMPL-20**: SetDiscriminant VCGen verified as fully functional (not no-op) with end-to-end test
- [ ] **COMPL-21**: Ghost local assignment guard (`is_ghost_place`) verified working with regression test
- [ ] **COMPL-22**: `uses_spec_int_types()` detection verified complete with regression test
- [ ] **COMPL-23**: `std::ptr::read`/`write`/`copy`/`copy_nonoverlapping` stdlib contracts with overlap and alignment VCs
- [ ] **COMPL-24**: `std::mem::swap`/`replace` stdlib contracts ensuring correct value exchange
- [ ] **COMPL-25**: Async multi-threaded execution model documented as known limitation with clear boundary

### Core Language Features (LANG)

- [ ] **LANG-01**: Const generic parameters (`<const N: usize>`) extracted from MIR, encoded as SMT integer constants, substituted during monomorphization
- [ ] **LANG-02**: Higher-ranked trait bounds (`for<'a> F: Fn(&'a T)`) parsed and encoded as universally quantified lifetime constraints
- [ ] **LANG-03**: Union types recognized as ADTs with field access encoded as reinterpretation casts and safety VCs for reads
- [ ] **LANG-04**: `Drop::drop()` invocations modeled at end of scope, drop order verified, double-drop prevention VCs generated
- [ ] **LANG-05**: `Pin<P>` modeled as transparent wrapper with move-prevention invariant; `Pin::new_unchecked` callers verified
- [ ] **LANG-06**: `catch_unwind` modeled as exception-catching boundary with cleanup verification during unwinding
- [ ] **LANG-07**: `impl Trait` in return position resolved to concrete types for verification; RPITIT contracts inferred from trait specs
- [ ] **LANG-08**: Generic Associated Types (GATs) with parameterized associated types and well-formedness constraints
- [ ] **LANG-09**: Trait upcasting (`dyn SubTrait` → `dyn SuperTrait`) modeled with vtable compatibility and contract preservation
- [ ] **LANG-10**: Negative trait implementations (`impl !Trait`) recorded in trait database and used to strengthen verification assumptions
- [ ] **LANG-11**: Operator overloading `impl Add`/`Sub`/`Ord` verified for mathematical properties (commutativity, total order, etc.)
- [ ] **LANG-12**: Custom `Deref`/`DerefMut` implementations verified for purity and invariant preservation
- [ ] **LANG-13**: Custom `Index`/`IndexMut` implementations verified for panic-freedom and contract satisfaction
- [ ] **LANG-14**: Unsafe `Send`/`Sync` impls verified for soundness — types implementing `Send` can safely cross threads, `Sync` allows shared access
- [ ] **LANG-15**: FFI (`extern "C"`) functions modeled as opaque callees with user-specified contracts; `#[repr(C)]` layout verified
- [ ] **LANG-16**: `transmute` modeled as bitwise reinterpretation with size/alignment compatibility VCs; `MaybeUninit<T>` initialization state tracked

### Pattern Matching (PAT)

- [ ] **PAT-01**: `let`-`else` patterns verified via MIR desugaring with integration test covering diverging else path
- [ ] **PAT-02**: Slice patterns (`[first, .., last]`) verified with length-guarded destructuring VCs
- [ ] **PAT-03**: Range patterns in match (`1..=5`) verified via SwitchInt with integration test
- [ ] **PAT-04**: `@` bindings in patterns verified via MIR desugaring with integration test

### Standard Library Contracts (STDLIB)

- [ ] **STDLIB-01**: `HashSet<T>` contracts for insert/remove/contains modeled as unordered set in SMT
- [ ] **STDLIB-02**: `VecDeque<T>` contracts for push_front/push_back/pop_front/pop_back with ring buffer semantics
- [ ] **STDLIB-03**: `BTreeMap<K,V>` / `BTreeSet<T>` contracts maintaining sorted invariant modeled as sorted sequence
- [ ] **STDLIB-04**: `BinaryHeap<T>` contracts maintaining heap invariant
- [ ] **STDLIB-05**: `LinkedList<T>` contracts modeled as SMT sequence with front/back access
- [ ] **STDLIB-06**: `Weak<T>` contracts for `new`/`upgrade` with strong-count-zero failure modeling
- [ ] **STDLIB-07**: `Cell<T>` interior mutability contracts for `get`/`set` modeled as mutable state through shared references
- [ ] **STDLIB-08**: `OnceCell<T>` / `OnceLock<T>` one-time initialization invariant verified for get-or-init patterns
- [ ] **STDLIB-09**: `Path` / `PathBuf` join/push invariant contracts and canonicalization safety
- [ ] **STDLIB-10**: `DoubleEndedIterator` reverse iteration contracts with `next_back()` and `rev()` adapter verification
- [ ] **STDLIB-11**: `collect()` / `FromIterator` contract preserving element-level properties across collection conversion
- [ ] **STDLIB-12**: Custom `Iterator::next()` implementations accept `#[ensures]`/`#[requires]` contracts used during for-loop verification
- [ ] **STDLIB-13**: `format!` / `write!` macros treated as opaque with optional format-string type verification
- [ ] **STDLIB-14**: `OsStr` / `OsString` platform-specific string representation contracts
- [ ] **STDLIB-15**: `inline asm!` blocks treated as opaque with user-specified contracts

### Async Extensions (ASYNC)

- [ ] **ASYNC-01**: Async closures (`async || {}`) detected as coroutine-producing closures with combined capture + state machine verification
- [ ] **ASYNC-02**: Async streams / async iterators modeled as repeated polls of a stream future
- [ ] **ASYNC-03**: Cancellation safety verified — dropping a future at any `.await` point leaves state consistent; `select!` branch safety checked

### Concurrency Extensions (CONC)

- [ ] **CONC-01**: `Condvar` wait/notify operations modeled with spurious wakeup handling and predicate-holds-on-wakeup verification
- [ ] **CONC-02**: `Barrier` synchronization modeled with all-threads-reach-before-proceed verification
- [ ] **CONC-03**: Thread-local storage (`thread_local!`) modeled as per-thread state with no cross-thread access
- [ ] **CONC-04**: Standalone `fence()` operations modeled as synchronization points in RC11 execution graph

## v2 Requirements

Deferred to future release. Tracked but not in current roadmap.

### Nightly/Experimental

- **NIGHTLY-01**: Trait specialization — overlapping impls verification
- **NIGHTLY-02**: `dyn*` thin trait objects
- **NIGHTLY-03**: Type alias impl trait (TAIT)
- **NIGHTLY-04**: Trait aliases
- **NIGHTLY-05**: `Try` trait for custom types beyond Result/Option

### Research-Level

- **RESEARCH-01**: Liveness properties — temporal logic for async termination and progress guarantees
- **RESEARCH-02**: Multi-threaded async — combined coroutine state machines with RC11 memory model
- **RESEARCH-03**: Variance/covariance verification — PhantomData markers and unsound lifetime extension
- **RESEARCH-04**: Custom allocator (`GlobalAlloc`) verification

## Out of Scope

| Feature | Reason |
|---------|--------|
| Forked Rust compiler | Zero-friction `cargo verify` workflow is key differentiator |
| Custom SMT solver | Use Z3/CVC5 ecosystem |
| Full dependent types | Academic complexity; stick to refinement types |
| Interactive theorem proving | Automated verification focus |
| GPU/SIMD verification | Specialized domain |
| Probabilistic verification | Deterministic proof only |
| Dynamic linking verification | Beyond single-crate analysis scope |
| Runtime reflection | Not applicable to static verification |
| Macro correctness | Macros expand before MIR; verifier sees expanded code |

## Traceability

Which phases cover which requirements. Updated during roadmap creation.

| Requirement | Phase | Status |
|-------------|-------|--------|
| COMPL-01 | Phase 46 | Pending |
| COMPL-02 | Phase 47 | Pending |
| COMPL-03 | Phase 47 | Pending |
| COMPL-04 | Phase 49 | Pending |
| COMPL-05 | Phase 46 | Pending |
| COMPL-06 | Phase 47 | Pending |
| COMPL-07 | Phase 46 | Pending |
| COMPL-08 | Phase 48 | Pending |
| COMPL-09 | Phase 48 | Pending |
| COMPL-10 | Phase 49 | Pending |
| COMPL-11 | Phase 46 | Pending |
| COMPL-12 | Phase 47 | Pending |
| COMPL-13 | Phase 48 | Pending |
| COMPL-14 | Phase 48 | Pending |
| COMPL-15 | Phase 49 | Pending |
| COMPL-16 | Phase 48 | Pending |
| COMPL-17 | Phase 49 | Pending |
| COMPL-18 | Phase 49 | Pending |
| COMPL-19 | Phase 45 | Pending |
| COMPL-20 | Phase 45 | Pending |
| COMPL-21 | Phase 45 | Pending |
| COMPL-22 | Phase 45 | Pending |
| COMPL-23 | Phase 50 | Pending |
| COMPL-24 | Phase 50 | Pending |
| COMPL-25 | Phase 50 | Pending |
| LANG-01 | Phase 51 | Pending |
| LANG-02 | Phase 51 | Pending |
| LANG-03 | Phase 51 | Pending |
| LANG-04 | Phase 51 | Pending |
| LANG-05 | Phase 51 | Pending |
| LANG-06 | Phase 52 | Pending |
| LANG-07 | Phase 52 | Pending |
| LANG-08 | Phase 52 | Pending |
| LANG-09 | Phase 52 | Pending |
| LANG-10 | Phase 52 | Pending |
| LANG-11 | Phase 53 | Pending |
| LANG-12 | Phase 53 | Pending |
| LANG-13 | Phase 53 | Pending |
| LANG-14 | Phase 53 | Pending |
| LANG-15 | Phase 50 | Pending |
| LANG-16 | Phase 50 | Pending |
| PAT-01 | Phase 45 | Pending |
| PAT-02 | Phase 45 | Pending |
| PAT-03 | Phase 45 | Pending |
| PAT-04 | Phase 45 | Pending |
| STDLIB-01 | Phase 54 | Pending |
| STDLIB-02 | Phase 54 | Pending |
| STDLIB-03 | Phase 54 | Pending |
| STDLIB-04 | Phase 54 | Pending |
| STDLIB-05 | Phase 54 | Pending |
| STDLIB-06 | Phase 54 | Pending |
| STDLIB-07 | Phase 54 | Pending |
| STDLIB-08 | Phase 54 | Pending |
| STDLIB-09 | Phase 55 | Pending |
| STDLIB-10 | Phase 55 | Pending |
| STDLIB-11 | Phase 55 | Pending |
| STDLIB-12 | Phase 55 | Pending |
| STDLIB-13 | Phase 55 | Pending |
| STDLIB-14 | Phase 55 | Pending |
| STDLIB-15 | Phase 55 | Pending |
| ASYNC-01 | Phase 56 | Pending |
| ASYNC-02 | Phase 56 | Pending |
| ASYNC-03 | Phase 56 | Pending |
| CONC-01 | Phase 56 | Pending |
| CONC-02 | Phase 56 | Pending |
| CONC-03 | Phase 56 | Pending |
| CONC-04 | Phase 56 | Pending |

**Coverage:**
- v0.8 requirements: 67 total
- Mapped to phases: 67
- Unmapped: 0 ✓

---
*Requirements defined: 2026-03-04*
*Last updated: 2026-03-04 after v0.8 roadmap creation (phases 45-56)*
