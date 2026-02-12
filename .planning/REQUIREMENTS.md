# Requirements: rust-fv v0.2

**Defined:** 2026-02-12
**Core Value:** Sound, automated verification of Rust code properties with minimal developer burden

## v0.2 Requirements

Requirements for v0.2 Advanced Verification. Each maps to roadmap phases.

### Recursive Functions (REC)

- [ ] **REC-01**: Recursive functions verified via uninterpreted function encoding with axioms for base and recursive cases
- [ ] **REC-02**: `#[decreases(expr)]` annotation specifies termination measure that must decrease on every recursive call
- [ ] **REC-03**: Termination VC generated: measure at recursive call site strictly less than measure at function entry
- [ ] **REC-04**: Mutual recursion detected via call graph SCC analysis and verified with shared termination metrics
- [ ] **REC-05**: Non-terminating recursive function (missing or invalid `#[decreases]`) rejected by verifier

### Closures (CLO)

- [ ] **CLO-01**: Closure environment captured variables encoded as SMT datatype (struct-like)
- [ ] **CLO-02**: Closure call desugared to function call with explicit environment parameter
- [ ] **CLO-03**: Fn trait closures (immutable captures) verified with closure contract at call site
- [ ] **CLO-04**: FnMut closures (mutable captures) verified using prophecy variables for captured &mut state
- [ ] **CLO-05**: FnOnce closures (consuming captures) verified with ownership transfer semantics
- [ ] **CLO-06**: Closure contracts specifiable via `#[requires]`/`#[ensures]` on closure-accepting functions

### Trait Objects (TRT)

- [ ] **TRT-01**: Trait-level contracts (`#[requires]`/`#[ensures]` on trait methods) verified for each implementing type
- [ ] **TRT-02**: Dynamic dispatch (`dyn Trait`) call sites use trait-level contracts (not implementation-specific)
- [ ] **TRT-03**: Each `impl Trait for Type` verified to satisfy trait-level method contracts (behavioral subtyping)
- [ ] **TRT-04**: Sealed traits (`pub(crate)` or `#[sealed]`) use closed-world verification (enumerate all impls)
- [ ] **TRT-05**: Public traits use open-world verification (uninterpreted functions, no impl assumptions)

### Lifetime Reasoning (LIF)

- [ ] **LIF-01**: Lifetime parameters tracked through function signatures and borrow chains
- [ ] **LIF-02**: Borrow expiry verification using prophecy variables (final value after lifetime ends)
- [ ] **LIF-03**: Lifetime bounds (`T: 'a`) checked statically and encoded as SMT outlives constraints
- [ ] **LIF-04**: NLL-based (non-lexical) lifetime tracking using control-flow-sensitive analysis
- [ ] **LIF-05**: SSA-based parameter encoding resolves prophecy limitation with direct &mut param reassignment
- [ ] **LIF-06**: Reborrow chains tracked through MIR borrow graph

### Unsafe Code (USF)

- [ ] **USF-01**: Unsafe blocks detected and flagged in verification output with source location
- [ ] **USF-02**: Raw pointer dereference generates null-check VC (`ptr != null`)
- [ ] **USF-03**: Pointer arithmetic generates bounds-check VC (`offset < allocation_size`)
- [ ] **USF-04**: `#[unsafe_requires]`/`#[unsafe_ensures]` annotations for unsafe function contracts
- [ ] **USF-05**: `#[verifier::trusted]` annotation marks functions as axiomatically correct (skip verification body)
- [ ] **USF-06**: Unsafe code with no annotations produces warning (not hard error) with suggestion to add contracts

### Floating-Point (FPV)

- [ ] **FPV-01**: `f32` mapped to SMT `(_ FloatingPoint 8 24)` and `f64` to `(_ FloatingPoint 11 53)` (IEEE 754)
- [ ] **FPV-02**: Float arithmetic encoded with rounding mode (default RNE: round-to-nearest, ties-to-even)
- [ ] **FPV-03**: NaN propagation VCs generated for all float operations (`!fp.isNaN(result)`)
- [ ] **FPV-04**: Infinity checks generated for operations that may overflow to Inf
- [ ] **FPV-05**: Float comparison respects IEEE 754 semantics (NaN != NaN, -0.0 == +0.0)
- [ ] **FPV-06**: Performance warning emitted when floating-point verification enabled (FPA theory 2-10x slower)

### Concurrency (CON)

- [ ] **CON-01**: Thread spawn sites detected from MIR and encoded with thread-local state
- [ ] **CON-02**: Happens-before relations encoded as partial order in SMT for synchronization points
- [ ] **CON-03**: Data race freedom VCs generated for shared mutable state across threads
- [ ] **CON-04**: Atomic operations (SeqCst) encoded with total ordering constraints
- [ ] **CON-05**: Bounded verification with configurable max threads and context switches (prevent state explosion)
- [ ] **CON-06**: Mutex/RwLock invariants verifiable via `#[lock_invariant]` annotation

### Infrastructure (INF)

- [ ] **INF-01**: `petgraph` dependency added for call graph SCC analysis (recursive function detection)
- [ ] **INF-02**: `VcKind` enum extended with Termination, ClosureWellFormed, DynamicDispatch, MemorySafety, BorrowValidity, FloatingPointNaN, DataRaceFreedom
- [ ] **INF-03**: Diagnostics extended with feature-specific error messages and fix suggestions per new VcKind
- [ ] **INF-04**: Each feature has dedicated soundness tests (incorrect programs rejected) and completeness tests (correct programs verified)

## v0.3+ Requirements (Deferred)

### Advanced Closures

- **ACLO-01**: Higher-order function verification with specification entailments (Fn trait bounds as contracts)
- **ACLO-02**: Iterator combinator verification (map, filter, fold with closure contracts)

### Advanced Unsafe

- **AUSF-01**: Bounded model checking for unsafe code (Kani-style bounded exploration)
- **AUSF-02**: Separation logic integration for heap reasoning (Prusti-style)

### Advanced Concurrency

- **ACON-01**: Weak memory model support (Relaxed, Acquire, Release atomics)
- **ACON-02**: Async/await verification (Future trait, executor semantics)
- **ACON-03**: Deadlock detection for Mutex/RwLock ordering

### Ecosystem

- **ECO-01**: Standard library contracts for Vec, HashMap, Option, Result
- **ECO-02**: Trigger customization (`#[trigger]`) for quantifier performance tuning
- **ECO-03**: Z3 bv2int native integration
- **ECO-04**: VSCode extension for real-time verification feedback
- **ECO-05**: rust-analyzer integration for inline diagnostics

## Out of Scope

| Feature | Reason |
|---------|--------|
| Forked Rust compiler | Zero-friction cargo workflow is key differentiator |
| Fully automatic verification (no annotations) | Undecidable for general programs; 80-90% automation target |
| Full dependent types | Academic complexity; stick to refinement types |
| Custom SMT solver | Use Z3/CVC5 ecosystem |
| Formal proof certificates | Too heavy for developer workflow |
| Windows support | Focus on macOS/Linux first |
| Automatic closure contract inference | Requires specification entailments (academic frontier) |
| General recursion without decreases clause | Termination undecidable; unsound to assume |
| Full separation logic for unsafe | Years of research effort; use conservative approximations |
| Weak memory models (v0.2) | Sequential consistency first; relaxed atomics deferred |

## Traceability

| Requirement | Phase | Status |
|-------------|-------|--------|
| REC-01 | Pending | Pending |
| REC-02 | Pending | Pending |
| REC-03 | Pending | Pending |
| REC-04 | Pending | Pending |
| REC-05 | Pending | Pending |
| CLO-01 | Pending | Pending |
| CLO-02 | Pending | Pending |
| CLO-03 | Pending | Pending |
| CLO-04 | Pending | Pending |
| CLO-05 | Pending | Pending |
| CLO-06 | Pending | Pending |
| TRT-01 | Pending | Pending |
| TRT-02 | Pending | Pending |
| TRT-03 | Pending | Pending |
| TRT-04 | Pending | Pending |
| TRT-05 | Pending | Pending |
| LIF-01 | Pending | Pending |
| LIF-02 | Pending | Pending |
| LIF-03 | Pending | Pending |
| LIF-04 | Pending | Pending |
| LIF-05 | Pending | Pending |
| LIF-06 | Pending | Pending |
| USF-01 | Pending | Pending |
| USF-02 | Pending | Pending |
| USF-03 | Pending | Pending |
| USF-04 | Pending | Pending |
| USF-05 | Pending | Pending |
| USF-06 | Pending | Pending |
| FPV-01 | Pending | Pending |
| FPV-02 | Pending | Pending |
| FPV-03 | Pending | Pending |
| FPV-04 | Pending | Pending |
| FPV-05 | Pending | Pending |
| FPV-06 | Pending | Pending |
| CON-01 | Pending | Pending |
| CON-02 | Pending | Pending |
| CON-03 | Pending | Pending |
| CON-04 | Pending | Pending |
| CON-05 | Pending | Pending |
| CON-06 | Pending | Pending |
| INF-01 | Pending | Pending |
| INF-02 | Pending | Pending |
| INF-03 | Pending | Pending |
| INF-04 | Pending | Pending |

**Coverage:**
- v0.2 requirements: 44 total
- Mapped to phases: 0 (pending roadmap creation)
- Unmapped: 44

---
*Requirements defined: 2026-02-12*
*Last updated: 2026-02-12 after v0.2 milestone research*
