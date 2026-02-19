# Architecture Integration: v0.4 Full Rust Verification

**Domain:** Compiler-integrated formal verification tool for Rust
**Researched:** 2026-02-19
**Confidence:** HIGH (based on direct codebase analysis)

---

## Existing Architecture (v0.3 Baseline)

### System Overview

```
┌─────────────────────────────────────────────────────────────┐
│                    User Code Layer                          │
│  #[requires], #[ensures], #[pure], #[invariant],            │
│  #[decreases], #[ghost], #[trigger], #[lock_invariant]      │
└────────────────┬────────────────────────────────────────────┘
                 │ proc macro expansion
┌────────────────▼────────────────────────────────────────────┐
│                   crates/macros                             │
│  Embeds specs as hidden doc attrs                           │
└────────────────┬────────────────────────────────────────────┘
                 │ rustc compilation hook
┌────────────────▼────────────────────────────────────────────┐
│                   crates/driver                             │
│  ┌─────────┐  ┌──────────┐  ┌─────────┐  ┌──────────┐      │
│  │callbacks│→ │mir_conv  │→ │parallel │→ │ cache    │      │
│  │(rustc)  │  │          │  │executor │  │(dual-hash│      │
│  └─────────┘  └──────────┘  └─────────┘  └──────────┘      │
│  ┌─────────┐  ┌──────────┐                                  │
│  │json_out │  │diagnostic│                                  │
│  └─────────┘  └──────────┘                                  │
└────────────────┬────────────────────────────────────────────┘
                 │ IR + VCGen
┌────────────────▼────────────────────────────────────────────┐
│                  crates/analysis                            │
│  ┌──────┐  ┌──────┐  ┌─────────┐  ┌──────────┐             │
│  │ ir   │→ │vcgen │→ │ encode  │→ │contract  │             │
│  │      │  │      │  │term/sort│  │   db     │             │
│  └──────┘  └──────┘  └─────────┘  └──────────┘             │
│  concurrency/ (happens_before, thread_encoding,             │
│               lock_invariants, channel_verification,        │
│               deadlock_detection)                           │
│  defunctionalize.rs  closure_analysis.rs                    │
│  behavioral_subtyping.rs  heap_model.rs                     │
│  encode_prophecy.rs  encode_quantifier.rs                   │
│  borrow_conflict.rs  monomorphize.rs  bv2int.rs             │
│  stdlib_contracts/  trait_analysis.rs                       │
└────────────────┬────────────────────────────────────────────┘
                 │ SMT-LIB2 AST
┌────────────────▼────────────────────────────────────────────┐
│                   crates/smtlib                             │
│  Term, Sort, Command, Script, Formatter                     │
└────────────────┬────────────────────────────────────────────┘
                 │ check_sat
┌────────────────▼────────────────────────────────────────────┐
│                   crates/solver                             │
│  SolverBackend trait                                        │
│  Z3Process / Z3Native / Cvc5Process / YicesProcess          │
│  SolverResult { Sat(Option<Model>), Unsat, Unknown }        │
└─────────────────────────────────────────────────────────────┘
```

### Crate Responsibilities

| Crate | Responsibility | Key Files |
|-------|----------------|-----------|
| **macros/** | Proc macros: #[requires], #[ensures], etc. → hidden doc attrs | `lib.rs` |
| **driver/** | rustc integration, MIR→IR, parallel execution, dual-hash cache, JSON output | `callbacks.rs`, `mir_converter.rs`, `parallel.rs`, `cache.rs` |
| **analysis/** | IR, VCGen, SMT encoding, all verification logic modules | `ir.rs`, `vcgen.rs`, `concurrency/`, `defunctionalize.rs` |
| **smtlib/** | Pure SMT-LIB2 AST (Term, Sort, Command, Script, Formatter) | `term.rs`, `sort.rs`, `command.rs` |
| **solver/** | SolverBackend trait, subprocess/native backends, model extraction | `backend.rs`, `result.rs`, `model.rs` |

### Existing IR::Function Fields Relevant to v0.4

The `ir::Function` struct already has (confirmed from codebase):
- `atomic_ops: Vec<AtomicOp>` with `AtomicOrdering` (Relaxed/Acquire/Release/AcqRel/SeqCst)
- `thread_spawns: Vec<ThreadSpawn>`
- `sync_ops: Vec<SyncOp>`
- `lock_invariants: Vec<(String, SpecExpr)>`
- `concurrency_config: Option<ConcurrencyConfig>`
- `unsafe_blocks`, `unsafe_operations`, `unsafe_contracts`
- Closure types: `Ty::Closure(Box<ClosureInfo>)`, `ClosureTrait` (Fn/FnMut/FnOnce)
- `prophecies: Vec<ProphecyInfo>` (mutable borrow reasoning)

The `SolverResult::Sat(Option<Model>)` already carries counterexample data.
The `Model` struct already has `assignments: Vec<(String, String)>`.

---

## Feature 1: Counterexample Generation

### What Is Missing

`SolverResult::Sat(Option<Model>)` already exists and `Model` is populated by Z3/CVC5 via `(get-model)`. The gap is **presentation**: the raw SMT variable names (e.g., `_1`, `_2_add_result`) are surfaced to users as-is. There is no translation from SMT model variables back to Rust source variable names, no human-readable formatting, and no IDE-surface pathway.

### Integration Points

**Existing:**
- `solver/src/model.rs`: `Model { assignments: Vec<(String, String)> }`
- `solver/src/result.rs`: `SolverResult::Sat(Option<Model>)`
- `solver/src/parser.rs`: Parses `(get-model)` output
- `driver/src/json_output.rs`: JSON serialization layer

**New components:**

```
analysis/src/counterexample.rs   (NEW)
    CounterexampleRenderer
        - maps SMT var names → Rust source names
        - pretty-prints model assignments per Rust type
        - formats as: "x = 5, y = -3" not "_1 = #b00000101, _2 = #b11111101"

driver/src/diagnostics.rs        (MODIFY)
    - integrate CounterexampleRenderer output into Ariadne spans
    - add counterexample block below failing VC diagnostic

vscode-extension                  (MODIFY)
    - display counterexample inline below the failing line
    - JSON schema already carries model; extend to carry rendered text
```

**Data flow change:**

```
EXISTING: SolverResult::Sat(Some(model)) → "Verification failed (counterexample available)"
NEW:      SolverResult::Sat(Some(model))
              ↓
          CounterexampleRenderer::render(model, vc_location, ir_function)
              ↓
          RenderedCounterexample { variables: Vec<(String, String)>, trace: Vec<String> }
              ↓
          Ariadne diagnostic with counterexample block
          JSON output with rendered counterexample
          VSCode: inline counterexample text under failing line
```

**Variable name mapping strategy:**

The driver crate's `mir_converter.rs` constructs `ir::Function` from MIR. During that conversion, it must build a `VarNameMap: HashMap<String, String>` (SMT name → Rust source name) using MIR's `LocalDecls` which carry `source_info` (name + span). This map must be carried through to `VerificationCondition` so the renderer has access.

**Required changes:**

| Component | Change | Scope |
|-----------|--------|-------|
| `analysis/src/vcgen.rs` | Add `var_name_map: HashMap<String, String>` to `VerificationCondition` | Medium |
| `driver/src/mir_converter.rs` | Extract LocalDecls source names during conversion, pass to VCGen | Medium |
| `analysis/src/counterexample.rs` | NEW: CounterexampleRenderer, RenderedCounterexample | ~200 lines |
| `driver/src/diagnostics.rs` | Integrate rendered counterexample into Ariadne output | Medium |
| `driver/src/json_output.rs` | Add `counterexample` field to JSON failure record | Low |

**No changes needed:** smtlib, solver (model already populated), macros.

---

## Feature 2: Async/Await Verification

### How Rust Async Compiles to MIR

Rust compiles `async fn` and `async` blocks to coroutine/generator MIR (stabilized in Rust 1.75 as coroutines). In rustc's MIR:
- Each `async fn` becomes a state machine struct (the coroutine type)
- The state machine has a `resume` method with a `SwitchInt` on the coroutine state discriminant
- Each suspension point (`.await`) is a state transition: save locals to state struct fields, yield, restore on resume
- The driver's `after_analysis` hook already sees this MIR

**Confirmed:** `driver/src/mir_converter.rs` already processes MIR at the `after_analysis` phase, which includes coroutine MIR.

### Key Insight: Treat Coroutine States as Separate Functions

The verification approach for async is to treat each coroutine state (the code between two `await` points) as a separate sub-function verification problem. Each state has:
- Entry conditions: what holds when entering this state (the coroutine's invariant)
- Local variables (desugared to coroutine struct fields)
- Exit conditions: what holds when yielding or returning

### Integration Points

**New IR constructs (in `analysis/src/ir.rs`):**

```rust
/// A coroutine/async state machine derived from an async fn.
pub struct CoroutineInfo {
    /// The original async function name
    pub fn_name: String,
    /// Each suspension state (code segment between awaits)
    pub states: Vec<CoroutineState>,
    /// Fields persisted across await points (captured locals)
    pub persistent_fields: Vec<(String, Ty)>,
    /// User-provided invariant that holds across ALL states
    pub cross_state_invariant: Option<SpecExpr>,
}

pub struct CoroutineState {
    pub state_id: usize,
    /// Pre-condition entering this state
    pub entry_condition: Option<SpecExpr>,
    /// Blocks of IR code for this state segment
    pub basic_blocks: Vec<BasicBlock>,
    /// Post-condition on yield/return
    pub exit_condition: Option<SpecExpr>,
}
```

**New macros (in `crates/macros/`):**

```rust
#[async_requires(expr)]   // precondition before first await
#[async_ensures(expr)]    // postcondition on Future::Output
#[state_invariant(expr)]  // invariant preserved across all await points
```

**New analysis module:**

```
analysis/src/async_encoding.rs   (NEW)
    CoroutineFlattener
        - detect coroutine MIR pattern in ir::Function
        - split into CoroutineState segments at yield terminators
        - generate VCs for: initial state, each state transition, final state
        - verify cross_state_invariant is preserved at each yield
```

**Integration into existing VCGen:**

`vcgen.rs::generate_vcs` already dispatches per-function. Add a pre-pass: if the function's MIR pattern indicates a coroutine (driver detects this), construct `CoroutineInfo` and dispatch to `async_encoding::generate_coroutine_vcs` instead of the normal path.

**Driver change (in `mir_converter.rs`):**

Add coroutine detection: check rustc MIR `CoroutineKind` on the MIR body. If present, extract the coroutine struct layout (field names/types for persistent locals) and the state discriminant switch.

**Data flow change:**

```
EXISTING: async fn foo() → MIR body → ir::Function → VCGen (treats as regular fn, misses state invariants)
NEW:      async fn foo() → MIR body
              ↓ (driver: detect coroutine MIR)
          CoroutineInfo { states: [...], persistent_fields: [...] }
              ↓ (analysis: async_encoding)
          Per-state VerificationConditions
          Cross-state invariant VCs
              ↓ (solver)
          SolverResult per state
```

**Required changes:**

| Component | Change | Scope |
|-----------|--------|-------|
| `analysis/src/ir.rs` | Add `CoroutineInfo`, `CoroutineState` | Low (additive) |
| `analysis/src/async_encoding.rs` | NEW: coroutine flattener + VC generator | ~400 lines |
| `analysis/src/vcgen.rs` | Dispatch to async_encoding when coroutine detected | Low |
| `driver/src/mir_converter.rs` | Detect coroutine MIR, extract state machine structure | Medium |
| `crates/macros/src/lib.rs` | Add `#[async_requires]`, `#[async_ensures]`, `#[state_invariant]` | Low |

**No changes needed:** smtlib (existing Term types sufficient), solver (existing backend), concurrency modules.

---

## Feature 3: Weak Memory Models (Relaxed/Acquire/Release)

### What Already Exists

The codebase has (confirmed):
- `ir::AtomicOrdering` with all 5 orderings: `Relaxed, Acquire, Release, AcqRel, SeqCst`
- `ir::AtomicOp` with `ordering: AtomicOrdering` and `kind: AtomicOpKind`
- `analysis/src/concurrency/happens_before.rs`: `encode_atomic_ordering()` which maps all 5 orderings to SMT Terms
- The current encoding: SeqCst → `BvSLt(ts_store, ts_load)`, Release/Acquire/AcqRel → `Implies(reads_from, happens_before)`, Relaxed → `BoolLit(true)`

The existing encoding is **sound for SC and a conservative approximation for weaker orderings** but does not model the full C11/LLVM weak memory model. Specifically:
- It does not model the out-of-thin-air problem
- It does not model that `Relaxed` can observe stale values from the same thread (per-location order)
- It does not model coherence (all threads agree on the modification order of each atomic)

### Integration Points

**The integration is entirely within `analysis/src/concurrency/`.**

The IR types are sufficient — `AtomicOrdering` is already fully enumerated. The solver backend is sufficient — the SMT encoding is what needs improvement.

**New module:**

```
analysis/src/concurrency/weak_memory.rs   (NEW)
    WeakMemoryModel (enum: Conservative, C11Coherence, FullC11)

    fn encode_weak_memory(
        accesses: &[AtomicOp],
        model: WeakMemoryModel,
        coherence_axioms: bool,
    ) -> Vec<Command>

    // Additional axioms to add to SMT script:
    // 1. Coherence: for each atomic location, all stores form a total order (mo)
    // 2. Per-location sequentially consistent behavior (for SeqCst)
    // 3. Release sequences: a release that initiates a release sequence
    // 4. Reads-from respects modification order (rf ⊆ mo^-1)
```

**Modify `happens_before.rs`:**

The current `encode_atomic_ordering` encodes pairwise constraints. Extend to add:
- `coherence_constraints(accesses: &[MemoryAccess]) -> Vec<Term>`: for each atomic variable, all stores form a total order
- `rf_mo_consistency(accesses: &[MemoryAccess]) -> Vec<Term>`: reads-from is consistent with modification order

**Integration point in VCGen:**

`vcgen.rs` already calls `concurrency::data_race_freedom_vcs` for functions with `concurrency_config`. Add a call to `weak_memory::encode_weak_memory` when `atomic_ops` are present and ordering is weaker than SeqCst.

**SMT encoding strategy (confirmed feasible with existing Term types):**

Declare per-location modification order:
```smt
(declare-fun mo_x (Int Int) Bool)  ; modification order for location x
(assert (forall ((i Int) (j Int)) (=> (mo_x i j) (not (mo_x j i)))))  ; antisymmetric
(assert (forall ((i Int) (j Int) (k Int)) (=> (and (mo_x i j) (mo_x j k)) (mo_x i k))))  ; transitive
```

The existing `Term::Forall`, `Term::Implies`, `Term::And` variants support this directly.

**Required changes:**

| Component | Change | Scope |
|-----------|--------|-------|
| `analysis/src/concurrency/weak_memory.rs` | NEW: C11 coherence axioms, modification order encoding | ~300 lines |
| `analysis/src/concurrency/happens_before.rs` | Add coherence constraints, RF-MO consistency | Medium (~100 lines) |
| `analysis/src/vcgen.rs` | Call weak_memory module when non-SeqCst atomics present | Low |
| `analysis/src/ir.rs` | Add `WeakMemoryModel` field to `ConcurrencyConfig` | Trivial |

**No changes needed:** smtlib (existing quantifier/array terms sufficient), solver, driver, macros.

**Dependency:** Feature 1 (counterexample) helps debug weak memory violations; build Feature 3 after Feature 1.

---

## Feature 4: Higher-Order Closures with Specification Entailments

### What Already Exists

The codebase has (confirmed):
- `defunctionalize.rs`: `defunctionalize_closure_call()` → `ClosureEncoding` with `env_datatype_name`, `defunctionalized_name`
- `closure_analysis.rs`: `extract_closure_info()`, `detect_closure_calls()`
- `ir::ClosureInfo`: captures `env_fields`, `params`, `return_ty`, `trait_kind`
- `ir::Ty::Closure(Box<ClosureInfo>)` type variant
- `vcgen.rs::VcKind::ClosureContract` already exists

**What is missing:** When a closure is passed as an argument to a higher-order function (e.g., `map`, `filter`, `fold`), there is no way to:
1. Specify what the passed closure must satisfy (a specification entailment / closure precondition)
2. Verify that the closure satisfies that specification before the call
3. Use the closure's specification inside the higher-order function body

### Integration Points

**New macro (in `crates/macros/`):**

```rust
// Specify that a closure argument must satisfy a spec:
// fn apply<F: Fn(i32) -> i32>(f: F, x: i32) -> i32
#[requires(fn_spec(f, |x| x > 0 => f(x) > 0))]  // f must preserve positivity
```

`fn_spec(closure_arg, |params| precond => postcond)` is a new spec expression form.

**New IR constructs:**

```rust
// In ir.rs — extend SpecExpr for closure specifications:
pub struct ClosureSpec {
    /// The closure argument name being constrained
    pub closure_name: String,
    /// Precondition on closure inputs
    pub input_condition: SpecExpr,
    /// Postcondition on closure output (given input satisfies precond)
    pub output_condition: SpecExpr,
}

// In ir::Function — add closure specs to Contracts:
pub struct Contracts {
    // ... existing fields ...
    pub closure_specs: Vec<ClosureSpec>,  // NEW
}
```

**New VCGen logic:**

When generating VCs for a call site where a closure argument has a `ClosureSpec`:
1. Generate a VC: the actual closure passed satisfies the spec (precondition entailment check)
2. Inside the callee function body: assume the closure satisfies its spec (use as axiom)

The encoding uses the existing defunctionalization pattern:
```smt
; Closure spec as universally quantified axiom:
(assert (forall ((x Int))
  (=> (input_condition x)                    ; if input condition holds
      (output_condition (closure_impl env x))))) ; then output condition holds
```

This is expressible with existing `Term::Forall`, `Term::Implies`.

**New analysis module:**

```
analysis/src/closure_spec.rs   (NEW)
    ClosureSpecEncoder
        - parse fn_spec() expressions from SpecExpr
        - generate axiom SMT terms for closure specifications
        - generate entailment check VCs
```

**Modification to defunctionalize.rs:**

Extend `ClosureEncoding` to carry the closure's specification (if present), so VCGen can emit axioms.

**Required changes:**

| Component | Change | Scope |
|-----------|--------|-------|
| `analysis/src/ir.rs` | Add `ClosureSpec`, add `closure_specs` to `Contracts` | Low |
| `analysis/src/closure_spec.rs` | NEW: spec encoder, entailment VC generation | ~250 lines |
| `analysis/src/defunctionalize.rs` | Extend `ClosureEncoding` with optional spec | Low |
| `analysis/src/vcgen.rs` | Emit closure spec axioms + entailment VCs at call sites | Medium |
| `analysis/src/spec_parser.rs` | Parse `fn_spec(...)` expressions | Medium |
| `crates/macros/src/lib.rs` | No new macro needed; `fn_spec` is a spec expression form | None |

**No changes needed:** smtlib (existing quantifier terms), solver, driver (closure info already extracted).

**Dependency:** Builds on existing defunctionalization. Feature 4 can be built independently of Features 1-3.

---

## Feature 5: Separation Logic

### What Already Exists

The codebase has (confirmed):
- `analysis/src/heap_model.rs`: heap-as-array encoding for unsafe code (`heap: Array (BitVec 64) (BitVec 8)`, `allocated`, `alloc_base`, `alloc_size`)
- `analysis/src/ownership.rs`: ownership constraint tracking
- `analysis/src/borrow_conflict.rs`: borrow conflict detection
- `ir::UnsafeOperation`: RawDeref, PtrArithmetic, PtrCast with provenance

**What is missing:** The heap model is a flat byte array — no separation logic heap predicates, no `*` (separating conjunction), no points-to assertions (`x ↦ v`), no frame rule reasoning.

### Separation Logic Target Scope for v0.4

Separation logic for safe Rust is most useful for:
1. Specifying ownership of heap-allocated data structures (Box<T>, Vec<T>'s buffer)
2. Frame reasoning: a function modifying `ptr.field_a` does not affect `ptr.field_b`
3. Specifications on unsafe code that manipulates raw pointers

**Integration approach: Shallow embedding into existing Term/Sort**

Rather than implementing a full separation logic proof system, use a **shallow embedding** via SMT arrays: separation logic predicates become assertions about the existing `heap` array model.

**New IR constructs (in `analysis/src/ir.rs`):**

```rust
/// A separation logic heap predicate in a specification.
pub enum HeapPred {
    /// Points-to: location `ptr` contains value `val` of type `ty`
    PointsTo { ptr: String, val: SpecExpr, ty: Ty },
    /// Separating conjunction: P1 * P2 (disjoint heap regions)
    SepConj(Box<HeapPred>, Box<HeapPred>),
    /// Emp: empty heap (no heap ownership)
    Emp,
    /// Existential: ∃x. P(x)
    Exists { var: String, ty: Ty, body: Box<HeapPred> },
}

// Extend SpecExpr to allow heap predicates in requires/ensures:
// #[requires(sep: x |-> v * y |-> w)]
```

**New macro syntax (in `crates/macros/`):**

```rust
#[requires(sep: "x |-> 5 * y |-> 3")]  // separation logic precondition
#[ensures(sep: "x |-> result")]          // separation logic postcondition
```

The `sep:` prefix distinguishes separation logic specs from regular specs.

**New analysis modules:**

```
analysis/src/separation_logic.rs   (NEW)
    SepLogicEncoder
        - encode HeapPred as SMT assertions over existing heap array
        - PointsTo(ptr, val) → (= (select heap ptr) val) ∧ (allocated ptr)
        - SepConj(P, Q) → disjoint_regions(P.footprint, Q.footprint) ∧ P ∧ Q
        - generate frame axioms: function with footprint F does not modify heap outside F

    FootprintAnalyzer
        - compute the footprint (set of heap locations) of a heap predicate
        - used for frame rule: caller retains ownership of locations not in callee footprint
```

**Integration with existing heap_model.rs:**

`heap_model.rs` already declares `heap`, `allocated`, `alloc_base`, `alloc_size`. The separation logic encoder uses these directly. No change to heap_model.rs needed — SepLogicEncoder composes on top of it.

**Integration with VCGen:**

Add a separation logic VC generation pass in `vcgen.rs`:
1. If `contracts.requires` contains `sep:` annotations, emit heap predicate assertions
2. At function call sites, emit frame VCs: callee does not modify locations outside its footprint
3. For postconditions with `sep:`, generate the heap assertion after the function body

**SMT encoding of separating conjunction:**

```smt
; Footprint of P as an uninterpreted set function
(declare-fun footprint_P (Int) Bool)  ; true iff location is in P's footprint

; Disjointness of footprints:
(assert (forall ((loc Int))
  (not (and (footprint_P loc) (footprint_Q loc)))))

; Points-to encoding:
(assert (= (select heap ptr) expected_val))
(assert (footprint_PointsTo ptr))  ; footprint is {ptr}
(assert (forall ((loc Int)) (=> (footprint_PointsTo loc) (= loc ptr))))
```

This uses existing `Term::Forall`, `Term::And`, `Term::Not`, `Term::Select`, `Term::Eq`.

**Required changes:**

| Component | Change | Scope |
|-----------|--------|-------|
| `analysis/src/ir.rs` | Add `HeapPred` enum | Medium (~80 lines) |
| `analysis/src/separation_logic.rs` | NEW: SepLogicEncoder, FootprintAnalyzer | ~400 lines |
| `analysis/src/spec_parser.rs` | Parse `sep: "..."` prefix in spec expressions | Medium |
| `analysis/src/vcgen.rs` | Dispatch sep logic encoding when HeapPred specs present | Medium |
| `crates/macros/src/lib.rs` | Handle `sep:` prefix in requires/ensures macros | Low |

**No changes needed:** smtlib (existing Term/Sort sufficient), solver, driver.

**Dependency:** Builds on heap_model.rs and ownership.rs (already complete). Can be built independently but benefits from Feature 1 (counterexample) to show which heap region was violated.

---

## Recommended Build Order

```
Feature 1: Counterexample Generation
    ↓ (no deps, highest user value, enables debugging all other features)
Feature 4: Higher-Order Closures with Spec Entailments
    ↓ (no deps, extends existing defunctionalization cleanly)
Feature 2: Async/Await Verification
    ↓ (no deps, new MIR detection pathway)
Feature 3: Weak Memory Models
    ↓ (builds on existing concurrency infrastructure, benefits from CE generation)
Feature 5: Separation Logic
    (most complex, benefits from all prior features working)
```

### Rationale

1. **Counterexample first**: Every other feature produces verification failures. Without useful counterexamples, developers cannot debug why a proof fails. This is the force multiplier.

2. **Closures before async**: Async state machines contain closure-like behavior (captures across await points). Building spec entailments for closures first creates reusable patterns for the async encoding.

3. **Async before weak memory**: Both involve concurrency reasoning. Async establishes the coroutine MIR detection pathway in the driver, which weak memory verification may reuse for detecting async atomic operations.

4. **Weak memory before separation logic**: Weak memory is additive to existing concurrency infrastructure (happens_before.rs already has the skeleton). Separation logic is the largest new system.

5. **Separation logic last**: Requires heap model extensions that interact with ownership reasoning. Building last ensures the preceding features provide debugging capability (counterexamples) and don't interfere.

---

## Component Boundaries

### New vs Modified Summary

| Component | Status | Feature | Primary Crate |
|-----------|--------|---------|--------------|
| `analysis/src/counterexample.rs` | NEW | 1: Counterexample | analysis |
| `analysis/src/async_encoding.rs` | NEW | 2: Async | analysis |
| `analysis/src/concurrency/weak_memory.rs` | NEW | 3: Weak Memory | analysis |
| `analysis/src/closure_spec.rs` | NEW | 4: Closure Specs | analysis |
| `analysis/src/separation_logic.rs` | NEW | 5: Sep Logic | analysis |
| `analysis/src/ir.rs` | MODIFY | 2,4,5 | analysis |
| `analysis/src/vcgen.rs` | MODIFY | 1,2,3,4,5 | analysis |
| `analysis/src/spec_parser.rs` | MODIFY | 4,5 | analysis |
| `analysis/src/defunctionalize.rs` | MODIFY | 4 | analysis |
| `analysis/src/concurrency/happens_before.rs` | MODIFY | 3 | analysis |
| `driver/src/mir_converter.rs` | MODIFY | 1,2 | driver |
| `driver/src/diagnostics.rs` | MODIFY | 1 | driver |
| `driver/src/json_output.rs` | MODIFY | 1 | driver |
| `crates/macros/src/lib.rs` | MODIFY | 2,5 | macros |
| **smtlib/** | NONE | all | smtlib |
| **solver/** | NONE | all | solver |

### Key Architectural Observation

All 5 features are **analysis-layer additions**. The smtlib and solver crates require no changes because:
- `Term` already has: `Forall`, `Exists`, `Implies`, `And`, `Or`, `Select`, `Store`, `App`, `Annotated` (patterns) — sufficient for all 5 features
- `SolverResult::Sat(Some(Model))` already carries counterexample data
- `SolverBackend` trait is already stable and extensible

This confirms the architectural layering works as intended.

---

## Data Flow Changes Per Feature

### Feature 1: Counterexample

```
BEFORE: SolverResult::Sat(Some(Model { assignments }))
            ↓ (driver)
        "Verification failed at line X"

AFTER:  SolverResult::Sat(Some(Model { assignments }))
            ↓ (CounterexampleRenderer + var_name_map)
        RenderedCounterexample { "x = 5, y = -3, result = 2" }
            ↓ (Ariadne diagnostics)
        "Verification failed: postcondition 'result > 0' violated
         Counterexample: x = 5, y = -3, computed result = 2"
```

### Feature 2: Async

```
BEFORE: async fn poll() → treated as regular fn with state machine MIR
            (verification either fails or is unsound)

AFTER:  async fn poll()
            ↓ (mir_converter: detect coroutine MIR)
        CoroutineInfo { states: [State0, State1, State2], persistent_fields: [...] }
            ↓ (async_encoding::generate_coroutine_vcs)
        [VC_state0_entry, VC_state0_exit, VC_state1_entry, ..., VC_invariant_preservation]
            ↓ (solver)
        [SolverResult per state]
```

### Feature 3: Weak Memory

```
BEFORE: AtomicOp { ordering: Relaxed }
            ↓ (encode_atomic_ordering)
        BoolLit(true)  [no constraint — conservative]

AFTER:  AtomicOp { ordering: Relaxed }
            ↓ (weak_memory::encode_weak_memory with C11Coherence)
        [coherence axioms for this atomic location]
        + per-location modification order constraints
        + rf-coherence constraints
```

### Feature 4: Closure Specs

```
BEFORE: fn apply<F: Fn(i32) -> i32>(f: F, x: i32) -> i32
        #[requires(x > 0)]  → only constrains x, nothing about f

AFTER:  fn apply<F: Fn(i32) -> i32>(f: F, x: i32) -> i32
        #[requires(x > 0, fn_spec(f, |y| y > 0 => f(y) > 0))]
            ↓ (closure_spec::ClosureSpecEncoder)
        SMT axiom: (forall ((y Int)) (=> (> y 0) (> (f_impl f_env y) 0)))
            ↓ (VCGen adds axiom to script)
        Call site VC: does the actual closure passed satisfy this spec?
```

### Feature 5: Separation Logic

```
BEFORE: #[requires("ptr is non-null")]  → boolean assertion only

AFTER:  #[requires(sep: "ptr |-> init_val")]  → heap ownership assertion
            ↓ (separation_logic::SepLogicEncoder)
        (assert (= (select heap ptr) init_val))
        (assert (allocated ptr))
        (assert (footprint_f ptr))  ; ptr is in f's footprint
            ↓ (VCGen adds frame VC)
        frame_vc: forall loc, (not (footprint_f loc)) => (= (select heap_post loc) (select heap_pre loc))
```

---

## Anti-Patterns to Avoid

### Anti-Pattern 1: New SMT Term Variants for Separation Logic

**What NOT to do:** Add new `Term::SepConj`, `Term::PointsTo` variants to `smtlib/src/term.rs`.

**Why wrong:** The smtlib crate is a pure SMT-LIB2 AST. Separation logic is not part of SMT-LIB2. Adding domain concepts here violates the crate's single responsibility.

**Do this instead:** Encode all separation logic as combinations of existing `Term` variants (Forall, Select, App with footprint functions). Keep smtlib pure.

### Anti-Pattern 2: Coroutine State Machine Detection in Analysis Crate

**What NOT to do:** Detect coroutine MIR patterns inside `analysis/src/async_encoding.rs` using rustc-internal types.

**Why wrong:** The analysis crate is decoupled from rustc on purpose — it works on stable IR. Rustc MIR types are nightly-only.

**Do this instead:** Coroutine detection happens in `driver/src/mir_converter.rs` (which already uses rustc APIs). The analysis crate only sees the resulting `CoroutineInfo` in the stable IR.

### Anti-Pattern 3: Counterexample Rendering in Solver Crate

**What NOT to do:** Add Rust-name-mapping logic to `solver/src/model.rs`.

**Why wrong:** The solver crate is a pure SMT interface. It has no concept of Rust variable names.

**Do this instead:** Counterexample rendering belongs in `analysis/src/counterexample.rs` which has access to `ir::Function` (and its variable names) and receives the `Model` from the solver result.

### Anti-Pattern 4: One VcKind per Feature

**What NOT to do:** Reuse `VcKind::DataRaceFreedom` for weak memory violations or add overly general `VcKind::WeakMemory`.

**Why wrong:** Diagnostics need precise classification. Users need to know whether a failure is a coherence violation vs a happens-before violation.

**Do this instead:** Add specific `VcKind` variants: `WeakMemoryCoherence`, `WeakMemoryRF`, `AsyncStateInvariant`, `ClosureSpecEntailment`, `SeparationLogicFrame`, `SeparationLogicPointsTo`.

### Anti-Pattern 5: Mutable Global for Coroutine State

**What NOT to do:** Use a thread-local or static HashMap to track coroutine states during verification.

**Why wrong:** The parallel executor already runs multiple functions concurrently. Global state causes data races in the verifier itself.

**Do this instead:** Carry `CoroutineInfo` as a field on `ir::Function` (or as a separate IR type), passed explicitly through the VCGen pipeline.

---

## Integration Points Summary

| Boundary | Feature | Communication Pattern |
|----------|---------|----------------------|
| driver → analysis (counterexample) | 1 | `VarNameMap` added to `VerificationCondition` |
| driver → analysis (async) | 2 | `CoroutineInfo` added to `ir::Function` |
| analysis::vcgen → analysis::counterexample | 1 | Function call: `CounterexampleRenderer::render(model, vc)` |
| analysis::vcgen → analysis::async_encoding | 2 | Function call: `generate_coroutine_vcs(coroutine_info)` |
| analysis::vcgen → analysis::concurrency::weak_memory | 3 | Function call when `atomic_ops` non-empty + non-SeqCst |
| analysis::vcgen → analysis::closure_spec | 4 | Function call when `contracts.closure_specs` non-empty |
| analysis::vcgen → analysis::separation_logic | 5 | Function call when `sep:` predicates in contracts |
| analysis::defunctionalize → analysis::closure_spec | 4 | `ClosureEncoding` extended with optional spec |
| analysis::heap_model → analysis::separation_logic | 5 | Composition: sep logic uses declared heap constants |
| solver::SolverResult → analysis::counterexample | 1 | `Model` passed to renderer |
| analysis → driver::diagnostics | 1 | `RenderedCounterexample` in `VerificationCondition` |

---

## Sources

- **Codebase analysis** (HIGH confidence): Direct inspection of `crates/analysis/src/ir.rs`, `vcgen.rs`, `concurrency/`, `defunctionalize.rs`, `heap_model.rs`, `solver/src/result.rs`, `model.rs`
- **Rust coroutine MIR** (MEDIUM confidence): Rust async/coroutine compilation to generator MIR is documented in rustc-dev-guide; stabilized as coroutines in Rust 1.75+
- **C11 weak memory model** (HIGH confidence): The existing `happens_before.rs` comments reference C11 semantics explicitly and the encoding matches standard happens-before/reads-from/modification-order decomposition
- **Separation logic shallow embedding** (MEDIUM confidence): Pattern used by Prusti, Creusot, and VeriFast — encoding heap predicates as array constraints is standard practice

---

*Architecture research for: rust-fv v0.4 Full Rust Verification Features*
*Researched: 2026-02-19*
*Confidence: HIGH — Based on direct codebase analysis of all 5 crates*
