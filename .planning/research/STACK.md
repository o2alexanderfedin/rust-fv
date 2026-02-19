# Stack Research

**Domain:** Formal Verification Tooling for Rust — v0.4 New Features
**Researched:** 2026-02-19
**Confidence:** HIGH (core SMT/Z3 APIs verified via official docs; architectural patterns verified against academic literature and existing tools)

---

## Scope: What This Document Covers

This document covers only **new** stack requirements for v0.4's five features:

1. Counterexample generation (witness extraction + diagnostic rendering)
2. Async/await verification (coroutine state-machine modeling)
3. Weak memory models (Relaxed/Acquire/Release axiomatic encoding)
4. Higher-order closures with spec entailments
5. Separation logic for heap reasoning

**Not re-researched:** proc macros (`syn`/`quote`), SMT-LIB2 core, bitvectors, Z3/CVC5/Yices backends, MIR extraction, incremental caching, VSCode/LSP, stdlib contracts. Those are stable in the existing stack.

---

## Feature 1: Counterexample Generation

### What Already Exists

The `rust-fv-solver` crate already has a `Model` struct (`crates/solver/src/model.rs`) with `assignments: Vec<(String, String)>` parsed from Z3's `(get-model)` SMT-LIB text output. The parser extracts raw string key-value pairs. The `rust-fv-diagnostics` crate uses `ariadne` for error rendering.

### What Is Needed

The existing `Model` is raw strings — sufficient for `Sat` detection but insufficient for:
- Typed value reconstruction (map `#b00001010` back to `i8 = 10`)
- Associating model constants back to source-level variable names (MIR locals `_3` → `x`)
- Rendering counterexample witnesses inline in `ariadne` diagnostics

### New Stack Requirements

| Technology | Version | Purpose | Why |
|------------|---------|---------|-----|
| No new crates | — | Counterexample core is pure Rust | All needed infrastructure exists: z3 0.19 has `Model::eval`, `Model::get_const_interp`; SMT-LIB parser already in `crates/solver/src/parser.rs`; `ariadne` already in `crates/diagnostics` |

### Implementation Approach

**Typed Model Reconstruction** (changes to `crates/solver/src/model.rs`):

Extend `Model` to carry typed assignments:

```rust
#[derive(Debug, Clone)]
pub enum ModelValue {
    Bool(bool),
    Int(i128),
    BitVec { value: u128, width: u32 },
    Array(Vec<(ModelValue, ModelValue)>),  // finite array interpretation
    Uninterpreted(String),                 // fallback raw string
}

pub struct TypedModel {
    pub assignments: Vec<(String, ModelValue)>,
}
```

Parse from existing SMT-LIB `(get-model)` text output — extend `parser.rs` to pattern-match Z3's `define-fun` output format.

**Source Variable Mapping** (changes to `crates/analysis`):

Maintain a `VarMap: HashMap<SmtConst, SourceLocation>` during VCGen that maps SMT constant names (e.g., `x_3_pre`) back to MIR local indices and source spans. Pass this map alongside the `TypedModel` to diagnostics.

**Diagnostic Rendering** (changes to `crates/diagnostics`):

`ariadne` supports arbitrary label text — add a `render_counterexample(model: &TypedModel, var_map: &VarMap)` function that annotates source spans with "= value" labels. No new crate needed.

**What NOT to do:**
- Do not use z3 native `Model::eval` API for subprocess-based backends (CVC5/Yices are subprocess-only) — keep model extraction in the SMT-LIB text parser
- Do not try to display array models exhaustively — truncate at 8 entries with "..." suffix

---

## Feature 2: Async/Await Verification

### How Rust Compiles Async

Rust async functions become coroutines in MIR (since Rust 1.75+, previously called "generators"). The MIR transformation in `rustc_mir_transform::coroutine` converts `async fn` bodies into state machines with explicit `Suspend` and `Return` terminators. Each `yield`/`.await` point becomes a state machine variant holding live variables.

**Key MIR constructs:**
- `TerminatorKind::Yield { value, resume, drop }` — suspension point
- `TerminatorKind::GeneratorDrop` — cleanup on early drop
- MIR body contains a `CoroutineDef` with `yield_ty` and `resume_ty`

### Verification Strategy

Encode async state machines as **unrolled transition systems** in SMT:
- Each `await` point → new SMT "epoch" with fresh variable copies
- `Poll::Pending` path → skip (not yet executed)
- `Poll::Ready(v)` path → continue to next epoch
- Preconditions on resume arguments, postconditions on final value

This is equivalent to bounded model checking of a state machine — no new SMT theories needed (use existing LIA + Arrays). The SMT formula `pre(args) ∧ step₀ ∧ step₁ ∧ ... ∧ ¬post` checks correctness of the full async chain.

### New Stack Requirements

| Technology | Version | Purpose | Why |
|------------|---------|---------|-----|
| No new crates | — | Async MIR is reachable from existing `rustc_driver` | `crates/driver` already extracts MIR; async bodies are just MIR with `Yield` terminators |

**Changes to existing crates:**

- `crates/driver`: Add handling for `TerminatorKind::Yield` in MIR walk — treat as function call boundary with `(resume_value, resume_state)` as outputs
- `crates/analysis` (VCGen): Add `AsyncVcGen` that tracks "epoch" index, threads postconditions through `Yield` points, introduces `resume_arg` as a fresh constant per epoch
- `crates/smtlib` (sort.rs): No changes needed — Int sort suffices for state index encoding

### Implementation Pattern

```rust
// In VCGen: each .await point creates an "epoch boundary"
// async_state: current coroutine state variant (Int constant)
// resume_val: what the awaited future returns (typed per context)
let epoch_pre = mk_and(vec![
    pre_conditions_hold.clone(),
    state_machine_transition(state_i, state_j),
]);
let epoch_post = encode_suffix_from(state_j, &remaining_body);
// Final VC: epoch_pre => epoch_post
```

**What NOT to do:**
- Do not try to verify infinite async loops (add bounded unrolling limit, default 3 iterations, configurable via `#[verify_async(unroll = N)]`)
- Do not model the executor (tokio/async-std) — model only the `Future::poll` contract abstractly
- Do not handle `async-trait` objects specially in v0.4 — treat as opaque `FnOnce` with spec

---

## Feature 3: Weak Memory Models (Relaxed/Acquire/Release)

### Background

C11/Rust atomic memory ordering (Relaxed, Acquire, Release, AcqRel, SeqCst) cannot be verified with simple happens-before encoding. The correct approach is **axiomatic encoding**: encode the memory model as SMT constraints over events (reads/writes) and their ordering relations.

**Academic basis:** Dartagnan (bounded model checker for weak memory) encodes `ψ_prog ∧ ψ_assert ∧ ψ_mm` where `ψ_mm` encodes the axiomatic CAT memory model as SMT. The key insight: encoding memory-order relations as SMT bitvector/integer constraints over event timestamps is decidable and practical for bounded programs.

### SMT Encoding

**Event model** (encode in LIA + UF):
```smt2
; Each atomic access is an event
(declare-sort Event 0)
(declare-fun thread_of (Event) Int)
(declare-fun loc_of (Event) Int)
(declare-fun val_of (Event) Int)
(declare-fun order_of (Event) Int)  ; 0=Relaxed,1=Acquire,2=Release,3=AcqRel,4=SeqCst
(declare-fun po (Event Event) Bool)  ; program-order
(declare-fun rf (Event Event) Bool)  ; reads-from
(declare-fun mo (Event Event) Bool)  ; modification-order (total per location)
(declare-fun hb (Event Event) Bool)  ; happens-before (derived)
```

**Memory model axioms** (SW relation for Acquire/Release):
```smt2
; Synchronizes-with: Release write W synchronizes with Acquire read R if rf(W,R)
(assert (forall ((w Event) (r Event))
  (=> (and (is-write w) (is-read r) (rf w r)
           (>= (order_of w) 2)  ; Release or stronger
           (>= (order_of r) 1)) ; Acquire or stronger
      (sw w r))))
; Happens-before: po ∪ sw transitively closed
```

### New Stack Requirements

| Technology | Version | Purpose | Why |
|------------|---------|---------|-----|
| No new Rust crates | — | Encoding is pure SMT-LIB2 text generation | The `crates/smtlib` AST already supports `Forall`, `App` (uninterpreted functions), `Sort::Uninterpreted` — sufficient for event model |
| `petgraph` (already in `crates/analysis`) | 0.8 | Build happens-before graph from MIR atomic ops | Already a dep. Use for static analysis of ordering constraints before SMT encoding |

**New SMT-LIB term variants needed in `crates/smtlib/src/term.rs`:**

The existing `Sort::Uninterpreted(String)` and `Term::App(String, Vec<Term>)` cover uninterpreted functions. The `Term::Forall` already handles axiom encoding. **No new term variants required** — the existing AST is sufficient.

**New enum in `crates/analysis`:**

```rust
pub enum AtomicOrder {
    Relaxed = 0,
    Acquire = 1,
    Release = 2,
    AcqRel = 3,
    SeqCst = 4,
}

pub struct AtomicEvent {
    pub kind: EventKind,  // Read | Write | Fence | Rmw
    pub order: AtomicOrder,
    pub location: MirPlace,
    pub thread: ThreadId,
}
```

**Changes to existing crates:**
- `crates/driver`: Detect `Terminator::Call` to `std::sync::atomic::*` methods; extract `Ordering` argument; emit `AtomicEvent` records
- `crates/analysis`: Add `WeakMemVcGen` that builds event graph, emits SMT axioms for chosen memory model (`Relaxed`/`AcqRel`/`SeqCst`)
- `crates/smtlib`: No changes needed

**Scope for v0.4:**
- Support `Ordering::Relaxed`, `Ordering::Acquire`, `Ordering::Release`, `Ordering::AcqRel`
- Defer `SeqCst` (requires global total order, expensive) to v0.5
- Bounded: max 2 threads, max 10 events (configurable)

**What NOT to do:**
- Do not implement a full CAT language parser (Dartagnan approach) — directly hardcode C11-subset axioms
- Do not use CVC5's experimental SL theory for memory (it's for heap SL, not memory ordering)
- Do not model TSO or ARM memory models in v0.4

---

## Feature 4: Higher-Order Closures with Spec Entailments

### Background

The existing pipeline already handles closures via **defunctionalization** (v0.3): each closure becomes a named SMT function. That covers simple closures. For v0.4, the new requirement is **spec entailments**: a higher-order function `map(f: F, xs: Vec<T>)` needs to verify that if `f` satisfies spec `S`, then `map` produces a correct result.

**Academic basis:** Wolff et al. 2021 ("Modular Specification and Verification of Closures in Rust") encoded closure specification entailment into first-order logic for Prusti. The key insight: define `call_description(f, args, result)` as an SMT predicate, and `spec_entailment(f, pre_S, post_S)` as a universal quantification over all valid calls.

### SMT Encoding

**Spec entailment as SMT predicate:**
```smt2
; closure_spec_holds: "closure f satisfies spec S"
(define-fun closure_spec_holds ((f_id Int) (x T)) Bool
  (forall ((args ArgTuple))
    (=> (pre_S args)           ; if precondition S holds
        (let ((result (apply_f f_id args)))
          (post_S args result))))) ; postcondition holds
```

The `f_id` is the defunctionalized closure discriminant (already exists from v0.3). Spec entailment adds a universally-quantified wrapper around the existing defunctionalized application.

### New Stack Requirements

| Technology | Version | Purpose | Why |
|------------|---------|---------|-----|
| No new crates | — | Encoding uses existing SMT-LIB terms | `Term::Forall` + `Term::App` + defunctionalization (v0.3) covers the pattern |

**Macro additions to `crates/macros`:**

```rust
// New attributes for higher-order specs
#[fn_spec(
    requires = "pre_S(x)",
    ensures = "post_S(x, result)"
)]
// Applied to closure-typed parameters: specifies what the closure must satisfy
// Processed by VCGen to emit spec_entailment SMT predicate
```

**New `Term` variant in `crates/smtlib/src/term.rs`:**

None strictly needed. Use existing `Forall` + `App` to encode spec entailments. The `Annotated` variant with `:spec-entailment` annotation can carry metadata for diagnostics.

**Changes to existing crates:**
- `crates/macros`: Add `#[fn_spec(...)]` attribute for annotating closure-typed function parameters
- `crates/analysis` (VCGen): When calling a higher-order function, look up `#[fn_spec]` on closure parameter, emit `closure_spec_holds(f_id, ...)` SMT assertion before call
- `crates/ir` (if exists) / `crates/analysis`: Extend closure defunctionalization to emit `closure_spec_holds` predicates alongside `apply_closure` functions

**What NOT to do:**
- Do not encode full higher-order logic — keep everything as first-order via defunctionalization + universal quantification
- Do not try to infer closure specs automatically (require explicit `#[fn_spec]` annotations)
- Do not use CVC5 for spec entailment queries preferentially — Z3's MBQI handles universal quantifiers better than CVC5 for this pattern

---

## Feature 5: Separation Logic for Heap Reasoning

### SMT Theory Choice

**Z3 approach (recommended):** Encode separation logic **shallowly** using Z3's existing Array theory (`Array(Loc, Val)`) with explicit heap threading. No native SL theory in Z3 — but GRASShopper, Viper, and similar tools all use this approach successfully.

**CVC5 native SL (not recommended for v0.4):** CVC5 has a built-in experimental SL theory (`declare-heap`, `sep`, `pto`, `wand` operators). It supports the QF_S logic (quantifier-free SL). However: (1) it's classified "experimental" and may be removed; (2) it requires switching CVC5's logic to `QF_S` or `QF_SL` — incompatible with mixing other theories (no LIA+SL in one solver call); (3) no Rust crate wraps it. Therefore, defer CVC5-native SL.

**Chosen encoding:** Heap-as-function (`Array(Int, Int)` or `Array(Int, Val)`) with ownership tracked via **permission sets** as SMT integer sets.

```smt2
; Heap as SMT array (already exists: Term::Select/Store, Sort::Array)
; Ownership: a set of addresses owned by current frame
; Separating conjunction: disjoint union of ownership sets
; Points-to: heap(addr) = val AND addr ∈ owned

; Frame rule as: if pre * frame holds, after mutation, post * frame holds
; Encode "disjoint" as: forall a. (a ∈ owned1) => (a ∉ owned2)
```

### New Stack Requirements

| Technology | Version | Purpose | Why |
|------------|---------|---------|-----|
| No new crates | — | Heap-as-array encoding uses existing `Sort::Array`, `Term::Select`, `Term::Store` | Already in v0.3 unsafe/heap-as-array work. SL adds ownership tracking on top |

**New `Sort` variant in `crates/smtlib/src/sort.rs`:**

```rust
/// Set sort for ownership tracking: `(Set T)`
/// Encoded as `Array T Bool` — membership via `(select set elem)`
Set(Box<Sort>),
```

Or reuse `Array(Box<Sort>, Box<Sort>)` with `Bool` value sort — no new variant strictly needed.

**New `Term` variants in `crates/smtlib/src/term.rs`:**

```rust
// Separation logic combinators (encoded over heap arrays)
/// Separating conjunction: own1 and own2 are disjoint, both hold
/// Desugars to: Disjoint(own1, own2) ∧ P(heap, own1) ∧ Q(heap, own2)
SepConj(Box<Term>, Box<Term>),

/// Points-to predicate: addr ↦ val (owns addr, heap[addr] = val)
/// Desugars to: In(addr, owned) ∧ Select(heap, addr) = val
PointsTo(Box<Term>, Box<Term>),

/// Magic wand: P -* Q (given P, can produce Q) — for frame reasoning
/// Defer to v0.5: magic wand encoding is complex (requires second heap var)
// MagicWand(Box<Term>, Box<Term>),  // NOT in v0.4
```

**New module in `crates/analysis`: `sl_vcgen.rs`**

```rust
/// Separation logic VCGen pass
pub struct SlVcGen {
    /// Current heap variable name in SMT
    pub heap_var: String,
    /// Current ownership set variable name
    pub owned_var: String,
}

impl SlVcGen {
    /// Encode `x.field` read: assert addr ∈ owned, emit heap[addr]
    pub fn encode_field_read(...) -> Term { ... }

    /// Encode `*ptr = val` write: assert addr ∈ owned, emit Store
    pub fn encode_deref_write(...) -> Term { ... }

    /// Encode allocation: Box::new(x) → fresh addr, add to owned
    pub fn encode_alloc(...) -> Term { ... }

    /// Encode deallocation: drop(ptr) → remove from owned
    pub fn encode_dealloc(...) -> Term { ... }

    /// Encode frame rule for function call
    pub fn encode_frame(...) -> Term { ... }
}
```

**Changes to existing crates:**
- `crates/smtlib/src/term.rs`: Add `SepConj` and `PointsTo` variants (magic wand deferred)
- `crates/smtlib/src/sort.rs`: Optional `Set(Box<Sort>)` variant, or reuse `Array(Box<Sort>, Bool)`
- `crates/analysis`: Add `sl_vcgen.rs` module, integrate with existing VCGen for unsafe/heap code paths
- `crates/macros`: Add `#[sep_pre]`/`#[sep_post]` proc macro attributes using SL syntax: `#[sep_pre = "x ↦ v * list(p)"]` parsed to `SepConj(PointsTo(...), App("list", [...]))`

**What NOT to do:**
- Do not use CVC5 experimental SL theory (experimental, theory mixing limitation, no Rust wrapper)
- Do not implement inductive predicates (list/tree) via SL in v0.4 — use unfolding bounded to depth 3
- Do not implement magic wand in v0.4 (complex, rarely needed, schedule for v0.5)
- Do not use Z3's python-only SL extensions — use standard SMT-LIB2 encoding

---

## Consolidated New Dependencies

The v0.4 feature set requires **zero new crates**. All five features build on existing infrastructure:

### Existing Stack Leveraged

| Crate (existing) | Used for v0.4 |
|------------------|---------------|
| `z3` 0.19 | `Model::eval`, `Model::get_const_interp` for counterexample extraction (z3-native backend) |
| `crates/solver/src/parser.rs` | Extend to parse typed `define-fun` values from `(get-model)` |
| `crates/smtlib` (Term, Sort) | Add `SepConj`, `PointsTo` variants; rest already covers weak memory + async encoding |
| `crates/analysis` (petgraph 0.8) | Build event graphs for weak memory model |
| `ariadne` (in diagnostics) | Render counterexample variable assignments inline |
| `crates/macros` (syn 2.x, quote 1.x) | Add `#[fn_spec]`, `#[sep_pre]`, `#[sep_post]`, `#[verify_async]` attributes |

### Workspace Cargo.toml Changes

```toml
# No new workspace dependencies required for v0.4
# All capabilities covered by existing:
# z3 = { version = "0.19" }
# petgraph = "0.8" (in crates/analysis)
# syn = { version = "2.0", features = ["full", "parsing"] }
# ariadne (in crates/diagnostics)
```

---

## SMT Theory Map by Feature

| Feature | SMT Theories Used | Z3 Supported | CVC5 Supported | Yices Supported |
|---------|------------------|-------------|----------------|-----------------|
| Counterexample | LIA + Arrays + BV (existing) | YES | YES | YES |
| Async/Await | LIA + Arrays (epoch unrolling) | YES | YES | YES |
| Weak Memory | LIA + UF (uninterp. functions) | YES | YES | YES (partial) |
| Closure Entailments | LIA + UF + Forall (MBQI) | YES (best) | MEDIUM | LIMITED |
| Separation Logic | Arrays + LIA (heap encoding) | YES | YES | YES |

**Critical:** Closure spec entailments use universal quantifiers (`Forall`) — Z3's MBQI handles these best. For queries containing `#[fn_spec]`-annotated higher-order specs, prefer Z3 backend automatically (route in `crates/solver/src/backend.rs`).

---

## Alternatives Considered

| Category | Recommended | Alternative | Why Not |
|----------|-------------|-------------|---------|
| SL heap encoding | Heap-as-Array (existing) | CVC5 native SL (`declare-heap`) | CVC5 SL is experimental, no theory mixing (can't combine with LIA), no Rust wrapper |
| SL heap encoding | Heap-as-Array | Z3 native SL (Python-only) | Z3's SL extension is Python-only, not in SMT-LIB text interface |
| Async modeling | Bounded epoch unrolling | Full temporal logic (LTL/CTL) | LTL/CTL requires model checker (not SMT), vastly more complex, out of scope |
| Weak memory | Custom axiomatic encoding | Dartagnan integration | Dartagnan is Java, complex integration; our bounded scope (≤2 threads) doesn't need full CAT |
| Closure specs | `#[fn_spec]` + FOL encoding | Higher-order logic (HOL) | HOL requires theorem provers (Isabelle/HOL, Lean); SMT-based FOL encoding (Prusti/Wolff approach) is more automated |
| Counterexample types | Extend parser.rs | z3 native `Model::eval` | Native eval only works for `z3-native` feature; CVC5/Yices backends are subprocess-only — need unified text-parse approach |

---

## What NOT to Use

| Avoid | Why | Use Instead |
|-------|-----|-------------|
| CVC5 built-in `declare-heap` SL | Experimental flag; mutually exclusive with other theories in same query | Heap-as-Array encoding (Array theory + LIA) |
| Magic wands in v0.4 | Require second heap variable and complex frame encoding; no tooling precedent in automated SMT | Defer to v0.5; use frame axioms without wand |
| Full CAT memory model language | Out of scope; Dartagnan approach requires Java tool integration | Direct SMT axiom generation for C11-subset |
| `SeqCst` ordering in v0.4 | Requires global total order (expensive SMT encoding, quantifier alternation) | Support Relaxed/Acquire/Release/AcqRel only |
| HOL provers for closure specs | Isabelle/HOL, Lean require manual proofs; not automated | Wolff-style FOL encoding + SMT (Z3 MBQI) |
| Inductive SL predicates (lists, trees) without bound | Undecidable in general | Bounded unfolding to depth 3 (configurable) |

---

## Version Compatibility

| Package | Compatible With | Notes |
|---------|-----------------|-------|
| `z3` 0.19 (existing) | Z3 4.13+ solver | `Model::eval`, `Model::get_const_interp` verified in z3 0.19.8 (Feb 2026 release) |
| `petgraph` 0.8 (existing) | Rust 1.85+ | Directed graph for happens-before; no upgrade needed |
| `syn` 2.x (existing) | Rust 1.85+ | New attributes `#[fn_spec]`, `#[sep_pre]`, `#[sep_post]`, `#[verify_async]` use same syn 2.x patterns |
| SMT-LIB2 (Array theory) | Z3, CVC5 1.x, Yices 2.x | All three backends support QF_ALIA; weak memory UF queries need quantifiers (Z3/CVC5 preferred) |

---

## Sources

### High Confidence (Official Docs + GitHub)

- [z3 crate 0.19 docs — Model struct API](https://docs.rs/z3/latest/z3/struct.Model.html) — `eval`, `get_const_interp`, `get_func_interp`, `iter` methods verified
- [z3.rs GitHub — v0.19.8 release Feb 13 2026](https://github.com/prove-rs/z3.rs) — current version confirmed
- [rustc_mir_transform::coroutine](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_mir_transform/coroutine/index.html) — `Yield` terminator and state machine transform
- [cvc5 theory references — Separation Logic (experimental)](https://cvc5.github.io/docs/cvc5-1.0.2/theories/theories.html) — confirmed experimental status
- [SL-COMP: Encoding Separation Logic in SMT-LIB v2.5](https://sl-comp.github.io/docs/smtlib-sl.pdf) — `declare-heap`, `sep`, `pto`, `wand` operators

### Medium Confidence (Academic Literature, Verified Against Implementations)

- [Wolff et al. 2021 — Modular Specification and Verification of Closures in Rust](https://pm.inf.ethz.ch/publications/WolffBilyMathejaMuellerSummers21.pdf) — spec entailment FOL encoding (Prusti implementation)
- [Dartagnan — BMC for Weak Memory](https://hernanponcedeleon.github.io/pdfs/svcomp20.pdf) — `ψ_prog ∧ ψ_assert ∧ ψ_mm` SMT encoding pattern
- [XMM — Relaxed Memory Concurrency Re-executed, POPL 2025](https://www.st.ewi.tudelft.nl/sschakraborty/papers/popl2025-xmm.pdf) — acquire/release semantics in axiomatic model
- [Automating Separation Logic Using SMT (Piskac/Wies/Zufferey)](https://cs.nyu.edu/~wies/publ/tr_automating_separation_logic_using_smt.pdf) — heap-as-array + ownership encoding approach
- [Philip Zucker — Shallow Embedding Logics in Z3](https://www.philipzucker.com/shallow_logic_knuckle/) — SL encoding in Z3 arrays (March 2025)

### Low Confidence (WebSearch only, not officially verified)

- CVC5 SL no theory-mixing limitation: inferred from "safe-options disables SL" and absence of combined QF_SLIA logic in SL-COMP — needs direct CVC5 testing to confirm

---

*Stack research for: rust-fv v0.4 — counterexample generation, async/await, weak memory, closure entailments, separation logic*
*Researched: 2026-02-19*
*Confidence: HIGH (zero new crates required; all features build on verified existing stack)*
