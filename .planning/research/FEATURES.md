# Feature Landscape: v0.4 Full Rust Verification

**Domain:** SMT-based formal verification for Rust — advanced language features
**Researched:** 2026-02-19
**Confidence:** MEDIUM-HIGH

---

## Context

This research covers **5 advanced verification features** for rust-fv v0.4, building on v0.3's production usability (stdlib contracts, triggers, IDE integration, bv2int).

**Already implemented (v0.1–v0.3 Complete):**
- Proc macro annotations, path-sensitive VCGen, inter-procedural verification
- Z3/CVC5/Yices multi-solver backends, incremental VC caching
- VSCode/rust-analyzer IDE integration, stdlib contracts (Vec/HashMap/Option/Result/Iterator)
- Closures via defunctionalization (Fn/FnMut/FnOnce), traits/behavioral subtyping
- Lifetimes/NLL, unsafe/heap-as-array, IEEE 754 FPA
- Bounded concurrency/happens-before (SeqCst only), bv2int optimization, trigger customization

**New features to research (v0.4 focus):**
1. Counterexample generation (from SMT models)
2. Async/await verification (Future state machines)
3. Weak memory models (Relaxed/Acquire/Release atomics)
4. Higher-order closures with specification entailments
5. Separation logic for heap reasoning (unsafe raw pointer contracts)

---

## Table Stakes

Features that, once v0.4 is scoped this way, users expect to be present. Missing these = the feature feels half-done.

| Feature | Why Expected | Complexity | Notes |
|---------|--------------|------------|-------|
| **Counterexample generation** | When a VC fails, "assertion failed at line 42" is useless without knowing *what values* triggered it. Every mature verifier (Dafny, Kani, Why3) shows concrete variable values when the SMT solver returns SAT (the negated VC is satisfiable). | MEDIUM | Z3's `get-model` returns a SAT model when the negated VC is satisfiable. The hard part is mapping SMT model variables back to Rust source identifiers, pretty-printing types (structs, enums, references), and filtering out internal SSA temporaries. This is a prerequisite for all other features: without it, debugging any v0.4 failure is blind. |
| **Higher-order closures: basic spec entailment** | rust-fv already handles closures via defunctionalization. When a closure is passed to a higher-order function (e.g., `map`, `filter`, user-defined HOF), the callee's spec must be able to express what the closure must guarantee. Without this, HOF contracts are vacuously true or unprovable. | HIGH | Prusti's `|=` operator (specification entailment) is the reference design. The user writes `f |= |x: i32| [requires(x > 0), ensures(result >= 0)]` in the `#[requires]` of the HOF. Internally this encodes behavioral subtyping: the closure's actual pre/post must be at least as strong as the entailment requires. Depends on defunctionalization (already done). |

---

## Differentiators

Features that separate rust-fv from tools that stop at sequential SMT verification.

| Feature | Value Proposition | Complexity | Notes |
|---------|-------------------|------------|-------|
| **Async/await verification** | Async Rust is pervasive (Tokio, async-std); no existing tool fully verifies async Rust functionally. Kani explicitly says "await expressions: No." Verus has an early draft PR (#1839) not yet merged. Being first with functional verification of async/await would be a significant differentiator. | VERY HIGH | The canonical encoding: desugared async fn → state machine enum implementing `Future`, each `.await` point → enum variant with live variables + awaited future. VCGen must handle state machine transitions as control-flow paths. Specs on async fns follow the same `#[requires]/#[ensures]` syntax but apply to the *completed* computation (the `Poll::Ready` value). SeqCst executor model (single-threaded polling) suffices for functional properties. Does NOT require weak memory model. |
| **Weak memory model: Acquire/Release atomics** | SeqCst atomics (already in v0.3) cover safe concurrent code. Acquire/Release is the next tier: used in `Arc<T>` (reference counting), `Mutex<T>` (lock/unlock), `RwLock<T>`, `Once`. Without Acq/Rel, can't verify any lock-based concurrent data structure. | VERY HIGH | The standard encoding (from Dartagnan/POPL 2025 XMM work) is axiomatic: program events (reads/writes/fences) + happens-before (hb) + modification order (mo) + reads-from (rf) + coherence axioms. SMT encodes: "does any execution satisfying the memory model axioms violate this assertion?" Builds on existing happens-before infrastructure. Relaxed (no synchronization) can be added simultaneously at low marginal cost. |
| **Separation logic: raw pointer contracts** | Unsafe Rust with raw pointers (`*mut T`, `*const T`) cannot be verified with the existing heap-as-array model for non-trivial data structures (linked lists, trees, custom allocators). Separation logic's separating conjunction (A * B: A and B own disjoint heap regions) is the standard tool. Verus uses `PtsTo<T>` ghost resources; VeriFast uses `*P |-> V` annotations. | VERY HIGH | Two sub-features: (a) `PtsTo<T>` ownership predicate in spec language — user writes `#[requires(pts_to(p, v))]` to say pointer p points to value v and we own it; (b) separating conjunction in specs — `A * B` encodes disjoint ownership. SMT encoding: encode ownership as ghost integer tokens; separating conjunction as disjointness constraints. Depends on existing unsafe/heap-as-array model (upgrade, not replace). |

---

## Anti-Features

Features to explicitly NOT build for v0.4.

| Anti-Feature | Why Avoid | What to Do Instead |
|--------------|-----------|-------------------|
| **Full Iris/Coq integration** | Iris is a Coq proof assistant framework requiring manual interactive theorem proving. Integration means exposing Coq tactics to Rust developers — a completely different user model than SMT automation. Years of research effort (RustBelt/RefinedRust scope). | Use SMT-encodable fragment of separation logic only. Support `pts_to` and separating conjunction for common patterns. Document that complex invariants (e.g., fractional permissions, ghost state monoids) are deferred to a hypothetical Iris backend. |
| **Full C++11 memory model (all orderings)** | SeqCst + Acq/Rel covers 99%+ of real Rust code. SeqCst-Fences, consume ordering (deprecated in C++17), and mixed-size accesses are edge cases with almost no Rust usage. The SMT encoding complexity grows super-linearly with the number of orderings supported. | Support: Relaxed, Acquire, Release, AcqRel, SeqCst. Explicitly document: no consume ordering (deprecated), no mixed-size atomics (UB in Rust), no sequentially-consistent fences as distinct from SeqCst stores. |
| **Async runtime verification (Tokio scheduler)** | Verifying the *scheduler* behavior (task wakeup, executor fairness, Tokio specifics) is a completely different problem from verifying what an async function *computes*. Requires modeling executor non-determinism, wakeup order, and runtime state. Academic open problem. | Verify async fns with the "single-threaded sequential polling" model: each `.await` point returns the value when the future completes, without modeling when/how it is polled. This covers all functional properties. Document explicitly: no liveness properties (termination of async tasks), no runtime/scheduler modeling. |
| **Closure contract inference** | Automatically inferring what spec a closure must satisfy when passed to a HOF (e.g., inferring that `map`'s closure must preserve positivity) is undecidable in general. No tool has solved this. Verus/Prusti both require manual annotation. | Require explicit spec entailments. Provide good error messages: "cannot verify HOF call: closure spec not entailed. Add `#[requires(f |= |x| [ensures(result > 0)])]`." |
| **Separation logic for safe Rust** | Safe Rust's borrow checker already provides separation logic guarantees (unique ownership = separating conjunction, shared refs = fractional permissions). Re-encoding this in SMT duplicates the compiler's work and creates false positives. | Use borrow-checker information (already available via MIR) to extract ownership facts. Only deploy explicit separation logic for `unsafe` blocks with raw pointers where the borrow checker is disabled. |
| **Concurrent async verification (multi-threaded executor)** | Multi-threaded async (tokio's `spawn`, `tokio::task`, shared `Arc<Mutex<T>>` across tasks) requires both async state machine modeling AND weak memory model reasoning simultaneously. The combination is a current research frontier with no practical tool support. | Verify single-threaded async (functional properties) and concurrent safe code (SeqCst/Acq/Rel) as separate features. Document that cross-cutting async + concurrent verification is future work (v0.5+). |

---

## Feature Landscape: What Each Feature Looks Like

### Feature 1: Counterexample Generation

**What the user sees:**
```
error[rust-fv]: postcondition not satisfied
  --> src/lib.rs:12:5
   |
12 |   x / y
   |   ^^^^^
   |
   = postcondition: result > 0
   = counterexample:
       x = -5   (i32)
       y = 2    (i32)
       result = -2  (i32)
   = note: function called with x = -5, y = 2 violates ensures(result > 0)
```

**What the SMT encoding is:**
- VCGen already generates negated VC: `NOT (precondition => postcondition)`
- When Z3 returns SAT, issue `(get-model)` command
- Z3 returns S-expression model: `((x (- 5)) (y 2) (result (- 2)) ...)`
- Map SMT variable names back to Rust source names via existing symbol table
- Filter out internal SSA temporaries (variables prefixed `_`)
- Pretty-print: i32 as decimal, u8/u16/u32/u64 as decimal (or hex for addresses), bool as true/false, struct fields recursively

**What "passing" means:**
- Counterexample shown for every VC failure (not just "assertion failed at line N")
- Counterexample values are valid Rust values (no internal SMT artifacts)
- Multi-variable counterexample shows all function parameters + local variables
- If solver returns Unknown, show "solver could not find counterexample (timeout)" instead of silence

**SMT complexity:** LOW — Z3 already returns models; the work is mapping/formatting
**Implementation complexity:** MEDIUM — SSA→source variable mapping requires tracking through MIR lowering

**Dependencies on existing features:**
- VCGen (v0.1 Phase 1) — already generates SMT scripts with named variables
- Symbol table (v0.1 Phase 1) — maps SSA names to Rust source names
- Z3 native API (v0.1 Phase 4) — already used; `model()` call is direct
- Diagnostic infrastructure (v0.1 Phase 5) — extend to include counterexample block

---

### Feature 2: Async/Await Verification

**What the user writes:**
```rust
#[requires(x > 0)]
#[ensures(result > x)]
async fn fetch_and_increment(x: i32) -> i32 {
    let fetched = db_fetch(x).await;   // .await point
    fetched + 1
}

// HOF async spec:
#[requires(x > 0)]
#[ensures(result > 0)]
async fn process(x: i32) -> i32 {
    fetch_and_increment(x).await
}
```

**What the SMT encoding is:**
- Rust compiler desugars `async fn` into a `Future`-implementing state machine enum
- The MIR for an async fn already encodes the state machine (rust-fv reads MIR)
- VCGen treats each `.await` as a function call to the awaited future's `poll` function that returns `Poll::Ready(v)` (complete value) — sequential polling model
- State machine transitions = control-flow edges in VCGen (already handled)
- `#[requires]/#[ensures]` apply to the overall computation from entry to `Poll::Ready` return
- No executor modeling needed for functional properties

**What "passing" means:**
- Annotated async fn verified: SMT proves all paths from entry to `Poll::Ready(result)` satisfy postconditions given preconditions
- No modeling of wakeup/polling count — only what the final result is
- `.await` on verified async fn uses that fn's contract (just like sync inter-procedural verification)
- Unverified awaited futures get havoced (current assumption: may return any value satisfying type constraints)

**What the user does NOT get:**
- No liveness: cannot prove async fn ever returns (termination not modeled)
- No scheduler reasoning: cannot prove concurrent async tasks don't deadlock
- No Tokio-specific properties (wakeup order, fairness)

**SMT complexity:** MEDIUM — state machine is already in MIR; VCGen treats `.await` as call
**Implementation complexity:** HIGH — MIR for async fns has generator/coroutine structure (GeneratorKind, SwitchInt on state); requires special handling in MIR→IR lowering

**Dependencies on existing features:**
- MIR converter (driver, v0.1) — extend to handle GeneratorKind::Async
- IR (analysis, v0.1) — add AsyncAwait IR node or normalize to call
- VCGen (analysis, v0.1) — handle Poll::Ready/Poll::Pending state transitions
- Inter-procedural verification (v0.1 Phase 3) — async fn calls other async fns

**Reference:** Verus PR #1839 (draft, not merged) uses wrapper function + external_body pattern. rust-fv can take a simpler approach via MIR directly since the state machine is already materialized in MIR.

---

### Feature 3: Weak Memory Models (Relaxed/Acquire/Release)

**What the user writes (no new annotation syntax required):**
```rust
use std::sync::atomic::{AtomicI32, Ordering};

static X: AtomicI32 = AtomicI32::new(0);
static Y: AtomicI32 = AtomicI32::new(0);

#[thread_local_invariant(thread_id < 2)]
#[ensures(/* no assertion violation in any sequentially consistent execution */)]
fn message_passing_test() {
    // Thread 1:
    X.store(1, Ordering::Release);
    Y.store(1, Ordering::Release);

    // Thread 2:
    let y = Y.load(Ordering::Acquire);
    if y == 1 {
        let x = X.load(Ordering::Acquire);
        assert!(x == 1);  // Must hold under Acq/Rel
    }
}
```

**What the SMT encoding is (axiomatic memory model):**
- Represent each memory event as an SMT record: `(event_id thread_id location value ordering type)`
- Encode memory model relations as SMT functions:
  - `reads_from(r, w)`: read r gets value from write w
  - `happens_before(e1, e2)`: derived from program order + synchronizes_with
  - `synchronizes_with(w, r)`: write w (Release) synchronizes with read r (Acquire) if rf(r,w) ∧ w.ord=Release ∧ r.ord=Acquire
  - `modification_order(w1, w2)`: total order on writes to same location
- Coherence axioms (from C11/Rust memory model):
  - CoRR: if hb(r1,r2) and rf(r2,w), then not rf(r1,w') where mo(w,w')
  - CoWR: if hb(w,r) and rf(r,w'), then mo(w,w') or w=w'
  - CoRW, CoWW: similar
- Bounded: bound number of threads T and events per thread N (following v0.3 bounded concurrency approach)
- Existential: ∃ events. (program constraints) ∧ (memory model axioms) ∧ (¬assertion) — solver finds violating execution

**What "passing" means:**
- No reachable execution under the Rust memory model (RC11 for Relaxed/Acq/Rel) violates any assertion
- Races detected: if two threads access same non-atomic location where one is a write (data race = UB)
- Proof: UNSAT of the above existential (no violating execution exists)

**Relaxed ordering:** zero synchronization — adds events with `ord=Relaxed` to the encoding; relaxed reads can see any write in modification order (no happens-before constraint from Acq/Rel)

**SMT complexity:** HIGH — quadratic in number of events (pairwise relations); N threads × M events per thread → N×M events, N²×M² relation pairs
**Implementation complexity:** VERY HIGH — new IR nodes for atomic load/store/fence; new VCGen path for atomic operations; new SMT theory for memory model relations; interaction with existing happens-before encoding (SeqCst)

**Dependencies on existing features:**
- Bounded concurrency (v0.3 Phase 12) — provides thread model, thread_local_invariant
- Happens-before encoding (v0.3 Phase 12) — extend rather than replace
- SMTLib crate (v0.1) — add uninterpreted sort for events, relation functions
- VCGen (v0.1) — new case for MIR atomic load/store/fence instructions

**Reference:** Dartagnan (BMC for Weak Memory), POPL 2025 XMM paper. Encoding follows "Effective Program Verification for Relaxed Memory Models" (Summers/Mueller 2018, UBC).

---

### Feature 4: Higher-Order Closures with Specification Entailments

**What the user writes:**
```rust
// Higher-order function with closure spec entailment
#[requires(
    n >= 0,
    f |= |x: i32| [requires(x >= 0), ensures(result >= 0)]
)]
#[ensures(result >= 0)]
fn map_non_negative(v: &Vec<i32>, f: impl Fn(i32) -> i32) -> i32 {
    let mut sum = 0;
    for &x in v.iter() {
        if x >= 0 {
            sum += f(x);   // verified: f's precondition holds (x >= 0)
        }
    }
    sum
}

// User calls it with a specific closure:
let result = map_non_negative(&vec, |x| x * 2);
// rust-fv verifies: |x| x * 2 satisfies [requires(x >= 0), ensures(result >= 0)]
```

**What the SMT encoding is:**

The existing defunctionalization (v0.2) represents closures as structs. Specification entailment adds:

1. **Entailment check at call site:** For `f |= |x| [requires(P(x)), ensures(Q(x, result))]`:
   - Generate VC: `∀ env, x. P(x) ∧ closure_body(env, x) = r ⟹ Q(x, r)`
   - Where `closure_body` is the already-defunctionalized closure function
   - This VC is added to the verification conditions for the *caller*, not the HOF

2. **HOF body uses entailment:** Inside HOF body, at `f(x)` call site:
   - Assume `P(x)` holds (check as VC)
   - Conclude `Q(x, result)` holds after call
   - This is standard pre/post contract use (already in VCGen)

3. **Stateful closures (FnMut):** Track closure environment evolution:
   - `env_before` → call → `env_after`
   - Entailment: `∀ env_before, x. P(env_before, x) ∧ next(env_before, x) = (env_after, r) ⟹ Q(env_before, x, env_after, r)`
   - Requires existential quantification over FnMut call sequences

**Spec entailment syntax (new in proc macro):**
```
f |= |params| [requires(P), ensures(Q)]
```
Encoded as doc attribute: `rust_fv::entails::f::|params|::requires::P::ensures::Q`

**What "passing" means:**
- HOF body verified: every call to the closure argument is safe given the entailment
- Call site verified: the specific closure passed satisfies the entailment
- Behavioral subtyping respected: closure's actual spec is at least as strong as required

**SMT complexity:** MEDIUM — quantified over closure inputs; triggers needed for instantiation
**Implementation complexity:** HIGH — new syntax (|= operator), new spec IR node, new VCGen rule for entailment checks, interaction with defunctionalization's environment encoding

**Dependencies on existing features:**
- Defunctionalization (v0.2 Phase 9) — closure → struct representation already done
- Trigger customization (v0.3) — entailment VCs use quantifiers, triggers needed
- Spec parser (v0.1 Phase 1) — extend to parse `|=` operator
- Inter-procedural (v0.1 Phase 3) — entailment check at call site follows same pattern

**Reference:** Prusti specification entailment (`|=` syntax), Wolff et al. OOPSLA 2021 "Modular Specification and Verification of Closures in Rust."

---

### Feature 5: Separation Logic for Heap Reasoning

**What the user writes:**
```rust
use std::ptr;

// Raw pointer function: requires ownership of the pointed-to memory
#[requires(pts_to(p, _v))]          // owns *p (any current value)
#[ensures(pts_to(p, new_val))]      // *p now equals new_val
unsafe fn write_ptr(p: *mut i32, new_val: i32) {
    ptr::write(p, new_val);
}

// Disjoint ownership: two pointers don't alias
#[requires(pts_to(p, vp) * pts_to(q, vq))]   // * = separating conjunction
#[ensures(pts_to(p, vq) * pts_to(q, vp))]    // values swapped
unsafe fn swap(p: *mut i32, q: *mut i32) {
    let tmp = ptr::read(p);
    ptr::write(p, ptr::read(q));
    ptr::write(q, tmp);
}

// Linked list node predicate (user-defined recursive predicate)
#[ghost_predicate]
fn list_seg(head: *mut Node, tail: *mut Node, vals: Seq<i32>) -> bool {
    if head == tail {
        vals.is_empty()
    } else {
        exists(|v, next| pts_to(head, Node { val: v, next }) * list_seg(next, tail, vals.tail()))
    }
}
```

**What the SMT encoding is:**

Separation logic in SMT uses a *permission/token* model (standard approach in Viper/Silicon):

1. **`pts_to(p, v)` predicate:**
   - Ghost resource: an uninterpreted token `own(p)` asserting exclusive write access to address p
   - Heap function `heap: Addr → Value` maps addresses to current values
   - `pts_to(p, v)` ≡ `own(p) ∧ heap[p] = v`
   - Tokens are linear (consumed when used, cannot be duplicated)

2. **Separating conjunction `A * B`:**
   - `(A * B)(heap, tokens)` ≡ `∃ heap1, heap2, tokens1, tokens2. heap = heap1 ⊕ heap2 ∧ tokens = tokens1 ⊕ tokens2 ∧ A(heap1, tokens1) ∧ B(heap2, tokens2)`
   - In SMT: encoded as `disjoint_dom(tokens1, tokens2) ∧ A(...) ∧ B(...)`
   - Key: `disjoint_dom` proves non-aliasing

3. **`ptr::read(p)` → load:** `assume own(p); result := heap[p]`
4. **`ptr::write(p, v)` → store:** `assume own(p); heap := heap[p ↦ v]`
5. **Frame rule:** If function consumes `pts_to(p, v)` and caller owns `pts_to(p, v) * pts_to(q, w)`, caller retains `pts_to(q, w)` untouched

6. **User-defined predicates (`#[ghost_predicate]`):**
   - Encoded as SMT recursive functions (or uninterpreted with axioms for soundness)
   - Folding/unfolding predicates = assert/assume the definition

**What "passing" means:**
- All `ptr::read`/`ptr::write` in unsafe block are preceded by valid `pts_to` ownership in precondition
- All `pts_to` resources are transferred correctly (no double-free, no use-after-free)
- Separating conjunction proves aliasing freedom (two mutable raw pointers don't alias)
- Custom predicates fold/unfold correctly (heap invariant maintained)

**SMT complexity:** HIGH — separation logic in SMT requires quantifiers over heap/token partitions; careful trigger design needed; recursive predicates require finiteness bound or approximation
**Implementation complexity:** VERY HIGH — new ghost type system (`pts_to`, `*` operator in specs), new IR for heap resources, new VCGen rules for unsafe loads/stores, interaction with existing unsafe/heap-as-array model (upgrade)

**Dependencies on existing features:**
- Unsafe/heap-as-array (v0.2 Phase 11) — existing heap model; separation logic replaces/extends it
- Trigger customization (v0.3) — separation logic VCs are quantifier-heavy
- SMTLib crate (v0.1) — new sorts for heap, token domains
- Spec parser (v0.1) — new `pts_to`, `*` syntax, `#[ghost_predicate]`
- Quantifier encoding (v0.1 Phase 2) — separation logic uses quantifiers for partition

---

## Feature Dependencies

```
Counterexample Generation
  → Requires: VCGen with SMT model output (v0.1) ✓
  → Requires: Z3 native API (v0.1 Phase 4) ✓
  → Requires: Symbol table / SSA→source name mapping (v0.1) ✓
  → Requires: Diagnostic infrastructure (v0.1 Phase 5) ✓
  → Provides: Debuggability for all other v0.4 features (build first)
  → Enhances: All features (counterexample for any VC failure)

Async/Await Verification
  → Requires: MIR converter (v0.1) — extend for GeneratorKind::Async
  → Requires: Inter-procedural VCGen (v0.1 Phase 3) ✓
  → Requires: Closures/defunctionalization (v0.2) ✓ (async closures reuse)
  → Requires: Counterexample generation (v0.4, build before async for debuggability)
  → Conflicts with: Weak memory model (different concurrency model; don't combine in Phase 1)

Weak Memory Model (Relaxed/Acq/Rel)
  → Requires: Bounded concurrency/happens-before (v0.3 Phase 12) ✓
  → Requires: SMTLib new sorts (v0.1 smtlib crate, extend)
  → Requires: Counterexample generation (v0.4, essential for debugging memory model violations)
  → Extends: SeqCst atomic encoding (v0.3) — adds new orderings
  → Conflicts with: Async (see anti-features; keep separate in roadmap)

Higher-Order Closures with Spec Entailments
  → Requires: Defunctionalization (v0.2 Phase 9) ✓
  → Requires: Trigger customization (v0.3) ✓ (entailment VCs are quantified)
  → Requires: Spec parser extension (v0.1) — extend for |= syntax
  → Provides: Correct HOF verification (currently HOFs with closure args have weak contracts)
  → Enhances: Stdlib contracts (v0.3) — Iterator.map/filter with proper closure specs

Separation Logic for Heap
  → Requires: Unsafe/heap-as-array (v0.2 Phase 11) ✓ (replace/extend)
  → Requires: Trigger customization (v0.3) ✓ (separation logic VCs are quantifier-heavy)
  → Requires: SMTLib extension for heap/token sorts (v0.1 smtlib crate)
  → Requires: Counterexample generation (v0.4, essential for debugging pointer errors)
  → Conflicts with: Heap-as-array (use separation logic for unsafe blocks, array for safe)
```

### Dependency Notes

- **Counterexample generation must be built first:** All other v0.4 features produce new, complex VC failures that are impossible to debug without concrete counterexamples. Build it in Phase 1.
- **Async and weak memory model must be kept separate:** Async adds coroutine/state-machine complexity; weak memory adds memory-model complexity. Combining both in one verification problem is a current research frontier with no practical solution. Build as distinct features in separate phases.
- **Spec entailments enhance stdlib contracts:** Once HOF closure specs work, stdlib's `Vec::iter().map()` and `filter()` can have verified closure composition specs — a natural extension of v0.3 stdlib contracts.
- **Separation logic replaces heap-as-array for unsafe:** The v0.2 heap-as-array model (treat heap as one big array) cannot prove aliasing freedom. Separation logic supersedes it for `unsafe` blocks. For safe Rust, the borrow checker provides the separation argument implicitly — no change needed.

---

## MVP Definition

### v0.4 Launch With (Essential for the Milestone)

- [x] **Counterexample generation** — unlocks debuggability for all other features; foundational
- [x] **Higher-order closures with spec entailments** — completes closure story started in v0.2; moderate complexity, high value
- [x] **Async/await verification (sequential polling model)** — differentiator; no competitor does it
- [x] **Weak memory model: Acquire/Release atomics** — completes atomic story; needed for Arc/Mutex verification
- [x] **Separation logic: pts_to + separating conjunction** — completes unsafe story; needed for custom allocators, linked lists

### Suggested Phase Order (Based on Dependencies)

**Phase 1: Counterexample Generation**
- Rationale: enables debugging for all subsequent phases. Low risk, medium effort.

**Phase 2: Higher-Order Closures with Spec Entailments**
- Rationale: builds directly on v0.2 defunctionalization + v0.3 triggers. Highest user-facing impact per effort. No new IR concepts.

**Phase 3: Async/Await Verification**
- Rationale: requires counterexample generation (Phase 1) for debuggability. MIR async desugaring is complex; needs isolation from other new features.

**Phase 4: Weak Memory Model (Relaxed/Acquire/Release)**
- Rationale: builds on existing SeqCst/happens-before. Requires counterexample generation. Keep separate from async (different concurrency model).

**Phase 5: Separation Logic for Heap Reasoning**
- Rationale: most complex. Builds on all previous phases. Requires counterexample generation (pointer errors are impossible to debug otherwise). New ghost type system, new VCGen rules.

### Future Consideration (v0.5+)

- [ ] **Multi-threaded async (async + weak memory combined)** — research frontier, no practical tool exists; defer until both features are stable individually
- [ ] **Recursive separation logic predicates (full induction)** — bounded unrolling covers most use cases; full induction requires interactive proof steps; defer
- [ ] **Async liveness properties** — proving async fns terminate requires temporal logic or ranking functions for coroutines; out of scope for SMT-only approach
- [ ] **Consume memory ordering** — deprecated in C++17, essentially unused in Rust; no demand

---

## Feature Prioritization Matrix

| Feature | User Value | Implementation Cost | Priority |
|---------|------------|---------------------|----------|
| Counterexample generation | HIGH | MEDIUM | P1 |
| Higher-order closure spec entailments | HIGH | HIGH | P1 |
| Async/await verification | VERY HIGH | VERY HIGH | P1 |
| Weak memory model (Acq/Rel) | HIGH | VERY HIGH | P1 |
| Separation logic (pts_to) | HIGH | VERY HIGH | P1 |

All five are P1 for v0.4 — the milestone commits to all five. Phase ordering addresses the implementation cost sequentially.

---

## Competitor Feature Analysis

| Feature | Verus | Prusti | Kani | Creusot | rust-fv v0.4 |
|---------|-------|--------|------|---------|--------------|
| Counterexample generation | No (UNSAT only) | Limited | YES (concrete playback, byte vectors) | No | YES (variable values, pretty-printed) |
| Async/await | Draft PR #1839 (not merged) | No | No (explicitly "await: No") | No | YES (sequential polling model) |
| Relaxed atomics | No | No | No (sequential only) | No | YES (Acq/Rel/Relaxed) |
| SeqCst atomics | Partial | No | No | No | YES (v0.3) |
| HOF closure spec entailment | Partial (fn specs) | Prototype (not merged) | No | No (uses prophecy) | YES (|= syntax) |
| Separation logic (raw ptr) | YES (PtsTo linear ghost) | Implicit via Viper | No | No | YES (pts_to + *) |

**Key differentiator position:** rust-fv v0.4 would be the first SMT-based Rust verifier with async/await functional verification. Kani (bounded MC) is the only other tool with concrete counterexamples, but uses byte-vector format; rust-fv will provide human-readable Rust-typed values.

---

## Complexity Notes

**Counterexample Generation (MEDIUM):**
- Z3's `model()` via native API is direct; already integrated
- SSA→source name mapping requires extending symbol table (currently tracks names through MIR lowering)
- Pretty-printer must handle Rust value types: primitives, tuples, structs, enums, references
- Risk: SSA temporaries leak into counterexample (filter by name convention)
- Risk: Z3 returns model with partial evaluation for quantified formulas (use `model_completion=true`)

**Async/Await Verification (HIGH):**
- MIR for async fns uses `GeneratorKind::Async` and `SwitchInt` on state discriminant
- Each await point introduces a `Yield` terminator in MIR
- VCGen must unfold state machine: track live variables across state transitions as SSA
- Key insight: treat `Poll::Ready(v)` as the function's return value; ignore `Poll::Pending` for functional verification
- Risk: nested async fns (async calling async); requires inter-procedural handling with coroutine MIR
- Risk: async closures (Rust 2024 edition) add another complexity layer; defer async closures to later

**Weak Memory Model (VERY HIGH):**
- Event representation: O(threads × events_per_thread) SMT variables
- Relation encoding: O(events²) pairs for `reads_from`, `happens_before`, etc.
- Coherence axioms: 4 axioms (CoRR, CoWR, CoRW, CoWW) × O(events²) instantiations
- Risk: SMT explosion — even with bounded model (10 events × 4 threads = 40 events → 1600 pairs)
- Mitigation: Dartagnan's "relation analysis" reduces encoding by static analysis of which pairs can relate; implement similar optimization
- Risk: Interaction with existing SeqCst encoding (SeqCst is a special case of the new model; unify carefully)

**Higher-Order Closure Spec Entailments (HIGH):**
- `|=` parsing: new token in spec language; extend proc macro and spec parser
- Entailment VC generation: `∀ env, args. pre(args) ⟹ post(closure_body(env, args))` — quantified, needs triggers
- FnMut entailments: must track environment evolution across calls; requires sequence of calls model
- Risk: FnOnce entailments are simplest (single call); FnMut (stateful) requires more careful encoding
- Risk: Nested HOFs (closure passed to closure-taking HOF) require recursive entailment unfolding

**Separation Logic (VERY HIGH):**
- New ghost type `pts_to<T>(p: *mut T, v: T)` in spec language: new proc macro, new IR type
- Separating conjunction `*` in specs: new operator with partition semantics
- SMT encoding of partition: `disjoint_dom(S1, S2) ∧ union(S1, S2) = full_dom`
- `#[ghost_predicate]` recursive predicates: SMT uninterpreted functions with axioms; bounded unrolling for automation
- Frame rule: automatically infer unchanged resources across function calls (may require manual annotation for complex cases)
- Risk: Ghost predicate unfolding not automated → user must manually call `fold`/`unfold` (like VeriFast)
- Risk: Separation logic + existing heap-as-array model conflict; must clearly separate unsafe (sep logic) from safe (array model)

---

## Sources

### Counterexample Generation
- [Kani Concrete Playback Internship 2022](https://model-checking.github.io//kani-verifier-blog/2022/09/22/internship-projects-2022-concrete-playback.html) — byte-vector format, generated unit test structure, debug workflow
- [Kani Concrete Playback Reference](https://model-checking.github.io/kani/reference/experimental/concrete-playback.html) — --concrete-playback=print|inplace flags, cargo kani playback subcommand
- [Better Counterexamples for Dafny (TACAS 2022)](https://dl.acm.org/doi/10.1007/978-3-030-99524-9_23) — SMT model to user-facing format transformation
- [Programming Z3](https://theory.stanford.edu/~nikolaj/programmingz3.html) — model() API, get-model, model.eval()
- [Kani Rust Feature Support](https://model-checking.github.io/kani/rust-feature-support.html) — async/await explicitly not supported

### Async/Await Verification
- [Verus Async PR #1839](https://github.com/verus-lang/verus/pull/1839) — wrapper function + external_body approach; draft, not merged
- [Rust Future Trait](https://doc.rust-lang.org/std/future/trait.Future.html) — poll() → Poll::Ready(T) | Poll::Pending contract
- [Understanding Async Await State Machine (eventhelix.com)](https://www.eventhelix.com/rust/rust-to-assembly-async-await/) — MIR state machine structure, enum variant per await point

### Weak Memory Models
- [BMC for Weak Memory Models: Relation Analysis (TACAS 2019)](https://link.springer.com/chapter/10.1007/978-3-030-25540-4_19) — Dartagnan's compact SMT encoding, relation analysis optimization
- [Relaxed Memory Concurrency Re-executed POPL 2025](https://www.st.ewi.tudelft.nl/sschakraborty/papers/popl2025-xmm.pdf) — XMM axiomatic-operational framework for Relaxed/Acq/Rel
- [Automating Deductive Verification for Weak-Memory (Summers/Mueller 2018)](https://www.cs.ubc.ca/~alexsumm/papers/SummersMueller18.pdf) — Viper-based encoding of release-acquire; relaxed separation logic
- [Strong Logic for Weak Memory: Release-Acquire in Iris (ECOOP 2017)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2017.17) — Iris logic for Acq/Rel reasoning
- [Modular Verification of Rust's Atomic ARC (arXiv 2025)](https://arxiv.org/pdf/2505.00449) — tied resources for modular atomic verification; ARC verification result
- [RustMC: GenMC for Rust (arXiv 2025)](https://arxiv.org/html/2502.06293) — stateless model checking for Rust weak memory; LLVM IR approach

### Higher-Order Closures / Spec Entailments
- [Prusti Specification Entailments](https://viperproject.github.io/prusti-dev/user-guide/verify/spec_ent.html) — `|=` syntax, HOF closure contract semantics
- [Modular Specification and Verification of Closures in Rust (OOPSLA 2021)](https://pm.inf.ethz.ch/publications/WolffBilyMathejaMuellerSummers21.pdf) — Wolff et al.; formal treatment of spec entailments
- [Prusti Closure Docs](https://viperproject.github.io/prusti-dev/user-guide/verify/closure.html) — current status: not yet supported in Prusti proper

### Separation Logic
- [VeriFast for Rust Reference](https://verifast.github.io/verifast/rust-reference/) — pts_to annotation syntax, unsafe function contracts, ghost predicates
- [VeriFast's Separation Logic (arXiv 2025)](https://arxiv.org/html/2505.04500) — higher-order separation logic without laters, comparison with Iris
- [A Hybrid Approach to Semi-automated Rust Verification (arXiv 2024)](https://arxiv.org/html/2403.15122v1) — Gillian-Rust; typed points-to predicate; combining safe (Creusot) and unsafe (sep logic) verification
- [Formal Foundations for Translational SL Verifiers (POPL 2025)](https://dardinier.me/papers/POPL25_CoreIVL.pdf) — CoreIVL; sound basis for SL-based tools (Viper, VeriFast, Gillian)
- [Contracts: owned and block primitives (rust-lang/compiler-team #942)](https://github.com/rust-lang/compiler-team/issues/942) — ownership assertions for unsafe Rust contracts

---

*Feature research for: rust-fv v0.4 Full Rust Verification*
*Researched: 2026-02-19*
*Confidence: MEDIUM-HIGH — Based on reference tool documentation, 2024-2025 papers, official feature tracking.*
*Note: Async/await encoding is MEDIUM confidence (Verus draft PR is not merged; no production tool exists); weak memory SMT complexity is HIGH confidence from Dartagnan literature.*
