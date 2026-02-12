# Feature Landscape: Advanced Verification Features

**Domain:** Advanced formal verification for Rust
**Researched:** 2026-02-11
**Confidence:** HIGH

## Context

This research focuses on **7 advanced features** for a subsequent milestone building on rust-fv v0.1's foundation:

**Already implemented (v0.1):**
- Path-sensitive VCGen with loop invariants
- Inter-procedural verification with contract summaries
- Ownership-aware verification (move/copy/borrow)
- Quantifiers (forall/exists) with trigger inference
- Prophecy variables for &mut reasoning
- Generic monomorphization
- Formula simplification, VC caching, parallel verification
- cargo verify with diagnostics and JSON output

**New features to research:**
1. Recursive function verification
2. Closure verification
3. Trait object verification
4. Unsafe code verification
5. Lifetime reasoning
6. Floating-point verification
7. Concurrency verification

---

## Table Stakes

Features users expect in advanced verification tools. Missing = incomplete tool.

| Feature | Why Expected | Complexity | Dependencies | Notes |
|---------|--------------|------------|--------------|-------|
| **Recursive function verification with termination** | Recursion ubiquitous in algorithms (factorial, tree traversal, divide-and-conquer). Users assume verifiers handle it. | MEDIUM | Requires: Well-founded relations, decreases clause, fuel mechanism | Verus: `decreases` clause + optional proof function. Creusot: `variant` clause in Why3. Dafny standard. |
| **Simple closure verification** (non-capturing, capturing immutable) | Rust uses closures extensively (iterators, callbacks). Must verify closure-using code. | MEDIUM | Requires: First-class function encoding, environment capture model | Prusti: prototype PR #138. Verus: proof closures in PR #1524. Kani: bounded verification of closures. |
| **Basic lifetime reasoning** (lifetime parameters, borrow expiry) | Lifetimes are Rust's defining feature. Verification must respect lifetime constraints. | HIGH | Requires: Prophecy variables (DONE), borrow tracking, lifetime logic | RustBelt: lifetime logic in Iris. Creusot: prophecy-based. Already have prophecy variables - extend to full lifetime reasoning. |
| **Unsafe code detection** (flag unsafe blocks, basic pointer checks) | Unsafe code bypasses Rust safety. Users expect warnings + basic validation. | LOW-MEDIUM | Requires: MIR inspection, pointer encoding, undefined behavior detection | Kani: detects UB in unsafe. Miri: dynamic checking. Don't need full verification - flag + best-effort checks. |
| **Basic trait object verification** (monomorphic trait calls, simple vtables) | Rust uses trait objects for dynamic dispatch (Box<dyn Trait>). Common in real code. | HIGH | Requires: Trait encoding (DONE via generics), vtable modeling, dynamic dispatch encoding | Kani: first tool to verify trait objects (2022). Build on existing generic support. |

## Differentiators

Features that set advanced tools apart. Valued by expert users.

| Feature | Value Proposition | Complexity | Dependencies | Notes |
|---------|-------------------|------------|--------------|-------|
| **Advanced recursive verification** (mutual recursion, fuel control, separate proof functions) | Handle complex algorithms (parser combinators, tree balancing, graph algorithms). | HIGH | Requires: Table stakes recursion + fuel annotations, proof mode, mutual recursion graph | Verus: `decreases ... via ...` for separate proofs. Fuel parameter controls unfolding depth. Differentiates from basic recursion. |
| **Higher-order closure verification** (closures as arguments, FnOnce/FnMut/Fn semantics) | Verify iterator combinators (map, filter, fold), callback-based APIs. | VERY HIGH | Requires: Specification entailments, closure trait encoding, closure mode tracking | Prusti research: specification entailments for HOF. Verus: proof closures. Academic frontier. |
| **Floating-point correctness** (beyond just safety) | Prove numerical properties (accuracy bounds, NaN handling, rounding). | VERY HIGH | Requires: SMT-LIB FPA theory, rounding mode modeling, NaN reasoning | Stainless (2026): FP verification. Z3 FPA theory exists but expensive. Most tools skip this. |
| **Concurrent separation logic** (atomic invariants, thread-local reasoning) | Verify lock-free algorithms, concurrent data structures, sync primitives. | VERY HIGH | Requires: Separation logic, atomic operations, invariant protocol, VerusSync-style tokens | Creusot 0.9.0: AtomicI32, AtomicInvariant. Verus: VerusSync research. Bleeding edge. |
| **Lifetime inference for verification** (auto-infer prophecy annotations) | Reduce annotation burden for &mut reasoning. | HIGH | Requires: Table stakes lifetime reasoning + inference algorithm | Creusot 0.9.0: auto-infers immutable vars in loops. Extend to prophecies. High automation value. |

## Anti-Features

Features that seem valuable but create problems. Avoid or limit scope.

| Feature | Why Requested | Why Problematic | Alternative |
|---------|---------------|-----------------|-------------|
| **Verify all unsafe code automatically** | "Unsafe is dangerous - auto-check it" | Pointer aliasing undecidable. Breaks ownership. Requires whole-program analysis. | **Flag unsafe blocks.** Basic checks (null, bounds). Bounded verification (Kani-style). Full verification requires manual annotations. |
| **Full floating-point verification by default** | "Verify numerical correctness" | SMT FPA theory slow. NaN != NaN breaks reflexivity. Most code doesn't need it. | **Integer verification only (v0.2).** FP as opt-in expert feature (v1.0+). Most users verify logic, not numerics. |
| **Automatic closure contract inference** | "Closures should just work" | Closure capture complex (move vs borrow). Higher-order specs require entailments. | **Require explicit closure specs.** Like function contracts. Clear annotation burden. |
| **Verify dynamic trait objects without vtable constraints** | "Polymorphism should be transparent" | Dynamic dispatch hides concrete type. Vtable correctness non-trivial. | **Require trait-level contracts.** Verify vtable construction. Monomorphic fast path where possible. |
| **General recursion without decreases clause** | "Tool should infer termination" | Termination undecidable. False positives frustrate users. | **Require explicit `decreases`.** Like loop invariants. Clear, predictable. |
| **Concurrent verification without synchronization specs** | "Rust prevents data races - auto-verify" | Rust prevents *data races*, not *race conditions*. Atomics have acquire/release semantics. | **Require atomic invariants.** Like Creusot AtomicInvariant. Explicit synchronization specs. |

---

## Feature Dependencies

```
Recursive Function Verification
    └──requires──> Termination Checking (decreases clause)
                       └──uses──> Well-Founded Relations
    └──requires──> Fuel Mechanism (control unfolding)
    └──builds-on──> Inter-procedural Verification (DONE)

Closure Verification
    ├──basic──> Environment Capture Encoding
    │               └──builds-on──> Ownership Reasoning (DONE)
    └──advanced──> Specification Entailments
                       └──requires──> Higher-Order Function Contracts

Trait Object Verification
    └──requires──> Vtable Encoding
    └──requires──> Trait-Level Contracts
    └──builds-on──> Generic Verification (DONE via monomorphization)

Unsafe Code Verification
    ├──detection──> MIR Inspection (flag unsafe blocks)
    ├──basic-checks──> Pointer Bounds Checks
    └──full-verification──> Separation Logic + Manual Annotations
                               └──requires──> Concurrency Verification (for aliasing)

Lifetime Reasoning
    └──requires──> Prophecy Variables (DONE)
    └──requires──> Borrow Tracking
    └──requires──> Lifetime Logic (RustBelt-style)
    └──enhances──> Ownership Reasoning (DONE)

Floating-Point Verification
    └──requires──> SMT-LIB FPA Theory
    └──requires──> Rounding Mode Encoding
    └──requires──> NaN Handling (non-reflexive equality)
    └──conflicts-with──> Standard SMT Automation (slow)

Concurrency Verification
    └──requires──> Separation Logic (Iris-style)
    └──requires──> Atomic Invariants
    └──requires──> Thread-Local Reasoning
    └──requires──> Atomic Operations Encoding
    └──builds-on──> Ownership Reasoning (DONE)
```

---

## Feature Breakdown

### 1. Recursive Function Verification

**What it is:**
Verify recursive functions (factorial, tree traversal, divide-and-conquer) by proving termination via well-founded relations and checking correctness via SMT.

**Expected behavior:**
- User annotates recursive function with `#[decreases(n)]` clause (like Verus, Dafny)
- Tool checks measure strictly decreases on each recursive call
- Tool encodes function via fuel mechanism (bounded unfolding) or proof function

**Patterns from existing tools:**

**Verus approach (SMT-based):**
- `decreases` clause specifies measure (e.g., `n`, `(a, b)` lexicographic)
- Optional `when` clause for conditional termination
- Optional `via` clause to separate proof from definition
- Fuel parameter controls unfolding depth (spec functions use fuel)
- For complex proofs: write recursive proof function as induction
- **Source:** [Verus decreases reference](https://verus-lang.github.io/verus/guide/reference-decreases.html)

**Creusot approach (Why3-based):**
- `variant` clause in Why3 encoding
- Leverages Why3's termination checker
- Supports lexicographic measures
- **Source:** [Creusot Why3 encoding](https://github.com/creusot-rs/creusot/blob/master/ARCHITECTURE.md)

**F*/Dafny approach (standard):**
- Well-founded relation on measure
- Check measure decreases on each call
- Lexicographic tuples for mutual recursion
- **Source:** [F* termination proofs](https://fstar-lang.org/tutorial/book/part1/part1_termination.html)

**Complexity factors:**
- MEDIUM for simple recursion (single decreases measure)
- HIGH for mutual recursion (need call graph + lexicographic measures)
- HIGH for fuel mechanism (need bounded unfolding in SMT)

**Dependencies on existing:**
- Builds on inter-procedural verification (DONE)
- Builds on contract summaries (DONE)
- Needs: termination checker, fuel annotations

**Recommended approach:**
1. **Phase 1 (table stakes):** Single-function recursion with `decreases` clause. Check measure decreases. Encode via fuel (bounded unfolding).
2. **Phase 2 (differentiator):** Mutual recursion, `via` proof functions (Verus-style), automatic fuel inference.

**Test cases:**
- Factorial: `decreases(n)`
- Tree depth: `decreases(tree_size(node))`
- Mutual recursion: even/odd functions with lexicographic measure

---

### 2. Closure Verification

**What it is:**
Verify code using closures (lambdas) including environment capture and higher-order functions (map, filter, fold).

**Expected behavior:**
- User annotates closure with `requires`/`ensures` (like Prusti proposal)
- Tool encodes closure as function + captured environment struct
- Tool checks closure body satisfies contract
- Tool checks closure usage (HOF) satisfies specification entailments

**Patterns from existing tools:**

**Prusti approach (Viper-based):**
- **Status:** Prototype in PR #138, not yet released
- Syntax: `closure!(requires(a > b), ensures(result > b), |a, b| { a })`
- Requires explicit types and return type
- Specification entailments for HOF: caller proves closure satisfies required contract
- **Source:** [Prusti closures](https://viperproject.github.io/prusti-dev/user-guide/verify/closure.html)

**Verus approach (SMT-based):**
- **Proof closures:** Recent PR #1524
- Closures in proof mode for induction
- Full closure support still research
- **Source:** [Verus proof closures PR](https://github.com/verus-lang/verus/pull/1524)

**Academic approach:**
- Paper: "Modular specification and verification of closures in Rust" (2021)
- Key idea: Closures capture environment; must specify which vars captured and how (move vs borrow)
- Specification entailments: For `fn apply<F: Fn(i32) -> i32>(f: F)`, caller proves closure satisfies `Fn(i32) -> i32` contract
- **Source:** [ACM paper](https://dl.acm.org/doi/10.1145/3485522)

**Complexity factors:**
- MEDIUM for non-capturing closures (desugar to function)
- MEDIUM for capturing immutable environment (encode as struct fields)
- HIGH for capturing mutable environment (requires &mut reasoning - DONE via prophecy)
- VERY HIGH for higher-order functions (requires specification entailments)

**Dependencies on existing:**
- Builds on ownership reasoning (DONE) for capture semantics
- Builds on prophecy variables (DONE) for mutable captures
- Needs: Closure trait encoding (Fn/FnMut/FnOnce), specification entailments for HOF

**Recommended approach:**
1. **Phase 1 (table stakes):** Non-capturing closures + immutable captures. Syntax: `closure!(requires(...), ensures(...), |args| body)`. Encode as function + env struct.
2. **Phase 2 (differentiator):** Mutable captures (use prophecy), higher-order functions (specification entailments).

**Test cases:**
- Iterator map: `arr.iter().map(|x| x * 2).collect()`
- Filter with closure: `arr.iter().filter(|&x| x > 0)`
- Fold with accumulator: `arr.iter().fold(0, |sum, x| sum + x)`

---

### 3. Trait Object Verification

**What it is:**
Verify code using dynamic dispatch via trait objects (`Box<dyn Trait>`, `&dyn Trait`).

**Expected behavior:**
- User defines trait with contracts on methods
- User creates trait object from concrete type
- Tool verifies trait object method calls satisfy contracts
- Tool verifies vtable construction is sound

**Patterns from existing tools:**

**Kani approach (bounded model checking):**
- **First tool to verify trait objects (2022)**
- Key insight: Vtable is MIR-level construct - verify vtable construction + indirect calls
- Encodes vtable as function pointer table
- Verifies concrete type satisfies trait bounds
- **Source:** [Kani trait objects paper](https://ieeexplore.ieee.org/document/9794041)

**Prusti approach (Viper-based):**
- **Status:** No support in early versions (pre-2022)
- Would require encoding trait as interface + vtable as dispatch table

**Verus approach (SMT-based):**
- Extensive trait support at type level
- Trait bounds encoded in SMT
- Monomorphization-based (like generics)
- Not clear if dynamic dispatch supported (likely no based on forked compiler limitations)

**Vtable structure:**
- Vtable = data structure with:
  - Function pointers for each trait method
  - Destructor pointer
  - Size and alignment metadata
- Fat pointer = (data pointer, vtable pointer)
- **Source:** [Rust trait objects internals](https://cs.wellesley.edu/~avh/dyn-trait-icse-seip-2022-preprint.pdf)

**Complexity factors:**
- HIGH: Vtable encoding in SMT (uninterpreted functions or function pointers)
- HIGH: Dynamic dispatch (indirect call requires all possible implementations)
- MEDIUM: Trait-level contracts (like interface contracts)

**Dependencies on existing:**
- Builds on generic verification (DONE) - trait as generic bound
- Builds on inter-procedural verification (DONE) - method calls
- Needs: Vtable encoding, trait-level contracts, dynamic dispatch encoding

**Recommended approach:**
1. **Phase 1 (table stakes):** Monomorphic trait objects (known set of impls). Encode vtable as dispatch map. Verify each impl satisfies trait contract.
2. **Phase 2 (differentiator):** Full dynamic dispatch with vtable soundness proofs.

**Test cases:**
- Simple trait object: `fn process(obj: &dyn Display) { println!("{}", obj) }`
- Trait object in collection: `Vec<Box<dyn Animal>>` with verified method calls
- Trait object with associated types

---

### 4. Unsafe Code Verification

**What it is:**
Verify or flag unsafe Rust code (raw pointers, transmute, unsafe blocks).

**Expected behavior:**
- **Minimum:** Flag unsafe blocks, warn user
- **Basic:** Check null pointers, bounds on raw pointer access
- **Advanced:** Full separation logic verification (like RustBelt)

**Patterns from existing tools:**

**Kani approach (bounded model checking):**
- Detects undefined behavior in unsafe code
- Checks: null deref, use-after-free, invalid transmute
- **Limitations:** No data races, no pointer aliasing (sequential code only)
- **Source:** [Kani undefined behavior](https://model-checking.github.io/kani/undefined-behaviour.html)

**Miri approach (dynamic checking):**
- Interpreter-based UB detection
- Checks: pointer aliasing (Stacked Borrows), uninitialized memory, data races
- Not formal verification (dynamic, not exhaustive)
- **Source:** [Miri 2026 POPL paper](https://research.ralfj.de/papers/2026-popl-miri.pdf)

**RustBelt approach (formal semantics):**
- Iris separation logic in Coq
- Lifetime logic for borrows
- Proves soundness of unsafe abstractions (e.g., Vec, Rc)
- **Complexity:** Requires manual proofs, expert knowledge
- **Source:** [RustBelt](https://plv.mpi-sws.org/rustbelt/)

**RefinedRust approach (type system):**
- Refined ownership types
- Borrow names link mutable references to underlying data
- Foundational verification in Coq
- **Source:** [RefinedRust paper](https://plv.mpi-sws.org/refinedrust/paper-refinedrust.pdf)

**Complexity factors:**
- LOW: Flag unsafe blocks (MIR inspection)
- MEDIUM: Basic null/bounds checks (encode pointers as bitvectors)
- VERY HIGH: Full separation logic (requires Iris-style reasoning, manual proofs)

**Dependencies on existing:**
- Builds on MIR inspection (DONE)
- Builds on ownership reasoning (DONE) - unsafe bypasses this
- Needs: Pointer encoding, separation logic (for advanced), UB detection

**Recommended approach:**
1. **Phase 1 (table stakes):** Flag unsafe blocks. Basic checks (null, bounds). Warn user.
2. **Phase 2 (optional):** Bounded verification (Kani-style) for unsafe.
3. **Phase 3 (research):** Separation logic for unsafe abstractions (expert feature).

**Test cases:**
- Detect null dereference: `unsafe { *ptr }`
- Detect out-of-bounds: `unsafe { *ptr.add(n) }`
- Flag transmute: `unsafe { transmute::<i32, u32>(x) }`

---

### 5. Lifetime Reasoning

**What it is:**
Verify code respects Rust's lifetime constraints (borrow expiry, lifetime parameters, subtyping).

**Expected behavior:**
- Tool tracks lifetime parameters ('a, 'b)
- Tool ensures borrows expire when lifetime ends
- Tool verifies lifetime bounds (e.g., `T: 'a`)
- Tool uses prophecy variables to reason about future values after borrow expires

**Patterns from existing tools:**

**Creusot approach (prophecy-based):**
- Prophecy variables (`^x`) represent future value after borrow expires
- Prophecy solves "borrow ends later" problem elegantly
- Example: `fn double(x: &mut i32) { *x = *x * 2 }` - prophecy `^x` is `old(x) * 2`
- **Source:** [Creusot POPL 2026 tutorial](https://popl26.sigplan.org/details/POPL-2026-tutorials/6/Creusot-Formal-verification-of-Rust-programs)

**RustBelt approach (lifetime logic in Iris):**
- Custom lifetime logic for semantic requirements
- Lifetimes as tokens in separation logic
- Opening/closing borrows modeled as token exchange
- **Source:** [RustBelt paper](https://people.mpi-sws.org/~dreyer/papers/rusthornbelt/paper.pdf)

**RefinedRust approach (borrow names):**
- Borrow names link mutable reference to underlying data
- Lifetime logic derived from RustBelt
- Type system automation (less manual than RustBelt)
- **Source:** [RefinedRust paper](https://plv.mpi-sws.org/refinedrust/paper-refinedrust.pdf)

**Aeneas approach (functional translation):**
- Ownership-centric semantics (loans, not lifetimes)
- Backward functions to handle borrow expiry
- Translates to pure lambda calculus (no memory model)
- **Source:** [Aeneas paper](https://arxiv.org/abs/2206.07185)

**Complexity factors:**
- HIGH: Lifetime parameter tracking
- HIGH: Borrow expiry reasoning (prophecy-based or lifetime logic)
- MEDIUM: Lifetime bounds checking (static)

**Dependencies on existing:**
- Builds on prophecy variables (DONE) - already have `^` operator
- Builds on ownership reasoning (DONE) - lifetimes extend ownership
- Needs: Lifetime parameter encoding, borrow expiry tracking, lifetime logic

**Recommended approach:**
1. **Phase 1 (table stakes):** Lifetime parameter tracking. Verify lifetime bounds. Use existing prophecy for &mut.
2. **Phase 2 (differentiator):** Full lifetime logic (RustBelt-inspired). Auto-infer prophecy annotations (Creusot 0.9.0 approach).

**Test cases:**
- Lifetime parameter: `fn longest<'a>(x: &'a str, y: &'a str) -> &'a str`
- Borrow expiry: Verify prophecy `^x` after mutable borrow
- Lifetime bounds: `struct Ref<'a, T: 'a> { r: &'a T }`

---

### 6. Floating-Point Verification

**What it is:**
Verify correctness of floating-point arithmetic (f32, f64) beyond just safety.

**Expected behavior:**
- **Basic:** Flag floating-point operations (warn precision loss)
- **Advanced:** Prove numerical properties (accuracy bounds, NaN handling)

**Patterns from existing tools:**

**Stainless approach (2026):**
- Recent work on FP verification (January 2026)
- Combines FP with higher-order functions, ADTs
- Key challenge: NaN != NaN breaks reflexivity
- **Source:** [Stainless FP paper](https://www.arxiv.org/pdf/2601.14059)

**SMT-LIB FPA theory:**
- IEEE 754-2008 floating-point standard
- SMT sorts: `Float16`, `Float32`, `Float64`
- Operations: `fp.add`, `fp.mul`, `fp.div` with rounding modes
- **Challenge:** Expensive for SMT solvers
- **Source:** [SMT-LIB FPA](https://smt-lib.org/theories-FloatingPoint.shtml)

**Z3 FPA support:**
- Z3 supports FPA theory
- Approximation framework for performance
- 10x speedup over bit-blasting for SAT problems
- **Source:** [Z3 FPA approximation](https://pmc.ncbi.nlm.nih.gov/articles/PMC6109943/)

**KeY approach (Java verification):**
- Combines SMT-LIB FPA with rule-based reasoning
- Exploit complementary strengths: SMT for numerics, rules for structure
- **Source:** [KeY FP verification](https://link.springer.com/article/10.1007/s10009-022-00691-x)

**Complexity factors:**
- LOW: Flag FP operations (warn user)
- MEDIUM: Encode FP in SMT-LIB FPA
- VERY HIGH: Prove numerical correctness (slow SMT, NaN reasoning)

**Dependencies on existing:**
- Builds on SMT solver integration (DONE) - add FPA theory
- Conflicts with fast SMT (FPA is slow)
- Needs: FPA encoding, rounding mode, NaN handling

**Recommended approach:**
1. **Phase 1 (v0.2):** Integer-only verification. Flag FP as unsupported.
2. **Phase 2 (v1.0+):** Opt-in FP verification for expert users. Use Z3 FPA theory. Warn about performance.

**Test cases:**
- Basic FP: `fn add_floats(a: f64, b: f64) -> f64 { a + b }`
- NaN handling: `fn safe_div(a: f64, b: f64) -> f64 { if b.is_nan() { 0.0 } else { a / b } }`
- Accuracy bound: Prove `|computed - exact| < epsilon`

---

### 7. Concurrency Verification

**What it is:**
Verify thread-safe Rust code (threads, atomics, locks, channels).

**Expected behavior:**
- User annotates atomic invariants (what must hold around atomic ops)
- Tool verifies invariants preserved across threads
- Tool checks synchronization correctness (acquire/release semantics)

**Patterns from existing tools:**

**Creusot approach (AtomicInvariant):**
- Creusot 0.9.0 (January 2026): Adds `AtomicI32`, `AtomicInvariant` inspired by Iris
- Atomic invariant = predicate that holds around atomic operation
- Example: `AtomicInvariant(counter, |v| v >= 0)` ensures counter never negative
- **Source:** [Creusot 0.9.0 devlog](https://creusot-rs.github.io/devlog/2026-01-19/)

**Verus approach (VerusSync):**
- Permission-based (token-based) concurrency toolkit
- Sharding strategy: split state into ghost shards per thread
- Transitions define how threads update shared state + ghost shards
- Makes concurrency proofs nearly as easy as sequential
- **Source:** [Verus concurrent separation logic](https://matthias-brun.ch/assets/publications/verus_oopsla2023.pdf)

**Iris approach (separation logic):**
- Higher-order concurrent separation logic
- Invariants protect shared state
- Opening/closing invariants requires tokens
- RustBelt builds on Iris
- **Source:** [Iris invariants](https://iris-project.org/tutorial-pdfs/lecture9-invariants.pdf)

**Miri approach (dynamic checking):**
- Detects data races at runtime
- Not formal verification (dynamic tool)
- **Source:** [Miri 2026 POPL](https://research.ralfj.de/papers/2026-popl-miri.pdf)

**Complexity factors:**
- VERY HIGH: Separation logic (Iris-style)
- VERY HIGH: Atomic invariants (protocol design)
- VERY HIGH: Thread-local reasoning (ownership + sync)

**Dependencies on existing:**
- Builds on ownership reasoning (DONE) - threads have separate ownership
- Builds on ghost state (prophecy variables DONE) - extend to tokens
- Needs: Separation logic, atomic operations encoding, invariant protocol

**Recommended approach:**
1. **Phase 1 (v1.0+):** Single-threaded verification only. Flag concurrency as unsupported.
2. **Phase 2 (v2.0+):** Atomic invariants (Creusot-style). Sequential consistency model.
3. **Phase 3 (research):** Full VerusSync-style sharding + protocols.

**Test cases:**
- Atomic counter: `AtomicI32` with increment/decrement
- Lock-protected state: Mutex with invariant on guarded data
- Lock-free queue: Atomic operations with happens-before reasoning

---

## MVP Recommendation

### Prioritization for Subsequent Milestone

Given rust-fv v0.1 foundation, prioritize features by **impact × feasibility**:

**Phase 1 (High Impact, Medium Feasibility) — Table Stakes:**

1. **Recursive function verification** — MEDIUM complexity, HIGH user value
   - Users expect recursion support (factorial, tree traversal)
   - Builds on existing inter-procedural verification
   - Deliverable: `#[decreases(n)]` clause, termination checking, fuel-based encoding

2. **Basic closure verification** — MEDIUM complexity, HIGH user value
   - Rust uses closures everywhere (iterators)
   - Deliverable: Non-capturing + immutable captures, `closure!(requires, ensures, |args| body)` syntax

3. **Basic trait object verification** — HIGH complexity, HIGH user value
   - Common in real Rust (Box<dyn Trait>)
   - Builds on existing generic monomorphization
   - Deliverable: Trait-level contracts, vtable encoding for known impls

4. **Lifetime reasoning** — HIGH complexity, CRITICAL for Rust
   - Already have prophecy variables - extend to full lifetime tracking
   - Deliverable: Lifetime parameter tracking, borrow expiry verification, lifetime bounds

5. **Unsafe code detection** — LOW complexity, HIGH safety value
   - Flag unsafe blocks, basic pointer checks
   - Deliverable: Warn on unsafe, check null/bounds, prepare for future bounded verification

**Phase 2 (Differentiators) — Defer to v1.0+:**

6. **Floating-point verification** — VERY HIGH complexity, LOW current demand
   - Defer: Most users verify logic, not numerics
   - Plan: Opt-in FP for v1.0+ expert users

7. **Concurrency verification** — VERY HIGH complexity, VERY HIGH value (but small user base)
   - Defer: Bleeding edge, requires separation logic
   - Plan: Research collaboration, v2.0+ feature

---

## Feature Complexity Matrix

| Feature | Implementation Cost | User Value | Dependency Risk | Priority |
|---------|---------------------|------------|-----------------|----------|
| Recursive functions | MEDIUM (termination checker + fuel) | HIGH (ubiquitous) | LOW (builds on inter-proc) | **P1** |
| Basic closures | MEDIUM (env encoding) | HIGH (iterators) | LOW (builds on ownership) | **P1** |
| Trait objects | HIGH (vtable + dispatch) | HIGH (common in Rust) | MEDIUM (needs trait contracts) | **P1** |
| Lifetime reasoning | HIGH (lifetime logic) | CRITICAL (Rust essence) | LOW (have prophecy) | **P1** |
| Unsafe detection | LOW (MIR + basic checks) | HIGH (safety) | LOW (incremental) | **P1** |
| Higher-order closures | VERY HIGH (spec entailments) | MEDIUM (advanced users) | HIGH (academic frontier) | **P2** |
| Floating-point | VERY HIGH (FPA theory) | LOW (niche) | MEDIUM (SMT performance) | **P3** |
| Concurrency | VERY HIGH (separation logic) | VERY HIGH (but niche) | VERY HIGH (Iris-level) | **P3** |

**Priority key:**
- **P1**: Table stakes for advanced verifier (v0.2 milestone)
- **P2**: Differentiators for expert users (v1.0)
- **P3**: Research features (v2.0+)

---

## Competitor Feature Comparison

| Feature | Verus | Prusti | Kani | Creusot | rust-fv v0.1 | rust-fv v0.2 Goal |
|---------|-------|--------|------|---------|--------------|-------------------|
| **Recursive functions** | ✅ decreases + fuel | ✅ variant | ❌ bounded | ✅ variant | ❌ | ✅ decreases + fuel |
| **Basic closures** | 🔬 proof closures | 🔬 PR #138 | ✅ bounded | ✅ partial | ❌ | ✅ closure!(...) |
| **HOF closures** | 🔬 research | 🔬 spec entailments | ❌ | ⚠️ limited | ❌ | 🔬 research (v1.0+) |
| **Trait objects** | ⚠️ via generics | ❌ early versions | ✅ vtables | ✅ via Why3 | ⚠️ via generics | ✅ vtable + dispatch |
| **Lifetime reasoning** | ⚠️ tracked borrows | ⚠️ pledges | ✅ bit-precise | ✅ prophecies | ⚠️ prophecy vars | ✅ full lifetime logic |
| **Unsafe detection** | ❌ | ❌ | ✅ UB checks | ❌ | ❌ | ✅ flag + basic checks |
| **Unsafe verification** | ❌ | ❌ | ✅ bounded MC | ❌ | ❌ | ⏳ v1.0+ (bounded) |
| **Floating-point** | ❌ | ❌ | ⚠️ bit-precise | ❌ | ❌ | ⏳ v1.0+ (FPA opt-in) |
| **Concurrency** | 🔬 VerusSync | ❌ | ❌ | ✅ AtomicI32 (0.9.0) | ❌ | ⏳ v2.0+ (research) |

**Legend:**
- ✅ Full support
- ⚠️ Partial/limited
- ❌ No support
- 🔬 Research/experimental
- ⏳ Planned future

**rust-fv positioning after v0.2:**
- **Matches Verus:** Recursive functions, closures, lifetime reasoning
- **Matches Creusot:** Prophecy-based lifetimes, trait objects
- **Matches Kani:** Unsafe detection (but not full bounded MC yet)
- **Unique:** Zero-friction cargo workflow + Verus-level expressiveness

---

## Implementation Guidance

### Recursive Function Verification

**Design:**
- Syntax: `#[decreases(n)]` or `#[decreases((tree_size(node), height))]` for lexicographic
- Semantics:
  - Check measure is well-founded (always decreasing to base case)
  - Encode function via **fuel mechanism**: `f_fuel_k(args)` unfolds k times
  - Generate VC: `measure(recursive_args) < measure(current_args)` at each call site

**Example:**
```rust
#[decreases(n)]
#[requires(n >= 0)]
#[ensures(result == n * factorial(n - 1))]
fn factorial(n: i64) -> i64 {
    if n <= 1 { 1 } else { n * factorial(n - 1) }
}
```

**VC generation:**
1. Check `decreases(n)` decreases: `(n - 1) < n` when `n > 1` ✓
2. Encode as `factorial_fuel_k(n)`:
   - `k = 0`: uninterpreted (returns arbitrary value)
   - `k = 1`: `if n <= 1 { 1 } else { n * factorial_fuel_0(n - 1) }`
   - `k = 2`: `if n <= 1 { 1 } else { n * factorial_fuel_1(n - 1) }`
3. Check postcondition with sufficient fuel

**Complexity:**
- MEDIUM: Single recursion with simple measure
- HIGH: Mutual recursion (need call graph + lex measure)

**Test cases:**
- Factorial
- Fibonacci
- Binary tree depth
- GCD (Euclid's algorithm)

---

### Basic Closure Verification

**Design:**
- Syntax: `closure!(requires(x > 0), ensures(result > 0), |x: i32| -> i32 { x + 1 })`
- Semantics:
  - Non-capturing closure → desugar to function
  - Immutable capture → encode as struct with fields
  - Verify closure body satisfies contract
  - At call site: substitute closure contract

**Example:**
```rust
fn apply_twice(x: i32) -> i32 {
    let adder = closure!(
        requires(x > 0),
        ensures(result == x + 1),
        |x: i32| -> i32 { x + 1 }
    );
    adder(adder(x))
}
```

**Encoding:**
1. Desugar closure to:
   ```rust
   struct Closure_adder { }
   fn Closure_adder_call(env: Closure_adder, x: i32) -> i32 {
       x + 1
   }
   ```
2. Verify `Closure_adder_call` satisfies `requires(x > 0)`, `ensures(result == x + 1)`
3. At call sites: substitute contract

**Complexity:**
- MEDIUM: Non-capturing + immutable captures
- HIGH: Mutable captures (use prophecy)
- VERY HIGH: Higher-order functions (spec entailments)

**Test cases:**
- Non-capturing: `|x| x + 1`
- Immutable capture: `let y = 5; |x| x + y`
- Iterator map: `arr.iter().map(|x| x * 2)`

---

### Trait Object Verification

**Design:**
- Syntax: Trait with `#[requires]`/`#[ensures]` on methods
- Semantics:
  - Encode trait as SMT sort with method signatures
  - Encode vtable as dispatch map: `vtable[Type][Method] = impl_function`
  - Verify each impl satisfies trait contract
  - At trait object call site: use trait contract (not impl contract)

**Example:**
```rust
trait Drawable {
    #[requires(true)]
    #[ensures(result >= 0)]
    fn area(&self) -> i32;
}

struct Circle { radius: i32 }

impl Drawable for Circle {
    fn area(&self) -> i32 { 3 * self.radius * self.radius }
}

fn total_area(shapes: &[Box<dyn Drawable>]) -> i32 {
    shapes.iter().map(|s| s.area()).sum()
}
```

**Encoding:**
1. Trait contract: `Drawable::area` requires `true`, ensures `result >= 0`
2. Verify `Circle::area` satisfies trait contract:
   - VC: `3 * radius * radius >= 0` (true for all `radius`)
3. At call site `s.area()`:
   - Use trait contract (not Circle impl)
   - Ensures `result >= 0` without knowing concrete type

**Complexity:**
- HIGH: Vtable encoding
- HIGH: Dynamic dispatch (all possible impls)
- MEDIUM: Trait-level contracts (like interface)

**Test cases:**
- Simple trait object: `Box<dyn Display>`
- Trait object collection: `Vec<Box<dyn Animal>>`
- Trait with associated types

---

### Lifetime Reasoning

**Design:**
- Syntax: Lifetime parameters `'a`, lifetime bounds `T: 'a`
- Semantics:
  - Track lifetime scope: where lifetime starts/ends
  - At borrow: create prophecy `^x` for value after lifetime expires
  - At lifetime end: verify prophecy holds
  - Check lifetime bounds statically

**Example:**
```rust
fn swap<'a>(x: &'a mut i32, y: &'a mut i32) {
    let temp = *x;
    *x = *y;
    *y = temp;
}
```

**Encoding:**
1. Prophecy: `^x` is value of `x` after lifetime `'a` expires
2. Prophecy: `^y` is value of `y` after lifetime `'a` expires
3. VC: After swap, `^x == old(y)` and `^y == old(x)`

**Complexity:**
- HIGH: Lifetime parameter tracking
- HIGH: Prophecy for borrow expiry
- MEDIUM: Lifetime bounds checking

**Test cases:**
- Simple borrow: `fn double(x: &mut i32) { *x *= 2 }`
- Lifetime parameter: `fn longest<'a>(x: &'a str, y: &'a str) -> &'a str`
- Lifetime bounds: `struct Ref<'a, T: 'a> { r: &'a T }`

---

### Unsafe Code Detection

**Design:**
- Phase 1: Flag unsafe blocks, warn user
- Phase 2: Basic checks (null, bounds)
- Phase 3: Bounded verification (like Kani)

**Example:**
```rust
fn read_ptr(ptr: *const i32) -> i32 {
    unsafe {
        *ptr  // WARN: Unsafe dereference. Check null before dereferencing.
    }
}
```

**Encoding (Phase 2):**
1. Encode pointer as bitvector (address)
2. Check: `ptr != 0` (null check)
3. Check: `ptr >= base && ptr < base + size` (bounds check, if base known)

**Complexity:**
- LOW: Flag unsafe (MIR inspection)
- MEDIUM: Null/bounds checks
- VERY HIGH: Full separation logic

**Test cases:**
- Null dereference detection
- Bounds check for pointer arithmetic
- Transmute safety (flag as unchecked)

---

## Sources

### Recursive Functions
- [Verus decreases - Verus Tutorial and Reference](https://verus-lang.github.io/verus/guide/reference-decreases.html)
- [Verus spec vs proof functions](https://verus-lang.github.io/verus/guide/spec_vs_proof.html)
- [F* Termination Proofs](https://fstar-lang.org/tutorial/book/part1/part1_termination.html)
- [Creusot Why3 encoding](https://github.com/creusot-rs/creusot/blob/master/ARCHITECTURE.md)
- [Lean Well-Founded Recursion](https://lean-lang.org/doc/reference/latest/Recursive-Definitions/Well-Founded-Recursion/)

### Closures
- [Prusti Closures](https://viperproject.github.io/prusti-dev/user-guide/verify/closure.html)
- [Modular specification and verification of closures in Rust (ACM)](https://dl.acm.org/doi/10.1145/3485522)
- [Verus proof closures PR](https://github.com/verus-lang/verus/pull/1524)

### Trait Objects
- [Verifying Dynamic Trait Objects in Rust (paper)](https://cs.wellesley.edu/~avh/dyn-trait-icse-seip-2022-preprint.pdf)
- [Kani trait objects (IEEE)](https://ieeexplore.ieee.org/document/9794041)

### Unsafe Code
- [Kani Undefined Behaviour](https://model-checking.github.io/kani/undefined-behaviour.html)
- [Miri 2026 POPL paper](https://research.ralfj.de/papers/2026-popl-miri.pdf)
- [RustBelt](https://plv.mpi-sws.org/rustbelt/)
- [RefinedRust paper](https://plv.mpi-sws.org/refinedrust/paper-refinedrust.pdf)

### Lifetime Reasoning
- [Creusot POPL 2026 Tutorial](https://popl26.sigplan.org/details/POPL-2026-tutorials/6/Creusot-Formal-verification-of-Rust-programs)
- [RustHornBelt paper](https://people.mpi-sws.org/~dreyer/papers/rusthornbelt/paper.pdf)
- [Aeneas: Rust Verification by Functional Translation](https://arxiv.org/abs/2206.07185)
- [RefinedRust paper](https://plv.mpi-sws.org/refinedrust/paper-refinedrust.pdf)

### Floating-Point
- [Stainless FP verification (2026)](https://www.arxiv.org/pdf/2601.14059)
- [SMT-LIB Floating-Point Theory](https://smt-lib.org/theories-FloatingPoint.shtml)
- [Z3 FPA approximation](https://pmc.ncbi.nlm.nih.gov/articles/PMC6109943/)
- [KeY FP verification](https://link.springer.com/article/10.1007/s10009-022-00691-x)

### Concurrency
- [Creusot 0.9.0 devlog](https://creusot-rs.github.io/devlog/2026-01-19/)
- [Verus concurrent separation logic (OOPSLA)](https://matthias-brun.ch/assets/publications/verus_oopsla2023.pdf)
- [Iris invariants](https://iris-project.org/tutorial-pdfs/lecture9-invariants.pdf)
- [Miri 2026 POPL](https://research.ralfj.de/papers/2026-popl-miri.pdf)

---

**Research Confidence:** HIGH
- All major tools surveyed (Verus, Prusti, Kani, Creusot)
- Official documentation + academic papers + 2026 developments
- Builds on rust-fv v0.1 foundation (known capabilities)
- Complexity assessed based on existing tool implementations
