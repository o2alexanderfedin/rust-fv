# Domain Pitfalls: Advanced Verification Features

**Domain:** Adding recursive functions, closures, trait objects, unsafe code, lifetime reasoning, floating-point, and concurrency verification to existing SMT-based Rust verifier
**Researched:** 2026-02-11
**Confidence:** MEDIUM-HIGH

## Executive Summary

This document catalogs pitfalls specific to **adding** advanced verification features to an existing SMT-based formal verification tool for Rust. Unlike general domain pitfalls (see existing PITFALLS.md), these focus on integration challenges and feature-specific mistakes when extending from basic verification (path-sensitive VCGen, loop invariants, ownership) to advanced capabilities.

**Critical insight:** Most failures come from **underestimating encoding complexity**, not implementation difficulty. Features that seem "just add support for X" require careful SMT encoding, trigger selection, and soundness proofs.

## Critical Pitfalls

### Pitfall 1: Recursive Function Termination Without Measure Functions

**What goes wrong:**
Verifier accepts recursive functions without termination proofs. SMT solver with recursive function axioms returns `sat` for unsatisfiable queries (soundness bug). Example: `fn loop_forever() { loop_forever() }` verifies successfully.

**Why it happens:**
- SMT-LIB supports recursive function definitions via axioms
- Without termination checking, axioms create circular reasoning: `f(x) = ... f(x) ...`
- SMT solver may assume function terminates when it doesn't
- Verus/F*/Dafny all require explicit decrease measures, but easy to forget in implementation

**Root cause:** First-order logic has no built-in notion of computation or termination. Encoding recursive functions as universally quantified formulas without well-founded measure allows non-terminating functions to "verify."

**Consequences:**
- **Soundness catastrophe**: Non-terminating function's postcondition vacuously verified
- User writes `#[ensures(false)] fn diverge() { diverge() }` and it verifies
- Downstream code assumes postcondition holds, builds on unsound foundation
- Whole verification result becomes meaningless

**Prevention:**
1. **Mandatory decreasing measures**: Require `#[decreases(expr)]` annotation on every recursive function
2. **Well-founded relation checking**: Verify measure decreases on recursive call by well-founded relation (e.g., `<` on natural numbers)
3. **Syntactic termination analysis first**: Before SMT encoding, check for obvious non-termination (direct recursion without decreasing arg)
4. **SMT encoding strategy**:
   - Use fuel-based unfolding (limit recursion depth) for bounded verification
   - For unbounded: generate VC that measure decreases: `old(measure) > new(measure) && new(measure) >= 0`
5. **Error on missing measure**: Don't default to "assume terminates" - fail loudly

**Warning signs:**
- Recursive function without `#[decreases]` attribute verifies
- Obvious infinite loop passes verification
- Verification time suspiciously fast for recursive code
- Adding contradictory postcondition to recursive function still verifies

**Example:**
```rust
// WRONG - verifies but diverges
#[ensures(result > 0)]
fn bad_factorial(n: i32) -> i32 {
    if n <= 0 { 1 } else { n * bad_factorial(n) }  // No decrease!
}

// CORRECT - requires decreasing measure
#[requires(n >= 0)]
#[decreases(n)]  // Measure must decrease
#[ensures(result > 0)]
fn factorial(n: i32) -> i32 {
    if n == 0 { 1 } else { n * factorial(n - 1) }  // n-1 < n
}
```

**Phase to address:** Phase N+1 (Recursive Functions)
- Research spike: Study F* and Verus termination checking (both proven sound)
- Implement syntactic decrease checker before SMT encoding
- Test with mutual recursion, nested recursion, structural recursion
- Defer higher-order recursion (functions as arguments) to later phase

**Confidence:** HIGH - Well-documented in F*, Dafny, Verus. Multiple sources confirm this is a soundness hole if omitted.

**Sources:**
- [Well-founded Relations and Termination (F* Tutorial)](https://fstar-lang.org/tutorial/book/part2/part2_well_founded.html)
- [Proofs of Termination (F* Tutorial)](https://fstar-lang.org/tutorial/book/part1/part1_termination.html)
- [Model Finding for Recursive Functions in SMT](http://homepage.divms.uiowa.edu/~ajreynol/ijcar16a.pdf)

---

### Pitfall 2: Closure Capture Semantics Mismodeling

**What goes wrong:**
Verifier treats all closures as `Fn` (shared borrow), misses mutations through `FnMut` captures or move semantics with `FnOnce`. Result: aliasing bugs accepted as safe, or correct code rejected.

**Why it happens:**
- Rust has three closure traits: `Fn`, `FnMut`, `FnOnce` with different capture semantics
- `FnMut` captures by mutable reference - changes observable outside closure
- `FnOnce` consumes captured values - can only be called once
- Naive encoding: treat closure as pure function, lose track of capture mode
- MIR desugars closures to structs + trait impl, but fields hidden in MIR representation

**Root cause:** Closures are first-class values with environment capture, not simple functions. Encoding must track:
1. Which variables captured and by what mode (move/borrow/mut borrow)
2. Lifetime of captured references
3. FnOnce exclusivity (can't call twice)

**Consequences:**
- **False negative**: `FnMut` closure mutates captured var, verifier doesn't track mutation, proves wrong postcondition
- **False positive**: `FnOnce` closure used correctly (called once), but verifier requires `Fn` contract, rejects correct code
- Cannot verify higher-order functions taking closures (`map`, `filter`, etc.)

**Prevention:**
1. **Detect closure trait bound in MIR**: Identify if parameter is `Fn`, `FnMut`, or `FnOnce`
2. **Capture environment encoding**:
   - `Fn`: Immutable borrows - use shared reference encoding (already have)
   - `FnMut`: Mutable borrows - use prophecy variables for final state (Phase 4)
   - `FnOnce`: Move semantics - mark captured values as consumed
3. **Track closure identity**: Closure is struct with fields (captured vars), not just function
4. **Encode trait bounds as preconditions**:
   - `F: Fn(i32) -> bool` → closure body doesn't mutate captures
   - `F: FnMut(i32) -> bool` → closure may mutate, requires prophecy for final capture values
   - `F: FnOnce(i32) -> bool` → closure called at most once
5. **Start simple**: Phase N only `Fn` (immutable captures), defer `FnMut`/`FnOnce` to Phase N+1

**Warning signs:**
- Higher-order function using closure parameter fails verification
- `FnMut` closure compiles but verification rejects
- Closure captures mutable reference, verification doesn't reflect mutation
- Same closure body verifies differently based on call site trait bound

**Example:**
```rust
// FnMut closure mutates capture
#[ensures(*counter == old(*counter) + arr.len())]
fn count_positive(arr: &[i32], counter: &mut i32) {
    arr.iter().for_each(|&x| {  // FnMut closure
        if x > 0 { *counter += 1; }  // Mutates capture
    });
}

// VCGen must track:
// 1. `counter` captured by mutable reference
// 2. Closure body increments `*counter`
// 3. Final value of `*counter` after all iterations
```

**Encoding strategy:**
```smt2
; Closure as struct with captured environment
(declare-datatype Closure (
  (mk-closure (captured-counter (Ref Int)))
))

; FnMut call updates captured state
(assert (= counter-final
           (+ counter-initial (count-if arr is-positive))))

; For FnOnce: track that closure consumed
(assert (=> (closure-called c) (not (closure-callable c))))
```

**Phase to address:** Phase N+2 (Closure Verification)
- Phase N+1: Higher-order functions with `Fn` closures (read-only)
- Phase N+2: Add `FnMut` with prophecy variables for captures
- Defer `FnOnce` consumption tracking if too complex

**Confidence:** MEDIUM - Creusot and Verus handle closures, but encoding is non-trivial. No detailed SMT encoding documentation found; requires source code study.

**Sources:**
- [FnMut in std::ops - Rust](https://doc.rust-lang.org/std/ops/trait.FnMut.html)
- [How Rust Handles Closures: Fn, FnMut, and FnOnce](https://leapcell.medium.com/how-rust-handles-closures-fn-fnmut-and-fnonce-5550724859ed)

---

### Pitfall 3: Trait Object Vtable Open-World vs Closed-World Assumptions

**What goes wrong:**
Verifier assumes closed-world (all trait implementations known at verification time), but Rust allows open-world (new impls in downstream crates). Result: verified code breaks when new trait impl added.

**Why it happens:**
- Trait objects use dynamic dispatch via vtable
- Verifier must model all possible vtable entries (trait method implementations)
- **Closed-world**: Assume only trait impls visible at verification time exist
- **Open-world**: Account for unknown future trait impls
- Closed-world is simpler but unsound for public traits

**Root cause:** Trait objects enable polymorphism, but verifier must decide: verify against all possible implementations (sound but expensive) or only known implementations (fast but unsound if trait is public).

**Consequences:**
- **Soundness bug**: Function verified against `dyn Trait`, assumes all impls satisfy property, but downstream crate adds impl violating property
- **Incompleteness**: Open-world verification rejects correct code because it can't prove property for all future impls
- **Maintenance hell**: Adding new trait impl invalidates previous verification results

**Prevention:**
1. **Default to open-world for public traits**: Require trait bounds to be provable from trait definition alone
2. **Closed-world opt-in**: `#[sealed]` or `#[verifier::closed]` attribute for traits verified in closed-world
3. **Encode trait methods as assumptions**: For `fn f(x: &dyn Trait)`, assume only trait method contracts, not implementation details
4. **Vtable modeling**:
   - Closed-world: Enumerate all known impls, VC per impl
   - Open-world: Treat vtable method as uninterpreted function satisfying trait contract
5. **Marker traits**: Track if trait is implemented via marker (e.g., `Send`, `Sync`) - these are closed-world by design

**Warning signs:**
- Verification succeeds in library crate, fails when new downstream crate added
- Trait object method call assumes specific implementation behavior
- Different verification results for same code when trait impl count changes
- Public trait verified in closed-world mode

**Example:**
```rust
pub trait Shape {
    #[ensures(result >= 0.0)]
    fn area(&self) -> f64;
}

// Closed-world: verify only against Circle, Rectangle
impl Shape for Circle { fn area(&self) -> f64 { PI * r * r } }
impl Shape for Rectangle { fn area(&self) -> f64 { w * h } }

#[requires(shapes.iter().all(|s| is_valid(s)))]
#[ensures(result >= 0.0)]  // Verified in closed-world
fn total_area(shapes: &[Box<dyn Shape>]) -> f64 {
    shapes.iter().map(|s| s.area()).sum()
}

// BREAKS when downstream crate adds:
impl Shape for Triangle {
    fn area(&self) -> f64 { -1.0 }  // BUG: violates contract!
}
```

**Encoding strategy:**
```smt2
; Open-world: vtable method is uninterpreted function
(declare-fun Shape.area (ShapeVTable ShapeObject) Real)

; Trait contract as axiom (must hold for all impls)
(assert (forall ((vtbl ShapeVTable) (obj ShapeObject))
  (>= (Shape.area vtbl obj) 0.0)))

; Function verification uses only trait contract
(assert (= total (sum (map (lambda (s) (Shape.area (vtbl s) s)) shapes))))
(assert (>= total 0.0))  ; Provable from trait contract
```

**Phase to address:** Phase N+3 (Trait Object Verification)
- Start with closed-world for sealed traits only
- Document limitation: public traits not yet supported
- Phase N+4: Add open-world verification with trait contract enforcement

**Confidence:** MEDIUM-HIGH - Open/closed-world is well-studied in verification. Rust-specific vtable handling less documented.

**Sources:**
- [Closed-world assumption - Wikipedia](https://en.wikipedia.org/wiki/Closed-world_assumption)
- [Verifying Dynamic Trait Objects in Rust](https://cs.wellesley.edu/~avh/dyn-trait-icse-seip-2022-preprint.pdf)
- [UNSOUND 2026 Workshop](https://2026.ecoop.org/home/unsound-2026)

---

### Pitfall 4: Unsafe Code Verification Soundness Boundaries

**What goes wrong:**
Verifier treats `unsafe` blocks same as safe code, or axiomatizes all unsafe operations, creating soundness holes. Verified safe code calls unverified unsafe code, bugs slip through.

**Why it happens:**
- Unsafe code can violate Rust's safety invariants (aliasing, lifetime, initialization)
- Verifier must decide: verify unsafe's implementation or trust its safety contract?
- If verify: need model of raw pointers, uninitialized memory, FFI - extremely complex
- If trust: unsafe becomes axiom, bugs in unsafe propagate to safe code
- Existing tools (Kani, Verus, Prusti) all struggle with unsafe verification

**Root cause:** Safe Rust's soundness depends on unsafe code upholding safety invariants. Verifier must check unsafe doesn't violate invariants, but unsafe code uses operations verification doesn't model (raw pointer arithmetic, transmute, inline assembly).

**Consequences:**
- **Unsound verification**: Unsafe code with bug (e.g., aliasing violation) gets axiomatized, safe code verified against wrong assumptions
- **False sense of security**: Codebase "verified" but crashes due to unsafe code bug
- **Incomplete coverage**: Can't verify code using common unsafe patterns (intrinsics, FFI)

**Prevention:**
1. **Separate unsafe analysis pipeline**: Don't mix safe and unsafe verification
2. **Conservative unsafe contracts**:
   - Require explicit `#[unsafe_requires]` and `#[unsafe_ensures]` annotations
   - Unsafe preconditions become axioms (trusted), not verified
   - Document what verification assumes about unsafe code
3. **Restrict verifiable unsafe subset**:
   - Allow: raw pointer dereference with bounds check, `UnsafeCell` access
   - Disallow (for now): transmute, union field access, inline asm, FFI
4. **Safety encapsulation checking**: Verify unsafe code doesn't leak unsafety to safe interface
   ```rust
   // Verify: even if unsafe code bugs, safe interface can't trigger UB
   pub fn safe_wrapper(x: &[i32]) -> i32 {
       unsafe { unchecked_index(x, 0) }  // Must prove x.len() > 0
   }
   ```
5. **Explicit verification boundary**: Mark unsafe functions as `#[verifier::trusted]` or `#[verifier::verify_unsafe]`

**Warning signs:**
- Unsafe code verifies without additional annotations
- Raw pointer operations accepted without bounds checks
- Transmute operations in verified code
- No distinction between safe and unsafe verification results

**Example:**
```rust
// WRONG - unsafe axiomatized
#[ensures(result < arr.len())]
fn find_first(arr: &[i32], target: i32) -> usize {
    unsafe {
        // BUG: out-of-bounds access if target not found
        unchecked_first(arr.as_ptr(), arr.len(), target)
    }
}

// CORRECT - unsafe requires proof
#[requires(len > 0)]
#[requires(exists(|i: usize| i < len && *ptr.add(i) == target))]
#[unsafe_ensures(result < len)]
#[unsafe_ensures(*ptr.add(result) == target)]
unsafe fn unchecked_first(ptr: *const i32, len: usize, target: i32) -> usize {
    // Verification assumes precondition (not verified)
    for i in 0..len {
        if *ptr.add(i) == target { return i; }
    }
    unreachable!()
}
```

**Encoding strategy:**
```rust
// In VCGen
match function.safety {
    Safety::Safe => {
        // Normal verification: check all operations
        generate_full_vcs(function)
    }
    Safety::Unsafe => {
        if has_attr(function, "verifier::trusted") {
            // Axiomatize: assume contracts without proof
            axiomatize_function(function)
        } else {
            // Verify with unsafe operations allowed
            generate_unsafe_vcs(function)
        }
    }
}
```

**Phase to address:** Phase N+4 (Unsafe Verification)
- Phase N+3: Mark unsafe as `#[verifier::trusted]`, document limitation
- Phase N+4: Add verification for restricted unsafe subset (raw pointers with bounds)
- Defer full unsafe verification (transmute, unions, FFI) to research phase

**Confidence:** HIGH - Multiple sources confirm unsafe verification is hard, existing tools have limitations. Conservative approach (axiomatize with explicit trust) is safest.

**Sources:**
- [Modular Formal Verification of Rust Programs with Unsafe Blocks](https://arxiv.org/abs/2212.12976)
- [RefinedRust: A Type System for High-Assurance Verification](https://plv.mpi-sws.org/refinedrust/paper-refinedrust.pdf)
- [Verify the Safety of the Rust Standard Library](https://aws.amazon.com/blogs/opensource/verify-the-safety-of-the-rust-standard-library/)
- [Annotating and Auditing the Safety Properties of Unsafe Rust](https://arxiv.org/pdf/2504.21312)

---

### Pitfall 5: Non-Lexical Lifetimes (NLL) Complexity in Encoding

**What goes wrong:**
Verifier uses lexical scope for lifetime reasoning, rejects code accepted by NLL borrow checker. Users get "verification failed" on code that compiles fine.

**Why it happens:**
- Rust's borrow checker uses NLL (non-lexical lifetimes) since 2018
- NLL tracks lifetime based on control flow graph, not lexical scope
- Lifetime ends at last use, not end of scope
- Verifier using lexical lifetime encoding is stricter than Rust compiler
- Polonius (next-gen borrow checker) even more permissive, divergence grows

**Root cause:** Encoding lifetimes precisely requires control-flow-sensitive analysis. Lexical scoping is simpler but rejects valid code. Verifier's lifetime model must match Rust's actual borrow checking.

**Consequences:**
- **Usability failure**: Correct Rust code fails verification
- **User confusion**: "Code compiles but doesn't verify - is verifier broken?"
- **Workaround hell**: Users restructure code to fit lexical lifetime model
- **Future incompatibility**: Polonius adoption will increase divergence

**Prevention:**
1. **Use NLL-based lifetime reasoning**: Track lifetime based on last use in CFG, not lexical scope
2. **Reborrow chain tracking**: Model reborrowing (borrow from borrow) correctly
   ```rust
   let r1 = &mut x;
   let r2 = &mut *r1;  // Reborrow: r1 suspended while r2 active
   *r2 = 5;
   *r1 = 6;  // r1 resumed after r2 ends
   ```
3. **Leverage MIR lifetime information**: MIR includes region inference results, use them
4. **Two-phase borrows**: Model two-phase borrows (mutable borrow activated on use, not creation)
5. **Test against borrow checker**: Verification should accept same code as `rustc --emit=mir`

**Warning signs:**
- Code compiles with `rustc` but fails verification
- Reordering statements (without semantic change) affects verification
- Manual lifetime annotations change verification outcome
- Error message: "borrow outlives use" on code that compiles

**Example:**
```rust
// NLL accepts this
fn use_then_reassign(v: &mut Vec<i32>) {
    let r = &v[0];           // Borrow starts
    println!("{}", r);       // Last use of r
    v.push(1);               // Mutable use of v - OK! r lifetime ended
}

// Lexical lifetimes reject: r's scope includes v.push(), conflict detected

// Verification encoding must track:
// 1. r's lifetime ends at println
// 2. v becomes available for mutation after last use of r
```

**Encoding strategy:**
```rust
// In VCGen: track lifetime based on use, not scope
struct LifetimeTracker {
    /// Maps borrow to last use point in CFG
    last_use: HashMap<Local, BasicBlockId>,
    /// Active borrows at each program point
    active_at: HashMap<BasicBlockId, HashSet<Local>>,
}

impl LifetimeTracker {
    fn borrow_ends(&self, borrow: Local, point: BasicBlockId) -> bool {
        self.last_use[&borrow] <= point
    }

    fn is_mutable_available(&self, var: Local, point: BasicBlockId) -> bool {
        // Check no active borrows of var at this point
        !self.active_at[&point].iter().any(|b| borrows(b, var))
    }
}
```

**Phase to address:** Phase N+5 (Lifetime Reasoning)
- Phase N+4: Use lexical lifetimes, document limitation
- Phase N+5: Implement NLL-based lifetime tracking
- Research spike: Study Polonius if adoption imminent

**Confidence:** MEDIUM - NLL is well-documented, but integrating into verifier non-trivial. Reborrow chains and two-phase borrows add complexity.

**Sources:**
- [Non-Lexical Lifetimes RFC](https://github.com/rust-lang/rfcs/blob/master/text/2094-nll.md)
- [How to Understand Non-Lexical Lifetimes in Rust](https://oneuptime.com/blog/post/2026-01-25-non-lexical-lifetimes-rust/view)
- [Polonius Working Group](https://rust-lang.github.io/compiler-team/working-groups/polonius/)

---

### Pitfall 6: Floating-Point NaN Propagation Breaks Postcondition Reasoning

**What goes wrong:**
Verifier proves `result > 0.0` for floating-point function, but runtime produces `NaN`. Postcondition unsound because verifier didn't model NaN propagation.

**Why it happens:**
- IEEE 754 floating-point has special values: `NaN`, `Inf`, `-Inf`, `-0.0`
- Operations on `NaN` produce `NaN` (propagate), not follow normal arithmetic rules
- `NaN != NaN` (reflexivity violation), `NaN < x` is false for all x
- SMT-LIB FloatingPoint theory models IEEE 754, but easy to forget NaN handling
- Verifier may encode `x + y > 0` without checking if inputs are NaN

**Root cause:** Floating-point arithmetic is not real arithmetic. SMT encoding must account for NaN, infinity, rounding modes, subnormals. Forgetting NaN produces unsound postconditions.

**Consequences:**
- **Soundness bug**: Verifier proves `result >= 0.0`, runtime gets `NaN` (not >= 0)
- **Unexpected behavior**: Comparisons with NaN return false, break control flow assumptions
- **Difficult debugging**: NaN propagates silently, bug appears far from source

**Prevention:**
1. **Explicit NaN checks in VCs**: For every float operation, generate VC checking operands not NaN
   ```smt2
   ; Addition VC with NaN check
   (assert (not (isNaN x)))
   (assert (not (isNaN y)))
   (assert (= result (fp.add RNE x y)))
   (assert (fp.gt result 0.0))  ; Safe to check since result not NaN
   ```

2. **Require NaN handling in contracts**:
   ```rust
   #[requires(!x.is_nan() && !y.is_nan())]
   #[ensures(!result.is_nan() && result >= 0.0)]
   fn safe_add(x: f64, y: f64) -> f64 { x + y }
   ```

3. **Use SMT-LIB FloatingPoint theory predicates**:
   - `isNaN`, `isInfinite`, `isZero`, `isSubnormal`, `isNormal`
   - Rounding modes: `RNE` (round to nearest even), `RNA`, `RTP`, `RTN`, `RTZ`

4. **Document NaN semantics**:
   - "All floating-point preconditions must exclude NaN unless explicitly handled"
   - "Postconditions using comparisons (>, <, ==) invalid for NaN inputs"

5. **Test with NaN inputs**: Property-based testing with NaN, Inf, -0.0 edge cases

**Warning signs:**
- Float postcondition uses `result > 0.0` without NaN precondition
- Verification assumes `x == x` for floats (false for NaN)
- No `isNaN` checks in generated VCs for float operations
- Runtime panic on NaN where verification claimed safety

**Example:**
```rust
// WRONG - doesn't handle NaN
#[ensures(result >= 0.0)]
fn unsafe_sqrt(x: f64) -> f64 {
    x.sqrt()  // Returns NaN for negative x, violates postcondition
}

// CORRECT - explicit NaN handling
#[requires(!x.is_nan())]
#[requires(x >= 0.0)]
#[ensures(!result.is_nan())]
#[ensures(result * result <= x && x <= (result + f64::EPSILON) * (result + f64::EPSILON))]
fn safe_sqrt(x: f64) -> f64 {
    x.sqrt()
}
```

**Encoding strategy:**
```smt2
; SMT-LIB FloatingPoint encoding
(declare-const x (_ FloatingPoint 11 53))  ; f64
(declare-const result (_ FloatingPoint 11 53))

; Precondition: not NaN and >= 0
(assert (not (fp.isNaN x)))
(assert (fp.geq x (_ +zero 11 53)))

; Operation
(assert (= result (fp.sqrt RNE x)))

; Postcondition: not NaN and approximate square
(assert (not (fp.isNaN result)))
(assert (fp.leq (fp.mul RNE result result) x))
```

**Phase to address:** Phase N+6 (Floating-Point Verification)
- Use SMT-LIB FloatingPoint theory (already in codebase)
- Require NaN preconditions on all float operations
- Test with IEEE 754 edge cases (NaN, Inf, -0.0, subnormals)

**Confidence:** HIGH - SMT-LIB FloatingPoint theory well-specified, NaN handling documented in IEEE 754 standard.

**Sources:**
- [SMT-LIB FloatingPoint Theory](https://smt-lib.org/theories-FloatingPoint.shtml)
- [NaN Propagation (IEEE 754 Issues)](https://grouper.ieee.org/groups/msc/ANSI_IEEE-Std-754-2019/background/nan-propagation.pdf)
- [Correct Approximation of IEEE 754 Floating-Point Arithmetic](https://link.springer.com/article/10.1007/s10601-021-09322-9)
- [Parallel Floating Point Exception Tracking and NaN Propagation](https://www.agner.org/optimize/nan_propagation.pdf)

---

### Pitfall 7: Concurrency State Explosion with Weak Memory Models

**What goes wrong:**
Verifier tries to check all possible interleavings for concurrent code, SMT solver runs out of memory or times out. Or verifier assumes sequential consistency, misses relaxed atomics bugs.

**Why it happens:**
- Rust allows relaxed memory ordering (`Ordering::Relaxed`) for atomics
- Relaxed atomics permit reordering, weak memory model has more behaviors than sequential consistency
- Encoding all possible orderings causes exponential VC growth
- SMT solvers struggle with existential quantification over interleavings

**Root cause:** Concurrent verification is hard. Weak memory models make it harder. State explosion: N threads with M states each → M^N possible interleavings.

**Consequences:**
- **Incompleteness**: Verifier times out on realistic concurrent code
- **False negatives**: Weak memory model bugs (load buffering, store buffering) missed by sequential consistency model
- **Scalability failure**: Can only verify 2-3 threads, not production concurrency

**Prevention:**
1. **Don't tackle weak memory models in early phases**: Start with sequential consistency only
2. **Use bounded model checking**: Limit interleaving depth (e.g., check up to 10 context switches)
3. **Partial order reduction**: Prune equivalent interleavings using independence relations
4. **Stateless model checking**: Explore interleavings lazily, not all upfront
5. **For weak memory models**:
   - Use C11/C20 memory model formalization (Dartagnan, GenMC)
   - CAT (Concurrency Abstract Model) for memory model specification
   - Relation analysis to reduce encoding size
6. **Defer to specialized tools**: Link with existing concurrency verifiers (CBMC, GenMC) rather than re-implementing

**Warning signs:**
- Verification timeout on simple concurrent code (2 threads, 10 LOC each)
- Memory usage explodes (>10GB) for concurrent VCs
- Relaxed atomics in code but verifier doesn't model weak memory
- Bug appears in runtime with specific thread interleaving but verification passed

**Example:**
```rust
// Relaxed atomics - weak memory behavior
static X: AtomicBool = AtomicBool::new(false);
static Y: AtomicBool = AtomicBool::new(false);

// Thread 1
fn thread1() {
    X.store(true, Ordering::Relaxed);
    let y = Y.load(Ordering::Relaxed);
    // Can observe y == false even if thread2 ran first
}

// Thread 2
fn thread2() {
    Y.store(true, Ordering::Relaxed);
    let x = X.load(Ordering::Relaxed);
    // Can observe x == false even if thread1 ran first
}

// Weak memory allows both threads to read false (load buffering)
// Sequential consistency forbids this
```

**Encoding strategy (bounded, sequential consistency only):**
```rust
// Bounded verification: limit interleaving depth
struct ConcurrencyVCGen {
    max_context_switches: usize,  // e.g., 10
    max_threads: usize,            // e.g., 3
}

impl ConcurrencyVCGen {
    fn generate_vcs(&self, threads: &[Thread]) -> Vec<VC> {
        if threads.len() > self.max_threads {
            return vec![VC::Skip("Too many threads for bounded verification")];
        }

        // Generate VCs for bounded interleavings only
        self.bounded_interleavings(threads, self.max_context_switches)
    }
}
```

**Phase to address:** Phase N+7 (Concurrency Verification) - ADVANCED/RESEARCH
- Phase N+6: Sequential code only
- Phase N+7: Sequential consistency (SC) atomics, bounded verification
- Research phase: Weak memory models (defer to specialized tools or future work)

**Confidence:** MEDIUM-HIGH - Concurrency verification well-studied, but Rust-specific weak memory model verification is cutting-edge research (RustBelt Relaxed 2024-2026).

**Sources:**
- [RustBelt Meets Relaxed Memory](https://plv.mpi-sws.org/rustbelt/rbrlx/paper.pdf)
- [An Approach for Modularly Verifying Rust's Atomic Reference Counting](https://arxiv.org/pdf/2505.00449)
- [BMC for Weak Memory Models: Relation Analysis for Compact SMT Encodings](https://link.springer.com/chapter/10.1007/978-3-030-25540-4_19)
- [Static Analysis of Memory Models for SMT Encodings](https://dl.acm.org/doi/10.1145/3622855)

---

## Moderate Pitfalls

### Pitfall 8: Recursive Function Stack Overflow in VCGen

**What goes wrong:**
VCGen naively inlines recursive calls, stack overflow when generating VC for deep recursion.

**Prevention:**
Use fuel-based unfolding or function summary encoding. Limit inlining depth (e.g., max 5 recursive calls).

**Warning signs:**
- Stack overflow during VC generation
- VCGen time exponential in recursion depth
- Can't verify recursive functions with depth > 10

---

### Pitfall 9: Quantifier Instantiation Matching Loops

**What goes wrong:**
Quantifier trigger causes instantiation that creates new term matching same trigger, infinite loop.

**Prevention:**
- Conservative trigger selection (Phase 4 approach)
- Z3 `:qid` and `:no-pattern` annotations
- Test with Z3 `-v` flag to detect matching loops

**Warning signs:**
- Z3 never returns (timeout on simple VC)
- Z3 verbose output shows millions of instantiations
- Memory usage grows unbounded

**Source:** [Programming Z3: Quantifiers](https://theory.stanford.edu/~nikolaj/programmingz3.html)

---

### Pitfall 10: Closure Environment Size Explosion

**What goes wrong:**
Closure captures many variables, environment struct becomes huge datatype, SMT solver slow.

**Prevention:**
- Only encode captured variables actually used in closure body
- Share environment representation across closures with same captures
- Warn on closures capturing >10 variables

**Warning signs:**
- Verification slow on functions with closures
- SMT datatype has 20+ fields
- Closure works in code but times out in verification

---

### Pitfall 11: Trait Object Devirtualization Failure

**What goes wrong:**
Trait object method call encoded as uninterpreted function, can't prove simple properties.

**Prevention:**
- Devirtualize when possible (single impl known at verification time)
- Encode trait contract as axiom, use in reasoning
- For sealed traits, enumerate all impls

**Warning signs:**
- Trait method postcondition not usable at call site
- Must manually assume trait contract after call
- Different results for trait object vs concrete type

---

### Pitfall 12: Unsafe Pointer Arithmetic Overflow

**What goes wrong:**
Pointer arithmetic in unsafe code overflows, creates out-of-bounds pointer, UB not detected.

**Prevention:**
- Model pointers as (base, offset) pair
- Check `0 <= offset < allocation_size` on every pointer operation
- Require bounds as `#[unsafe_requires]` on raw pointer functions

**Warning signs:**
- Unsafe code with pointer arithmetic verifies without bounds checks
- Out-of-bounds access at runtime after verification
- `ptr.add(n)` operations without proof that `n` in bounds

---

## Minor Pitfalls

### Pitfall 13: Lifetime Elision in Contracts

**What goes wrong:**
Contract uses lifetime elision rules differently than Rust compiler, verification rejects.

**Prevention:**
Explicitly write all lifetime parameters in contracts, don't rely on elision.

---

### Pitfall 14: Float Rounding Mode Ignored

**What goes wrong:**
Float operations use default rounding (RNE), code requires different mode (RTP/RTN).

**Prevention:**
Encode rounding mode as parameter, check against actual mode used.

---

### Pitfall 15: Weak Memory Model Litmus Test Coverage

**What goes wrong:**
Verifier claims to support weak memory but fails standard litmus tests (SB, MP, LB).

**Prevention:**
Test against C11/C20 litmus test suite before claiming weak memory support.

---

## Integration Gotchas

| Feature | Naive Approach (WRONG) | Correct Approach |
|---------|------------------------|------------------|
| Recursive functions | Inline all calls | Fuel-based unfolding + termination measure |
| Closures | Treat as pure functions | Encode environment capture + trait bounds |
| Trait objects | Assume single impl | Open-world encoding or closed-world opt-in |
| Unsafe code | Verify same as safe code | Separate analysis + trusted axioms |
| NLL lifetimes | Use lexical scope | Control-flow-sensitive lifetime tracking |
| Floating-point | Ignore NaN/Inf | Explicit IEEE 754 special value handling |
| Concurrency | Encode all interleavings | Bounded verification + partial order reduction |

---

## Performance Traps

| Feature | Scalability Issue | Mitigation |
|---------|-------------------|------------|
| Recursive functions | Exponential VC size from inlining | Fuel limit + function summaries |
| Closures | Large environment datatypes | Only encode used captures |
| Trait objects | VC per implementation | Devirtualization when possible |
| Concurrency | M^N interleaving explosion | Bounded model checking, limit threads/context switches |
| Quantifiers | Matching loop non-termination | Conservative triggers + `:qid` annotations |
| Floating-point | IEEE 754 theory slower than bitvectors | Axiomatize common operations (sqrt, abs) |

---

## Phase-Specific Warnings

| Phase Feature | Critical Pitfall | Must Address Before Release |
|---------------|------------------|---------------------------|
| Recursive functions | Non-termination accepted | Termination measure checker |
| Closures | Capture semantics wrong | FnMut/FnOnce encoding |
| Trait objects | Open-world unsoundness | Closed-world validation |
| Unsafe code | Axiomatized without bounds | Explicit trust annotation |
| Lifetimes | NLL divergence | Control-flow lifetime tracking |
| Floating-point | NaN propagation | IEEE 754 edge case tests |
| Concurrency | Weak memory bugs missed | Sequential consistency first, defer relaxed |

---

## Research-Specific Warnings

Based on 2024-2026 verification research:

**Recursive Functions:**
- Termination checking is decidable for structural recursion, undecidable in general
- Measure functions must be well-founded (common: lexicographic tuples, natural numbers)
- Mutual recursion requires joint decrease measure
- Higher-order recursion (functions as arguments) extremely complex, defer

**Closures:**
- Rust closure desugaring to structs + traits not formally specified
- MIR representation of closures changes across rustc versions
- FnOnce consumption tracking requires linear types or ownership encoding
- Closure verification in Prusti/Verus is limited (manual encoding often needed)

**Trait Objects:**
- Vtable soundness bugs exist (malicious actors can exploit)
- Serializing trait objects (serde_traitobject) has known soundness holes
- Fat pointer (vtable + data) representation complicates encoding
- No verification tool fully supports open-world trait objects (2026)

**Unsafe Code:**
- Standard library has 57 soundness issues filed in last 3 years (2024-2026)
- 20 CVEs in Rust stdlib, 28% discovered in 2024
- RefinedRust (2024) is most advanced unsafe verifier, still research-level
- Unsafe verification requires modeling: raw pointers, uninitialized memory, FFI, inline asm

**Lifetimes:**
- Polonius (next-gen borrow checker) still experimental (2026)
- Reborrow chains not fully specified in Rust reference
- Two-phase borrows edge cases not well-documented
- Region inference results in MIR sometimes imprecise

**Floating-Point:**
- SMT-LIB FloatingPoint theory exists but performance varies across solvers
- Fused multiply-add (FMA) and transcendental functions (sin, log) not in SMT-LIB standard
- NaN payload propagation not standardized until IEEE 754-2019
- Subnormals and signed zero add verification complexity

**Concurrency:**
- Weak memory models (C11, ARMv8, x86-TSO) formalization still evolving
- Dartagnan (weak memory model checker) requires CAT specification - learning curve
- Relaxed atomics verification tools (GenMC, CBMC) separate from general verifiers
- VerusSync (permission-based concurrency) very recent (2025), not battle-tested
- Deadlock detection (both thread and Rc/borrow cycles) remains open problem

---

## Recovery Strategies

| Pitfall | Recovery Cost | Recovery Steps |
|---------|---------------|----------------|
| Non-terminating recursion verified | HIGH | 1. Add termination measure checker<br>2. Re-verify all recursive functions<br>3. Add soundness tests (diverging functions should fail) |
| Closure capture semantics wrong | MEDIUM-HIGH | 1. Study MIR closure desugaring<br>2. Implement environment encoding<br>3. Add Fn/FnMut/FnOnce distinction |
| Open-world trait unsoundness | MEDIUM | 1. Add `#[sealed]` check<br>2. Reject public traits or require explicit open-world mode |
| Unsafe code axiomatized | LOW-MEDIUM | 1. Add `#[verifier::trusted]` attribute<br>2. Document unsafe assumptions<br>3. Plan separate unsafe analysis |
| NLL divergence | MEDIUM | 1. Implement control-flow lifetime tracking<br>2. Test against rustc borrow checker results |
| NaN not handled | LOW | 1. Add `isNaN` checks to float VCs<br>2. Require NaN preconditions<br>3. Test with IEEE 754 edge cases |
| Concurrency state explosion | HIGH | 1. Limit scope (sequential consistency only, bounded verification)<br>2. Document limitation<br>3. Defer weak memory to future/specialized tool |

---

## Success Criteria Checklist

Before claiming support for advanced feature:

- [ ] **Recursive functions:**
  - [ ] Termination measure required and checked
  - [ ] Non-terminating function fails verification
  - [ ] Mutual recursion supported
  - [ ] Tested with structural and numeric measures

- [ ] **Closures:**
  - [ ] Fn/FnMut/FnOnce distinction encoded
  - [ ] Environment capture tracked
  - [ ] Higher-order functions verified
  - [ ] Tested with mutable captures

- [ ] **Trait objects:**
  - [ ] Open vs closed-world decision documented
  - [ ] Sealed traits verified correctly
  - [ ] Vtable modeling prevents soundness bugs
  - [ ] Tested with multiple implementations

- [ ] **Unsafe code:**
  - [ ] Separate unsafe analysis pipeline
  - [ ] Trusted axioms explicitly marked
  - [ ] Safety encapsulation checked
  - [ ] Tested with raw pointer operations

- [ ] **Lifetimes:**
  - [ ] NLL-based lifetime tracking
  - [ ] Reborrow chains handled
  - [ ] Two-phase borrows supported
  - [ ] Tested against rustc borrow checker

- [ ] **Floating-point:**
  - [ ] NaN/Inf handling in all operations
  - [ ] Rounding modes encoded
  - [ ] IEEE 754 edge cases tested
  - [ ] SMT-LIB FloatingPoint theory used

- [ ] **Concurrency:**
  - [ ] Memory model specified (SC vs weak)
  - [ ] Bounded verification if state explosion
  - [ ] Litmus tests pass
  - [ ] Thread/interleaving limits documented

---

## Sources

**Recursive Functions & Termination:**
- [Well-founded Relations and Termination (F* Tutorial)](https://fstar-lang.org/tutorial/book/part2/part2_well_founded.html)
- [Proofs of Termination (F* Tutorial)](https://fstar-lang.org/tutorial/book/part1/part1_termination.html)
- [Model Finding for Recursive Functions in SMT](http://homepage.divms.uiowa.edu/~ajreynol/ijcar16a.pdf)
- [SMT-Based Model Checking for Recursive Programs](https://link.springer.com/chapter/10.1007/978-3-319-08867-9_2)
- [Formal Verification of Termination Criteria for First-Order Recursive Functions](https://shemesh.larc.nasa.gov/fm/papers/itp2021.pdf)

**Closures:**
- [FnMut in std::ops - Rust](https://doc.rust-lang.org/std/ops/trait.FnMut.html)
- [FnOnce in std::ops - Rust](https://doc.rust-lang.org/std/ops/trait.FnOnce.html)
- [How Rust Handles Closures: Fn, FnMut, and FnOnce](https://leapcell.medium.com/how-rust-handles-closures-fn-fnmut-and-fnonce-5550724859ed)
- [Closures - The Rust Programming Language](https://doc.rust-lang.org/book/ch13-01-closures.html)

**Trait Objects:**
- [Verifying Dynamic Trait Objects in Rust](https://cs.wellesley.edu/~avh/dyn-trait-icse-seip-2022-preprint.pdf)
- [UNSOUND 2026 Workshop](https://2026.ecoop.org/home/unsound-2026)
- [The Trait Object Vtable Lookup](https://medium.com/@theopinionatedev/the-trait-object-vtable-lookup-no-one-talks-about-9135c6e3c9fe)
- [Rust Deep Dive: Borked Vtables and Barking Cats](https://geo-ant.github.io/blog/2023/rust-dyn-trait-objects-fat-pointers/)

**Unsafe Code:**
- [Modular Formal Verification of Rust Programs with Unsafe Blocks](https://arxiv.org/abs/2212.12976)
- [RefinedRust: A Type System for High-Assurance Verification](https://plv.mpi-sws.org/refinedrust/paper-refinedrust.pdf)
- [Verify the Safety of the Rust Standard Library](https://aws.amazon.com/blogs/opensource/verify-the-safety-of-the-rust-standard-library/)
- [Annotating and Auditing the Safety Properties of Unsafe Rust](https://arxiv.org/pdf/2504.21312)
- [RustHornBelt: A Semantic Foundation for Functional Verification of Unsafe Rust](https://people.mpi-sws.org/~dreyer/papers/rusthornbelt/paper.pdf)

**Lifetimes & NLL:**
- [Non-Lexical Lifetimes RFC](https://github.com/rust-lang/rfcs/blob/master/text/2094-nll.md)
- [How to Understand Non-Lexical Lifetimes in Rust](https://oneuptime.com/blog/post/2026-01-25-non-lexical-lifetimes-rust/view)
- [Polonius Working Group](https://rust-lang.github.io/compiler-team/working-groups/polonius/)
- [Non-Lexical Lifetimes: Introduction](https://smallcultfollowing.com/babysteps/blog/2016/04/27/non-lexical-lifetimes-introduction/)

**Floating-Point:**
- [SMT-LIB FloatingPoint Theory](https://smt-lib.org/theories-FloatingPoint.shtml)
- [NaN Payload Propagation (IEEE 754)](https://grouper.ieee.org/groups/msc/ANSI_IEEE-Std-754-2019/background/nan-propagation.pdf)
- [Parallel Floating Point Exception Tracking and NaN Propagation](https://www.agner.org/optimize/nan_propagation.pdf)
- [Correct Approximation of IEEE 754 Floating-Point Arithmetic](https://link.springer.com/article/10.1007/s10601-021-09322-9)
- [An SMT-LIB Theory of Binary Floating-Point Arithmetic](http://www.ccs.neu.edu/home/wahl/Publications/rw10.pdf)
- [Alive-FP: Automated Verification of Floating Point Based Peephole Optimizations](https://people.cs.rutgers.edu/~sn349/papers/alive-fp-sas16.pdf)

**Concurrency & Weak Memory:**
- [RustBelt Meets Relaxed Memory](https://plv.mpi-sws.org/rustbelt/rbrlx/paper.pdf)
- [Miri: Practical Undefined Behavior Detection for Rust (POPL 2026)](https://research.ralfj.de/papers/2026-popl-miri.pdf)
- [An Approach for Modularly Verifying Rust's Atomic Reference Counting](https://arxiv.org/pdf/2505.00449)
- [BMC for Weak Memory Models: Relation Analysis for Compact SMT Encodings](https://link.springer.com/chapter/10.1007/978-3-030-25540-4_19)
- [Static Analysis of Memory Models for SMT Encodings](https://dl.acm.org/doi/10.1145/3622855)
- [Atomics - The Rustonomicon](https://doc.rust-lang.org/nomicon/atomics.html)

**SMT & Quantifiers:**
- [Programming Z3: Quantifiers](https://theory.stanford.edu/~nikolaj/programmingz3.html)
- [The Axiom Profiler: Understanding and Debugging SMT Quantifier Instantiations](https://link.springer.com/chapter/10.1007/978-3-030-17462-0_6)
- [Tunable Automation in Automated Program Verification](https://arxiv.org/html/2512.03926)

---

**Researched:** 2026-02-11
**Confidence:** MEDIUM-HIGH - Based on research papers, official docs, and existing tool limitations. Recursive functions, unsafe code, and concurrency are research-level; closures and lifetimes are moderately well-documented; floating-point is well-specified.

**Note:** This document focuses on **adding** these features to an existing verifier. It complements the general PITFALLS.md with feature-specific integration challenges.
