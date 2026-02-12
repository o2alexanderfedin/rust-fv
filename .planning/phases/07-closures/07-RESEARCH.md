# Phase 7: Closures - Research

**Researched:** 2026-02-12
**Domain:** Closure verification via defunctionalization and prophecy variables
**Confidence:** MEDIUM-HIGH

## Summary

Closure verification transforms higher-order function problems into first-order SMT problems through **defunctionalization**, where closures become algebraic datatypes encoding captured environments. The codebase already has prophecy variable infrastructure for `&mut` reasoning (Phase 1), which extends naturally to `FnMut` closures with mutable captures.

**Key insight:** Rust MIR already lowers closures to anonymous structs with captured variables as fields, and closure calls to trait method invocations (`Fn::call`, `FnMut::call_mut`, `FnOnce::call_once`). Our IR can mirror this by introducing `Ty::Closure` with environment fields and transforming closure calls to regular function calls with explicit environment parameters.

**Primary recommendation:** Follow the Prusti pattern of encoding higher-order closure contracts into first-order logic via defunctionalization, leveraging existing `DeclareDatatype` infrastructure for closure environments and `ProphecyInfo` for FnMut captures. Closure contracts attach to closure-accepting function parameters as trait bound specifications.

## Standard Stack

### Core

This phase builds entirely on existing codebase infrastructure - no external dependencies needed.

| Component | Version | Purpose | Why Standard |
|-----------|---------|---------|--------------|
| SMT-LIB2 Datatypes | Built-in | Closure environment encoding | Industry standard for algebraic types in SMT |
| Z3 SMT Solver | 4.13.4+ | First-order logic solving | Project standard (already integrated) |
| Rust MIR Semantics | rustc 1.85+ | Closure lowering semantics | Canonical Rust representation |

### Supporting

| Library | Version | Purpose | When to Use |
|---------|---------|---------|-------------|
| Existing IR (`crates/analysis/src/ir.rs`) | Current | Add `Ty::Closure` and closure call encoding | Core representation |
| Existing `ProphecyInfo` | Current | FnMut mutable capture reasoning | Already proven in Phase 1 |
| Existing `DeclareDatatype` | Current | Closure environment structs | Already proven in Phase 2 |
| Contract DB | Current | Closure summary storage | Inter-procedural verification |

### Alternatives Considered

| Instead of | Could Use | Tradeoff |
|------------|-----------|----------|
| Defunctionalization | Direct higher-order SMT | SMT solvers don't efficiently support higher-order; defunctionalization is proven standard (Reynolds 1972) |
| Prophecy variables (FnMut) | Two-state logic | Prophecies are Creusot/RustHornBelt standard, already implemented in codebase |
| Trait-based contracts | Function pointer contracts only | Rust closures ARE traits (Fn/FnMut/FnOnce); must match language semantics |

**Installation:**
No new dependencies - builds on existing workspace crates.

## Architecture Patterns

### Recommended Project Structure

Extend existing analysis crate structure:

```
crates/analysis/src/
├── ir.rs                  # Add Ty::Closure, ClosureInfo
├── closure_analysis.rs    # NEW: Detect closure calls, extract environments
├── defunctionalize.rs     # NEW: Transform closure calls to first-order
├── vcgen.rs               # Extend: Handle closure contract VCs
├── encode_sort.rs         # Extend: Closure environment → SMT datatype
└── spec_parser.rs         # Extend: Parse closure contracts on parameters
```

### Pattern 1: Closure Environment as Datatype

**What:** Encode closure captured variables as SMT algebraic datatype (struct-like).

**When to use:** Every closure that captures variables (all except `|| { literal }`).

**Example:**

```rust
// Rust code:
let x = 5;
let y = 10;
let add_captured = |z| x + y + z;  // Captures x, y

// IR representation (conceptual):
Ty::Closure {
    name: "closure_add_captured",
    env_fields: vec![("x", Ty::Int(I32)), ("y", Ty::Int(I32))],
    params: vec![("z", Ty::Int(I32))],
    return_ty: Ty::Int(I32),
    trait_kind: ClosureTrait::Fn,  // Immutable captures
}

// SMT encoding:
(declare-datatype ClosureEnv_add_captured
  ((mk-ClosureEnv_add_captured
    (ClosureEnv_add_captured-x (_ BitVec 32))
    (ClosureEnv_add_captured-y (_ BitVec 32)))))
```

**Source:** [Defunctionalization of Higher-Order CHC](https://ar5iv.labs.arxiv.org/html/1810.03598) - "For each top-level function F with arity n, create n+1 constructors representing F applied to i arguments."

### Pattern 2: Defunctionalization of Closure Calls

**What:** Transform higher-order closure call to first-order function call with explicit environment parameter.

**When to use:** Every closure invocation site.

**Example:**

```rust
// Rust code:
fn apply<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 {
    f(x)  // Closure call
}

// MIR view (conceptual):
// f(x) desugars to: Fn::call(&f, (x,))

// IR transformation:
Terminator::Call {
    func: "Fn::call",
    args: [Operand::Move(f_place), Operand::Move(x_place)],
    ...
}

// Becomes first-order call:
Terminator::Call {
    func: "closure_apply_impl",
    args: [Operand::Move(f_env), Operand::Move(x_place)],  // Environment explicit
    ...
}
```

**Source:** [Defunctionalization Wikipedia](https://en.wikipedia.org/wiki/Defunctionalization) - "Every function application is replaced by a call to the apply function with the function identifier as the first argument."

### Pattern 3: Prophecy Variables for FnMut Closures

**What:** FnMut closures mutably capture variables - use prophecy variables to reason about initial and final capture state.

**When to use:** Any closure that implements `FnMut` (mutable captures).

**Example:**

```rust
// Rust code:
let mut count = 0;
let mut increment = || { count += 1; };  // FnMut - mutates count
increment();
increment();
// count is now 2

// Prophecy encoding (existing ProphecyInfo pattern):
ProphecyInfo {
    param_name: "count_capture",
    initial_var: "count_initial",     // count at closure creation
    prophecy_var: "count_prophecy",   // count after all calls
    inner_ty: Ty::Int(I32),
}

// Verification condition includes:
// ASSUME: count_initial = 0
// ASSERT: count_prophecy = count_initial + (number_of_calls)
```

**Source:** [The Future is Ours: Prophecy Variables in Separation Logic](https://plv.mpi-sws.org/prophecies/) - "Prophecy variables enable reasoning about mutable state by representing both current and final values."

### Pattern 4: Closure Contracts on Parameters

**What:** Specify closure behavior via `#[requires]`/`#[ensures]` on closure-accepting function parameters.

**When to use:** Functions accepting closures where closure behavior must satisfy specific contracts.

**Example:**

```rust
// Rust specification pattern:
#[requires(forall(|x: i32| x > 0 ==> closure(x) > 0))]
#[ensures(result > 0)]
fn apply_positive<F: Fn(i32) -> i32>(closure: F, value: i32) -> i32 {
    closure(value)
}

// IR representation:
Contracts {
    requires: vec![
        SpecExpr { raw: "forall(|x: i32| x > 0 ==> closure(x) > 0)" }
    ],
    ensures: vec![
        SpecExpr { raw: "result > 0" }
    ],
    ...
}

// VCGen generates:
// ASSUME: (forall ((x (_ BitVec 32)))
//           (=> (bvsgt x #x00000000)
//               (bvsgt (apply_closure env x) #x00000000)))
// ... function body encoding ...
// ASSERT: (bvsgt result #x00000000)
```

**Source:** [Modular Specification and Verification of Closures in Rust (Prusti)](https://dl.acm.org/doi/abs/10.1145/3485522) - "Combines Rust's type system guarantees and novel specification features to enable formal verification of rich functional properties."

### Anti-Patterns to Avoid

- **Anti-pattern: Direct higher-order SMT encoding**
  - **Why it's bad:** SMT solvers struggle with higher-order quantification; solving is incomplete/inefficient.
  - **What to do instead:** Always defunctionalize to first-order before SMT encoding.

- **Anti-pattern: Ignoring closure trait distinctions**
  - **Why it's bad:** `Fn`, `FnMut`, and `FnOnce` have different ownership/mutability semantics that affect soundness.
  - **What to do instead:** Track trait kind explicitly; use prophecies for `FnMut`, ownership transfer for `FnOnce`.

- **Anti-pattern: Inline closure contract checking**
  - **Why it's bad:** Breaks modularity; re-verifies closure for each call site; doesn't support separate compilation.
  - **What to do instead:** Store closure summaries in Contract DB; verify at definition, assume at call site.

- **Anti-pattern: Treating closures as opaque function pointers**
  - **Why it's bad:** Loses environment capture information; can't verify correctness of captured state.
  - **What to do instead:** Model closure as `(environment, function_body)` pair; encode environment explicitly.

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Closure environment extraction | Custom MIR analysis for upvars | Rust MIR already provides upvar info | MIR `ClosureSubsts` contains captured variable metadata; leverage compiler's work |
| Higher-order contract encoding | Custom SMT higher-order logic | Defunctionalization to first-order | Reynolds (1972) defunctionalization is proven; SMT solvers don't efficiently support higher-order |
| Mutable capture reasoning | Two-state logic or frame axioms | Existing `ProphecyInfo` infrastructure | Already implemented in Phase 1; Creusot/RustHornBelt proven pattern |
| Closure trait dispatch | Custom trait resolution | Rust type checker provides trait impl info | Type checker already resolved `Fn`/`FnMut`/`FnOnce`; trust compiler's trait selection |
| Algebraic datatype encoding | Custom struct-to-SMT logic | Existing `DeclareDatatype` from Phase 2 | Already proven for structs/enums; closure envs are just anonymous structs |

**Key insight:** Closures are **not new** in our verification architecture - they're combinations of existing capabilities:
- Closure environment = struct encoding (Phase 2) ✓
- Mutable captures = prophecy variables (Phase 1) ✓
- Closure calls = inter-procedural verification (Phase 3) ✓
- **NEW work:** Defunctionalization transformation, closure contract syntax

## Common Pitfalls

### Pitfall 1: Forgetting Closure Capture Mode

**What goes wrong:** Treating all closures as `Fn` (immutable capture) when some require `FnMut` or `FnOnce`.

**Why it happens:** Rust's capture inference is automatic; easy to overlook that `move ||` or mutable captures change trait implementation.

**How to avoid:**
- Parse closure capture mode from MIR `ClosureKind` (Fn/FnMut/FnOnce)
- Add IR field `trait_kind: ClosureTrait` to closure representation
- Validation: Check that closure call sites match trait kind (e.g., can't call `FnOnce` twice)

**Warning signs:**
- Verification fails on mutable closure with "immutable borrow" error
- `move` closures incorrectly allow multiple calls (should be `FnOnce`)
- Contract violations not detected when closure mutates captures

**Example:**
```rust
// WRONG: Treating as Fn (immutable)
let mut sum = 0;
let mut add = |x| sum += x;  // FnMut - mutates sum
// If verified as Fn, mutation soundness is lost!

// CORRECT: Detect FnMut, use prophecy variables
// ProphecyInfo { param_name: "sum_capture", initial_var: "sum_i", prophecy_var: "sum_f", ... }
```

### Pitfall 2: Missing Environment Capture in Nested Closures

**What goes wrong:** Nested closures (closure returning closure) don't capture outer closure environment correctly.

**Why it happens:** Environment chain isn't tracked - inner closure needs both its own captures AND parent closure environment access.

**How to avoid:**
- For v0.1: Defer to advanced features (ACLO-01: higher-order closures out of scope)
- For v0.2+: Track environment chain - inner closure env includes reference to outer env
- Detect nested closure pattern during IR construction; mark for special handling

**Warning signs:**
- Inner closure can't access outer closure's captured variables
- Type errors in closure environment field types
- Verification fails with "undefined variable" for outer captures

**Example (deferred to v0.2+):**
```rust
// DEFERRED - Higher-order closure (returns closure)
fn make_adder(x: i32) -> impl Fn(i32) -> i32 {
    move |y| x + y  // Inner closure captures outer x
}
// Environment chain: inner_env { outer_env: { x }, y }
```

### Pitfall 3: Closure Contract Scope Confusion

**What goes wrong:** Closure contract applies to closure-accepting function instead of closure itself; or vice versa.

**Why it happens:** Two levels of specification: (1) function accepting closure, (2) closure parameter behavior. Easy to conflate.

**How to avoid:**
- **Function-level contract:** Constrains function's pre/postconditions given closure behavior assumptions
  ```rust
  #[requires(forall(|x| x > 0 ==> closure(x) > 0))]  // Assumes closure property
  fn apply<F: Fn(i32) -> i32>(closure: F, x: i32) -> i32
  ```
- **Closure parameter contract:** Embedded in parameter specification (trait bound context)
  ```rust
  // Via trait bound extension (future syntax):
  fn apply<F: Fn(i32) -> i32 where F: requires(|x| x > 0) ensures(|r| r > 0)>(f: F, x: i32)
  ```
- **Current approach:** Closure contracts attach to closure-accepting function's parameter specs; VCGen interprets as closure behavior assumptions

**Warning signs:**
- Closure contract violation points to wrong call site (function call instead of closure call)
- Verification succeeds when it should fail (contract not actually checked)
- Contract duplication across multiple functions accepting same closure type

### Pitfall 4: Prophecy Variable Confusion with Multiple FnMut Calls

**What goes wrong:** Multiple calls to `FnMut` closure don't compose prophecy correctly - final value doesn't match actual state after all calls.

**Why it happens:** Prophecy represents *final* value at end of scope, but intermediate calls see intermediate states.

**How to avoid:**
- Prophecy applies to **closure lifetime scope**, not individual call
- For multiple calls in sequence:
  ```rust
  let mut x = 0;
  let mut inc = || { x += 1; };
  inc();  // x = 1 (intermediate)
  inc();  // x = 2 (final prophecy value)
  // Prophecy: x_prophecy = x_initial + 2
  ```
- Intermediate states: Use SSA-style locals for intermediate values; prophecy assertion only at scope end
- VCGen: Track prophecy fulfillment point (lifetime end, not call site)

**Warning signs:**
- Prophecy assertion fails mid-function (should only assert at end)
- Incorrect intermediate value assumptions (uses prophecy instead of current state)
- Multiple `FnMut` calls don't accumulate effects correctly

**Example:**
```rust
// WRONG: Assert prophecy at each call
inc();
assert!(x_capture == x_prophecy);  // TOO EARLY - prophecy is for END of scope
inc();

// CORRECT: Track intermediate states, assert prophecy at end
let x_after_call1 = x_initial + 1;  // Intermediate
let x_after_call2 = x_after_call1 + 1;  // Intermediate
// ... end of closure scope ...
assert!(x_capture == x_prophecy);  // CORRECT - final value
```

### Pitfall 5: Soundness: Closure Contract Bypass via Aliasing

**What goes wrong:** Closure captures `&mut T`, function mutates `T` directly, bypassing closure contract checks.

**Why it happens:** Rust borrow checker prevents this at runtime, but verification must model borrow exclusivity.

**How to avoid:**
- When closure captures `&mut x`, encode **exclusive access** - no other mutations to `x` during closure lifetime
- Use existing prophecy encoding: `x_initial` at capture, `x_prophecy` at release, no intermediate direct mutations
- Borrow exclusivity VC: `assert!(no_direct_mutations_to_x_during_closure_lifetime)`
- Phase 8 (Lifetimes) will formalize this; for Phase 7, conservatively assume closure lifetime = function scope

**Warning signs:**
- Closure contract verified but actual mutation bypasses it
- Test shows contract violation but verification passes
- Aliasing allows mutation of captured variable outside closure

**Example:**
```rust
// SOUNDNESS RISK:
let mut x = 0;
let mut inc = || { x += 1; };  // Captures &mut x
inc();
x += 10;  // DIRECT mutation - bypasses closure contract!
inc();
// Verification must detect that direct `x` mutation violates closure capture exclusivity

// CORRECT encoding:
// During closure lifetime: `x` is exclusively owned by closure environment
// No direct mutations allowed; all `x` updates go through closure
```

## Code Examples

### Example 1: Simple Fn Closure with Immutable Captures

```rust
// Rust code:
fn test_fn_closure() {
    let x = 5;
    let y = 10;
    let add = |z: i32| -> i32 { x + y + z };
    let result = add(3);
    assert!(result == 18);
}

// IR representation (pseudo):
// Closure definition:
Ty::Closure {
    name: "closure_add",
    env_fields: vec![("x", Ty::Int(I32)), ("y", Ty::Int(I32))],
    params: vec![("z", Ty::Int(I32))],
    return_ty: Ty::Int(I32),
    trait_kind: ClosureTrait::Fn,  // Immutable captures
}

// Closure creation (environment construction):
Statement::Assign(
    Place::Local("_closure_env"),
    Rvalue::Aggregate(
        AggregateKind::Closure("closure_add"),
        vec![Operand::Copy("_x"), Operand::Copy("_y")]
    )
)

// Closure call:
Terminator::Call {
    func: "closure_add",
    args: vec![Operand::Move("_closure_env"), Operand::Constant(3)],
    destination: Place::Local("_result"),
    target: 1,
}

// SMT encoding:
// 1. Declare closure environment datatype
(declare-datatype ClosureEnv_add
  ((mk-ClosureEnv_add
    (ClosureEnv_add-x (_ BitVec 32))
    (ClosureEnv_add-y (_ BitVec 32)))))

// 2. Construct environment
(define-const env ClosureEnv_add
  (mk-ClosureEnv_add #x00000005 #x0000000a))

// 3. Define closure function (defunctionalized)
(define-fun closure_add_impl
  ((env ClosureEnv_add) (z (_ BitVec 32))) (_ BitVec 32)
  (bvadd (bvadd (ClosureEnv_add-x env) (ClosureEnv_add-y env)) z))

// 4. Call closure
(define-const result (_ BitVec 32)
  (closure_add_impl env #x00000003))

// 5. Assert postcondition
(assert (= result #x00000012))  // 18 in hex
```

**Source:** Adapted from [Rust MIR RFC 1211](https://rust-lang.github.io/rfcs/1211-mir.html) closure lowering semantics.

### Example 2: FnMut Closure with Prophecy Variables

```rust
// Rust code:
fn test_fnmut_closure() {
    let mut count = 0;
    let mut increment = || { count += 1; };
    increment();
    increment();
    assert!(count == 2);
}

// IR representation (pseudo):
// Closure definition:
Ty::Closure {
    name: "closure_increment",
    env_fields: vec![("count_mut_ref", Ty::Ref(Box::new(Ty::Int(I32)), Mutability::Mutable))],
    params: vec![],
    return_ty: Ty::Unit,
    trait_kind: ClosureTrait::FnMut,  // Mutable capture
}

// Prophecy info for mutable capture:
ProphecyInfo {
    param_name: "count_capture",
    initial_var: "count_initial",
    prophecy_var: "count_prophecy",
    inner_ty: Ty::Int(I32),
}

// SMT encoding:
// 1. Declare prophecy variables
(declare-const count_initial (_ BitVec 32))
(declare-const count_prophecy (_ BitVec 32))

// 2. Initial value
(assert (= count_initial #x00000000))

// 3. Closure environment (contains mutable reference semantics)
(declare-datatype ClosureEnv_increment
  ((mk-ClosureEnv_increment
    (ClosureEnv_increment-count_ref (_ BitVec 32)))))  // Simplified: ref as value

// 4. First call: count_after_call1 = count_initial + 1
(define-const count_after_call1 (_ BitVec 32)
  (bvadd count_initial #x00000001))

// 5. Second call: count_after_call2 = count_after_call1 + 1
(define-const count_after_call2 (_ BitVec 32)
  (bvadd count_after_call1 #x00000001))

// 6. Prophecy fulfillment at end of closure lifetime
(assert (= count_prophecy count_after_call2))

// 7. Final assertion
(assert (= count_prophecy #x00000002))
```

**Source:** Based on [Creusot prophecy-based verification](https://inria.hal.science/hal-03737878v1/document) - "Prophecies represent mutable borrows as pair of current and final values."

### Example 3: Closure Contract on Function Parameter

```rust
// Rust code:
#[requires(forall(|x: i32| x > 0 ==> predicate(x) == true))]
#[ensures(result > 0)]
fn find_first<F: Fn(i32) -> bool>(predicate: F, start: i32) -> i32 {
    let mut current = start;
    while !predicate(current) {
        current += 1;
    }
    current
}

// IR representation:
Contracts {
    requires: vec![
        SpecExpr { raw: "forall(|x: i32| x > 0 ==> predicate(x) == true)" }
    ],
    ensures: vec![
        SpecExpr { raw: "result > 0" }
    ],
    ...
}

// SMT encoding:
// 1. Closure contract as uninterpreted function with axiom
(declare-fun predicate_impl ((_ BitVec 32)) Bool)

// 2. Contract assumption (from #[requires])
(assert
  (forall ((x (_ BitVec 32)))
    (=> (bvsgt x #x00000000)
        (= (predicate_impl x) true))))

// 3. Function body encoding (loop with invariant)
(define-const start (_ BitVec 32) ...)
(declare-const current (_ BitVec 32))
// ... loop invariant: current >= start, predicate not yet satisfied ...

// 4. Postcondition VC
(assert (=> (= (predicate_impl current) true)
            (bvsgt current #x00000000)))
```

**Source:** Pattern from [Prusti closure specification](https://dl.acm.org/doi/abs/10.1145/3485522) - "Closure contracts encoded as first-order assumptions on uninterpreted functions."

### Example 4: FnOnce Closure with Move Semantics

```rust
// Rust code:
fn test_fnonce_closure() {
    let data = vec![1, 2, 3];
    let consume = move || {
        let sum: i32 = data.iter().sum();
        sum
    };
    let result = consume();
    // data is consumed - can't use again
    assert!(result == 6);
}

// IR representation (pseudo):
Ty::Closure {
    name: "closure_consume",
    env_fields: vec![("data", Ty::Struct("Vec", ...))],  // Owned, not reference
    params: vec![],
    return_ty: Ty::Int(I32),
    trait_kind: ClosureTrait::FnOnce,  // Consumes environment
}

// Key difference from Fn/FnMut:
// - Closure call consumes environment (ownership transfer)
// - Can only call once (enforce in IR validation)

// SMT encoding:
// 1. Closure environment (owned data)
(declare-datatype ClosureEnv_consume
  ((mk-ClosureEnv_consume
    (ClosureEnv_consume-data Vec_i32))))  // Owned Vec

// 2. Environment construction
(define-const env ClosureEnv_consume
  (mk-ClosureEnv_consume (mk-Vec ...)))  // data moved into env

// 3. Closure call (consumes env)
(define-fun closure_consume_impl
  ((env ClosureEnv_consume)) (_ BitVec 32)
  (vec_sum (ClosureEnv_consume-data env)))

// 4. Call (ownership transfer - env no longer valid after)
(define-const result (_ BitVec 32)
  (closure_consume_impl env))

// 5. VALIDATION: Reject second call
// Terminator::Call { func: "closure_consume", args: [env], ... }  // ERROR: env moved
```

**Source:** Ownership semantics from [Rust Closure RFC 114](https://rust-lang.github.io/rfcs/0114-closures.html) - "FnOnce consumes its environment."

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| Higher-order SMT (incomplete) | Defunctionalization to first-order | Reynolds 1972, adopted by verification tools 2018+ | SMT solvers can efficiently solve closure verification problems |
| Frame axioms for mutation | Prophecy variables | Introduced to separation logic 2020 (Jung et al., POPL) | Compositional reasoning about mutable borrows; adopted by Creusot 2022 |
| Closure inlining only | Closure summaries in Contract DB | Prusti 2021 (OOPSLA) | Modular verification; separate compilation support |
| Opaque function pointers | Environment + function pairs | RustHornBelt 2021, standard in Rust verifiers | Captures closure semantics accurately; enables capture reasoning |

**Deprecated/outdated:**
- **Manual closure contract encoding:** Prusti's 2021 work showed automated closure contract inference for simple cases; v0.2+ should explore auto-inference (out of scope for v0.1).
- **Direct higher-order SMT-LIB:** SMT-LIB2 has higher-order logic extensions, but solver support is poor; defunctionalization remains standard practice.

**Recent developments (2025-2026):**
- **Creusot POPL 2026 tutorial:** Confirms prophecy-based approach is state-of-practice for Rust verification.
- **Thrust (PLDI 2025):** Prophecy-based refinement types for Rust - validates prophecy variable approach for complex mutable borrowing patterns.

## Open Questions

### Question 1: Higher-Order Closures (Closures Returning Closures)

**What we know:**
- Deferred to v0.2+ (ACLO-01, ACLO-02)
- Requires environment chaining (inner env references outer env)
- Defunctionalization extends naturally (closure constructor contains closure)

**What's unclear:**
- Best IR representation for environment chain
- Contract composition rules (how do inner closure contracts relate to outer?)

**Recommendation:**
- Phase 7 v0.1: Detect higher-order closures during IR construction; emit error "Higher-order closures not yet supported (v0.2+)"
- Document pattern for future: `Ty::Closure` field `parent_env: Option<Box<Ty>>` for environment chain

### Question 2: Closure Contract Auto-Inference

**What we know:**
- Prusti (2021) demonstrates auto-inference for "simple closures" (pure, no complex control flow)
- Creusot 0.9.0 auto-infers immutable variables in loop invariants

**What's unclear:**
- Definition of "simple enough" for auto-inference
- Fallback strategy when inference fails

**Recommendation:**
- Phase 7 v0.1: Require explicit closure contracts (manual specification)
- Phase 10 v0.2: Explore auto-inference for `pure` closures with single expression body
- Strategy: Attempt inference, fall back to require manual contract if inference indeterminate

### Question 3: Generic Closures (Closures over Generic Types)

**What we know:**
- Closures can capture generic type parameters: `fn foo<T>(x: T) { let c = || use_x(x); }`
- Phase 5 (Generics) handles generic functions via monomorphization

**What's unclear:**
- Timing: Does closure monomorphization happen before or after defunctionalization?
- Interaction: Generic closure environment datatype requires parametric polymorphism in SMT

**Recommendation:**
- Follow Phase 5 pattern: Monomorphize closures alongside functions
- Closure environment datatype becomes concrete after monomorphization: `ClosureEnv_foo_i32`, `ClosureEnv_foo_String`, etc.
- Document interaction in Phase 7 → Phase 5 dependency notes

### Question 4: Recursive Closures

**What we know:**
- Rust doesn't directly support recursive closures (closure can't reference itself)
- Workaround: `let rec_fn = &mut None; *rec_fn = Some(|| rec_fn.unwrap()());` (uses mutation)
- Phase 6 handles recursive functions with termination measures

**What's unclear:**
- Should we support "tricky" recursive closure patterns?
- Or emit error and guide user to use regular recursive function?

**Recommendation:**
- Phase 7 v0.1: Detect recursive closure attempts; emit error "Recursive closures not supported - use recursive function instead"
- Rationale: Rare pattern, complex encoding, user can refactor to regular function

## Sources

### Primary (HIGH confidence)

- [Defunctionalization of Higher-Order Constrained Horn Clauses (ar5iv)](https://ar5iv.labs.arxiv.org/html/1810.03598) - Defunctionalization algorithm, closure representation, Apply/IOMatch encoding patterns
- [The Future is Ours: Prophecy Variables in Separation Logic (POPL 2020)](https://plv.mpi-sws.org/prophecies/) - Prophecy variable semantics, proof rules, mutable state handling
- [Rust MIR RFC 1211](https://rust-lang.github.io/rfcs/1211-mir.html) - Official Rust MIR closure lowering semantics
- [Rust Closure Types Reference](https://doc.rust-lang.org/reference/types/closure.html) - Fn/FnMut/FnOnce trait semantics
- [Closure Capture Inference - Rust Compiler Dev Guide](https://rustc-dev-guide.rust-lang.org/closure.html) - Upvar handling, environment struct representation

### Secondary (MEDIUM confidence)

- [Modular Specification and Verification of Closures in Rust (Prusti, OOPSLA 2021)](https://dl.acm.org/doi/abs/10.1145/3485522) - Closure contract patterns (paper not directly accessible; cited in search results)
- [Creusot: A Foundry for the Deductive Verification of Rust Programs](https://inria.hal.science/hal-03737878v1/document) - Prophecy-based Rust verification, closure contract inference mention
- [Z3 Datatypes Guide](https://microsoft.github.io/z3guide/docs/theories/Datatypes/) - SMT-LIB algebraic datatype encoding
- [Defunctionalization Wikipedia](https://en.wikipedia.org/wiki/Defunctionalization) - Historical context, Reynolds 1972, basic algorithm
- [RustHornBelt Paper](https://people.mpi-sws.org/~dreyer/papers/rusthornbelt/paper.pdf) - Mutable borrows as clairvoyant pairs (current + prophecy)

### Tertiary (LOW confidence - requires validation)

- [Contracts for Higher-Order Functions (ResearchGate)](https://www.researchgate.net/publication/2547311_Contracts_for_Higher-Order_Functions) - Higher-order contract challenges (not verified against original paper)
- [Soft Contract Verification for Higher-Order Stateful Programs (ResearchGate)](https://www.researchgate.net/publication/386703936_Soft_Contract_Verification_for_Higher-Order_Stateful_Programs) - Multi-stage contract logic (recent but not confirmed in official proceedings)
- WebSearch results on closure verification pitfalls - General formal verification challenges, not closure-specific (flagged as LOW confidence)

### Codebase (HIGH confidence - verified)

- `crates/analysis/src/ir.rs` (lines 29-31, 106-126) - Existing `ProphecyInfo` struct for mutable borrows
- `crates/smtlib/src/command.rs` (lines 50-54) - Existing `DeclareDatatype` for algebraic types
- `crates/analysis/src/ir.rs` (lines 377-404) - `Ty` enum (extend with `Ty::Closure`)
- `crates/analysis/src/ir.rs` (lines 167-173) - `Terminator::Call` (closure calls will use this)

## Metadata

**Confidence breakdown:**

- **Standard stack:** HIGH - Builds on verified existing infrastructure (DeclareDatatype, ProphecyInfo, IR)
- **Architecture patterns:** MEDIUM-HIGH - Defunctionalization is proven (Reynolds 1972), prophecy variables proven (POPL 2020, Creusot 2022), Rust MIR semantics official; uncertainty in implementation details (contract syntax parsing, environment extraction specifics)
- **Pitfalls:** MEDIUM - Based on reasoning from first principles + verification literature common themes; not closure-specific empirical data (no large-scale closure verification postmortem studies found)
- **Closure contracts:** MEDIUM - Prusti paper not directly accessible (ACM paywall); relying on abstract + secondary citations; syntax details need validation

**Research date:** 2026-02-12
**Valid until:** ~60 days (stable theoretical foundations; Rust MIR semantics slow-changing)

**Gaps requiring validation during implementation:**
1. Exact Prusti closure contract syntax - need to review paper or Prusti source code
2. MIR upvar extraction API - need to test with actual rustc MIR output
3. Z3 datatype performance with deeply nested closure environments - may need benchmarking
4. Prophecy variable composition with multiple FnMut calls - verify with test cases
