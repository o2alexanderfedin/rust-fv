# Specification Languages for Formal Verification: Applicability to Rust

## Executive Summary

This document surveys specification languages used in formal verification, analyzes their design principles, and proposes an approach for Rust-specific formal verification that respects ownership, lifetimes, and type system integration.

## 1. Specification Language Overview

### 1.1 ACSL (ANSI/ISO C Specification Language)

**Design Philosophy**: ACSL follows the design-by-contract paradigm with Hoare-style pre/postconditions for C programs.

**Key Features**:
- Annotations embedded in C comments (`/*@ ... */`)
- First-order logic semantics with total functions
- Supports function contracts, invariants, assertions
- Tool support via Frama-C

**Example**:
```c
/*@ requires x > 0;
    ensures \result >= x;
    assigns \nothing; */
int increment(int x) {
    return x + 1;
}
```

**Strengths**: Mature tooling, well-specified semantics, separation of specification from code.

**Limitations**: No native support for ownership or type state; designed for C's memory model.

### 1.2 JML (Java Modeling Language)

**Design Philosophy**: Model-based specifications combining Eiffel's pragmatism with VDM/Larch expressiveness.

**Key Features**:
- Annotations in special Java comments (`//@ ...` or `/*@ ... */`)
- Java expression syntax extended with specification constructs
- Side-effect specifications via `assignable` clauses
- Class invariants and method contracts

**Example**:
```java
//@ requires x > 0 && y > 0;
//@ ensures \result == x + y;
//@ pure
public int add(int x, int y) {
    return x + y;
}
```

**Strengths**: Accessible to Java programmers; rich model-based specifications; extensive tool ecosystem.

**Limitations**: Tied to Java's object model; limited handling of aliasing and mutable state.

### 1.3 Dafny

**Design Philosophy**: Verification-aware programming language where verification is first-class.

**Key Features**:
- Integrated language and verifier (no annotations-only approach)
- Unbounded/bounded quantifiers, calculational proofs
- Loop invariants, termination conditions, frame conditions
- Compiles to C#, Java, JavaScript, Go, Python

**Example**:
```dafny
method Max(a: int, b: int) returns (r: int)
    ensures r >= a && r >= b
    ensures r == a || r == b
{
    if a > b { return a; }
    else { return b; }
}
```

**Strengths**: Seamless verification workflow; auto-active verification; strong automation.

**Limitations**: Separate language (not a specification layer); different programming model than Rust.

### 1.4 SPARK Ada

**Design Philosophy**: Ada subset with enhanced contracts for high-assurance software.

**Key Features**:
- Eliminates undefined behavior through language subsetting
- Proof contexts via Ada aspects/pragmas
- Ghost code for specification without runtime cost
- Flow analysis and data dependencies

**Example**:
```ada
function Max (A, B : Integer) return Integer with
    Post => Max'Result >= A and Max'Result >= B and
            (Max'Result = A or Max'Result = B)
is
begin
    if A > B then return A; else return B; end if;
end Max;
```

**Strengths**: Mathematically proven contracts; mature tooling; proven in safety-critical systems.

**Limitations**: Ada-specific; heavy language subsetting requirements.

## 2. Rust-Specific Verification Approaches

### 2.1 Prusti

**Approach**: Procedural macro-based verification using Viper backend.

**Syntax Style**:
```rust
#[requires(x > 5)]
#[ensures(result >= 0)]
#[ensures(result == (x - 1) / 2)]
fn foo(x: i32) -> i32 {
    if x <= 5 { panic!(); }
    (x - 1) / 2
}
```

**Key Features**:
- Rust attribute macros for specifications
- `#[pure]` functions usable in contracts
- Loop invariants via `#[invariant(...)]`
- Uses `result` keyword for return values
- Leverages Rust's type system

### 2.2 Creusot

**Approach**: Translation to Why3 with prophecy-based reasoning for mutable borrows.

**Specification Language**: Pearlite (Rust-inspired logic language)

**Syntax Style**:
```rust
#[requires(x > 0)]
#[ensures(result@ > x@)]
fn increment(x: &mut i32) {
    *x = *x + 1;
}
```

**Key Features**:
- Model operator `@` for logical values
- Final operator `^` for prophecies (future values of mutable borrows)
- Ghost code and resources
- Type invariants (v0.9.0, January 2026)
- Handles unsafe code with pointer reasoning

**Example with Mutable Borrow**:
```rust
#[requires(*x@ > 0)]
#[ensures(^x@ == *x@ + 1)]
fn increment_mut(x: &mut i32) {
    *x += 1;
}
```

### 2.3 Flux (Liquid Types)

**Approach**: Refinement types integrated with ownership.

**Key Features**:
- SMT-based refinement type checking
- Synthesizes loop annotations automatically
- Handles pointer manipulation with refinements
- Integrates with Rust's borrow checker

**Example**:
```rust
#[flux::sig(fn(x: i32{x > 0}) -> i32{v: v > x})]
fn increment(x: i32) -> i32 {
    x + 1
}
```

### 2.4 Thrust

**Approach**: Prophecy-based refinement types for automated verification.

**Key Features**:
- Synthesizes inductive invariants for loops/recursion
- Handles pointer aliasing and borrowing precisely
- Automated verification with minimal annotations

### 2.5 RefinedRust

**Approach**: Foundational verification with refined ownership types.

**Key Features**:
- Handles real Rust code (including unsafe)
- Proof automation via separation logic
- Machine-checkable proofs in Coq
- First to combine practicality with soundness

## 3. Handling Rust's Unique Features

### 3.1 Ownership

**Challenge**: Specifications must express transfer of ownership and uniqueness invariants.

**Solutions**:
- **Prusti**: Leverages Rust's type system; ownership implicit in types
- **Creusot**: Uses ghost resources to track ownership explicitly
- **RefinedRust**: Refined ownership types in separation logic
- **Flux**: Refinements on owned values

**Recommended Approach**: Explicit ownership predicates in specifications when needed, but rely on Rust's type system where possible.

```rust
#[ensures(owns(result))]  // Explicit when needed
fn new_box(x: i32) -> Box<i32> {
    Box::new(x)
}
```

### 3.2 Lifetimes

**Challenge**: Specifications must reason about pointer validity across lifetime boundaries.

**Solutions**:
- **Creusot**: Prophecies (`^`) for final values at lifetime end
- **Flux**: Refinements track lifetime relationships
- **Formal Models**: Flow-sensitive type systems (Pearce 2021)

**Recommended Approach**:
- Use prophecy-style operators for mutable borrows
- Lifetime parameters in specifications mirror Rust's
- Frame conditions express which references remain valid

```rust
#[requires(valid(x, 'a))]
#[ensures(valid(x, 'a) && ^x@ == *x@ + 1)]
fn increment<'a>(x: &'a mut i32) {
    *x += 1;
}
```

### 3.3 Borrowing (Shared vs. Mutable)

**Challenge**: Specifications must distinguish read-only from read-write access.

**Solutions**:
- **Creusot**: Separate logical operators for current (`*x@`) and final (`^x@`) values
- **RefinedRust**: Separation logic with different predicates for shared/mutable borrows
- **ACSL-style**: Frame clauses (`assigns` in ACSL, implicit in Rust types)

**Recommended Approach**:
- Shared references: Specifications over current values only
- Mutable references: Specifications over both current and final values

```rust
// Shared reference: read-only
#[requires(*x@ > 0)]
#[ensures(result == *x@ * 2)]
fn double(x: &i32) -> i32 {
    x * 2
}

// Mutable reference: transformation
#[requires(*x@ > 0)]
#[ensures(*x@ == old(*x@) && ^x@ == *x@ + 1)]
fn increment(x: &mut i32) {
    *x += 1;
}
```

### 3.4 Type States

**Challenge**: Rust patterns like typestate (encoding state in types) need specification support.

**Solutions**:
- **Type Invariants** (Creusot 0.9.0): Properties all values of a type satisfy
- **Refinement Types** (Flux, Thrust): Dependent types encoding state
- **Ghost State**: Track abstract state alongside concrete values

**Recommended Approach**: Type invariants for data structure well-formedness; ghost state for protocol states.

```rust
#[invariant(self.len <= self.capacity)]
struct Vec<T> {
    data: *mut T,
    len: usize,
    capacity: usize,
}
```

## 4. Specification Language Design Principles

### 4.1 Core Principles

1. **Integration with Host Language**: Specifications should use host language syntax where possible (following JML/Prusti model)

2. **Separation of Concerns**: Clear distinction between:
   - Pure specifications (no side effects)
   - Imperative code
   - Ghost code (specification-only, erased at runtime)

3. **Progressive Precision**: Allow partial specifications; verify what's specified; assume the rest

4. **Modular Verification**: Function contracts enable modular reasoning without examining implementations

5. **Automation-Friendly**: Design for SMT solvers (e.g., decidable fragments, trigger annotations)

### 4.2 Syntax Design

**Annotation Style** (Prusti-like):
- Pros: Non-invasive; works with existing Rust; familiar attribute syntax
- Cons: Verbose for complex specifications; separate from code

**Embedded Style** (Dafny-like):
- Pros: Specifications near relevant code; single syntax
- Cons: Requires language changes; less backward-compatible

**Recommendation**: Start with annotation style using procedural macros for backward compatibility, potentially evolving toward language integration.

### 4.3 Expression Language

**Base**: Rust expression syntax (like JML uses Java)

**Extensions Needed**:
- **Logical operators**: `&&`, `||`, `!`, `==>` (implication), `<==>` (iff)
- **Quantifiers**: `forall<T>(|x: T| ...)`, `exists<T>(|x: T| ...)`
- **Special values**: `result`, `old(expr)` (value at function entry)
- **Model access**: `@` operator (logical view of value)
- **Prophecy**: `^` operator (final value of mutable borrow)
- **Frame conditions**: Implicit from Rust types, explicit when needed

## 5. Proposed Specification Approach for Rust

### 5.1 Syntax Proposal

**Basic Function Contracts**:
```rust
#[requires(precondition_expr)]
#[ensures(postcondition_expr)]
fn function_name(params) -> ReturnType {
    // implementation
}
```

**Pure Functions** (usable in specifications):
```rust
#[pure]
#[ensures(result >= a && result >= b)]
fn max(a: i32, b: i32) -> i32 {
    if a > b { a } else { b }
}
```

**Loop Invariants**:
```rust
fn sum(arr: &[i32]) -> i32 {
    let mut total = 0;
    let mut i = 0;

    #[invariant(i <= arr.len())]
    #[invariant(total == sum_of(arr, 0, i))]
    while i < arr.len() {
        total += arr[i];
        i += 1;
    }

    total
}
```

**Type Invariants**:
```rust
#[invariant(self.len <= self.capacity)]
#[invariant(self.capacity == 0 ==> self.ptr.is_null())]
struct Vec<T> {
    ptr: *mut T,
    len: usize,
    capacity: usize,
}
```

**Ghost Code**:
```rust
#[ghost]
fn abstract_value(&self) -> Seq<T> {
    // specification-only function
}

#[ensures(result.abstract_value() == old(self.abstract_value()))]
fn clone(&self) -> Self {
    // implementation
}
```

### 5.2 Handling Ownership and Borrowing

**Ownership Transfer**:
```rust
#[ensures(owns(result))]
fn new_string() -> String {
    String::new()
}

#[requires(owns(s))]
#[ensures(!owns(s))]  // ownership consumed
fn consume(s: String) {
    drop(s);
}
```

**Mutable Borrows with Prophecies**:
```rust
#[requires(*x@ < 100)]
#[ensures(*x@ == old(*x@))]  // Current value unchanged during call
#[ensures(^x@ == *x@ + 1)]   // Final value (after mutation)
fn increment(x: &mut i32) {
    *x += 1;
}
```

**Shared References**:
```rust
#[requires(arr@.len() > 0)]
#[ensures(result@ <= arr@[0])]
#[ensures(exists(|i| i < arr@.len() && arr@[i] == result@))]
fn find_min(arr: &[i32]) -> i32 {
    // implementation
}
```

### 5.3 Lifetime Specifications

```rust
#[requires(valid(data, 'a))]
#[ensures(valid(result, 'a))]
#[ensures(result@ == data@[index@])]
fn get<'a, T>(data: &'a [T], index: usize) -> &'a T {
    &data[index]
}
```

### 5.4 Unsafe Code Specifications

```rust
#[requires(ptr.is_valid())]
#[requires(ptr.is_aligned())]
#[ensures(result == *ptr@)]
unsafe fn read_ptr<T>(ptr: *const T) -> T {
    ptr.read()
}
```

## 6. Examples in Rust Context

### 6.1 Binary Search

```rust
#[pure]
fn is_sorted(arr: &[i32]) -> bool {
    forall(|i: usize, j: usize|
        i < j && j < arr.len() ==> arr[i] <= arr[j])
}

#[requires(is_sorted(arr))]
#[ensures(match result {
    Some(idx) => idx < arr.len() && arr[idx] == target,
    None => forall(|i| i < arr.len() ==> arr[i] != target)
})]
fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    let mut low = 0;
    let mut high = arr.len();

    #[invariant(low <= high && high <= arr.len())]
    #[invariant(forall(|i| i < low ==> arr[i] < target))]
    #[invariant(forall(|i| i >= high && i < arr.len() ==> arr[i] > target))]
    while low < high {
        let mid = low + (high - low) / 2;

        if arr[mid] < target {
            low = mid + 1;
        } else if arr[mid] > target {
            high = mid;
        } else {
            return Some(mid);
        }
    }

    None
}
```

### 6.2 Linked List

```rust
#[ghost]
fn list_model(&self) -> Seq<T> {
    match self.head {
        None => Seq::empty(),
        Some(ref node) => Seq::cons(node.value, node.next.list_model())
    }
}

#[invariant(self.len == self.list_model().len())]
struct LinkedList<T> {
    head: Option<Box<Node<T>>>,
    len: usize,
}

#[ensures(result.list_model() == Seq::empty())]
#[ensures(result.len == 0)]
fn new() -> LinkedList<T> {
    LinkedList { head: None, len: 0 }
}

#[ensures(self.list_model() == Seq::cons(value, old(self.list_model())))]
#[ensures(self.len == old(self.len) + 1)]
fn push_front(&mut self, value: T) {
    let new_node = Box::new(Node {
        value,
        next: self.head.take(),
    });
    self.head = Some(new_node);
    self.len += 1;
}
```

### 6.3 Vector Capacity Management

```rust
#[invariant(self.len <= self.capacity)]
#[invariant(self.capacity == 0 <==> self.ptr.is_null())]
#[invariant(forall(|i| i < self.len ==> valid(self.ptr.add(i))))]
struct Vec<T> {
    ptr: *mut T,
    len: usize,
    capacity: usize,
}

#[requires(new_cap > self.capacity)]
#[ensures(self.capacity >= new_cap)]
#[ensures(self.len == old(self.len))]
#[ensures(forall(|i| i < self.len ==> self[i] == old(self[i])))]
unsafe fn grow(&mut self, new_cap: usize) {
    // reallocation logic
}
```

## 7. Integration with Type System

### 7.1 Type-Level Specifications

Leverage Rust's type system for zero-cost specifications:

```rust
// NonZero types express invariants at type level
fn reciprocal(x: NonZeroI32) -> f64 {
    1.0 / (x.get() as f64)
}

// No runtime check needed; type guarantees non-zero
```

### 7.2 Refinement Types as Type Parameters

```rust
struct Vec<T, const N: usize> {
    // Length tracked at type level
}

impl<T, const N: usize> Vec<T, N> {
    #[ensures(result.len() == N)]
    fn new() -> Self { ... }
}
```

### 7.3 Phantom Types for State

```rust
struct File<State> {
    handle: FileHandle,
    _state: PhantomData<State>,
}

impl File<Closed> {
    #[ensures(valid(result))]
    fn open(path: &str) -> File<Open> { ... }
}

impl File<Open> {
    #[requires(valid(self))]
    fn read(&mut self) -> Vec<u8> { ... }

    #[ensures(!valid(self))]
    fn close(self) -> File<Closed> { ... }
}
```

## 8. Recommendations

### 8.1 Syntax Approach

**Short Term**: Adopt Prusti-style attribute macros for immediate compatibility:
- `#[requires(...)]`, `#[ensures(...)]`
- `#[pure]` for specification functions
- `#[invariant(...)]` for loops and types

**Long Term**: Work toward language integration similar to Rust's async/await evolution:
- Built-in contracts as language feature
- First-class support in compiler
- Better error messages and IDE integration

### 8.2 Semantic Operators

Essential operators for Rust specifications:
- `@`: Model/logical view operator (Creusot-style)
- `^`: Prophecy/final value operator (Creusot-style)
- `old(...)`: Pre-state values
- `result`: Return value in postconditions
- `forall`, `exists`: Quantifiers
- `==>`, `<==>`: Logical implication and equivalence

### 8.3 Tool Strategy

1. **Parser/Checker**: Procedural macro crate for syntax validation
2. **Backend**: Leverage existing tools (Why3, Z3, CVC5)
3. **Integration**: Cargo plugin for seamless workflow
4. **IDE Support**: LSP for inline verification feedback

### 8.4 Incremental Adoption

- Start with simple function contracts
- Add loop invariants for verified functions
- Introduce type invariants for data structures
- Handle unsafe code with low-level specifications
- Use refinement types for automation where beneficial

## 9. Conclusion

Rust's unique ownership and lifetime system requires specification languages that:
1. **Embrace the type system**: Leverage Rust's existing guarantees
2. **Handle state changes**: Prophecies for mutable borrows
3. **Support modularity**: Contracts enable separate verification
4. **Enable automation**: SMT-friendly specifications
5. **Maintain ergonomics**: Rust-like syntax, progressive precision

The proposed approach combines:
- **Prusti's attribute-based syntax** for compatibility
- **Creusot's prophecy operators** for mutable borrows
- **Flux's automation** through refinement types
- **ACSL/JML's maturity** in specification design

This creates a practical specification language that respects Rust's philosophy while enabling rigorous formal verification.

---

## References

### ACSL
- [ANSI/ISO C Specification Language - Wikipedia](https://en.wikipedia.org/wiki/ANSI/ISO_C_Specification_Language)
- [GitHub - acsl-language/acsl](https://github.com/acsl-language/acsl)
- [ANSI/ISO C Specification Language Version 1.23](https://www.frama-c.com/download/acsl.pdf)

### JML
- [Java Modeling Language - Wikipedia](https://en.wikipedia.org/wiki/Java_Modeling_Language)
- [Formal Specification with the Java Modeling Language](https://www.cse.chalmers.se/~ahrendt/papers/JML16chapter.pdf)
- [Java Modeling Language (JML) Reference Manual](https://www.openjml.org/documentation/JML_Reference_Manual.pdf)

### Dafny
- [Dafny 2026 - POPL 2026](https://popl26.sigplan.org/home/dafny-2026)
- [GitHub - dafny-lang/dafny](https://github.com/dafny-lang/dafny)
- [Dafny Documentation](https://dafny.org/dafny/DafnyRef/DafnyRef)
- [Getting Started with Dafny Guide](https://www.andrew.cmu.edu/course/18-330/2025s/reading/dafny_guide.pdf)

### SPARK Ada
- [SPARK Proof Manual](https://docs.adacore.com/sparkdocs-docs/Proof_Manual.htm)
- [SPARK: Formal Verification in Ada (2026)](https://jordansrowles.medium.com/spark-formal-verification-and-proving-program-correctness-in-ada-3105cc82694d)
- [SPARK Overview](https://learn.adacore.com/courses/intro-to-spark/chapters/01_Overview.html)

### Rust Verification Tools
- [Creusot: Formal verification of Rust programs (POPL 2026)](https://popl26.sigplan.org/details/POPL-2026-tutorials/6/Creusot-Formal-verification-of-Rust-programs)
- [Creusot 0.9.0 Release (January 2026)](https://creusot-rs.github.io/devlog/2026-01-19/)
- [The Prusti Project: Formal Verification for Rust](https://pm.inf.ethz.ch/publications/AstrauskasBilyFialaGrannanMathejaMuellerPoliSummers22.pdf)
- [Prusti User Guide](https://viperproject.github.io/prusti-dev/user-guide/basic.html)

### Refinement Types
- [RefinedRust: A Type System for High-Assurance Verification](https://plv.mpi-sws.org/refinedrust/)
- [Flux: Liquid Types for Rust](https://dl.acm.org/doi/10.1145/3591283)
- [Thrust: Prophecy-Based Refinement Types](https://dl.acm.org/doi/10.1145/3729333)

### Ownership and Lifetimes
- [A Lightweight Formalism for Reference Lifetimes and Borrowing](https://dl.acm.org/doi/fullHtml/10.1145/3443420)
- [KRust: A Formal Executable Semantics of Rust](https://arxiv.org/pdf/1804.10806)

### Rust Contracts and Formal Methods
- [Rust Contracts: Language Intrinsics](https://github.com/rust-lang/compiler-team/issues/759)
- [Rust Formal Methods Interest Group](https://rust-formal-methods.github.io/)
- [Rust Verification Workshop 2026 (RW2026)](http://www.mail-archive.com/types-announce@lists.seas.upenn.edu/msg11860.html)

### Design Principles
- [Design by Contract Introduction - Eiffel](https://www.eiffel.com/values/design-by-contract/introduction/)
- [Design by Contract - Wikipedia](https://en.wikipedia.org/wiki/Design_by_contract)
- [Programming Language Specification - Wikipedia](https://en.wikipedia.org/wiki/Programming_language_specification)
