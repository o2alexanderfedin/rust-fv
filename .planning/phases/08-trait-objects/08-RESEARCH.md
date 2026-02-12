# Phase 8: Trait Objects - Research

**Researched:** 2026-02-12
**Domain:** Trait object verification via behavioral subtyping and vtable encoding
**Confidence:** HIGH

## Summary

Trait object verification requires encoding two fundamentally different dispatch mechanisms: **static monomorphization** (generic trait bounds) and **dynamic dispatch** (`dyn Trait`). The core challenge is verifying that every `impl Trait for Type` satisfies the trait-level contracts (behavioral subtyping), enabling sound reasoning about trait object method calls without knowing the concrete runtime type.

The verification approach depends on trait visibility: **sealed traits** (closed-world) enumerate all known implementations as SMT sum types, while **public traits** (open-world) use uninterpreted functions with trait-level contracts as axioms. Dynamic dispatch verification follows Kani's 2022 ICSE approach: function pointer restriction at vtable call sites, using trait-level specifications rather than impl-specific contracts.

rust-fv already has all necessary infrastructure: `Ty::Generic` with trait bounds, `ContractDatabase` for modular verification, defunctionalization from Phase 7, and SMT datatype encoding from Phase 2. Phase 8 extends this with `Ty::TraitObject` for `dyn Trait` types, behavioral subtyping VCs that verify each impl refines the trait contract (stronger postconditions, weaker preconditions), and vtable encoding that constrains dynamic dispatch to use trait-level specifications.

**Primary recommendation:** Require trait-level `#[requires]`/`#[ensures]` annotations on trait methods. Generate behavioral subtyping VCs for each `impl Trait for Type` that verify impl contracts refine trait contracts. For `dyn Trait` method calls, use trait-level contracts with uninterpreted functions (open-world) or sum types over known impls (closed-world sealed traits). Follow Liskov substitution principle: impl postconditions must strengthen trait postconditions, impl preconditions must weaken trait preconditions.

## Standard Stack

### Core

This phase builds entirely on existing codebase infrastructure - no external dependencies needed.

| Component | Version | Purpose | Why Standard |
|-----------|---------|---------|--------------|
| SMT-LIB2 Datatypes | Built-in | Sum types for sealed traits | Industry standard for algebraic types in SMT |
| Z3 Uninterpreted Functions | 4.13.4+ | Open-world trait encoding | Project standard (already integrated) |
| Rust MIR Semantics | rustc 1.85+ | Trait resolution and vtables | Canonical Rust representation |
| Liskov Substitution Principle | 1987/1994 | Behavioral subtyping foundation | Theoretical soundness guarantee |

### Supporting

| Library | Version | Purpose | When to Use |
|---------|---------|---------|-------------|
| Existing IR (`crates/analysis/src/ir.rs`) | Current | Add `Ty::TraitObject`, `TraitDef` | Core representation |
| Existing `ContractDatabase` | Current | Trait-level contract storage | Cross-crate verification |
| Existing SMT encoding | Current | Behavioral subtyping VCs | Already proven in Phases 1-7 |
| Existing call graph | Current | Detect sealed trait usage | Closed-world analysis |

### Alternatives Considered

| Instead of | Could Use | Tradeoff |
|------------|-----------|----------|
| Trait-level contracts | Per-impl contracts only | Unsound - dynamic dispatch needs trait-level specification to avoid runtime type inspection |
| Behavioral subtyping VCs | Trust all impls | Unsound - impl could violate trait contract, breaking dyn Trait callers |
| Open-world uninterpreted functions | Always enumerate impls | Incomplete - public traits can have external impls unknown at verification time |
| Sealed trait detection | Manual annotation only | Error-prone - compiler knows trait is sealed via `pub(crate)` or private super-trait |

**Installation:**
No new dependencies - builds on existing workspace crates.

## Architecture Patterns

### Recommended Project Structure

Extend existing analysis crate structure:

```
crates/analysis/src/
├── ir.rs                  # Add Ty::TraitObject, TraitDef, TraitImpl
├── trait_analysis.rs      # NEW: Detect sealed traits, collect impls
├── behavioral_subtyping.rs # NEW: Generate trait contract refinement VCs
├── vcgen.rs               # Extend: Handle dyn Trait method calls
├── encode_sort.rs         # Extend: Sealed trait → SMT sum type
├── encode_term.rs         # Extend: Trait object method call encoding
└── spec_parser.rs         # Extend: Parse trait-level contracts
```

### Pattern 1: Trait Definition with Contracts

**What:** Trait methods annotated with `#[requires]`/`#[ensures]` specify behavioral contract that all implementations must satisfy.

**When to use:** Every trait with formal verification requirements (mandatory for traits used as trait objects).

**Example:**

```rust
// Rust code:
trait Stack {
    #[requires(self.len() < self.capacity())]
    #[ensures(self.len() == old(self.len()) + 1)]
    #[ensures(self.peek() == Some(value))]
    fn push(&mut self, value: i32);

    #[requires(self.len() > 0)]
    #[ensures(result.is_some())]
    fn pop(&mut self) -> Option<i32>;
}

// IR representation (new):
TraitDef {
    name: "Stack",
    methods: vec![
        TraitMethod {
            name: "push",
            params: vec![("self", Ty::Ref(Box::new(Ty::Generic("Self")), Mutable)), ("value", Ty::Int(I32))],
            return_ty: Ty::Unit,
            requires: vec![parse_spec("self.len() < self.capacity()")],
            ensures: vec![
                parse_spec("self.len() == old(self.len()) + 1"),
                parse_spec("self.peek() == Some(value)"),
            ],
        },
        TraitMethod {
            name: "pop",
            params: vec![("self", Ty::Ref(Box::new(Ty::Generic("Self")), Mutable))],
            return_ty: Ty::Option(Box::new(Ty::Int(I32))),
            requires: vec![parse_spec("self.len() > 0")],
            ensures: vec![parse_spec("result.is_some()")],
        },
    ],
    is_sealed: false,  // Public trait - open-world
}
```

**Source:** [Behavioral Subtyping, Specification Inheritance (Liskov & Wing 1994)](https://www.cs.cmu.edu/~wing/publications/LiskovWing94.pdf) - trait specifications define behavioral contract all implementations must satisfy.

### Pattern 2: Behavioral Subtyping Verification

**What:** For each `impl Trait for Type`, verify that impl method contracts refine trait method contracts (LSP compliance).

**When to use:** Every trait implementation in verified code.

**Example:**

```rust
// Rust code:
impl Stack for VecStack {
    fn push(&mut self, value: i32) {
        self.items.push(value);
    }
    // ... other methods
}

// Verification condition generated:
// For Stack::push impl:
// 1. Precondition weakening: trait_requires => impl_requires
//    (impl can accept MORE inputs than trait requires)
// 2. Postcondition strengthening: impl_ensures => trait_ensures
//    (impl must GUARANTEE AT LEAST what trait promises)

// SMT encoding (conceptual):
(assert (forall ((self VecStack) (value (_ BitVec 32)))
  (=>
    ; Trait precondition
    (< (len self) (capacity self))
    ; Impl precondition (if any)
    true  ; VecStack::push has no additional preconditions
  )))

(assert (forall ((self VecStack) (value (_ BitVec 32)))
  (=>
    ; Impl postcondition proven by impl verification
    (and (= (len self_after) (+ (len self_before) 1))
         (= (peek self_after) (Some value)))
    ; Trait postcondition (must be entailed)
    (and (= (len self_after) (+ (len self_before) 1))
         (= (peek self_after) (Some value)))
  )))
```

**Source:** [Behavioral Subtyping (ACM TOPLAS 2015)](https://dl.acm.org/doi/10.1145/2766446) - behavioral subtyping requires precondition weakening and postcondition strengthening.

### Pattern 3: Dynamic Dispatch Encoding (Open-World)

**What:** For public traits, encode trait object method calls using trait-level contracts with uninterpreted functions.

**When to use:** `dyn Trait` call sites where trait is public (not sealed).

**Example:**

```rust
// Rust code:
fn process(stack: &mut dyn Stack) {
    stack.push(42);
    let val = stack.pop();
}

// SMT encoding (conceptual):
; Declare uninterpreted function for trait method
(declare-fun Stack_push (TraitObjectPtr (_ BitVec 32)) Unit)

; Axiom: trait-level contract (from trait definition)
(assert (forall ((obj TraitObjectPtr) (value (_ BitVec 32)))
  (=>
    ; Precondition
    (< (Stack_len obj) (Stack_capacity obj))
    ; Postcondition
    (and (= (Stack_len (Stack_push obj value))
            (+ (Stack_len obj) 1))
         (= (Stack_peek (Stack_push obj value))
            (Some value))))))

; Verification of process function:
(assert (< (Stack_len stack) (Stack_capacity stack)))  ; precondition check
(define-const stack_after TraitObjectPtr (Stack_push stack 42))
; Can assume postcondition holds (from axiom):
(assert (= (Stack_len stack_after) (+ (Stack_len stack) 1)))
```

**Source:** [Kani Rust Verifier ICSE 2022](https://cs.wellesley.edu/~avh/dyn-trait-icse-seip-2022-preprint.pdf) - function pointer restriction for trait objects, using trait-level specifications.

### Pattern 4: Sealed Trait Encoding (Closed-World)

**What:** For sealed traits (pub(crate) or private super-trait), enumerate all known implementations as SMT sum type.

**When to use:** Trait is provably sealed (all impls known within current crate).

**Example:**

```rust
// Rust code:
pub trait SealedStack: private::Sealed {
    // ... methods with contracts
}

mod private {
    pub trait Sealed {}
}

impl private::Sealed for VecStack {}
impl SealedStack for VecStack { /* ... */ }

impl private::Sealed for ArrayStack {}
impl SealedStack for ArrayStack { /* ... */ }

// SMT encoding (conceptual):
; Sum type over all known implementations
(declare-datatype SealedStack
  ((SealedStack_VecStack (as-VecStack VecStack))
   (SealedStack_ArrayStack (as-ArrayStack ArrayStack))))

; Dynamic dispatch becomes pattern match:
(define-fun SealedStack_push
  ((obj SealedStack) (value (_ BitVec 32))) SealedStack
  (match obj
    ((SealedStack_VecStack vs)
      (SealedStack_VecStack (VecStack_push vs value)))
    ((SealedStack_ArrayStack as)
      (SealedStack_ArrayStack (ArrayStack_push as value)))))

; All implementations verified individually via behavioral subtyping VCs
; Therefore sum type dispatch is sound
```

**Source:** [Z3 Algebraic Datatypes](https://microsoft.github.io/z3guide/docs/theories/Datatypes/) - exhaustive pattern matching over finite known implementations.

### Pattern 5: Trait Object Type Representation

**What:** Introduce `Ty::TraitObject` to represent `dyn Trait` types in IR.

**When to use:** Any occurrence of `Box<dyn Trait>`, `&dyn Trait`, `&mut dyn Trait`.

**Example:**

```rust
// Rust code:
fn accepts_trait_object(stack: Box<dyn Stack>) { /* ... */ }

// IR representation:
Ty::TraitObject {
    trait_name: "Stack",
    // Trait bounds (for trait inheritance, e.g., `dyn Trait + Send`)
    bounds: vec!["Stack"],
    // Wrapper type (Box, Ref, etc.)
    container: TraitObjectContainer::Box,
}

// Alternative for references:
Ty::TraitObject {
    trait_name: "Stack",
    bounds: vec!["Stack"],
    container: TraitObjectContainer::Ref(Mutability::Mutable),
}
```

### Anti-Patterns to Avoid

- **Per-impl verification only:** UNSOUND - dynamic dispatch means caller doesn't know concrete type, so trait-level contract is the only sound specification for `dyn Trait` calls.

- **Mixing impl-specific and trait-level contracts at call sites:** UNSOUND - trait object calls MUST use trait-level contracts; using impl-specific contract requires runtime type inspection (contradicts abstraction).

- **Open-world enumeration:** INCOMPLETE - public traits can have implementations in downstream crates unknown at verification time; must use uninterpreted functions.

- **Closed-world for public traits:** UNSOUND - assumes no external implementations exist; wrong for public traits.

- **Skipping behavioral subtyping VCs:** UNSOUND - impl could violate trait contract; verifying impl in isolation doesn't prove it satisfies trait specification.

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Detecting sealed traits | Manual `#[sealed]` parsing only | Rust visibility + super-trait analysis | Rust already makes traits sealed via `pub(crate)` or private super-traits; compiler knows this |
| Trait contract inheritance | Copy-paste trait contracts to every impl | Behavioral subtyping VCs | Maintains single source of truth; detects contract violations automatically |
| Dynamic dispatch encoding | Custom vtable simulation | Uninterpreted functions (open) / Sum types (closed) | Standard formal methods; proven sound; avoids reimplementing vtable semantics |
| LSP verification | Manual contract comparison | Automated VC generation | Precondition weakening + postcondition strengthening are mechanical; tool should enforce |
| Type-based dispatch | Runtime type checks in SMT | Static type system + behavioral subtyping | Rust's type system already prevents type confusion; trust it |

**Key insight:** Trait verification is well-studied (Liskov 1987, Dafny 2015, Kani 2022). The hard parts (behavioral subtyping, closed/open-world, vtable soundness) have established solutions. Don't reinvent - adapt proven patterns to rust-fv's IR and SMT encoding.

## Common Pitfalls

### Pitfall 1: Forgetting Behavioral Subtyping for Sealed Traits

**What goes wrong:** Developer assumes sealed trait enumeration is sufficient - verifies each impl independently, but doesn't verify impls satisfy trait contracts. Later, trait object call assumes trait-level postcondition that an impl doesn't actually provide.

**Why it happens:** Conflating "closed-world enumeration" with "automatic contract satisfaction." Enumeration means you know all impls; behavioral subtyping means each impl refines the trait contract.

**How to avoid:** ALWAYS generate behavioral subtyping VCs for every `impl Trait`, regardless of whether trait is sealed. Sealed vs. public only affects call site encoding (sum types vs. uninterpreted functions), not impl verification.

**Warning signs:**
- Verification passes for individual impls
- Verification passes for `dyn Trait` call site
- But adding a new impl breaks existing `dyn Trait` calls

### Pitfall 2: Open-World Enumeration Incompleteness

**What goes wrong:** Tool attempts to enumerate all implementations of a public trait, generates sum type encoding. Downstream crate adds new impl; verification of original crate is now unsound because sum type was incomplete.

**Why it happens:** Confusing "I can see all impls in this crate" with "these are all possible impls." Public traits can be implemented by external code.

**How to avoid:** Detect trait visibility: if trait is `pub` (and not sealed via private super-trait or `pub(crate)`), use uninterpreted function encoding. Never enumerate impls for public traits.

**Warning signs:**
- Tool performs whole-program analysis on a library crate
- Sum type for public trait
- Error message "unknown implementation" when verifying downstream code

### Pitfall 3: Precondition Strengthening in Impls

**What goes wrong:** Trait method has precondition `requires(x > 0)`. Impl adds stricter precondition `requires(x > 10)`. Behavioral subtyping VC fails, but developer thinks "stricter is safer."

**Why it happens:** Misunderstanding LSP. Impl must accept AT LEAST what trait accepts (weaker precondition), not less.

**How to avoid:** Remember the caller perspective - caller only sees trait contract. If trait says "any x > 0 is valid," caller can pass x=5. Impl must handle x=5, so impl precondition CANNOT be stricter.

**Correct rule:** Impl preconditions must be WEAKER (or equal) to trait preconditions.

**Warning signs:**
- Behavioral subtyping VC fails on precondition check
- Error message: "impl precondition stronger than trait precondition"
- Developer adds precondition to trait instead of relaxing impl precondition

### Pitfall 4: Vtable Encoding Without Trait Contracts

**What goes wrong:** Tool encodes `dyn Trait` method calls as uninterpreted functions, but doesn't add axioms from trait-level contracts. Verifier can't prove anything about trait object calls.

**Why it happens:** Forgetting that uninterpreted functions are completely abstract - SMT solver knows NOTHING except function signature unless axioms are provided.

**How to avoid:** For every `dyn Trait` method call, add trait-level contract as SMT axiom linking the uninterpreted function to its specification.

**Warning signs:**
- Verification fails at `dyn Trait` call site with "cannot prove postcondition"
- Generated SMT contains `(declare-fun Trait_method ...)` but no corresponding `(assert (forall ...))` axioms
- Same code verifies with concrete type but fails with trait object

### Pitfall 5: Missing Trait Method in Impl

**What goes wrong:** Trait has method `foo`. Impl provides `bar` but not `foo`. Rust compiler catches this, but verifier runs on potentially incomplete MIR during development.

**Why it happens:** Verification runs on partial/broken code during development.

**How to avoid:** Before generating behavioral subtyping VCs, check that impl provides all trait methods. If missing, emit clear diagnostic rather than silently assuming default impl.

**Warning signs:**
- Verification fails with cryptic "cannot find method" error
- Trait requires method with contract
- Impl appears to verify without implementing the method

## Code Examples

Verified patterns from standard formal methods:

### Example 1: Trait Definition with Contracts

```rust
// Source: Adapted from Dafny trait patterns
trait Stack {
    #[pure]
    fn len(&self) -> usize;

    #[pure]
    fn capacity(&self) -> usize;

    #[requires(self.len() < self.capacity())]
    #[ensures(self.len() == old(self.len()) + 1)]
    fn push(&mut self, value: i32);

    #[requires(self.len() > 0)]
    #[ensures(old(self.len()) == self.len() + 1)]
    #[ensures(result.is_some())]
    fn pop(&mut self) -> Option<i32>;
}
```

### Example 2: Behavioral Subtyping Verification

```rust
// Source: Liskov Substitution Principle application
impl Stack for VecStack {
    // IMPLICIT BEHAVIORAL SUBTYPING VC:
    //   VecStack::push precondition => Stack::push precondition ✓
    //   VecStack::push postcondition => Stack::push postcondition ✓

    fn push(&mut self, value: i32) {
        // Impl-specific precondition (optional, must be weaker):
        // None - accepts all inputs trait accepts

        self.items.push(value);

        // Impl-specific postcondition (must imply trait postcondition):
        // Proven: self.len() == old(self.len()) + 1 ✓
    }
}
```

### Example 3: Dynamic Dispatch (Open-World)

```rust
// Source: Kani vtable verification patterns
fn process_stack(stack: &mut dyn Stack) {
    // Precondition check: use trait-level contract
    // VERIFY: stack.len() < stack.capacity()
    stack.push(42);

    // Postcondition assumption: use trait-level contract
    // ASSUME: stack.len() == old(stack.len()) + 1

    // Another call with trait-level contract
    if stack.len() > 0 {
        let val = stack.pop();
        // ASSUME: val.is_some() (from trait postcondition)
    }
}
```

### Example 4: Sealed Trait Enumeration

```rust
// Source: Adapted from Z3 algebraic datatype patterns
mod sealed {
    pub trait Sealed {}
}

pub trait CompressionAlgorithm: sealed::Sealed {
    #[requires(data.len() > 0)]
    #[ensures(result.len() <= data.len())]
    fn compress(&self, data: &[u8]) -> Vec<u8>;
}

impl sealed::Sealed for Gzip {}
impl CompressionAlgorithm for Gzip { /* ... */ }

impl sealed::Sealed for Lz4 {}
impl CompressionAlgorithm for Lz4 { /* ... */ }

// CLOSED-WORLD ENCODING (only 2 impls possible):
// (declare-datatype CompressionAlgorithm
//   ((CA_Gzip (as-Gzip Gzip))
//    (CA_Lz4 (as-Lz4 Lz4))))

fn compress_file(algo: &dyn CompressionAlgorithm, data: &[u8]) -> Vec<u8> {
    // VERIFY: data.len() > 0 (trait precondition)
    let result = algo.compress(data);
    // ASSUME: result.len() <= data.len() (trait postcondition)
    result
}
```

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| Manual trait contract checking | Behavioral subtyping VCs | Liskov & Wing 1994 | Formal foundation for LSP |
| Whole-program vtable analysis | Modular trait-level contracts | Dafny traits 2015 | Scalable verification |
| Rust object safety (pre-2024) | Dyn compatibility | Rust 1.80+ (2024) | Terminology aligned with semantic meaning |
| Kani function pointer restriction (2022) | Trait-level contract axioms | Standard practice (2023+) | More precise than unrestricted pointer analysis |

**Current state (2026):**
- **Verus:** Uses `external_trait_specification` for trait contracts, view traits for abstraction
- **Prusti:** Supports trait specifications via Viper encoding
- **Kani:** Function pointer restriction for vtables (ICSE 2022)
- **Dafny:** Native trait support with behavioral subtyping (since 2015)

**Deprecated/outdated:**
- "Object safety" terminology (now "dyn compatibility" in Rust 1.80+)
- Z3 `define-fun-rec` for trait methods (axiom-based encoding more flexible)
- Whole-program vtable enumeration for public traits (unsound)

## Open Questions

1. **Trait object upcast verification**
   - What we know: Rust allows casting `&dyn SubTrait` to `&dyn SuperTrait`
   - What's unclear: How to verify upcasts preserve contracts (sub-trait contract must imply super-trait contract)
   - Recommendation: Treat as special case of behavioral subtyping - generate VC that SubTrait::method contract refines SuperTrait::method contract. LOW priority (rare in practice).

2. **Associated types in trait objects**
   - What we know: Trait objects can have associated types (e.g., `dyn Iterator<Item = i32>`)
   - What's unclear: How to encode associated type constraints in SMT (type equality constraints)
   - Recommendation: Extend `Ty::TraitObject` with associated type bindings, encode as SMT axioms. MEDIUM priority (common pattern).

3. **Multi-trait objects (Trait + Trait)**
   - What we know: Rust supports `dyn Trait1 + Trait2 + Send`
   - What's unclear: How to verify method call when contract comes from composition of multiple traits
   - Recommendation: Encode as intersection of contract sets - must satisfy ALL trait contracts. MEDIUM priority (common for `+ Send` bounds).

4. **Performance of behavioral subtyping VCs**
   - What we know: Each impl generates N VCs (one per trait method)
   - What's unclear: Will this scale for traits with many methods or many implementations?
   - Recommendation: Measure in Phase 8 implementation. If slow, explore caching or incremental verification. LOW confidence prediction.

5. **Auto-traits (Send, Sync) in specifications**
   - What we know: Auto-traits affect trait object validity (`dyn Trait + Send`)
   - What's unclear: Do we need to verify auto-trait bounds in contracts?
   - Recommendation: Trust Rust's type system for auto-traits - they're marker traits with no methods. No verification needed. HIGH confidence.

## Sources

### Primary (HIGH confidence)

- [Kani Rust Verifier ICSE 2022 Paper](https://cs.wellesley.edu/~avh/dyn-trait-icse-seip-2022-preprint.pdf) - Vtable verification, function pointer restriction, dynamic trait objects
- [Liskov & Wing 1994: Behavioral Subtyping](https://www.cs.cmu.edu/~wing/publications/LiskovWing94.pdf) - Theoretical foundation for trait contract refinement
- [Rust Reference: Trait Objects](https://doc.rust-lang.org/reference/types/trait-object.html) - Official specification of trait object semantics
- [Rust Reference: Dyn Compatibility](https://doc.rust-lang.org/reference/items/traits.html) - Object safety rules
- [Z3 Guide: Algebraic Datatypes](https://microsoft.github.io/z3guide/docs/theories/Datatypes/) - Sum type encoding for sealed traits
- [Z3 Guide: Uninterpreted Functions](https://microsoft.github.io/z3guide/docs/logic/Uninterpreted-functions-and-constants/) - Open-world trait encoding

### Secondary (MEDIUM confidence)

- [Behavioral Subtyping ACM TOPLAS 2015](https://dl.acm.org/doi/10.1145/2766446) - Formal verification of behavioral subtyping
- [Dafny Trait Verification (Microsoft Research)](https://www.microsoft.com/en-us/research/publication/automatic-verification-dafny-programs-traits/) - Trait specification patterns
- [Verus Documentation](https://verus-lang.github.io/event-sites/2024-sosp/) - Rust verifier trait handling
- [Rust Compiler Dev Guide: Monomorphization](https://rustc-dev-guide.rust-lang.org/backend/monomorph.html) - How rustc handles static vs dynamic dispatch
- [Sealed Trait Pattern Guide](https://predr.ag/blog/definitive-guide-to-sealed-traits-in-rust/) - Detecting sealed traits in Rust

### Tertiary (LOW confidence - needs validation)

- [Open-World Logic Programs (Microsoft Research)](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/MSR-TR-2013-55.pdf) - Open-world assumption formalization
- [SMT-LIB Enumeration Types Discussion](https://cs.nyu.edu/pipermail/smt-lib/2011/000512.html) - Encoding enumerations in SMT (dated 2011, may be outdated)

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH - All existing infrastructure, well-established theory (LSP 1987)
- Architecture: HIGH - Follows Phases 6-7 patterns, adapts Kani 2022 approach
- Pitfalls: MEDIUM-HIGH - Based on LSP common errors and Rust-specific trait semantics
- Code examples: HIGH - Adapted from Liskov & Wing, Dafny, and Kani research

**Research date:** 2026-02-12
**Valid until:** ~90 days (stable domain - trait verification is well-established)

**Research notes:**
- Trait verification is mature field (30+ years since Liskov)
- Rust-specific challenges well-documented (Kani 2022)
- Main unknowns are implementation details (performance, diagnostics), not fundamental approach
- Phase 8 should be straightforward extension of existing patterns
