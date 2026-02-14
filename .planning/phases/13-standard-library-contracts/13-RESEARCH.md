# Phase 13: Standard Library Contracts - Research

**Researched:** 2026-02-14
**Domain:** Formal verification of Rust standard library types
**Confidence:** HIGH

## Summary

Standard library contracts for formal verification tools follow a well-established external crate pattern (Prusti/Verus model) with auto-loading mechanisms. The core technical challenge is balancing specification precision with completeness while avoiding unsoundness. SMT solvers (Z3, CVC5) provide sequence theories for modeling collections, though practical verification requires hybrid approaches combining array and sequence encodings. Property-based testing (proptest) serves as an oracle to validate contract soundness by comparing real stdlib operations against postconditions.

Critical lessons from the verify-rust-std effort: (1) internal safety properties cannot be checked as postconditions due to UB timing, (2) generic type verification requires concrete instantiation creating coverage gaps, (3) 67% of unsafe stdlib code is trivially safe, and (4) no bugs found despite extensive effort suggests methodology emphasizes proof over bug-finding.

**Primary recommendation:** Use external crate pattern with auto-load + opt-out, SMT sequence theory for collections (array theory fallback for indexing), proptest for oracle testing, and conservative specification strategy focusing on provable properties over completeness.

<user_constraints>
## User Constraints (from CONTEXT.md)

### Locked Decisions

**Contract scope & depth:**
- Vec<T>: Track both length AND capacity in contracts (reserve, shrink_to_fit modeled)
- Element-level contracts where safe and precise: vec.push(x) ensures vec[len-1] == x, vec.get(i) returns the i-th element
- HashMap<K,V>: Full mathematical map abstraction — insert(k,v) ensures get(k)==Some(v), remove(k) ensures get(k)==None
- Option<T> and Result<T,E>: Full behavioral contracts on unwrap, map, is_some, ok_or, etc.
- Tier 1 types: Vec, Option, Result, HashMap, Iterator, String, &str, and slice operations

**Contract packaging:**
- External crate pattern (Prusti/Verus model) — separate `rust-fv-contracts` crate
- Auto-load with opt-out: contracts loaded by default, `--no-stdlib-contracts` flag to disable
- Versioning: Claude's discretion on how to handle Rust edition/version differences, biased toward safety and precision
- Property-based oracle testing required: tests run real stdlib ops and compare against contract postconditions to catch unsound contracts

**Override mechanism:**
- Syntax: `#[override_contract]` attribute on extern function declarations
- Info-level notice when override is active: "Using custom contract for Vec::push (overriding stdlib)"
- Two modes: `#[override_contract]` for full replacement, `#[extend_contract]` for additive conditions on top of stdlib
- Basic soundness validation on user overrides (e.g., postcondition not contradicting precondition)

**Iterator contracts:**
- Model iterator chains as abstract sequence operations (mathematical sequence transformations in SMT)
- End-to-end chain verification: properties compose through map/filter/collect chains
- Infinite/lazy iterators: Claude's discretion, biased toward safety and precision
- Tier 1 adaptors: map, filter, collect, next, count, fold, any, all, zip, enumerate, take

### Claude's Discretion

- Exact SMT encoding strategy for sequence operations
- How to handle Rust version differences in stdlib API surface (lean toward safety/precision)
- Infinite/lazy iterator handling approach (lean toward safety/precision)
- Element-level contract depth calibration (lean toward safety/precision)
- Loading mechanism internals for external contract crate
- Oracle test framework choice

### Deferred Ideas (OUT OF SCOPE)

None — discussion stayed within phase scope

</user_constraints>

## Standard Stack

### Core

| Library | Version | Purpose | Why Standard |
|---------|---------|---------|--------------|
| proptest | 1.6+ | Property-based testing for oracle validation | Industry standard for Rust PBT, flexible strategy system, shrinking support, used by major projects |
| rustc_driver | nightly | Compiler integration for contract loading | Official rustc API for custom compiler passes, used by Clippy, Prusti, other verification tools |
| serde | 1.0+ | Contract serialization/metadata | De facto Rust serialization standard, zero-copy deserialization, derive macro support |

### Supporting

| Library | Version | Purpose | When to Use |
|---------|---------|---------|-------------|
| proc-macro2 | 1.0+ | Macro helpers for contract attributes | When implementing `#[override_contract]` and `#[extend_contract]` attributes |
| quote | 1.0+ | AST code generation | When generating contract validation code from attribute macros |
| syn | 2.0+ | Rust syntax parsing | When parsing contract attribute syntax and function signatures |
| arbitrary | 1.4+ | Trait for property test generation | When extending proptest strategies for custom contract types |

### Alternatives Considered

| Instead of | Could Use | Tradeoff |
|------------|-----------|----------|
| proptest | quickcheck | quickcheck is simpler but less flexible; proptest's per-value strategies enable more precise oracle tests |
| rustc_driver | cargo plugin | cargo plugins can't access compiler internals needed for contract integration; limited to build-time checks |
| serde | bincode | bincode is faster but not human-readable; contract metadata benefits from JSON/TOML for debugging |

**Installation:**
```bash
# For rust-fv-contracts crate
cargo add serde --features derive
cargo add --dev proptest
cargo add --dev arbitrary

# For build/integration
# rustc_driver, proc-macro2, quote, syn added as dependencies in Cargo.toml
```

## Architecture Patterns

### Recommended Project Structure
```
rust-fv-contracts/
├── src/
│   ├── lib.rs              # Public API, auto-loader
│   ├── prelude.rs          # Common contract imports
│   ├── collections/        # Vec, HashMap, etc.
│   │   ├── mod.rs
│   │   ├── vec.rs          # Vec<T> contracts
│   │   ├── hash_map.rs     # HashMap<K,V> contracts
│   │   └── slice.rs        # slice operations
│   ├── option.rs           # Option<T> contracts
│   ├── result.rs           # Result<T,E> contracts
│   ├── iterator/           # Iterator contracts
│   │   ├── mod.rs
│   │   ├── adaptors.rs     # map, filter, etc.
│   │   └── traits.rs       # Iterator trait contracts
│   ├── string/             # String, &str contracts
│   │   ├── mod.rs
│   │   ├── string.rs
│   │   └── str.rs
│   ├── smt/                # SMT encoding utilities
│   │   ├── sequences.rs    # Sequence theory helpers
│   │   ├── arrays.rs       # Array theory fallback
│   │   └── maps.rs         # Map abstraction
│   └── attributes/         # Override mechanism
│       ├── override.rs     # #[override_contract]
│       └── extend.rs       # #[extend_contract]
├── tests/
│   ├── oracle/             # Proptest oracle tests
│   │   ├── vec_oracle.rs
│   │   ├── hashmap_oracle.rs
│   │   └── iterator_oracle.rs
│   └── integration/        # End-to-end tests
└── examples/               # Usage examples
```

### Pattern 1: External Specification with Auto-Loading

**What:** Contracts defined separately from stdlib implementation, loaded automatically at verification time

**When to use:** For all stdlib contracts to enable versioning independence and opt-out capability

**Example:**
```rust
// In rust-fv-contracts/src/collections/vec.rs
use prusti_contracts::*;

#[extern_spec]
impl<T> Vec<T> {
    #[requires(self.len() < self.capacity())]
    #[ensures(self.len() == old(self.len()) + 1)]
    #[ensures(self[old(self.len())] == value)]
    fn push(&mut self, value: T);

    #[ensures(result.is_some() ==> result.unwrap() == old(self[self.len() - 1]))]
    #[ensures(result.is_some() ==> self.len() == old(self.len()) - 1)]
    #[ensures(result.is_none() ==> self.len() == 0)]
    fn pop(&mut self) -> Option<T>;

    #[pure]
    #[ensures(result == self.capacity >= self.len)]
    fn len(&self) -> usize;
}

// Auto-loaded via lib.rs unless --no-stdlib-contracts flag present
```

**Source:** [Prusti External Specifications](https://viperproject.github.io/prusti-dev/user-guide/verify/external.html)

### Pattern 2: Mathematical Map Abstraction for Collections

**What:** Model HashMap as pure mathematical map (functional abstraction) rather than imperative data structure

**When to use:** For HashMap and other associative containers to enable functional correctness proofs

**Example:**
```rust
// Abstract map model using SMT sequences/arrays
#[extern_spec]
impl<K, V> HashMap<K, V> {
    // Model as mathematical function: K -> Option<V>
    #[ensures(forall(|k: &K| k == key ==> self.model().lookup(k) == Some(value)))]
    #[ensures(forall(|k: &K| k != key ==> self.model().lookup(k) == old(self.model().lookup(k))))]
    fn insert(&mut self, key: K, value: V) -> Option<V>;

    #[pure]
    #[ensures(result == self.model().lookup(key))]
    fn get(&self, key: &K) -> Option<&V>;

    #[ensures(forall(|k: &K| k == key ==> self.model().lookup(k) == None))]
    #[ensures(forall(|k: &K| k != key ==> self.model().lookup(k) == old(self.model().lookup(k))))]
    fn remove(&mut self, key: &K) -> Option<V>;
}
```

**Source:** User requirement for "full mathematical map abstraction" from CONTEXT.md, inspired by Verus's view pattern

### Pattern 3: Iterator Chain Composition via Sequence Theory

**What:** Model iterator chains as mathematical sequence transformations that compose

**When to use:** For verifying properties across map/filter/collect chains

**Example:**
```rust
// Conceptual model - actual SMT encoding internal
#[extern_spec]
impl<I: Iterator> Iterator for I {
    // Base sequence model
    #[pure]
    fn seq_model(&self) -> Seq<Self::Item>;
}

// Map preserves length
#[extern_spec]
impl<I, F, B> Iterator for Map<I, F>
where
    I: Iterator,
    F: FnMut(I::Item) -> B,
{
    #[ensures(result.seq_model().len() == self.inner.seq_model().len())]
    #[ensures(forall(|i: usize| i < result.seq_model().len() ==>
              result.seq_model()[i] == (self.f)(self.inner.seq_model()[i])))]
    fn seq_model(&self) -> Seq<B>;
}

// Filter reduces/preserves length
#[extern_spec]
impl<I, P> Iterator for Filter<I, P>
where
    I: Iterator,
    P: FnMut(&I::Item) -> bool,
{
    #[ensures(result.seq_model().len() <= self.inner.seq_model().len())]
    #[ensures(forall(|i: usize| i < result.seq_model().len() ==>
              (self.predicate)(&result.seq_model()[i])))]
    fn seq_model(&self) -> Seq<I::Item>;
}
```

**Source:** [CVC5 Sequence Theory](https://cvc5.github.io/2024/02/15/sequences-theory.html), compositional reasoning patterns from iterator verification research

### Pattern 4: Oracle Testing with Proptest

**What:** Validate contract soundness by generating random inputs, running real stdlib ops, checking postconditions hold

**When to use:** Mandatory for all stdlib contracts to detect unsound specifications

**Example:**
```rust
// In tests/oracle/vec_oracle.rs
use proptest::prelude::*;

proptest! {
    #[test]
    fn vec_push_oracle(
        mut vec in vec(any::<i32>(), 0..100),
        value in any::<i32>()
    ) {
        let old_len = vec.len();
        let old_cap = vec.capacity();

        // Run real stdlib operation
        vec.push(value);

        // Validate postconditions from contract
        prop_assert_eq!(vec.len(), old_len + 1);
        prop_assert_eq!(vec[old_len], value);
        prop_assert!(vec.capacity() >= old_cap);
    }

    #[test]
    fn hashmap_insert_oracle(
        mut map in hash_map(any::<String>(), any::<i32>(), 0..50),
        key in any::<String>(),
        value in any::<i32>()
    ) {
        // Capture old state
        let old_contains = map.contains_key(&key);

        // Run real operation
        map.insert(key.clone(), value);

        // Validate mathematical map abstraction postconditions
        prop_assert_eq!(map.get(&key), Some(&value));
        // Other keys unchanged would require more complex oracle
    }
}
```

**Source:** [Proptest Oracle Testing Pattern](https://lib.rs/crates/proptest), user requirement for "property-based oracle testing"

### Pattern 5: Contract Override Mechanism

**What:** Allow users to replace or extend stdlib contracts with custom specifications

**When to use:** When stdlib contracts are too weak (missing needed properties) or too strong (unprovable for specific use case)

**Example:**
```rust
// Full replacement
#[override_contract]
extern "Rust" {
    // Weaker contract for specific domain where capacity doesn't matter
    #[requires(true)]  // No capacity check
    #[ensures(self.len() == old(self.len()) + 1)]
    fn vec_push<T>(vec: &mut Vec<T>, value: T);
}

// Additive extension
#[extend_contract]
extern "Rust" {
    // Add domain-specific invariant on top of stdlib contract
    #[ensures(self.iter().all(|x| *x >= 0))]  // Additional: all elements non-negative
    fn vec_push_positive(vec: &mut Vec<i32>, value: i32);
}

// Validation: tool checks new postcondition doesn't contradict precondition
// Emits: "Using custom contract for Vec::push (overriding stdlib)"
```

**Source:** User requirement from CONTEXT.md, Prusti trusted external specs pattern

### Anti-Patterns to Avoid

- **Postconditions on UB-triggering operations:** Don't check alignment/validity as postconditions - UB occurs before postcondition evaluation. Use inline assertions or preconditions instead.
  - **Source:** [Lessons Learned from Rust Stdlib Verification](https://arxiv.org/html/2510.01072v1) - "by the time the postcondition is evaluated, there might already be undefined behaviour"

- **Over-specified contracts:** Don't add unprovable details that aren't needed for client verification. 67% of unsafe stdlib code is trivially safe - contracts should reflect actual complexity.
  - **Source:** [Lessons Learned from Rust Stdlib Verification](https://arxiv.org/html/2510.01072v1)

- **Concrete-type only verification:** Verifying only `Vec<i32>` leaves `Vec<String>` uncovered due to monomorphization. Use bounded quantification or multiple instantiations.
  - **Source:** [Lessons Learned from Rust Stdlib Verification](https://arxiv.org/html/2510.01072v1)

- **Reimplementing stdlib in tests:** Oracle tests should use real stdlib ops, not reimplementations. Test contract against reality, not against another model.
  - **Source:** [Proptest round-trip pattern](https://lib.rs/crates/proptest)

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Property-based test generation | Custom random input generators | proptest with Arbitrary trait | Shrinking is complex (minimal failing case), composition is subtle, distribution quality matters for finding edge cases |
| SMT sequence encoding | Manual SMT-LIB AST construction | Z3/CVC5 sequence theory APIs | Hybrid string-array approach required for performance, quantifier handling non-trivial, solver-specific optimizations critical |
| Compiler integration | Cargo plugin | rustc_driver with Callbacks trait | Need access to MIR/HIR for contract analysis, cargo plugins limited to build scripts, clippy/prusti pattern proven |
| Rust syntax parsing | Regex or hand-written parser | syn crate | Rust syntax complex and evolving, syn maintained by dtolnay (serde author), handles macro expansion edge cases |
| Contract serialization | Custom binary format | serde with JSON/TOML | Human-readable debugging essential, versioning/migration support, ecosystem tooling (schema validation) |

**Key insight:** Formal verification infrastructure requires SMT solver expertise (hybrid sequence-array encodings), mature PBT frameworks (shrinking algorithms), and compiler internals knowledge (MIR transformations). Each has 5-10 years of research/engineering investment - building custom solutions introduces unsoundness risks and maintenance burden.

## Common Pitfalls

### Pitfall 1: Postcondition Timing with Undefined Behavior

**What goes wrong:** Contract postconditions checked after function execution fail to catch UB that occurs during execution (e.g., creating misaligned reference triggers UB before postcondition runs)

**Why it happens:** Verification assumes execution completes to evaluate postconditions, but UB can terminate execution earlier or invalidate assumptions

**How to avoid:**
- Use preconditions to prevent UB-triggering inputs
- Use inline assertions/assumes during execution for internal invariants
- Reserve postconditions for observable state after safe execution

**Warning signs:**
- Contracts on transmute/raw pointer operations with alignment/validity checks as postconditions
- Functions marked unsafe but no preconditions guarding UB triggers

**Source:** [Lessons Learned from Rust Stdlib Verification](https://arxiv.org/html/2510.01072v1) - section on "Internal Safety Properties"

### Pitfall 2: Generic Type Coverage Gap

**What goes wrong:** Verifying `fn process<T>` with concrete instantiation `T=i32` leaves other instantiations uncovered; monomorphization means each concrete type is separate compiled function

**Why it happens:** Rust monomorphizes generics at compile time; verifiers work on MIR which is per-monomorphization; no single proof covers all instantiations

**How to avoid:**
- Use bounded quantification when possible: `forall T: Trait`
- Verify multiple representative instantiations (primitive, complex, zero-sized)
- Document coverage gaps explicitly in contract metadata
- Leverage trait bounds to constrain behavior across instantiations

**Warning signs:**
- Test suite only uses one or two concrete types for generic functions
- Contracts make assumptions about type representation (size, alignment)
- No documentation of which instantiations are verified

**Source:** [Lessons Learned from Rust Stdlib Verification](https://arxiv.org/html/2510.01072v1) - section on "Generic Type Instantiation"

### Pitfall 3: Iterator Laziness and Infinite Sequences

**What goes wrong:** Iterator contracts that assume finite sequences fail for infinite iterators (e.g., `repeat(x)`); eager evaluation in verification diverges on lazy infinite chains

**Why it happens:** Rust iterators are lazy - `iter().map(f).filter(p)` does nothing until consumed; some iterators intentionally infinite; verification may try to materialize entire sequence

**How to avoid:**
- Model iterators as potentially infinite sequences in SMT
- Use step/leadsto predicates instead of materializing full sequence
- Verify consumption (collect, fold) separately from chain construction
- Add finiteness preconditions where required (`take(n)` makes infinite finite)

**Warning signs:**
- Contract uses `Seq<T>` without length bounds
- Verification diverges on iterator chain construction
- No distinction between finite and infinite iterator sources

**Source:** [Compositional Iterator Reasoning](https://www.cs.ubc.ca/~alexsumm/papers/BilyHansenMuellerSummers23.pdf) reference, CVC5 sequence theory for lazy structures

### Pitfall 4: HashMap Non-Determinism in Iteration Order

**What goes wrong:** Contracts assume stable iteration order for HashMap, but order is non-deterministic (depends on hash seed, insertion order varies)

**Why it happens:** HashMap uses randomized hashing for DoS resistance; iteration order is implementation detail not specified in API

**How to avoid:**
- Use mathematical map abstraction (unordered) not sequence
- Contracts on `.iter()` should use set semantics not sequence
- Never specify postconditions involving iteration order
- Document when BTreeMap's ordered iteration is needed for verification

**Warning signs:**
- Contract uses indexed access to HashMap iterator: `hashmap.iter()[i]`
- Postcondition compares iterator sequences for equality
- Test oracle assumes specific iteration order

**Source:** [Rust HashMap Documentation](https://doc.rust-lang.org/std/collections/struct.HashMap.html), mathematical map abstraction requirement from CONTEXT.md

### Pitfall 5: Rust Edition API Divergence

**What goes wrong:** Contracts written for Rust 2021 fail when user code uses Rust 2024 with different stdlib API (method signatures changed, new methods added)

**Why it happens:** Rust editions can introduce new APIs while deprecating old ones; stdlib evolves across versions; contracts pinned to specific edition/version

**How to avoid:**
- Use conditional compilation for edition-specific APIs: `#[cfg(rust_2024)]`
- Maintain contract variants for each supported edition
- Focus contracts on stable, core APIs less likely to change
- Version contract crate with semver reflecting Rust edition support

**Warning signs:**
- Contract fails to compile on different Rust edition
- No feature flags for edition-specific behavior
- Documentation doesn't specify supported Rust versions

**Source:** [Rust API Evolution Policy](https://rust-lang.github.io/rfcs/1105-api-evolution.html), [Rust Editions](https://doc.rust-lang.org/edition-guide/)

### Pitfall 6: Over-Trusting External Specifications

**What goes wrong:** External contract marked `#[trusted]` contains unsound specification (too strong postcondition, too weak precondition); verification succeeds but contract violations occur at runtime

**Why it happens:** Prusti/verification tools trust external specs without validation; human error in writing contracts; lack of oracle testing for custom contracts

**How to avoid:**
- Mandatory oracle testing for all contracts (stdlib and custom)
- Soundness validation for `#[override_contract]` (check precond ⊢ postcond consistent)
- Code review for contracts separate from implementation review
- Property-based testing with proptest to catch contradiction

**Warning signs:**
- External contract added without corresponding oracle tests
- Override contract contradicts stdlib behavior in edge cases
- Verification succeeds but runtime panics on contract violation

**Source:** [Prusti trusted external specs](https://viperproject.github.io/prusti-dev/user-guide/verify/external.html), user requirement for "basic soundness validation on user overrides"

## Code Examples

Verified patterns from official sources and research:

### Vec<T> Core Operations

```rust
// Source: Prusti external spec pattern + user requirements
use prusti_contracts::*;

#[extern_spec]
impl<T> Vec<T> {
    // Track both length and capacity (user requirement)
    #[pure]
    fn len(&self) -> usize;

    #[pure]
    fn capacity(&self) -> usize;

    // Element-level precision (user requirement)
    #[requires(self.len() < self.capacity())]
    #[ensures(self.len() == old(self.len()) + 1)]
    #[ensures(self[old(self.len())] == value)]  // Precise: new element at end
    fn push(&mut self, value: T);

    #[ensures(result.is_some() ==> self.len() == old(self.len()) - 1)]
    #[ensures(result.is_none() ==> self.len() == 0)]
    fn pop(&mut self) -> Option<T>;

    #[requires(index < self.len())]
    #[ensures(result == &self.seq_model()[index])]  // Element-level: i-th element
    fn get(&self, index: usize) -> Option<&T>;

    // Capacity management (user requirement)
    #[requires(new_cap >= self.len())]
    #[ensures(self.capacity() >= new_cap)]
    #[ensures(self.len() == old(self.len()))]
    #[ensures(forall(|i: usize| i < self.len() ==> self[i] == old(self[i])))]  // Elements preserved
    fn reserve(&mut self, new_cap: usize);

    #[ensures(self.capacity() == self.len())]
    #[ensures(forall(|i: usize| i < self.len() ==> self[i] == old(self[i])))]
    fn shrink_to_fit(&mut self);
}
```

### Option<T> Behavioral Contracts

```rust
// Source: Prusti examples + user requirement for "full behavioral contracts"
#[extern_spec]
impl<T> Option<T> {
    #[pure]
    #[ensures(result == matches!(self, Some(_)))]
    fn is_some(&self) -> bool;

    #[pure]
    #[ensures(result == matches!(self, None))]
    fn is_none(&self) -> bool;

    #[requires(self.is_some())]
    #[ensures(result == self.peek())]  // peek() is ghost function
    fn unwrap(self) -> T;

    #[ensures(match self {
        Some(x) => result == Some(f(x)),
        None => result == None,
    })]
    fn map<U, F: FnOnce(T) -> U>(self, f: F) -> Option<U>;

    #[ensures(match self {
        Some(_) => result == self,
        None => result == Some(default),
    })]
    fn ok_or<E>(self, default: E) -> Result<T, E>;
}
```

### HashMap<K,V> Mathematical Map Abstraction

```rust
// Source: User requirement "full mathematical map abstraction", Verus view pattern
use prusti_contracts::*;

// Ghost function for mathematical model
#[pure]
#[trusted]  // Axiomatic model
fn map_model<K, V>(m: &HashMap<K, V>) -> Map<K, V>;

#[extern_spec]
impl<K: Hash + Eq, V> HashMap<K, V> {
    // insert ensures get(k) == v (user requirement)
    #[ensures(map_model(&self).lookup(&key) == Some(&value))]
    #[ensures(forall(|k: &K| k != &key ==>
              map_model(&self).lookup(k) == old(map_model(&self).lookup(k))))]
    fn insert(&mut self, key: K, value: V) -> Option<V>;

    // get(k) returns associated value
    #[pure]
    #[ensures(result == map_model(&self).lookup(&key))]
    fn get(&self, key: &K) -> Option<&V>;

    // remove ensures get(k) == None (user requirement)
    #[ensures(map_model(&self).lookup(&key) == None)]
    #[ensures(forall(|k: &K| k != &key ==>
              map_model(&self).lookup(k) == old(map_model(&self).lookup(k))))]
    fn remove(&mut self, key: &K) -> Option<V>;

    #[pure]
    #[ensures(result == map_model(&self).contains(&key))]
    fn contains_key(&self, key: &K) -> bool;

    #[pure]
    #[ensures(result == map_model(&self).len())]
    fn len(&self) -> usize;
}
```

### Iterator Chain Composition

```rust
// Source: User requirement "properties compose through map/filter/collect", iterator verification research
use prusti_contracts::*;

// Ghost sequence model for iterators
trait IteratorModel {
    type Item;
    #[pure]
    fn seq_model(&self) -> Seq<Self::Item>;
}

// Map preserves length (user requirement)
#[extern_spec]
impl<I: Iterator, F, B> Iterator for Map<I, F>
where F: FnMut(I::Item) -> B
{
    #[ensures(self.seq_model().len() == self.inner.seq_model().len())]
    fn next(&mut self) -> Option<B>;
}

// Filter reduces length (user requirement)
#[extern_spec]
impl<I: Iterator, P> Iterator for Filter<I, P>
where P: FnMut(&I::Item) -> bool
{
    #[ensures(self.seq_model().len() <= self.inner.seq_model().len())]
    fn next(&mut self) -> Option<I::Item>;
}

// End-to-end property: map + filter
#[requires(iter.seq_model().len() == n)]
#[ensures(result.len() <= n)]  // Filter reduces
#[ensures(forall(|i: usize| i < result.len() ==> predicate(&map_fn(original[i]))))]
fn map_filter_collect<T, U>(
    iter: impl Iterator<Item = T>,
    map_fn: impl Fn(T) -> U,
    predicate: impl Fn(&U) -> bool,
) -> Vec<U> {
    iter.map(map_fn).filter(predicate).collect()
}
```

### Oracle Test for Contract Validation

```rust
// Source: User requirement "property-based oracle testing", proptest patterns
use proptest::prelude::*;

proptest! {
    // Validate Vec::push contract
    #[test]
    fn vec_push_contract_sound(
        mut vec in vec(any::<i32>(), 0..100),
        value in any::<i32>(),
    ) {
        // Capture precondition state
        let old_len = vec.len();
        let old_cap = vec.capacity();

        // If precondition violated, skip (or would panic)
        prop_assume!(old_len < old_cap);

        // Execute real stdlib operation
        vec.push(value);

        // Validate postconditions
        prop_assert_eq!(vec.len(), old_len + 1, "length postcondition");
        prop_assert_eq!(vec[old_len], value, "element postcondition");
    }

    // Validate HashMap::insert mathematical map abstraction
    #[test]
    fn hashmap_insert_contract_sound(
        mut map in hash_map(any::<String>(), any::<i32>(), 0..50),
        key in any::<String>(),
        value in any::<i32>(),
    ) {
        // Execute real stdlib operation
        map.insert(key.clone(), value);

        // Validate postcondition: get(k) == Some(v)
        prop_assert_eq!(map.get(&key), Some(&value));
    }

    // Validate iterator chain composition
    #[test]
    fn iterator_map_filter_length(
        vec in vec(any::<i32>(), 0..100),
    ) {
        let original_len = vec.len();

        // Execute chain
        let result: Vec<_> = vec.iter()
            .map(|x| x * 2)
            .filter(|x| *x > 10)
            .collect();

        // Validate postcondition: filter reduces length
        prop_assert!(result.len() <= original_len);
    }
}
```

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| Array theory only for sequences | Hybrid string-array sequence theory in CVC5 | 2024 | Enables native concat/length operations, reduces quantifier burden, used by move-prover at Meta |
| Prusti-specific contract language | Standardized Rust contract attributes (#[contracts::requires/ensures]) | 2025 (MCP-759) | Tool interoperability, compiler support, unified syntax across Prusti/Kani/Verus |
| Per-type quantification in quickcheck | Per-value strategies in proptest | proptest 0.9+ (2019) | More flexible composition, better shrinking for complex types, became Rust PBT standard |
| Compiler plugins (unstable) | rustc_driver with Callbacks | Ongoing | Clippy/Prusti pattern, stable across nightlies with pinning, access to MIR/HIR |
| Custom proc-macro parsing | syn crate ecosystem | syn 2.0 (2023) | Handles Rust syntax evolution, macro hygiene, maintained by ecosystem |

**Deprecated/outdated:**
- **quickcheck for complex verification:** Still maintained but proptest's strategy system better for contract oracle tests (per-value generation enables precise domain modeling)
- **Compiler plugins API:** Officially unstable and discouraged; rustc_driver pattern is blessed approach for verification tools
- **Pure SMT array theory for sequences:** Z3/CVC5 moved to dedicated sequence theories (Z3 has seq.nth, seq.concat; CVC5 has rich sequence operators)
- **Inline contracts in stdlib code:** Rust moving to external contract annotation in separate verify-rust-std fork to avoid runtime overhead in production builds

## Open Questions

1. **Infinite Iterator SMT Encoding**
   - What we know: CVC5 supports lazy sequences; step/leadsto predicates avoid materialization; research shows compositional reasoning possible
   - What's unclear: Optimal encoding for infinite iterators in rust-fv (sequence with symbolic length? explicit finite take()?)
   - Recommendation: Start with precondition requiring finiteness (`.take(n)` wrapper), extend to infinite with step predicates in Phase 14+. Conservative approach favors soundness.

2. **Rust Edition API Surface Versioning**
   - What we know: Editions can change APIs; `#[cfg(rust_2024)]` available; semver for contract crate versions
   - What's unclear: How granular to version contracts (per-edition? per-stdlib version? per-function?)
   - Recommendation: Version contract crate by Rust edition (rust-fv-contracts-2021, rust-fv-contracts-2024), use feature flags for point releases. Document minimum supported Rust version (MSRV).

3. **Generic Type Verification Coverage**
   - What we know: Monomorphization prevents single proof for all T; bounded quantification limited in SMT
   - What's unclear: Acceptable coverage threshold (3 representative types? All common primitives?)
   - Recommendation: Require verification for {primitive, complex, zero-sized} instantiations. Document coverage in contract metadata. Future: explore trait-bounded quantification.

4. **HashMap Concurrent Modification Contracts**
   - What we know: Mathematical map abstraction works for single-threaded; concurrent access needs different model
   - What's unclear: How to model Arc<Mutex<HashMap>> or DashMap contracts (locks? linearizability?)
   - Recommendation: Phase 13 scope limited to single-threaded contracts. Defer concurrent collection contracts to future phase (likely requires separation logic).

5. **Oracle Test Performance at Scale**
   - What we know: 200+ stdlib functions need contracts; proptest defaults to 256 cases per test
   - What's unclear: CI time budget for oracle suite (minutes? hours?), trade-off between coverage and speed
   - Recommendation: Stratify tests - fast smoke (10 cases, run always), thorough (256 cases, PR gate), exhaustive (10k cases, nightly). Use proptest's `#[proptest(cases = N)]`.

## Sources

### Primary (HIGH confidence)

- [Prusti External Specifications](https://viperproject.github.io/prusti-dev/user-guide/verify/external.html) - extern_spec syntax, trusted specs pattern
- [Rust Standard Library Contracts Initiative](https://rust-lang.github.io/rust-project-goals/2025h1/std-contracts.html) - MCP-759 contract attributes, 2025 roadmap
- [Lessons Learned From Rust Stdlib Verification](https://arxiv.org/html/2510.01072v1) - Specific pitfalls, unsoundness examples, generic type issues
- [CVC5 Sequence Theory](https://cvc5.github.io/2024/02/15/sequences-theory.html) - Hybrid string-array approach, operations available
- [Verus vstd Collections](https://verus-lang.github.io/verus/verusdoc/vstd/) - Seq/Map/Set models, view pattern
- [Proptest Documentation](https://lib.rs/crates/proptest) - Strategy system, oracle testing patterns, round-trip validation
- [SMT-LIB Array Theory](https://smt-lib.org/theories-ArraysEx.shtml) - select/store operations, extensionality axiom
- [Rust API Evolution RFC 1105](https://rust-lang.github.io/rfcs/1105-api-evolution.html) - Semver policy, stability guarantees
- [Kani Verification](https://model-checking.github.io/verify-rust-std/tools/kani.html) - Contract attribute syntax, stdlib integration

### Secondary (MEDIUM confidence)

- [Verify Rust Std Repository](https://github.com/model-checking/verify-rust-std) - 200+ annotated functions, challenge structure
- [AWS Rust Stdlib Safety Blog](https://aws.amazon.com/blogs/opensource/verify-the-safety-of-the-rust-standard-library/) - Community verification effort, challenge approach
- [rustc_driver Documentation](https://rustc-dev-guide.rust-lang.org/rustc-driver/intro.html) - Compiler integration patterns, Callbacks trait
- [Rust Conditional Compilation](https://doc.rust-lang.org/reference/conditional-compilation.html) - #[cfg] for edition handling
- [Reasoning About Vectors using SMT Sequences](https://arxiv.org/pdf/2205.08095) - SMT sequence theory for vectors (PDF parse failed but abstract confirms approach)

### Tertiary (LOW confidence)

- Compositional Iterator Reasoning paper (BilyHansenMuellerSummers23) - Referenced in search but PDF unavailable; step/leadsto predicates concept validated by other sources
- Z3 sequence operations - Documented in research but specific API details not verified from official Z3 docs

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH - proptest/rustc_driver are industry standard, verified via multiple sources
- Architecture patterns: HIGH - External crate pattern confirmed by Prusti/Verus; proptest oracle pattern documented; override mechanism based on user requirements
- SMT encoding: MEDIUM - CVC5 sequence theory documented, but optimal encoding for Rust iterators requires experimentation
- Pitfalls: HIGH - Derived from published research (arxiv 2510.01072v1) with specific examples
- Versioning strategy: MEDIUM - Conditional compilation standard, but optimal granularity for contract versioning needs validation

**Research date:** 2026-02-14
**Valid until:** 2026-03-14 (30 days - stable domain, Rust moves slowly, verification research evolving but foundational concepts stable)
