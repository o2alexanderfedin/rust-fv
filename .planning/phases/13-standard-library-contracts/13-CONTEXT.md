# Phase 13: Standard Library Contracts - Context

**Gathered:** 2026-02-14
**Status:** Ready for planning

<domain>
## Phase Boundary

Preloaded formal verification contracts for Rust's standard library types so developers can verify real-world code without writing stdlib specs. Covers Vec, HashMap, Option, Result, Iterator, String, and slice operations. Custom contract authoring and new verification capabilities are out of scope.

</domain>

<decisions>
## Implementation Decisions

### Contract scope & depth
- Vec<T>: Track both length AND capacity in contracts (reserve, shrink_to_fit modeled)
- Element-level contracts where safe and precise: vec.push(x) ensures vec[len-1] == x, vec.get(i) returns the i-th element
- HashMap<K,V>: Full mathematical map abstraction — insert(k,v) ensures get(k)==Some(v), remove(k) ensures get(k)==None
- Option<T> and Result<T,E>: Full behavioral contracts on unwrap, map, is_some, ok_or, etc.
- Tier 1 types: Vec, Option, Result, HashMap, Iterator, String, &str, and slice operations

### Contract packaging
- External crate pattern (Prusti/Verus model) — separate `rust-fv-contracts` crate
- Auto-load with opt-out: contracts loaded by default, `--no-stdlib-contracts` flag to disable
- Versioning: Claude's discretion on how to handle Rust edition/version differences, biased toward safety and precision
- Property-based oracle testing required: tests run real stdlib ops and compare against contract postconditions to catch unsound contracts

### Override mechanism
- Syntax: `#[override_contract]` attribute on extern function declarations
- Info-level notice when override is active: "Using custom contract for Vec::push (overriding stdlib)"
- Two modes: `#[override_contract]` for full replacement, `#[extend_contract]` for additive conditions on top of stdlib
- Basic soundness validation on user overrides (e.g., postcondition not contradicting precondition)

### Iterator contracts
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

</decisions>

<specifics>
## Specific Ideas

- External crate pattern follows Prusti/Verus proven model for versioning independence
- HashMap as mathematical map abstraction enables functional correctness proofs, not just structural ones
- Override mechanism supports both replacement and extension to handle real-world cases where stdlib contracts are too weak or too strong
- Iterator chain composition should propagate properties (e.g., filter reduces length, map preserves length)

</specifics>

<deferred>
## Deferred Ideas

None — discussion stayed within phase scope

</deferred>

---

*Phase: 13-standard-library-contracts*
*Context gathered: 2026-02-14*
