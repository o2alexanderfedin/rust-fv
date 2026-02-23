# v0.5 Requirements: SMT Completeness

## Active Requirements

### VCGEN-01: Memory Operations
VCGen must produce correct SMT VCs for all Rust memory access patterns:
- Array indexing (`a[i]`) — bounds-checked index with SMT Seq select
- `for`/iterator loops over slices, ranges, and collections
- Range expressions (`1..10`, `1..=10`, `0..n`) as iterable values
- Slice references (`&[T]`) — length + data pointer encoding
- Struct/tuple field access (`s.field`, `t.0`) — projection encoding

### VCGEN-02: Conditional Operators
VCGen must produce correct SMT VCs for all Rust branching constructs:
- `if`/`else` expressions (already partially handled; verify completeness)
- `match` expressions with patterns: literal, tuple, enum variant, wildcard, guard
- `if let` and `while let` pattern destructuring
- Exhaustiveness: match arms must cover all cases in VCs

### VCGEN-03: Typecasts
VCGen must produce correct SMT VCs for Rust type conversion operations:
- Numeric `as` casts with correct truncation/sign-extension semantics
- `i8 as u32`, `u64 as i32`, `f64 as u64`, etc.
- Unsafe `transmute` — model as bitvector reinterpretation
- Pointer-to-integer and integer-to-pointer casts (usize)
- No-op casts (same-size types) handled correctly

### VCGEN-04: Generics
VCGen must produce correct SMT VCs for generic functions and types:
- `where` clause constraints propagated into SMT premises
- Generic spec annotation propagation (e.g., `#[requires(T: Ord)]`)
- Monomorphization: each instantiation generates separate VCs
- Trait bound encoding as uninterpreted sort constraints

## Out of Scope (v0.5)

- Async closures (Rust 2024 edition) — deferred to v0.6
- Dependent types — academic complexity
- Full pattern matching on nested ADTs beyond depth-2 — deferred
- Const generics — deferred to v0.6

---
*Created: 2026-02-23 — v0.5 milestone start*
