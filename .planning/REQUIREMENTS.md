# v0.5 Requirements: SMT Completeness

## Active Requirements

### VCGEN-01: Memory Operations [PARTIAL — Phase 28 Plan 04]
VCGen must produce correct SMT VCs for all Rust memory access patterns:
- Array indexing (`a[i]`) — bounds-checked index with SMT Seq select — DONE (BoundsCheck VC via generate_index_bounds_vcs)
- Rvalue::Len — length encoding as `{arr}_len` SMT constant — DONE
- Struct/tuple field access (`s.field`, `t.0`) — projection encoding — DONE (regression guard passes)
- `for`/iterator loops over slices, ranges, and collections
- Range expressions (`1..10`, `1..=10`, `0..n`) as iterable values
- Slice references (`&[T]`) — length + data pointer encoding

### VCGEN-02: Conditional Operators [COMPLETE — Phase 28 Plan 03]
VCGen must produce correct SMT VCs for all Rust branching constructs:
- `if`/`else` expressions (already partially handled; verify completeness)
- `match` expressions with patterns: literal, tuple, enum variant, wildcard, guard — DONE (Rvalue::Discriminant binding)
- `if let` and `while let` pattern destructuring — DONE (SwitchInt + Discriminant)
- Exhaustiveness: match arms must cover all cases in VCs

### VCGEN-03: Typecasts
VCGen must produce correct SMT VCs for Rust type conversion operations:
- Numeric `as` casts with correct truncation/sign-extension semantics
- `i8 as u32`, `u64 as i32`, `f64 as u64`, etc.
- Unsafe `transmute` — model as bitvector reinterpretation
- Pointer-to-integer and integer-to-pointer casts (usize)
- No-op casts (same-size types) handled correctly

### VCGEN-04: Generics [COMPLETE — Phase 28 Plan 05]
VCGen must produce correct SMT VCs for generic functions and types:
- `where` clause constraints propagated into SMT premises — DONE (trait_bounds_as_smt_assumptions injects Assert premises)
- Generic spec annotation propagation (e.g., `#[requires(T: Ord)]`) — DONE (Ty::Generic as Sort::Uninterpreted)
- Monomorphization: each instantiation generates separate VCs — DONE (generate_vcs_monomorphized)
- Trait bound encoding as uninterpreted sort constraints — DONE (BoolLit(true) per bound, Z3 no-op)

## Out of Scope (v0.5)

- Async closures (Rust 2024 edition) — deferred to v0.6
- Dependent types — academic complexity
- Full pattern matching on nested ADTs beyond depth-2 — deferred
- Const generics — deferred to v0.6

---
*Created: 2026-02-23 — v0.5 milestone start*
