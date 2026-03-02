---
created: 2026-03-02T10:02:39.774Z
title: Implement missing and partial cross-verification features (generics, FnMut, cross-crate)
area: general
files:
  - crates/driver/src/mir_converter.rs:136
  - crates/driver/src/parallel.rs:264
  - crates/analysis/src/vcgen.rs:285-298,1032
  - crates/analysis/src/monomorphize.rs
  - crates/analysis/src/closure_analysis.rs
  - crates/analysis/src/behavioral_subtyping.rs
---

## Problem

Cross-verification support audit revealed three gaps of varying severity:

### Gap 1 — Generics (HIGH priority)
`mir_converter.rs:136` hardcodes `generic_params: vec![]`. The driver never calls `tcx.generics_of()`, so:
- Trait bound axioms are never injected (code path at `vcgen.rs:285-298` is dead)
- `generate_vcs_monomorphized` exists in `vcgen.rs:1032` but is never called from `crates/driver/` (0 references)
- A `fn max<T: Ord>()` is verified with `T` as a fully opaque type — ordering properties can't be proven

Fix: In `mir_converter.rs:convert_mir()`, call `tcx.generics_of(def_id)` to extract type parameter names + trait bounds. Update `parallel.rs:264` to route functions with non-empty `generic_params` through `generate_vcs_monomorphized` instead of `generate_vcs_with_db`.

### Gap 2 — FnMut prophecy (MEDIUM priority)
Mutable capture verification via prophecy variables is not implemented. FnMut closures are detected but mutation of captured state can't be verified. `Fn`/`FnOnce` work fine.

Fix: Implement prophecy variable encoding in `closure_analysis.rs` + `vcgen.rs` for FnMut captured state.

### Gap 3 — Cross-crate pre-compiled summaries (LOW / deferred)
Pre-compiled `.rlib` metadata summaries are absent. Only in-session (same `cargo check`) dependencies share contracts. Stdlib contracts are pre-loaded as a workaround. Requirements `XCRATE-01`/`XCRATE-02` are deferred per `v0.6-REQUIREMENTS.md`.

## Solution

1. **Generics (activate dormant pipeline)**:
   - `mir_converter.rs:convert_mir()`: replace `generic_params: vec![]` with extraction from `tcx.generics_of(def_id)` — collect `GenericParam { name, bounds: Vec<TraitBound> }`
   - `parallel.rs`: when `func.generic_params.is_empty() == false`, dispatch to `generate_vcs_monomorphized` with concrete instantiation examples from call sites
   - Write failing test: `fn max<T: Ord>(a: T, b: T) -> T` with `#[ensures(result == a || result == b)]` should verify

2. **FnMut prophecy**:
   - Add prophecy variable encoding in `vcgen.rs` for FnMut closure bodies
   - Track pre/post state of each mutable capture
   - Write failing test: closure mutating a counter with contract on final value

3. **Cross-crate summaries**: Defer — low priority, requires `.rlib` metadata parsing infrastructure.

### Current state of full support matrix:
| Construct | Supported? | Cross-Item? |
|-----------|-----------|-------------|
| Free functions | YES | YES |
| Struct methods (impl) | YES | YES |
| Closures / Lambdas | PARTIAL | PARTIAL |
| Generics | PARTIAL | NO |
| Structs/traits (behavioral subtyping) | YES | PARTIAL |
| Cross-crate | PARTIAL | YES |
