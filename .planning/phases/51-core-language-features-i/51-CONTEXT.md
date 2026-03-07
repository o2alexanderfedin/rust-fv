# Phase 51: Core Language Features I - Context

**Gathered:** 2026-03-07
**Status:** Ready for planning

<domain>
## Phase Boundary

Const generic parameters participate in verification, HRTB are encoded, union field access generates reinterpretation VCs, Drop invocations are modeled at scope exit, and Pin move-prevention is enforced. Five requirements: LANG-01 (const generics), LANG-02 (HRTB), LANG-03 (unions), LANG-04 (Drop), LANG-05 (Pin).

</domain>

<decisions>
## Implementation Decisions

### Const Generic Encoding (LANG-01)
- New `Ty::ConstGeneric(String, Ty)` IR variant — separate from `Ty::Generic(String)` which is for type parameters. Const params are SMT integer/bool constants, not sorts
- Full spec access: const params appear as named SMT constants in specs — users can write `#[requires(N > 0)]`, `#[ensures(result.len() == N)]`
- Array type `[T; N]` encoded as `(Array Int T)` with length bound `len == N`. At call sites with concrete N, N is asserted equal to the value. Generic paths keep N symbolic
- Supported const generic types: all integer types (usize, u8..u64, i8..i64, isize) and bool. Each maps to appropriate SMT sort (BitVec or Bool)
- Monomorphization registry (Phase 44) extended to substitute const generic values alongside type substitutions

### HRTB Encoding (LANG-02)
- Universally quantified lifetime constraints in SMT — `for<'a> F: Fn(&'a T) -> R` encoded as forall over lifetime parameter
- Builds on existing lifetime analysis infrastructure from Phase 9

### Claude's Discretion (HRTB)
- Exact SMT encoding for universally quantified lifetime bounds — choose approach toward safety, precision, and completeness
- Whether HRTB lifetimes are erased to universal quantifiers or tracked structurally
- Integration depth with existing NLL tracking and outlives reasoning
- Test fixture design for HRTB verification scenarios

### Union Field Reinterpretation (LANG-03)
- New `Ty::Union(String, Vec<(String, Ty)>)` IR variant — clean separation from `Ty::Struct` since unions have overlapping storage
- Bitwise reinterpretation VCs for field reads — union stored as bitvector of max field size, reading a field generates a reinterpretation-cast VC asserting bitwise equivalence (same pattern as transmute from Phase 50)
- Ghost variant tracking: per-union ghost variable `active_field: Int` tracks which field was last written. Reading a different field generates a safety VC. Follows MaybeUninit/RefCell ghost state patterns from Phase 48/50
- `#[repr(C)]` unions get special treatment: defined field offsets and sizes per C ABI, verifier can assert exact byte layout and size. Default unions only assert max size

### Drop Scope-Exit Modeling (LANG-04)
- Full drop-order model: Rust's guaranteed reverse-declaration-order drop at scope exit. Generate VCs asserting Drop::drop() postconditions in correct order. Catches drop-order-dependent bugs
- Compile-time diagnostic for Drop+Copy incompatibility: emit V-level diagnostic if a type implements both Drop and Copy (defensive check — Rust forbids this but catches unsafe impls or proc macro issues)
- Full Drop contract support: users can annotate `impl Drop` with `#[ensures]` to specify drop guarantees (e.g., resource freed, counter decremented). VCGen checks these at scope exit. Enables verifying RAII patterns
- Recursive field drop modeling: when a struct with Drop fields is dropped, generate VCs for each field's Drop in reverse declaration order, THEN the struct's own Drop. Matches Rust semantics exactly

### Pin Move-Prevention VCs (LANG-05)
- Ghost state `is_pinned` per local — follows RefCell/MaybeUninit ghost state pattern. `Pin::new()` sets `is_pinned = true`. Any subsequent move generates a MemorySafety VC asserting `!is_pinned || implements_unpin`
- Basic structural pinning: field projections from pinned structs — if `Pin<&mut Struct>`, accessing a field produces a pinned reference to that field. Covers the `pin_project` macro pattern (80% of real usage)
- Unpin detection via MIR-level trait bound check: check if the type's trait bounds include `Unpin` (or if the type is a primitive which is always Unpin). Uses existing trait bound infrastructure from Phase 40. Types implementing Unpin bypass Pin move-prevention VCs
- Dedicated PinSafety VC for `Pin::new_unchecked` on !Unpin types: asserting caller upholds Pin invariant. Requires user-provided `#[unsafe_ensures]` to discharge. Mirrors unsafe function contract pattern

### Claude's Discretion (General)
- Exact SMT encoding details for all five features
- MIR-level detection of const generic parameters, union ADTs, Drop impls, Pin types
- Test fixture design for all five requirement areas
- Diagnostic message wording for new VCs and warnings
- Integration with existing monomorphization, trait analysis, and ghost state infrastructure
- Whether to add new VcKind variants (PinSafety, DropOrder, UnionAccess) or reuse existing ones

</decisions>

<code_context>
## Existing Code Insights

### Reusable Assets
- `Ty::Generic(String)`: Existing type parameter representation — `Ty::ConstGeneric(String, Ty)` follows same pattern
- Monomorphization registry (Phase 44): `populate_monomorphization_registry` handles `Ty::Generic` → concrete substitution — extend for const params
- Transmute reinterpretation VCs (Phase 50): Bitwise cast pattern in `encode_term.rs` — reuse for union field access encoding
- MaybeUninit ghost state (Phase 50): Per-local ghost boolean declarations in SMT preamble — reuse pattern for union `active_field` and Pin `is_pinned` tracking
- RefCell ghost state (Phase 48): `RefCellGhostState` linear block walk pattern — established ghost tracking infrastructure
- `ptr::drop_in_place` stdlib contract (Phase 50): Existing drop-related contract in `stdlib_contracts/ptr.rs`
- `trait_bounds_as_smt_assumptions` (Phase 40): Trait bound SMT axiom generation — extend for Unpin detection
- Lifetime analysis (Phase 9): NLL tracking, outlives, reborrow chains — foundation for HRTB encoding
- `UnsafeOperation` enum in `vcgen.rs`: Existing unsafe operation detection — extend with UnionAccess, PinNewUnchecked

### Established Patterns
- ADT DefId matching: Used for Option, Result, Vec, NonNull, MaybeUninit detection — same pattern for Pin detection
- VcKind-based diagnostics: Each safety property gets VcKind + diagnostic code — continue for new VC types
- Per-local ghost variables: ProphecyInfo, RefCellGhostState, MaybeUninitGhostState patterns — reuse for union/Pin tracking
- Reverse-declaration-order processing: Rust drops locals in reverse order — VCGen must iterate locals in reverse at scope exit

### Integration Points
- `ir.rs`: Add `Ty::ConstGeneric(String, Ty)`, `Ty::Union(String, Vec<(String, Ty)>)` variants
- `mir_converter.rs`: Detect const generic params from MIR, union ADTs, Drop impls, Pin types
- `vcgen.rs`: Union access VCs, Drop scope-exit VCs, Pin move-prevention VCs, Drop+Copy diagnostic
- `encode_sort.rs`: SMT sort encoding for new Ty variants
- `encode_term.rs`: Union field reinterpretation encoding (reuse transmute pattern)
- `monomorphize.rs`: Extend for const generic value substitution
- `trait_analysis.rs`: Unpin trait detection, Drop impl detection
- `spec_parser.rs`: Const generic names available in spec expressions
- `diagnostics.rs`: New diagnostic codes for Drop+Copy, PinSafety, UnionAccess

</code_context>

<specifics>
## Specific Ideas

- Const generics use `Ty::ConstGeneric` (not extending `Ty::Generic`) for clean type-vs-value separation
- Union ghost state follows the same linear block walk pattern as RefCell and MaybeUninit — three consistent uses of the same pattern
- repr(C) unions get layout guarantees using `mem::size_of`/`mem::align_of` SMT constants (same as Phase 50 FFI repr(C) work)
- Drop modeling is recursive: fields first (reverse order), then struct's own Drop — matches Rust exactly
- Pin uses ghost state (not type-level wrapper) — `is_pinned` bool per local, consistent with existing ghost patterns
- Pin::new_unchecked generates dedicated PinSafety VC requiring `#[unsafe_ensures]` — mirrors unsafe function contract pattern
- HRTB toward safety, precision, and completeness (user preference) — not the simplest approach

</specifics>

<deferred>
## Deferred Ideas

None — discussion stayed within phase scope

</deferred>

---

*Phase: 51-core-language-features-i*
*Context gathered: 2026-03-07*
