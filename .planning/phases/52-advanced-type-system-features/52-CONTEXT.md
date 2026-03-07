# Phase 52: Advanced Type System Features - Context

**Gathered:** 2026-03-07
**Status:** Ready for planning

<domain>
## Phase Boundary

Model catch_unwind as an exception boundary with dual-path verification, resolve impl Trait/RPITIT return types for verification, generate GAT well-formedness constraints, preserve contracts through trait upcasting, and record negative impls to strengthen verification assumptions. Five requirements: LANG-06 (catch_unwind), LANG-07 (impl Trait/RPITIT), LANG-08 (GATs), LANG-09 (trait upcasting), LANG-10 (negative impls).

</domain>

<decisions>
## Implementation Decisions

### catch_unwind Exception Boundary Modeling (LANG-06)
- Dual-path verification: `catch_unwind(|| { body })` generates VCs for both the success path (`Ok(result)`) and the panic path (`Err(payload)`). Both paths must satisfy postconditions of surrounding code
- Closure body contracts checked independently: `#[requires]`/`#[ensures]` on the closure body are verified as normal; the catch_unwind wrapper adds the dual-path split
- Drop/cleanup integration: On the panic path, all in-scope variables with Drop impls generate drop-order VCs (reusing Phase 51 LANG-04 infrastructure). This ensures cleanup correctness under unwinding
- Detection via MIR callee name pattern matching: `std::panic::catch_unwind` identified by callee name at `Terminator::Call` sites (same pattern as W080 thread spawn detection from Phase 50)
- New `VcKind::PanicSafety` for catch_unwind boundary VCs — distinguishes from general MemorySafety. Diagnostic code V120
- `UnwindSafe`/`RefUnwindSafe` trait bound checking: if the closure captures `&mut T` where T is not `UnwindSafe`, generate a warning VC (not error — catch_unwind accepts `AssertUnwindSafe` wrapper)

### impl Trait / RPITIT Resolution (LANG-07)
- Concrete type resolution via MIR: `impl Trait` return types are resolved to their concrete types during MIR analysis — MIR has already monomorphized opaque types. Extract the real type from the MIR return type
- RPITIT (Return Position Impl Trait In Trait): when a trait method returns `impl Iterator<Item=i32>`, the trait-level spec (`#[ensures]`) applies to the opaque return type. Each impl's concrete return type must satisfy the trait's postcondition — verified via existing behavioral subtyping VCs (Phase 38)
- New `Ty::Opaque(String, Vec<TraitBound>)` IR variant for cases where concrete resolution fails (cross-crate opaque types). Encoded as uninterpreted sort with trait bound axioms — sound but incomplete (matches project philosophy: soundness non-negotiable)
- Trait bound extraction from opaque types: `impl Iterator<Item=i32>` generates SMT axioms asserting the Iterator contract (next() returns Option<i32>). Uses existing `trait_bounds_as_smt_assumptions` infrastructure (Phase 40)
- Auto-trait leakage prevention: opaque types do NOT leak auto-trait information (Send/Sync) unless the trait bound explicitly includes them — matches Rust semantics

### GAT Well-Formedness Constraints (LANG-08)
- `where Self: 'a` bounds on GATs generate SMT lifetime outlives assertions at use sites: `lifetime_of(self) >= lifetime_a`. Reuses HRTB lifetime encoding from Phase 51 (LANG-02) where lifetimes are Int SMT constants with non-negative constraints
- GAT parameter substitution: `type Item<'a>` instantiated at use sites substitutes the concrete lifetime. The well-formedness check asserts the where clause holds for the substituted lifetime
- Detection via HIR/MIR associated type analysis: GATs identified by associated types with generic parameters. Each use site generates a well-formedness VC asserting all where clauses
- New `VcKind::WellFormedness` for GAT constraint violations — diagnostic code V130. SAT result means the instantiation violates the GAT's constraints
- Interaction with HRTB: GATs with `for<'a>` bounds compose naturally — the HRTB universally quantified lifetime feeds into the GAT well-formedness check

### Trait Upcasting Contract Preservation (LANG-09)
- Vtable compatibility VC: casting `dyn SubTrait` to `dyn SuperTrait` generates a VC asserting vtable layout compatibility. SuperTrait methods must appear at the same vtable offsets — this is guaranteed by Rust's vtable layout but verified for soundness
- Contract preservation: all `#[requires]`/`#[ensures]` contracts on SuperTrait methods are preserved and checked at call sites through the upcast reference. Uses existing behavioral subtyping infrastructure — SubTrait impls already verify SuperTrait contracts via Liskov checks (Phase 38)
- Detection: trait upcasting identified via `CastKind` in MIR (pointer cast from `dyn SubTrait` to `dyn SuperTrait`). The `super_traits` field on `TraitDef` (already in IR) provides the hierarchy
- Upcast chain support: `dyn A` -> `dyn B` -> `dyn C` where A: B: C. Each link in the chain preserves contracts transitively. No new VC needed beyond pairwise checks — existing behavioral subtyping handles transitivity
- New `VcKind::TraitUpcasting` for vtable compatibility VCs — diagnostic code V140

### Negative Trait Implementations (LANG-10)
- `impl !Send for MyType` recorded in `TraitDatabase` as a negative impl entry. New field `negative_impls: HashMap<String, Vec<String>>` mapping trait name to list of types with negative impls
- Thread safety strengthening: when a function transfers a type with `impl !Send` across a thread boundary (detected via spawn/send patterns from Phase 50 W080 infrastructure), generate a `ThreadSafety` VC that is always SAT (violation). This makes the error unconditional — the type is definitively not thread-safe
- `impl !Sync` similarly: shared reference `&MyType` across threads generates a `ThreadSafety` VC
- Detection via HIR: negative impls are syntactically `impl !Trait for Type`. Parsed during trait collection in `callbacks.rs` alongside positive impls
- Negative impls also serve as axiom strengthening: in any function using `MyType`, the SMT context includes `NOT(is_send(MyType))` — this can help Z3 prove properties that depend on non-thread-safety (e.g., "this type is only used in single-threaded context")
- Conservative scope: only `Send` and `Sync` negative impls are tracked initially. Other negative impls (`!Copy`, `!Unpin`) are already handled via absence of positive impl in existing infrastructure

### Claude's Discretion
- Exact MIR-level detection patterns for catch_unwind call sites, opaque return types, GAT use sites, upcast casts, negative impls
- SMT encoding details for dual-path catch_unwind verification
- Test fixture design for all five requirement areas
- Diagnostic message wording for V120, V130, V140 codes
- Whether `Ty::Opaque` fallback is needed in practice or if MIR always resolves impl Trait
- Integration depth between GAT well-formedness and existing HRTB/lifetime infrastructure

</decisions>

<code_context>
## Existing Code Insights

### Reusable Assets
- `TraitDatabase` (`trait_analysis.rs`): Has `traits` and `impls` maps — extend with `negative_impls` field for LANG-10
- `TraitDef.super_traits: Vec<String>` (`ir.rs:70`): Already tracks super-trait hierarchy — directly usable for upcasting chain resolution
- `generate_subtyping_vcs` (Phase 38): Behavioral subtyping for Liskov checks — reuse for RPITIT contract verification
- `parse_dyn_dispatch_callee` (Phase 41): Dyn dispatch resolution via suffix-match — extend for upcast call sites
- W080 thread spawn detection (Phase 50): Callee name pattern matching for `tokio::spawn`/`std::thread::spawn` — reuse for negative impl ThreadSafety VC generation
- Drop scope-exit modeling (Phase 51 LANG-04): Drop-order VCs at scope exit — reuse for catch_unwind panic path cleanup
- HRTB lifetime encoding (Phase 51 LANG-02): Lifetimes as Int SMT constants — reuse for GAT well-formedness lifetime constraints
- `trait_bounds_as_smt_assumptions` (Phase 40): Trait bound SMT axiom generation — extend for opaque type trait bounds
- `UnsafeOperation` enum in `vcgen.rs`: Extensible for new operation classifications
- `VcKind` enum: Extensible for PanicSafety, WellFormedness, TraitUpcasting

### Established Patterns
- Callee name pattern matching for special function detection (catch_unwind, spawn, mem::swap, etc.)
- VcKind + diagnostic code pattern for new safety properties
- TraitDef/TraitImpl registration in callbacks.rs during HIR traversal
- Ghost state linear block walk for per-local tracking
- Behavioral subtyping VCs wired after verify_functions_parallel

### Integration Points
- `ir.rs`: Add `Ty::Opaque(String, Vec<TraitBound>)` variant; extend `TraitDatabase` with `negative_impls`
- `callbacks.rs`: Detect negative impls during HIR traversal; detect GAT definitions; detect opaque return types
- `vcgen.rs`: catch_unwind dual-path VCs, GAT well-formedness VCs, upcast VCs, negative impl ThreadSafety VCs
- `trait_analysis.rs`: Negative impl registration and query; upcast compatibility checks
- `behavioral_subtyping.rs`: RPITIT contract verification via existing Liskov infrastructure
- `encode_sort.rs`: SMT sort encoding for `Ty::Opaque`
- `mir_converter.rs`: Opaque type resolution from MIR return types

</code_context>

<specifics>
## Specific Ideas

- User preference: choose toward safety, precision, and completeness for all five features (consistent with Phase 51 HRTB decision)
- catch_unwind dual-path follows the "if it could happen, verify both paths" principle — no shortcuts
- RPITIT piggybacks on behavioral subtyping — minimal new machinery needed since Liskov checks already exist
- GAT well-formedness reuses HRTB lifetime-as-Int encoding — consistency across lifetime-related features
- Negative impls initially scoped to Send/Sync only — other negative impls (!Copy, !Unpin) already handled by absence of positive impl
- Opaque type fallback (`Ty::Opaque`) is sound but incomplete — matches project's non-negotiable soundness constraint

</specifics>

<deferred>
## Deferred Ideas

None — discussion stayed within phase scope

</deferred>

---

*Phase: 52-advanced-type-system-features*
*Context gathered: 2026-03-07*
