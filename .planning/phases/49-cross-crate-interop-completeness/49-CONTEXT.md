# Phase 49: Cross-Crate & Interop Completeness - Context

**Gathered:** 2026-03-05
**Status:** Ready for planning

<domain>
## Phase Boundary

Complete five verification gaps: cross-crate generic monomorphization registry population, mutable static data-race VCs, NonNull null-check elimination, From::from contract propagation through ? operator, and iterator adapter contract composition. Five requirements: COMPL-04, COMPL-10, COMPL-15, COMPL-17, COMPL-18.

</domain>

<decisions>
## Implementation Decisions

### Cross-Crate Generic Registry (COMPL-10)
- MIR call-site scanning: extend `populate_monomorphization_registry` to scan all local MIR for call terminators referencing external DefIds with concrete type args
- Eager VC generation: monomorphized VCs generated during the main VC pass (consistent with local generic handling)
- V060 opaque callee warning: when a cross-crate generic function has no contract in ContractDatabase, reuse existing V060 diagnostic (Phase 37 infrastructure)
- Substitution map only: store `HashMap<GenericParam, Ty>` per call site; monomorphization applies during VCGen (not pre-monomorphized Function)

### Mutable Static Race VCs (COMPL-15)
- Place-based static detection: detect Place references to static items via MIR's StaticKind; tag as unsafe memory access requiring synchronization proof
- Mutex/RwLock guard scope proof: if static mut access is inside a Mutex::lock() or RwLock guard scope, DataRaceFreedom VC is UNSAT; uses existing happens-before infrastructure
- Both reads and writes: any access to static mut without synchronization generates a DataRaceFreedom VC (sound for concurrent read-write scenarios)
- V100 diagnostic series: new V100 DataRaceFreedom diagnostic for mutable static access; message: "mutable static access requires synchronization (Mutex/RwLock guard or atomic ordering)"

### NonNull Encoding (COMPL-17)
- New `Ty::NonNull(Box<Ty>)` IR type variant: MIR converter recognizes std::ptr::NonNull via ADT DefId matching and emits Ty::NonNull
- Suppress null-check AND alignment VCs: NonNull implies both non-null and well-aligned (matching Rust's NonNull guarantees)
- ADT DefId matching: detect NonNull from MIR types via DefId (same pattern as Option/Result detection in stdlib contracts)
- Propagate through as_ptr(): NonNull::as_ptr() returns a *const T that inherits non-null property in SMT; reduces false positive null-check VCs after cast

### From::from at ? Operator (COMPL-18)
- Both builtin + user contracts: ship stdlib From contracts in stdlib_contracts/ for common impls AND allow user #[ensures] on custom From impls
- MIR pattern matching for ? detection: detect the match-on-Result-discriminant + Err-arm-calls-From::from + early-return pattern (rustc's ? desugaring)
- Postcondition flows to caller return: From::from postcondition becomes an assumption at the caller's early return site; caller's #[ensures] can reason about converted error
- Skip identity From<T> for T: detect reflexive conversions and skip VC generation (postcondition trivially true; avoids diagnostic noise)

### Iterator Adapter Chaining (COMPL-04)
- Claude's Discretion: compose filter/map/etc. contracts in SMT rather than falling back to BoolLit(true); element-level postconditions flow through adapter chain
- Existing iterator contracts (map, filter) in stdlib_contracts/iterator.rs provide the foundation

### Claude's Discretion
- Exact cross-crate MIR traversal implementation for discovering external generic call sites
- SMT encoding strategy for Mutex/RwLock guard scope detection (region-based vs statement-based)
- Specific common From impls to include as builtin contracts (e.g., From<io::Error> for Box<dyn Error>)
- Iterator adapter contract composition SMT encoding details
- Test fixture design for cross-crate generic scenarios

</decisions>

<code_context>
## Existing Code Insights

### Reusable Assets
- `MonomorphizationRegistry` + `populate_monomorphization_registry`: Phase 44/v0.7 infrastructure for local generic instantiation tracking — extend for cross-crate
- `ContractDatabase`: JSON-based cross-crate contract storage with lookup by DefId — integration point for generic contract resolution
- `needs_null_check()` in vcgen.rs: Controls null-check VC generation — add NonNull type check here
- `generate_null_check_assertion()` in heap_model.rs: Null-check VC building — skip when Ty::NonNull
- Concurrency module (`happens_before.rs`, `thread_encoding.rs`): Thread interleaving + data race detection infrastructure — reuse for static mut VCs
- Stdlib contracts (`iterator.rs`): Existing map/filter contract registration with `register_map()`, `register_filter()` — extend for composition
- `generate_vcs_monomorphized` in vcgen.rs: Production monomorphization path already activated in v0.7
- V060/V061 opaque callee diagnostics from Phase 37 — reuse for uncontracted cross-crate generics
- `UnsafeOperation` enum + scanning in vcgen.rs: Existing unsafe operation detection pattern — extend for static mut access

### Established Patterns
- ADT DefId matching: Used for Option, Result, Vec detection in stdlib contracts — same pattern for NonNull detection
- VcKind-based diagnostics: Each safety property gets its own VcKind + diagnostic code (V060-V091) — continue with V100 series
- Per-function VC generation: `generate_vcs_with_db` accepts ContractDatabase for inter-procedural reasoning — extend for From::from contracts
- Substitution-based monomorphization: GenericParam → concrete Ty mapping applied during VCGen — extend for cross-crate

### Integration Points
- `ir.rs`: Add `Ty::NonNull(Box<Ty>)` variant
- `mir_converter.rs`: Detect NonNull ADT type and emit Ty::NonNull; detect static mut places
- `vcgen.rs`: Skip null/alignment VCs for Ty::NonNull; generate DataRaceFreedom VCs for static mut; compose iterator adapter VCs; propagate From::from postconditions at ? sites
- `callbacks.rs`: Wire cross-crate monomorphization registry population with external DefId scanning
- `stdlib_contracts/`: Add From::from contracts module; extend iterator adapter composition
- `diagnostics.rs`: Add V100 DataRaceFreedom diagnostic for mutable statics

</code_context>

<specifics>
## Specific Ideas

- Cross-crate registry extends existing local-only `populate_monomorphization_registry` — not a new mechanism, just broader MIR scanning scope
- NonNull suppresses both null AND alignment VCs (user explicitly chose this over null-only)
- NonNull guarantee propagates through as_ptr() cast to reduce false positives on resulting raw pointers
- From::from contracts are BOTH builtin (stdlib) AND user-annotatable — dual source
- ? operator detection uses structural MIR pattern matching, not just any From::from call
- Identity From<T> for T is detected and skipped (no trivial UNSAT VCs)
- Mutable static VCs use V100 series (separate from V070 concurrency codes and V090 borrow codes)

</specifics>

<deferred>
## Deferred Ideas

None — discussion stayed within phase scope

</deferred>

---

*Phase: 49-cross-crate-interop-completeness*
*Context gathered: 2026-03-05*
