# Phase 30: SetDiscriminant VCGen Implementation - Context

**Gathered:** 2026-02-26
**Status:** Ready for planning

<domain>
## Phase Boundary

Add `ir::Statement::SetDiscriminant` to the IR and emit discriminant assertion VCs in `vcgen.rs`. This closes VCGEN-06 and MIRCONV-02 from partial to fully satisfied. Scope is limited to the basic SetDiscriminant statement: IR variant definition, MIR→IR lowering, and VC emission. Match/arm reasoning and advanced ADT patterns are out of scope.

</domain>

<decisions>
## Implementation Decisions

### Discriminant VC assertion form
- Integer equality form: `discriminant(place) == variant_index` (not symbolic/typed)
- Emitted as an inline assertion VC at the SetDiscriminant statement site
- Hard assert (checked VC — must prove discriminant is set correctly), not an assumption
- `variant_index` uses the raw integer index from MIR (`VariantIdx` as integer), not symbolic variant names

### Test coverage breadth
- Un-ignore `vcgen_06_set_discriminant_assertion` only — sufficient for phase closure per ROADMAP
- TDD RED test in plan 30-01: write BOTH a unit test (IR construction) AND an integration test (full MIR→IR→VCGen pipeline)
- Test assertions use contains-check: verify VC output contains `discriminant` and the variant index (not exact string match)

### Edge case handling
- Unit variants (no fields): handle in-scope — same VCGen path applies
- Single-variant ADTs: handle in-scope — integer equality VC applies naturally, no special-casing
- Out-of-range variant_index: `panic!` / `unreachable!` — IR is internal, malformed IR is a compiler bug
- Nested discriminants (place projections): handle in-scope if they arise naturally from MIR lowering; do not artificially block

### IR variant fields
- `SetDiscriminant { place: Place, variant_index: VariantIdx, adt_def: &'tcx AdtDef }`
- Include `AdtDef` for type info (needed for richer VC context even with integer equality form)
- Use `rustc_target::abi::VariantIdx` directly — no newtype wrapper
- `AdtDef` stored as `&'tcx AdtDef` reference (lifetime-bound, consistent with rustc TyCtxt interning)
- Implement `derive(Debug)` + manual `Display` for readable output like `SetDiscriminant(place, 1)`

### Claude's Discretion
- Exact `Display` format string
- Whether `AdtDef` is used in the VC emission or only carried for future use
- Exact test fixture construction for the RED test
- How to thread `&'tcx AdtDef` through the MIR→IR conversion (check existing conversion patterns)

</decisions>

<specifics>
## Specific Ideas

- The VC should look like: `assert discriminant(place) == 1` (or equivalent integer assertion)
- Follow the exact pattern that other `Statement` arms use in `vcgen.rs` for VC emission
- The `vcgen_06` test un-ignore in plan 30-03 is the final gate — full test suite must be GREEN

</specifics>

<deferred>
## Deferred Ideas

None — discussion stayed within phase scope

</deferred>

---

*Phase: 30-set-discriminant-vcgen*
*Context gathered: 2026-02-26*
