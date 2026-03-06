# Phase 48: Advanced Ownership & Borrows - Context

**Gathered:** 2026-03-05
**Status:** Ready for planning

<domain>
## Phase Boundary

Model RefCell interior mutability as ghost state, two-phase borrows with reservation/activation semantics, per-field partial move tracking with use-after-partial-move VCs, disjoint borrow splitting for struct fields, and trigger inference filtering to exclude datatype symbols. Five requirements: COMPL-08, COMPL-09, COMPL-13, COMPL-14, COMPL-16.

</domain>

<decisions>
## Implementation Decisions

### RefCell Ghost State (COMPL-09)
- Integer counter model: `borrow_count : Int` + `is_mut_borrowed : Bool` per RefCell-typed local
- Per-local ghost variables declared in SMT preamble (following prophecy variable pattern from ir.rs ProphecyInfo)
- `borrow()` asserts `!is_mut_borrowed`, increments `borrow_count`; `borrow_mut()` asserts `borrow_count == 0`, sets `is_mut_borrowed = true`
- Drop of Ref decrements counter; drop of RefMut clears flag
- Generate `VcKind::BorrowConflict` VCs (SAT = would panic at runtime)
- V090 error code series for borrow conflicts
- Model the FULL RefCell API: borrow, borrow_mut, try_borrow, try_borrow_mut, into_inner, replace, swap
- Contract violation model (not runtime panic modeling) — consistent with other VC patterns

### Partial Struct Moves (COMPL-14)
- Per-field boolean map: `HashMap<(LocalId, FieldIdx), Bool>` tracking moved/available state
- New `VcKind::UseAfterPartialMove` with V091 error code
- Full nested tracking: s.inner.x moved while s.inner.y still available (recursive field state at arbitrary projection depth)
- Diagnostic shows which field was moved and where

### Borrow Splitting (COMPL-16)
- Field-index disjointness assertion: different Projection::Field indices of the same struct don't conflict
- &mut s.x and &s.y simultaneously: assert field indices differ, no BorrowConflict VC generated
- &mut s.x and &s.x: same field, generate BorrowConflict VC
- Leverages existing BorrowInfo + Projection::Field infrastructure

### Two-Phase Borrows (COMPL-13)
- Reservation window pattern: `BorrowPhase` enum (Reserved/Activated) added to BorrowInfo
- Detection via MIR `BorrowKind::Mut { kind: TwoPhaseBorrow }` flag in mir_converter.rs
- Reserved borrows don't conflict with shared borrows; activation at call site Terminator
- Failed activation reuses `VcKind::BorrowConflict` (V090) with "two-phase borrow conflict" diagnostic message
- Full nesting support: track reservation phase through closure captures and nested calls

### Trigger Inference Filtering (COMPL-08)
- Structural recognition of datatype symbols (not manual blocklist): match Term::App name patterns for selectors, constructors, testers
- Filter ALL datatype symbols: selectors (Struct-field0), constructors (mk-Struct), and testers (is-Variant)
- Hardcoded filter (no config flag) — success criterion is absolute
- When filtering removes all candidates: generate spec-level wrapper trigger function (synthetic trigger wrapping the selector access)
- Only user-defined or spec-level symbols remain in filtered candidate list

### Claude's Discretion
- Exact SMT encoding for RefCell ghost state transitions
- Recursive field state tracking implementation details for nested partial moves
- Specific naming pattern for synthetic wrapper triggers
- Test fixture design for two-phase borrow closure nesting
- Diagnostic message wording for each new VcKind

</decisions>

<code_context>
## Existing Code Insights

### Reusable Assets
- `BorrowInfo` (`ir.rs:105-129`): Already tracks local name, region, mutability — extend with BorrowPhase field
- `ReborrowChain` (`ir.rs`): Models original->reborrow dependencies — useful for nesting
- `borrow_conflict.rs` (160 lines): BorrowConflict detection with live-range intersections — extend for two-phase and field-level
- `sep_logic.rs` (260 lines): Permission array + heap array model — spatial separation already works
- `ownership.rs` (110 lines): Argument classification + ownership constraints — integration point
- `encode_quantifier.rs` (2078 lines): Trigger inference with `infer_triggers()` + `annotate_quantifier()` — add filter step
- `Projection::Field(usize)` + `Projection::Downcast(usize)` in ir.rs — field-level tracking infrastructure
- `build_functional_update()` in vcgen.rs (lines 2044-2166): Struct field updates via selectors
- `ProphecyInfo` in ir.rs (lines 562-583): Pattern for per-local ghost variable declarations
- `ghost_predicate_db.rs` (80 lines): Ghost predicate registry — NOT used for RefCell (per-local pattern instead)

### Established Patterns
- Per-local ghost variables: ProphecyInfo declares dual vars (initial + prophecy) per &mut — same pattern for RefCell ghost state
- Projection chain resolution: encode_term.rs flattens Projection::Field chains to typed selector chains
- VcKind-based diagnostics: Each safety property gets its own VcKind + diagnostic code (V060-V091)
- MIR-to-IR conversion: mir_converter.rs reads MIR flags and populates IR structs — extend for BorrowPhase
- Exhaustive matching: Phase 47 audit ensures all new enum variants are handled everywhere

### Integration Points
- `ir.rs`: Add RefCellGhostState struct, BorrowPhase enum, extend BorrowInfo with phase field
- `mir_converter.rs`: Read TwoPhaseBorrow MIR flag, populate BorrowPhase::Reserved
- `vcgen.rs`: Generate BorrowConflict VCs for RefCell + partial moves + field borrows
- `borrow_conflict.rs`: Extend conflict detection for two-phase reservation and field-level disjointness
- `encode_quantifier.rs`: Add is_datatype_symbol filter in find_trigger_candidates or infer_triggers
- `diagnostics.rs`: Add V090 (BorrowConflict), V091 (UseAfterPartialMove) error codes
- `callbacks.rs`: Wire new VcKind variants to diagnostic strings

</code_context>

<specifics>
## Specific Ideas

- RefCell ghost state follows ProphecyInfo pattern: per-local declarations in SMT preamble with initial values
- Two-phase detection must use MIR's own BorrowKind::Mut { kind: TwoPhaseBorrow } flag — not heuristic detection
- Trigger filter is structural (name pattern matching), not a manual blocklist — adapts to new types automatically
- Nested partial move tracking requires recursive HashMap key structure: (LocalId, Vec<FieldIdx>) for arbitrary depth
- All five requirements produce distinct, testable VCs with Z3-checkable assertions
- V090 for BorrowConflict (both RefCell and two-phase), V091 for UseAfterPartialMove — consistent diagnostic numbering

</specifics>

<deferred>
## Deferred Ideas

None — discussion stayed within phase scope

</deferred>

---

*Phase: 48-advanced-ownership-borrows*
*Context gathered: 2026-03-05*
