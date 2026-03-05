# Phase 47: MIR Coverage Hardening - Context

**Gathered:** 2026-03-05
**Status:** Ready for planning

<domain>
## Phase Boundary

All pointer alignment casts generate safety VCs, CastKind variants are unambiguously encoded, ambiguous match arms are documented, and spec errors surface as rustc diagnostics. Four concrete deliverables: COMPL-02 (pointer alignment VCs), COMPL-03 (CastKind disambiguation), COMPL-06 (spec validation diagnostics), COMPL-12 (match arm fallthrough audit).

</domain>

<decisions>
## Implementation Decisions

### Alignment VC Scope
- ALL PtrToPtr casts generate alignment VCs, not just when alignment increases
- VC assertion shape: `addr % align_of::<TargetType>() == 0` (target alignment only, no source-to-target comparison)
- New `VcKind::AlignmentSafety` variant (distinct from MemorySafety) for precise diagnostic classification
- V070 error code series for pointer alignment violations (06x=callee, 07x=pointer safety)

### CastKind Encoding Split
- Rename `CastKind::Pointer` to `CastKind::PtrToPtr` to match success criterion naming
- Keep `FloatToFloat` variant (valid MIR cast kind, even though not in success criterion's 4-variant list)
- Final enum: IntToInt, IntToFloat, FloatToInt, FloatToFloat, PtrToPtr
- PtrToPtr's distinct SMT shape: returns src (identity) + emits side-effect alignment VC — only cast kind with a MemorySafety/AlignmentSafety side-condition
- Unit tests use BOTH structural Term comparison AND SMT-LIB string snapshot for regression

### Spec Error Recovery
- Emit `error[V080]` at annotation source span for syntactically invalid `#[requires(...)]` expressions
- Skip ONLY the broken annotation; continue verifying the function with code-inferred VCs and any remaining valid contracts
- Annotations are optional — code AST is primary source of VCs; broken annotation must not block code-level verification
- Include fix suggestions in diagnostics where a likely correction can be inferred (matching rustc experience)
- V080 series for spec validation errors (06x=callee, 07x=pointer safety, 08x=spec validation)

### Match Arm Documentation
- Inline doc-comments (`/// Intentionally no VC: [reason]`) directly above each skipped arm in vcgen.rs AND encode_term.rs
- Centralized audit table as module-level doc-comment (`//!`) at the top of vcgen.rs
- Additionally, a formal AUDIT.md record in `.planning/phases/47-*/` for the phase record
- Replace wildcard catch-all arms with explicit variant listings where practical (compiler enforces completeness on API changes)
- For large variant sets where explicit listing causes excessive churn, document the catch-all with the full list of covered variants
- Audit scope: vcgen.rs + encode_term.rs (both files in the VC generation pipeline)

### Claude's Discretion
- Exact alignment arithmetic encoding in SMT (modulo operation implementation details)
- Spec parse error suggestion heuristics (how to detect likely corrections)
- Audit table format details (column headers, grouping)
- Test fixture design for alignment VCs (synthetic IR structure)

</decisions>

<code_context>
## Existing Code Insights

### Reusable Assets
- `CastKind` enum (`ir.rs:839-850`): Currently has IntToInt, IntToFloat, FloatToInt, FloatToFloat, Pointer — Pointer to be renamed PtrToPtr
- `encode_cast()` (`encode_term.rs:718-734`): Dispatch function matching on CastKind — perfect integration point for alignment VCs
- `VcKind::MemorySafety` (`vcgen.rs:116`): Established VC classification — model for new AlignmentSafety variant
- `UnsafeOperation::PtrCast` (`ir.rs:162-186`): Already tracks pointer cast provenance in IR — can feed alignment info
- Diagnostic infrastructure (`diagnostics.rs`): Ariadne-based reporting with V-style codes (V060-V062) — extend with V070, V080
- `spec_parser.rs:parse_spec_expr()`: Already returns `Option<Term>` (None = parse failure) — wire to diagnostic emitter
- E2E test framework (`e2e_verification.rs`): Proven pattern from Phase 46-03 (IsTester) — template for alignment VC tests

### Established Patterns
- Rvalue encoding dispatch: match on variant, delegate to specialized encoder (encode_term.rs)
- VcKind-based diagnostics: diagnostics.rs keys report severity on vc_kind
- Exhaustive matching without wildcards: Phase 29 pattern, compiler enforces completeness
- Phase 46-03 IsTester integration: exact template for adding new Term variants + SwitchInt wiring + E2E tests

### Integration Points
- `encode_term.rs::encode_cast()` line 718: Add alignment VC generation for PtrToPtr
- `vcgen.rs::encode_rvalue_for_assignment()` line 1689: Already calls encode_cast, will pick up changes
- `diagnostics.rs`: Add V070 (AlignmentSafety) and V080 (SpecValidation) error code handling
- `spec_parser.rs`: Wire parse failures to diagnostic emitter instead of returning None silently

</code_context>

<specifics>
## Specific Ideas

- PtrToPtr is the ONLY cast kind that generates a side-effect safety VC — this is its distinguishing SMT "shape"
- Alignment assertion shape: `(assert (= (mod addr align) 0))` in QF_LIA
- Follow Phase 46-03 IsTester pattern exactly for new VcKind variant integration
- Both structural Term tests AND SMT-LIB snapshot tests for CastKind disambiguation (belt and suspenders)
- Module-level audit table in vcgen.rs serves as living documentation; AUDIT.md in .planning/ serves as phase record

</specifics>

<deferred>
## Deferred Ideas

None — discussion stayed within phase scope

</deferred>

---

*Phase: 47-mir-coverage-hardening*
*Context gathered: 2026-03-05*
