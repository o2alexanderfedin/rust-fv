# Phase 36: Summary Contract Inference - Context

**Gathered:** 2026-02-28
**Status:** Ready for planning

<domain>
## Phase Boundary

Users can annotate an uncontracted callee with `#[verifier::infer_summary]` and `cargo verify` auto-generates a minimal read/write effect contract for it. The inferred contract suppresses the V060-series diagnostic for that callee (it is no longer "uncontracted"), and is visible in `--output-format=json` output. Creating contracts manually, and verifying recursive cycles, are separate phases.

</domain>

<decisions>
## Implementation Decisions

### Inference strategy
- Conservative "assume pure" approach: infer that the callee reads nothing and writes nothing (no side-effect contract)
- This is the minimal contract — soundness is not guaranteed but it is the least-surprise default
- More precise param-type-driven inference (inspect &mut / raw pointer params) is deferred to a future phase

### Attribute placement
- `#[verifier::infer_summary]` is placed on the callee function itself, following the same pattern as `#[trusted]` in the macros crate
- Call-site override placement is not supported in this phase

### Suppression mechanism
- Inference populates the `contract_db` (or equivalent lookup) before VC generation runs
- When `generate_call_site_vcs` encounters the callee, it already has an inferred contract and does NOT emit `VcKind::OpaqueCallee` or `VcKind::OpaqueCalleeUnsafe`
- The existing deduplication guard in `vcgen.rs:2370` is unaffected — suppression is upstream, not a filter

### JSON output shape
- A new optional top-level field `inferred_summaries` is added to `JsonVerificationReport` (in `json_output.rs`)
- Each entry records: callee name, inferred contract text (e.g., "pure: reads nothing, writes nothing")
- Field is omitted when empty (`#[serde(skip_serializing_if = "Option::is_none")]`)
- `JsonFunctionResult` and `JsonFailure` are unchanged — inferred contracts are a report-level concern, not a per-failure concern

### Claude's Discretion
- Exact Rust struct names and field names for `inferred_summaries` in `json_output.rs`
- Whether the `InferredSummary` is stored in the existing `Contracts` struct (as a flag/variant) or as a separate field on `Function` in `ir.rs`
- The exact SMT encoding of the "pure" inferred contract (empty contract, or explicit `(assert true)` no-op assertions)
- How `#[verifier::infer_summary]` is parsed in the macros crate (proc-macro vs. attribute helper)
- Whether the macro embeds the annotation as a doc comment (like `#[requires]`) or via a separate mechanism

</decisions>

<specifics>
## Specific Ideas

- The inferred summary should make the V060 diagnostic disappear entirely — users should see no warning for annotated callees
- The JSON output must be stable enough for tooling to inspect; field naming should be consistent with existing `vc_kind`, `description` patterns in `JsonFailure`

</specifics>

<code_context>
## Existing Code Insights

### Reusable Assets
- `VcKind::OpaqueCallee` / `VcKind::OpaqueCalleeUnsafe` in `vcgen.rs`: Phase 35 additions that Phase 36 must suppress
- `diagnostics.rs::suggest_fix` for OpaqueCallee: currently suggests "Add `#[requires]`" — Phase 36 provides an alternative path
- `Contracts` struct in `ir.rs:479`: existing place to flag a function's contract state; may need an `is_inferred` bool or similar
- `JsonVerificationReport` in `json_output.rs`: already Serialize/Deserialize — adding a new optional field is low-risk
- `#[trusted]` proc-macro in `crates/macros/src/lib.rs:177`: establishes the pattern for `verifier::*` attribute macros

### Established Patterns
- Attribute macros embed annotations as hidden doc comments (`///`) on the item — `infer_summary` should follow this pattern
- Contract lookup happens in `vcgen.rs` before VC emission — inference must populate the lookup table before this point
- `#[serde(skip_serializing_if = "Option::is_none")]` is the established pattern for optional JSON fields

### Integration Points
- `vcgen.rs::generate_call_site_vcs` (around line 2370): the deduplication/OpaqueCallee emission path that inference suppresses
- `callbacks.rs` (driver): where `contract_db` / function contracts are assembled before passing to vcgen
- `json_output.rs::JsonVerificationReport`: where the new `inferred_summaries` field is added
- `crates/macros/src/lib.rs`: where `#[verifier::infer_summary]` proc-macro is registered

</code_context>

<deferred>
## Deferred Ideas

- Param-type-driven inference (inspecting &mut / raw pointer parameters for read/write effect classification) — future phase
- Call-site placement of `#[verifier::infer_summary]` (override at the call site rather than the callee) — future phase
- Sound inference via body-scan (scanning the callee MIR for memory operations) — requires deeper MIR access, future phase

</deferred>

---

*Phase: 36-summary-contract-inference*
*Context gathered: 2026-02-28*
