# Phase 35: Opaque Callee Diagnostics - Context

**Gathered:** 2026-02-28
**Status:** Ready for planning

<domain>
## Phase Boundary

Replace the silent `continue` at `vcgen.rs:2375` (when `contract_db.get()` returns `None` for a callee) with observable diagnostics — a V060-series warning for uncontracted callees in safe context, escalated to an error when the call occurs in an unsafe context. No suppression mechanism in this phase (OPAQUE-03, phase 36, adds `#[verifier::infer_summary]`).

</domain>

<decisions>
## Implementation Decisions

### Diagnostic mechanism
- Use the **always-SAT VC pattern** — emit a `VerificationCondition` with `Term::BoolLit(true)` and `Command::CheckSat` from `generate_call_site_vcs`, not a side-effect `eprintln!`/`tracing::warn!`
- This keeps the diagnostic inside the VC pipeline, making it testable by filtering `result.conditions` on `VcKind` — consistent with the concurrency warning and unsafe_no_contracts patterns
- Add **two new `VcKind` variants**:
  - `VcKind::OpaqueCallee` → renders as `warning[V060]` in `diagnostics.rs`
  - `VcKind::OpaqueCalleeUnsafe` → renders as `error[V061]` in `diagnostics.rs`
- Severity dispatch in `diagnostics.rs` adds `OpaqueCallee` to the warning branch, `OpaqueCalleeUnsafe` to the error branch

### Unsafe escalation scope
- A call is "in unsafe context" if **either** holds:
  - `func.is_unsafe_fn == true` (the entire caller function is `unsafe fn`)
  - `call_site.block_idx` matches any `func.unsafe_blocks[i].block_index`
- Use `OpaqueCalleeUnsafe` when either condition is met; `OpaqueCallee` otherwise
- This is the most precise check — single unsafe block inside a safe fn escalates only that call

### Warning message content (V060)
- Format: `"opaque callee: call to '{callee}' in '{caller}' has no verification contract — callee behavior is unverified"`
- Contract text (shown in ariadne label): `"Add #[requires] / #[ensures] to '{callee}' to enable cross-function verification"`
- V060 for warning, V061 for error (unsafe variant)

### Suppression / opt-out
- **No suppression in this phase** — OPAQUE-03 (phase 36) adds `#[verifier::infer_summary]`; a future phase may add `#[verifier::trust_callee]`
- The diagnostic fires for every uncontracted callee encountered during `generate_call_site_vcs`

### Claude's Discretion
- Exact placement within `generate_call_site_vcs` (replace the `None => { continue }` arm entirely)
- Whether to deduplicate diagnostics for repeated calls to the same callee within one function (dedup is nice-to-have — Claude decides)
- Source location field population on the VC (use `call_site.block_idx` to populate `block` field; `source_file`/`source_line` left `None` if not available from `CallSiteInfo`)

</decisions>

<code_context>
## Existing Code Insights

### Reusable Assets
- `always_sat_script()` helper pattern (inline in vcgen.rs): `Script::new()` → `SetLogic("QF_BV")` → `Assert(Term::BoolLit(true))` → `CheckSat` — used for DataRaceFreedom concurrency warning and can be extracted/reused
- `VcLocation` struct: carries `function`, `block`, `statement`, `source_file`, `source_line`, `source_column`, `contract_text`, `vc_kind` — all needed for the diagnostic VC
- `generate_call_site_vcs` signature at `vcgen.rs:2357`: `func: &Function`, `contract_db: &ContractDatabase`, `paths: &[CfgPath]`, `ghost_pred_db: &GhostPredicateDatabase` — `func.is_unsafe_fn` and `func.unsafe_blocks` are directly available

### Established Patterns
- **Always-SAT VC pattern** for non-falsifiable diagnostics: `Term::BoolLit(true)`, `Command::CheckSat` — solver returns SAT, driver maps SAT to "diagnostic fired" rather than "property violated"
- **VcKind-based severity dispatch** in `diagnostics.rs:78-85`: `if vc_kind == VcKind::MemorySafety || vc_kind == VcKind::FloatingPointNaN || vc_kind == VcKind::Deadlock { ReportKind::Warning } else { ReportKind::Error }` — add `OpaqueCallee` to this condition
- **Existing warning codes**: V001 (divergence), V002 (encoding), V003 (bv2int eligibility), V015-V018 (trigger validation) — V060/V061 are available

### Integration Points
- `generate_call_site_vcs` → replace `None => { tracing::debug!(...); continue; }` with diagnostic VC emission + continue
- `VcKind` enum in `vcgen.rs:86` → add two new variants: `OpaqueCallee`, `OpaqueCalleeUnsafe`
- `diagnostics.rs` severity dispatch (line ~78) → add `OpaqueCallee` to warning branch
- `diagnostics.rs` `report_verification_failure` or `suggest_fix` → add V060/V061 message and suggestion text
- `callbacks.rs` `report_verification_failure` call at line ~291 → no change needed (flows through existing path)

</code_context>

<specifics>
## Specific Ideas

- The REQUIREMENTS spec says "V060–V069" for the OPAQUE-01 range — use V060 for safe-callee warning, V061 for unsafe-callee error; leave V062-V069 reserved for future OPAQUE expansion
- The always-SAT VC means the solver will return SAT for this VC — the driver must NOT count SAT as a "verification failure" for OpaqueCallee (warning-only); it must count it as a "diagnostic" emitted. Check how the DataRaceFreedom always-SAT VC is handled in `callbacks.rs` to replicate that handling for OpaqueCallee

</specifics>

<deferred>
## Deferred Ideas

- `#[verifier::trust_callee]` suppression attribute — future phase (not OPAQUE-03 either, which is about inference)
- Deduplication of repeated opaque-callee warnings for the same callee within one function — nice-to-have, Claude decides
- Per-call-site source location annotation in the ariadne output — requires `CallSiteInfo` to carry source line info (not present today)

</deferred>

---

*Phase: 35-opaque-callee-diagnostics*
*Context gathered: 2026-02-28*
