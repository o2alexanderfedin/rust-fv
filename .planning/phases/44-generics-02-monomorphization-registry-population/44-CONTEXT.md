# Phase 44: GENERICS-02 MonomorphizationRegistry Population - Context

**Gathered:** 2026-03-03
**Status:** Ready for planning

<domain>
## Phase Boundary

Implement call-site type analysis in `callbacks.rs` during `after_analysis` (while TyCtxt is live) to populate `MonomorphizationRegistry` with concrete type substitutions (e.g., T→i32) from rustc MIR. Activates the `generate_vcs_monomorphized` production path in `parallel.rs` so generic functions are verified against concrete instantiations in addition to the parametric axiom path. All user discussion deferred to Claude's discretion — this is pure infrastructure.

</domain>

<decisions>
## Implementation Decisions

### Registry Architecture
- Build a **single shared registry** once during `after_analysis` before creating `VerificationTask`s
- All functions in the crate share one registry populated from all call sites
- Each `VerificationTask` receives an `Arc<MonomorphizationRegistry>` clone (already the pattern at `callbacks.rs:730`)
- Replace `MonomorphizationRegistry::new()` per-task with the shared pre-populated registry

### MIR Traversal Approach
- Traverse MIR **terminators** for all `hir_body_owners()` in the crate
- For each `TerminatorKind::Call { func, args, .. }`:
  - Resolve the callee `DefId` and name via `tcx.def_path_str()`
  - Extract `GenericArgs` from the call (via `Instance::resolve` or direct substs on the operand)
  - Map generic param names (from `tcx.generics_of(callee_def_id)`) to concrete resolved types
  - Convert resolved `rustc_middle::ty::Ty` → our `ir::Ty` via the existing `convert_ty` helper
- Skip callee if it has no generic params (`tcx.generics_of(id).params.is_empty()`)

### Unresolvable Type Handling
- If a generic arg can't be resolved to a concrete type (e.g., it's still a `ty::Param` because the caller is itself generic), **skip that instantiation silently** — do not add to registry
- Log skipped sites at `tracing::debug!` level: `"Skipping unresolvable generic instantiation: {callee} in {caller}"`
- Partial resolution (some params resolved, some not) → skip the whole instantiation
- This preserves soundness: parametric axiom path (Phase 40) remains the fallback for unresolvable cases

### Multiple Instantiations
- A generic function called with different concrete types (e.g., `max::<i32>` and `max::<u64>`) gets **both** registered — one `TypeInstantiation` per unique substitution set
- Dedup: if the same concrete substitution appears multiple times (same caller or different callers), register only once per function (compare `substitutions` HashMap equality)

### Claude's Discretion
- Exact rustc API calls for extracting `GenericArgs` from MIR call terminators
- Whether to use `Instance::resolve` vs direct substs extraction
- Internal helper function naming and placement (likely a new `populate_monomorphization_registry` function in `callbacks.rs`)
- Error handling for rustc API failures (use `unwrap_or_else` / `continue`)

</decisions>

<specifics>
## Specific Ideas

No specific user requirements — open to standard approaches.

Key invariant to preserve: the **parametric axiom path must remain the fallback** when the registry has no instantiations for a function. The routing logic in `parallel.rs:269-300` already implements this correctly — don't touch it.

The E2E test in `crates/driver/tests/generics_driver_e2e.rs` already has:
- `generic_function_with_empty_generic_params_still_verifies` — fallback path
- `monomorphized_path_fires_when_registry_has_instantiation` — manually populated registry

Phase 44 must make the **production driver** (via `callbacks.rs`) automatically populate the registry so the test `generic_ir_function_produces_nonempty_results_when_generic_params_populated` is also satisfied via the real pipeline.

</specifics>

<code_context>
## Existing Code Insights

### Reusable Assets
- `convert_ty()` in `mir_converter.rs`: existing helper to convert `rustc_middle::ty::Ty` → `ir::Ty` — reuse for type substitution mapping
- `MonomorphizationRegistry::register()` in `monomorphize.rs`: existing API for populating registry
- `TypeInstantiation::new()` in `monomorphize.rs`: existing struct for a single concrete substitution set
- `hir_body_owners()` loop at `callbacks.rs:538`: existing pattern for iterating all local functions

### Established Patterns
- All TyCtxt queries happen in `after_analysis` before parallelization — same pattern applies here
- `tcx.optimized_mir(def_id)` at `callbacks.rs:555`: existing pattern for getting MIR per function
- `Arc<T>` cloning for sharing data across `VerificationTask`s — existing pattern at `callbacks.rs:730`
- `tracing::debug!` for internal routing decisions — established in `parallel.rs:282`

### Integration Points
- `callbacks.rs:730`: Replace `MonomorphizationRegistry::new()` with clone of shared pre-populated registry
- New function: `populate_monomorphization_registry(tcx, &mut registry)` called during `after_analysis` before task creation loop
- MIR terminators accessible via `mir.basic_blocks[bb].terminator()` — same `mir` already fetched at `callbacks.rs:555`

</code_context>

<deferred>
## Deferred Ideas

None — discussion stayed within phase scope.

</deferred>

---

*Phase: 44-generics-02-monomorphization-registry-population*
*Context gathered: 2026-03-03*
