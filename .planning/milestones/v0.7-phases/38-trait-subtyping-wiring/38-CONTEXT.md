# Phase 38: Trait Subtyping Wiring - Context

**Gathered:** 2026-03-01
**Status:** Ready for planning

<domain>
## Phase Boundary

Wire `generate_subtyping_vcs` (fully implemented in `behavioral_subtyping.rs`) into the driver's `after_analysis` pipeline so behavioral subtyping VCs are submitted to Z3 for every trait impl annotated with `#[requires]`/`#[ensures]`. Closes TRT-01..05 gap from vAll cross-milestone audit.

This phase does NOT add new behavioral subtyping logic — the encoding, VC generation, and VcKind::BehavioralSubtyping diagnostic support already exist. The only work is connecting the existing island to the live pipeline.

</domain>

<decisions>
## Implementation Decisions

### Claude's Discretion

All implementation strategy decisions are delegated to Claude:

- **Pipeline insertion point**: Where subtyping VCs enter the pipeline (directly in callbacks.rs vs. through vcgen.rs). Prefer consistency with how similar VC kinds (float, async, expiry) are wired.
- **Trait/impl discovery**: How to identify trait impls with contracts at `after_analysis` time (scan HIR for `impl Trait for Type`, build TraitDatabase from contracts_map, or use rustc's `all_local_trait_impls`). Use whichever approach is most idiomatic with existing rustc callback patterns.
- **Parallel vs. sequential execution**: Whether subtyping VCs go through the parallel.rs worker pool or run sequentially. Follow existing patterns — if other secondary VC kinds use the pool, do the same.
- **TraitDatabase population**: How to populate `TraitDatabase` with HIR-extracted trait defs and impls. The struct already exists in `trait_analysis.rs`.
- **Output/diagnostics**: Use `VcKind::BehavioralSubtyping` (already defined in vcgen.rs and diagnostics.rs) for result reporting.
- **Error handling**: Follow existing conventions — skip on extraction failure, don't panic.

</decisions>

<code_context>
## Existing Code Insights

### Reusable Assets

- `generate_subtyping_vcs` (`behavioral_subtyping.rs:40`): Fully implemented, returns `Vec<SubtypingVc>`. Ready to call.
- `generate_subtyping_script` (`behavioral_subtyping.rs`): Converts SubtypingVcs to SMT-LIB scripts. Ready to use.
- `TraitDatabase` (`trait_analysis.rs`): Exists with `register_trait`, `register_impl`, `get_trait`, `get_impls`.
- `VcKind::BehavioralSubtyping` (`vcgen.rs`, `diagnostics.rs`): Already defined and mapped to `"behavioral_subtyping"` string.
- `Z3SolverAdapter` (`callbacks.rs`): Wraps Z3 solver, implements `SolverInterface`.
- `contracts_map` (built in `after_analysis`): Already maps `LocalDefId` → HIR contracts for all annotated functions.

### Established Patterns

- `after_analysis` in `callbacks.rs` is the primary integration site. It already:
  1. Extracts contracts from HIR (`extract_contracts`)
  2. Builds `contract_db`
  3. Iterates `tcx.hir_body_owners()` to find functions with contracts
  4. Converts to IR and collects `func_infos`
  5. Runs parallel verification

- Other secondary VC generators (float, async, expiry, termination, hof) are called inside `vcgen.rs::generate_vcs_with_mode`, not directly in callbacks.

- The parallel worker receives a `VerificationTask` struct — if subtyping VCs follow this path, they need to fit into that struct or use a separate sequential path.

- Trait impls in rustc HIR: `tcx.all_local_trait_impls(())` provides all local trait impl blocks. `tcx.impl_trait_ref(def_id)` gives the trait being implemented.

### Integration Points

- `crates/driver/src/callbacks.rs` → `after_analysis` method (~line 390): The insertion point
- `crates/analysis/src/behavioral_subtyping.rs` → `generate_subtyping_vcs` and `generate_subtyping_script`: The functions to call
- `crates/analysis/src/trait_analysis.rs` → `TraitDatabase`: Needs to be populated with trait defs + impls extracted from HIR
- `crates/analysis/tests/trait_verification.rs`: Existing unit tests that already test `generate_subtyping_vcs` in isolation — E2E test should complement these with a driver-level integration test

</code_context>

<specifics>
## Specific Ideas

- The audit identifies the exact gap: no call to `generate_subtyping_vcs` exists in `vcgen.rs`, `callbacks.rs`, or `parallel.rs`. The fix adds such a call in the correct location.
- `VcKind::BehavioralSubtyping` is already defined — diagnostics/reporting requires no new work.
- An E2E integration test should demonstrate that a trait impl violating LSP (e.g., stronger precondition than trait) produces a `FAIL` result when running `cargo verify`.
- Per the audit: TRT-01..05 are all blocked on this single wiring. Closing them requires the function to be called and VCs submitted.

</specifics>

<deferred>
## Deferred Ideas

None — discussion stayed within phase scope.

</deferred>

---

*Phase: 38-trait-subtyping-wiring*
*Context gathered: 2026-03-01*
