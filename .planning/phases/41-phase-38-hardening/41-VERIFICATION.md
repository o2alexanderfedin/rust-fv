---
phase: 41-phase-38-hardening
verified: 2026-03-02T00:00:00Z
status: passed
score: 7/7 must-haves verified
re_verification: false
---

# Phase 41: Phase-38-Hardening Verification Report

**Phase Goal:** Implement real sealed trait detection to replace the hardcoded `is_sealed: false`, fix `generate_subtyping_script` to emit proper SMT `declare-fun` statements so Z3 parse errors are no longer silently treated as verified, and wire dynamic dispatch call-site VCs to the behavioral subtyping pipeline.

**Verified:** 2026-03-02T00:00:00Z
**Status:** passed
**Re-verification:** No — initial verification

---

## Goal Achievement

### Observable Truths

| # | Truth | Status | Evidence |
|---|-------|--------|---------|
| 1 | A `pub(crate)` trait is detected as sealed (`TraitDef.is_sealed = true`) in the behavioral subtyping block | VERIFIED | `callbacks.rs:830-855` calls `tcx.visibility(*trait_def_id)`, formats as debug string, calls `detect_sealed_trait(vis_str_normalized, &super_trait_names)`. Unit test `test_sealed_trait_detection_uses_detect_sealed_trait_pub_crate` confirms `detect_sealed_trait("pub(crate)", &[])` returns `true`. |
| 2 | A `pub` trait is detected as open (`TraitDef.is_sealed = false`) | VERIFIED | Same code path; `vis_str.contains("Public")` maps to `"pub"`. Unit test `test_sealed_trait_detection_uses_detect_sealed_trait_pub` confirms `detect_sealed_trait("pub", &[])` returns `false`. |
| 3 | Z3 parse/unknown results in the behavioral subtyping block set `verified = false` (not silently pass) | VERIFIED | `callbacks.rs:903-910`: `_ => { tracing::warn!(..., "Behavioral subtyping Z3 check returned unknown/error — treating as unverified"); false }`. The old `_ => true` arm is gone. Test `test_behavioral_subtyping_z3_catchall_is_pessimistic` asserts presence of warn message. |
| 4 | `generate_subtyping_script` emits proper SMT `declare-fun` statements | VERIFIED | `behavioral_subtyping.rs:137,158`: `Command::DeclareFun(...)` is emitted for each trait predicate before it is used in `Term::App`. Integration tests in `trait_verification.rs` (e.g. `behavioral_subtyping_z3_proves_precondition_weakening_unsat`) confirm Z3 accepts these scripts without parse errors. |
| 5 | A function whose callee is dispatched via `dyn Trait` generates a call-site VC using trait-level contracts instead of OpaqueCallee | VERIFIED | `vcgen.rs:2427-2442`: `parse_dyn_dispatch_callee` called in `None` arm of `contract_db.get()`; suffix-match on `contract_db` resolves `<dyn Stack>::push` → `Stack::push` contract. Integration test `dyn_dispatch_call_site_uses_trait_contracts` passes (1/1). |
| 6 | The trait method contracts in `contract_db` are matched by method name when callee matches `<dyn TraitName>::method` | VERIFIED | `vcgen.rs:2430-2434`: `format!("{dyn_trait_name}::{dyn_method_name}")` as suffix match via `name.contains(&search_suffix)`. Unit tests `test_parse_dyn_dispatch_callee_standard` and `test_parse_dyn_dispatch_callee_as_form` confirm both `<dyn Stack>::push` and `<dyn Stack as Stack>::push` parse correctly. |
| 7 | All existing tests continue to pass | VERIFIED | `cargo test --workspace` — 0 failures. Full output confirms: 1264 analysis lib tests, 14 trait_verification tests, 123 driver tests, all passing. |

**Score:** 7/7 truths verified

---

### Required Artifacts

| Artifact | Expected | Status | Details |
|----------|----------|--------|---------|
| `crates/driver/src/callbacks.rs` | HIR-derived `is_sealed` computation using `detect_sealed_trait` + `tcx.visibility` | VERIFIED | Lines 777, 830-855, 860: imports `detect_sealed_trait`, uses `tcx.visibility(*trait_def_id)`, collects super-trait names via `tcx.explicit_super_predicates_of()`, calls `detect_sealed_trait(vis_str_normalized, &super_trait_names)`. Production `is_sealed: false` literal removed; test-only occurrences remain at lines 1883 and 1938 in `#[cfg(test)]` block. |
| `crates/analysis/src/vcgen.rs` | `parse_dyn_dispatch_callee` helper + dyn dispatch resolution in `generate_call_site_vcs` | VERIFIED | Lines 2197-2208: `parse_dyn_dispatch_callee` function exists. Lines 2427-2442: dyn dispatch resolution wired before OpaqueCallee fallback. Lines 2179-2180: `normalize_callee_name` guard preserves `<dyn ...>` forms intact. |
| `crates/analysis/tests/trait_verification.rs` | Integration test proving dyn dispatch call-site uses trait contracts | VERIFIED | Line 808: `fn dyn_dispatch_call_site_uses_trait_contracts()` exists with full test body. Test passes (confirmed by `cargo test -p rust-fv-analysis --test trait_verification`). |

---

### Key Link Verification

| From | To | Via | Status | Details |
|------|----|-----|--------|---------|
| `callbacks.rs` behavioral subtyping block | `rust_fv_analysis::trait_analysis::detect_sealed_trait` | `tcx.visibility(*trait_def_id)` debug-format heuristic mapped to `&str` | WIRED | Line 777: `use rust_fv_analysis::trait_analysis::{TraitDatabase, detect_sealed_trait}`. Line 855: `let is_sealed = detect_sealed_trait(vis_str_normalized, &super_trait_names)`. Line 860: `is_sealed` passed to `TraitDef`. |
| `callbacks.rs` Z3 result match | `verified = false` on parse/unknown error | `_ => { warn!(...); false }` arm in `SolverResult` match | WIRED | Lines 903-910 confirmed. No `_ => true` arm remains in the behavioral subtyping block. |
| `vcgen.rs generate_call_site_vcs` `call_site.callee_name` | `contract_db` lookup by trait method name | `parse_dyn_dispatch_callee` normalization + suffix-match `name.contains()` | WIRED | Lines 2427-2442 confirmed. `normalize_callee_name` also patched (line 2179) to preserve `<dyn ...>` prefix intact before resolution. |
| `trait_verification.rs` dyn dispatch test | `generate_call_site_vcs` (via `generate_vcs_with_db`) | `Terminator::Call { func: "<dyn Stack>::push", ... }` + `ContractDatabase` with `Stack::push` key | WIRED | Lines 808-909: test builds `caller` function with `<dyn Stack>::push` terminator, inserts `Stack::push` contract in `ContractDatabase`, asserts non-OpaqueCallee VC emitted. |

---

### Requirements Coverage

| Requirement | Source Plan | Description | Status | Evidence |
|-------------|------------|-------------|--------|---------|
| TRT-04 | 41-01-PLAN.md | Sealed traits use closed-world verification — `is_sealed` must be derived from HIR visibility | SATISFIED | Real HIR visibility detection active at `callbacks.rs:828-861`. `detect_sealed_trait` called with real `tcx.visibility` data. Two unit tests validate the `pub`/`pub(crate)` classification logic. |
| TRT-02 | 41-02-PLAN.md | `dyn Trait` call sites use trait-level contracts (not OpaqueCallee) | SATISFIED | `parse_dyn_dispatch_callee` + suffix-match lookup in `generate_call_site_vcs` (`vcgen.rs:2424-2442`). Integration test `dyn_dispatch_call_site_uses_trait_contracts` passes. |

No orphaned requirements found — ROADMAP.md Phase 41 declares exactly TRT-02 and TRT-04, both covered by plans 41-01 and 41-02 respectively.

---

### Anti-Patterns Found

| File | Line | Pattern | Severity | Impact |
|------|------|---------|----------|--------|
| `crates/analysis/src/vcgen.rs` | 3848 | `TODO: In a full implementation...` | Info | Pre-existing comment unrelated to phase 41 scope; not introduced by this phase. No impact on goal achievement. |

No blockers or warnings found in phase 41 modified files.

---

### Human Verification Required

None required. All key behaviors are verifiable programmatically:

- Sealed detection: unit tests directly invoke `detect_sealed_trait` with `pub(crate)` and `pub` inputs and assert correct boolean output.
- Z3 pessimism: source-level test asserts the warn message fragment exists in production code; no TyCtxt needed.
- Dyn dispatch resolution: integration test constructs a full `Function` + `ContractDatabase`, calls `generate_vcs_with_db`, and asserts non-OpaqueCallee VCs are emitted.
- Full workspace test suite: 0 failures across all crates.

---

### Gaps Summary

No gaps. All phase 41 must-haves are satisfied:

1. Real sealed trait detection is live — `is_sealed: false` hardcoding removed from production path in `callbacks.rs`. HIR visibility heuristic (`format!("{vis:?}").contains("Public")`) plus `detect_sealed_trait` are wired end-to-end.

2. Z3 pessimistic catch-all is live — `_ => true` soundness hole removed; replaced with `_ => { tracing::warn!(...); false }` in the behavioral subtyping Z3 result match.

3. `generate_subtyping_script` emits proper `declare-fun` statements — `Command::DeclareFun` precedes every predicate use in `encode_precondition_weakening_vc` and `encode_postcondition_strengthening_vc`. No Z3 parse errors from missing declarations.

4. Dyn dispatch call-site VCs wired to trait-level contracts — `parse_dyn_dispatch_callee` helper + suffix-match lookup bridges `<dyn TraitName>::method` callee names to `contract_db` entries. `normalize_callee_name` patched to preserve `<dyn ...>` prefix. Integration test confirms end-to-end behavior.

5. All workspace tests pass — 0 failures.

---

### Commits Verified

| Commit | Description | Plan |
|--------|-------------|------|
| `bf12fbc` | feat(41-01): replace hardcoded `is_sealed: false` with real HIR visibility detection | 41-01 Task 1 |
| `83db3ee` | fix(41-01): Z3 catch-all in behavioral subtyping block is now pessimistic (false) | 41-01 Task 2 |
| `bd95119` | feat(41-02): add `parse_dyn_dispatch_callee` + dyn dispatch resolution in `generate_call_site_vcs` | 41-02 Task 1 |
| `ff25d1c` | feat(41-02): add `dyn_dispatch_call_site_uses_trait_contracts` integration test + fix `normalize_callee_name` | 41-02 Task 2 |

All four commits confirmed present in git log.

---

_Verified: 2026-03-02T00:00:00Z_
_Verifier: Claude (gsd-verifier)_
