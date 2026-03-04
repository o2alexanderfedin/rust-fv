---
phase: 41-phase-38-hardening
plan: "02"
subsystem: vcgen
tags: [trt-02, dyn-dispatch, trait-contracts, vcgen, integration-test]
dependency_graph:
  requires: [41-01]
  provides: [TRT-02]
  affects: [vcgen.rs generate_call_site_vcs, trait_verification.rs]
tech_stack:
  added: []
  patterns: [dyn-dispatch callee name normalization, suffix-match contract_db lookup]
key_files:
  created:
    - path: crates/analysis/tests/trait_verification.rs
      note: added dyn_dispatch_call_site_uses_trait_contracts test (1 new test, 14 total)
  modified:
    - path: crates/analysis/src/vcgen.rs
      note: parse_dyn_dispatch_callee helper, dyn resolution in generate_call_site_vcs, normalize_callee_name fix
decisions:
  - "normalize_callee_name preserves <dyn TraitName>::method forms intact — dyn dispatch resolution requires the full form to remain after normalization"
  - "Contract lookup uses suffix-match (name.contains(TraitName::method)) to handle both bare and fully-qualified keys like Stack::push and crate::Stack::push"
  - "OpaqueCallee block duplicated into dyn-resolved None sub-arm and non-dyn None sub-arm — kept DRY at logic level, duplicated at struct level to avoid labeled break complexity"
metrics:
  duration_seconds: 800
  completed_date: "2026-03-03"
  tasks_completed: 2
  files_modified: 2
---

# Phase 41 Plan 02: Dyn Dispatch Call-Site VC Resolution Summary

**One-liner:** dyn Trait call-site VCs now resolve to trait-level contracts via `parse_dyn_dispatch_callee` + `normalize_callee_name` preservation of `<dyn TraitName>::method` forms.

## What Was Built

TRT-02 satisfied: `generate_call_site_vcs` now resolves callee names of the form `<dyn Stack>::push` to trait-level contracts in `contract_db` (keyed as `Stack::push`) instead of falling through to the OpaqueCallee diagnostic path.

### Key Implementation Points

1. **`normalize_callee_name` fix** (Rule 1 - Bug auto-fix): The function previously stripped `<dyn Stack>::push` to just `push` via `rsplit_once("::")`. Added a guard: if the stripped name starts with `<dyn `, return it intact. This preserves the full dyn-dispatch form so `parse_dyn_dispatch_callee` can operate on it.

2. **`parse_dyn_dispatch_callee` helper**: Private function in `vcgen.rs` near `normalize_callee_name`. Parses `<dyn Stack>::push` → `("Stack", "push")` and `<dyn Stack as Stack>::push` → `("Stack", "push")`. Returns `None` for non-dyn names.

3. **`generate_call_site_vcs` dyn resolution**: In the `None` arm of `contract_db.get(&call_site.callee_name)`, before emitting OpaqueCallee, try `parse_dyn_dispatch_callee`. If it matches, do a suffix-match `contract_db.iter().find(|(name, _)| name.contains(&search_suffix))`. If found, use that summary (no OpaqueCallee emitted). If not found, emit OpaqueCallee as before.

4. **4 unit tests** in `vcgen.rs` `#[cfg(test)]` block: standard form, as-form, non-dyn, empty string — all pass.

5. **Integration test** `dyn_dispatch_call_site_uses_trait_contracts` in `trait_verification.rs`: builds a caller with `Terminator::Call { func: "<dyn Stack>::push", ... }`, inserts `"Stack::push"` in `contract_db` with a `requires: _1 > 0` contract, calls `generate_vcs_with_db`, asserts at least one non-OpaqueCallee VC is emitted.

## Tasks Completed

| Task | Name | Commit | Files |
|------|------|--------|-------|
| 1 | Dyn dispatch callee name resolution in generate_call_site_vcs | bd95119 | crates/analysis/src/vcgen.rs |
| 2 | Integration test — dyn dispatch call-site uses trait contracts | ff25d1c | crates/analysis/src/vcgen.rs, crates/analysis/tests/trait_verification.rs |

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Fixed normalize_callee_name stripping dyn dispatch prefix**
- **Found during:** Task 2 (writing integration test)
- **Issue:** `normalize_callee_name("<dyn Stack>::push")` was returning `"push"` (just the last `::` segment), destroying the `<dyn Stack>` prefix needed by `parse_dyn_dispatch_callee`
- **Fix:** Added guard `if stripped.starts_with("<dyn ") { return stripped.to_string(); }` before the `rsplit_once` logic
- **Files modified:** `crates/analysis/src/vcgen.rs`
- **Commit:** ff25d1c

## Verification Results

- `cargo test -p rust-fv-analysis --test trait_verification` — 14/14 pass (13 existing + 1 new)
- `cargo test --workspace` — 0 failures across all crates
- `cargo clippy --workspace -- -D warnings` — clean
- `cargo fmt --check` — clean
- `grep "dyn_dispatch_call_site_uses_trait_contracts" crates/analysis/tests/trait_verification.rs` — found
- `grep "parse_dyn_dispatch_callee" crates/analysis/src/vcgen.rs` — found (helper + usage + 4 tests)

## Self-Check: PASSED

- [x] `crates/analysis/src/vcgen.rs` exists and contains `parse_dyn_dispatch_callee`
- [x] `crates/analysis/tests/trait_verification.rs` exists and contains `dyn_dispatch_call_site_uses_trait_contracts`
- [x] Commit bd95119 exists (Task 1)
- [x] Commit ff25d1c exists (Task 2)
- [x] All 14 trait_verification tests pass
- [x] Workspace test suite: 0 failures
