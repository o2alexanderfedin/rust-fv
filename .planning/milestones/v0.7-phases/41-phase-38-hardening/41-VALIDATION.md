---
phase: 41
slug: phase-38-hardening
status: complete
nyquist_compliant: true
wave_0_complete: true
created: 2026-03-03
---
# Phase 41 — Validation Strategy

**Retroactive validation.** Phase 41 is complete and verified (41-VERIFICATION.md score: 7/7).
This document records the test infrastructure and Nyquist sampling rate that was applied.

## Test Infrastructure

Framework: `cargo test` (Rust standard test runner)

Test suites exercised:
- `cargo test --workspace` — 0 failures (1264 analysis lib tests, 14 trait_verification tests, 123 driver tests)
- Unit tests in callbacks.rs `#[cfg(test)]` block:
  - `test_sealed_trait_detection_uses_detect_sealed_trait_pub_crate`
  - `test_sealed_trait_detection_uses_detect_sealed_trait_pub`
  - `test_behavioral_subtyping_z3_catchall_is_pessimistic`
- Unit tests in vcgen.rs:
  - `test_parse_dyn_dispatch_callee_standard`
  - `test_parse_dyn_dispatch_callee_as_form`
- Integration test in trait_verification.rs:
  - `dyn_dispatch_call_site_uses_trait_contracts`
  - `behavioral_subtyping_z3_proves_precondition_weakening_unsat` (Z3 accepts declare-fun scripts)

## Sampling Rate

Each production behavior added in Phase 41 has at least one automated test:
- Sealed trait detection from HIR visibility (`pub(crate)` → true, `pub` → false): 2 unit tests
- Z3 catch-all pessimism (`_ => false` not `_ => true`): 1 unit test asserting warn message
- `generate_subtyping_script` emits proper `declare-fun`: integration tests confirm no Z3 parse errors
- `parse_dyn_dispatch_callee` parsing both `<dyn Trait>::method` and `<dyn Trait as Trait>::method` forms: 2 unit tests
- Dyn dispatch resolution in `generate_call_site_vcs` uses trait contracts: 1 integration test

Nyquist criterion: Met — each of the 7 observable truths in 41-VERIFICATION.md maps to at least one automated test assertion.

## Per-Task Verification Map

| Plan | Task | Test(s) | Status |
|------|------|---------|--------|
| 41-01 | Sealed trait HIR visibility detection + Z3 pessimistic catch-all (TRT-04) | `test_sealed_trait_detection_uses_detect_sealed_trait_pub_crate`, `test_sealed_trait_detection_uses_detect_sealed_trait_pub`, `test_behavioral_subtyping_z3_catchall_is_pessimistic` | ✅ Verified |
| 41-02 | Dyn dispatch callee name resolution in generate_call_site_vcs (TRT-02) | `test_parse_dyn_dispatch_callee_standard`, `test_parse_dyn_dispatch_callee_as_form`, `dyn_dispatch_call_site_uses_trait_contracts` | ✅ Verified |

## Wave 0 Requirements

None — phase already completed. All test infrastructure was established during phase execution.

## Manual-Only Verifications

None. All phase 41 behaviors are programmatically verified:
- Sealed trait detection: unit tests directly invoke `detect_sealed_trait` with known inputs
- Z3 pessimism: source-level test asserts warn message fragment in production code
- Dyn dispatch: integration test builds full Function + ContractDatabase and asserts non-OpaqueCallee VC

## Validation Sign-Off

- **Score:** 7/7 must-have truths verified (see 41-VERIFICATION.md)
- **Regressions:** 0 (full workspace: 1264 + 14 + 123 tests pass)
- **Requirements satisfied:** TRT-04 (sealed trait detection), TRT-02 (dyn dispatch trait contracts)
- **Nyquist compliant:** Yes — every production behavior has a corresponding automated test
- **Signed off:** 2026-03-03 (retroactive — phase completed 2026-03-03)
