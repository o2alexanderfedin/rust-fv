---
phase: 37-cross-crate-scc-detection
verified: 2026-03-01T00:00:00Z
status: passed
score: 11/11 must-haves verified
re_verification: false
---

# Phase 37: Cross-Crate SCC Detection Verification Report

**Phase Goal:** Extend cross-crate SCC detection so Tarjan's algorithm can form SCCs spanning crate boundaries, wire vcgen to use ContractDatabase for cross-crate callee decreases, and add end-to-end integration tests.
**Verified:** 2026-03-01
**Status:** PASSED
**Re-verification:** No — initial verification

## Goal Achievement

### Observable Truths

| # | Truth | Status | Evidence |
|---|-------|--------|----------|
| 1 | CallGraph built with cross-crate edges correctly identifies a mutual SCC spanning two crates | VERIFIED | `from_functions_with_cross_crate_db` exists in `call_graph.rs` lines 115-162; `cross_crate_scc_detected_via_db` test passes |
| 2 | detect_recursion() returns a RecursiveGroup containing both the in-crate and cross-crate function name | VERIFIED | `cross_crate_scc_detected_via_db` test passes (7/7 unit tests GREEN) |
| 3 | Single-crate recursion detection is unchanged (all existing call_graph tests pass) | VERIFIED | Full test suite: 0 failures across all 1243+ tests |
| 4 | generate_termination_vcs uses contract_db to resolve the decreases measure for cross-crate callee | VERIFIED | `contract_db` parameter active (no underscore prefix, line 70 of `recursion.rs`); `db.get(callee_name)` called at line 204 |
| 5 | vcgen.rs passes contract_db into from_functions_with_cross_crate_db and generate_termination_vcs | VERIFIED | `vcgen.rs` lines 367-372: `match contract_db { Some(db) => from_functions_with_cross_crate_db(...), None => from_functions(...) }` |
| 6 | Cross-crate termination VC is generated with the correct decreases assertion | VERIFIED | `cross_crate_termination_vc_generated` and `cross_crate_vc_is_negated_less_than` unit tests GREEN |
| 7 | Single-crate termination VC generation is unchanged | VERIFIED | `single_crate_regression_unchanged` unit test GREEN; all pre-existing integration tests GREEN |
| 8 | cargo verify detects mutually recursive cycle spanning two crates and reports SCC members | VERIFIED | `test_cross_crate_scc_detection_reports_members` integration test passes |
| 9 | User can attach #[decreases(expr)] and cargo verify checks termination across crate boundaries | VERIFIED | `test_cross_crate_termination_decreasing_verifies_unsat` (Z3 UNSAT) and `test_cross_crate_termination_non_decreasing_produces_sat` (Z3 SAT) integration tests pass |
| 10 | Cross-crate SCC detection uses exported symbol contracts so crate boundaries are transparent to Tarjan's algorithm | VERIFIED | Virtual node injection + back-edge heuristic in `from_functions_with_cross_crate_db`; `tarjan_scc` operates over augmented graph |
| 11 | Single-crate recursive function verification remains GREEN with no regressions | VERIFIED | `test_single_crate_recursion_regression` integration test passes; 0 failures in full suite |

**Score:** 11/11 truths verified

### Required Artifacts

| Artifact | Expected | Status | Details |
|----------|----------|--------|---------|
| `crates/analysis/src/call_graph.rs` | `from_functions_with_cross_crate_db` constructor + cross-crate edge injection | VERIFIED | Public method at lines 105-162; virtual node injection + back-edge heuristic via `decreases.raw` substring match |
| `crates/analysis/src/recursion.rs` | `generate_termination_vcs` extended to handle cross-crate recursive call sites | VERIFIED | Parameter renamed `_contract_db` -> `contract_db`; `db.get(callee_name)` used at lines 202-212 for VC description enrichment; group check extended at line 106 for full-path cross-crate callee names |
| `crates/analysis/src/vcgen.rs` | vcgen passes contract_db to `from_functions_with_cross_crate_db` and `generate_termination_vcs` | VERIFIED | Lines 367-372: match expression uses `from_functions_with_cross_crate_db` when `contract_db` is `Some` |
| `crates/analysis/tests/recursion_verification.rs` | Integration tests for cross-crate SCC detection + termination verification | VERIFIED | 4 new tests at lines 1592-1797; 3 helper functions `make_cross_crate_local_foo`, `make_cross_crate_local_foo_decremented`, `make_cross_crate_db_with_back_edge` |

### Key Link Verification

| From | To | Via | Status | Details |
|------|----|-----|--------|---------|
| `call_graph.rs::from_functions_with_cross_crate_db` | `contract_db.rs::ContractDatabase` | `contract_db.get(callee_name)` + `contract_db.iter()` | WIRED | Line 141: `contract_db.get(callee_name)` for virtual node injection; `in_crate_norm` set for back-edge heuristic |
| `call_graph.rs::detect_recursion` | `RecursiveGroup` | `tarjan_scc` over graph including cross-crate virtual nodes | WIRED | `tarjan_scc` at module level (line 15 import); graph augmented by `from_functions_with_cross_crate_db` before `detect_recursion()` called |
| `vcgen.rs recursion analysis block` | `call_graph.rs::from_functions_with_cross_crate_db` | `match contract_db` at lines 367-372 | WIRED | Exact pattern `from_functions_with_cross_crate_db` confirmed at vcgen.rs line 369 |
| `recursion.rs::generate_termination_vcs` | `contract_db.rs::ContractDatabase::get` | look up cross-crate callee decreases at lines 202-208 | WIRED | `db.get(callee_name).or_else(|| db.iter().find(...))` at lines 204-208 |
| `recursion_verification.rs` | `vcgen::generate_vcs` | `generate_vcs(&foo, Some(&db))` at lines 1602, 1662, 1720, 1778 | WIRED | All 4 integration tests call `vcgen::generate_vcs` with `Some(&db)` or `None` as appropriate |

### Requirements Coverage

| Requirement | Source Plan | Description | Status | Evidence |
|-------------|------------|-------------|--------|----------|
| XCREC-01 | 37-01, 37-03 | User can detect mutually recursive call cycles spanning multiple crates (Tarjan's SCC extended across crate boundaries) | SATISFIED | `from_functions_with_cross_crate_db` injects virtual nodes + back-edges; `test_cross_crate_scc_detection_reports_members` integration test passes; REQUIREMENTS.md marks XCREC-01 Complete |
| XCREC-02 | 37-02, 37-03 | User can verify `#[decreases]` termination measures for mutually recursive functions across crate boundaries | SATISFIED | `generate_termination_vcs` uses `contract_db`; vcgen wired to `from_functions_with_cross_crate_db`; UNSAT/SAT integration tests pass; REQUIREMENTS.md marks XCREC-02 Complete |

**Orphaned requirements check:** REQUIREMENTS.md maps only XCREC-01 and XCREC-02 to Phase 37 — both accounted for. No orphaned requirements.

### Anti-Patterns Found

| File | Line | Pattern | Severity | Impact |
|------|------|---------|----------|--------|
| `crates/analysis/src/vcgen.rs` | 3693 | TODO comment re: error propagation | Info | Pre-existing comment unrelated to Phase 37 work; in trigger-parsing error handler, not in SCC/termination path |

No blocker or warning anti-patterns introduced by Phase 37.

### Human Verification Required

None. All observable truths are verifiable programmatically via the test suite and code inspection:

- Cross-crate SCC detection: verified via unit tests (7/7) and integration tests (4/4 new + 8 pre-existing)
- Z3 UNSAT/SAT results: confirmed by actual Z3 runs in integration tests
- Clippy clean: confirmed with zero warnings on `rust-fv-analysis`

### Gaps Summary

No gaps. All must-haves from all three plan frontmatter sections are verified:

- Plan 01 (call_graph.rs): `from_functions_with_cross_crate_db` exists, is substantive, and is wired via vcgen.rs
- Plan 02 (recursion.rs + vcgen.rs): `contract_db` parameter active, cross-crate callee lookup implemented, vcgen wiring confirmed
- Plan 03 (integration tests): 4 tests in `recursion_verification.rs`, all pass including Z3 UNSAT/SAT checks

**Bug fixed during phase (noted in SUMMARY-03):** `generate_termination_vcs` group membership check was extended from `group.contains(&normalized)` to `group.contains(&normalized) || group.contains(callee_name)` to handle cross-crate full-path callee names stored in `RecursiveGroup`. This fix was required for cross-crate termination VCs to be generated at all and is correctly committed in `53bf3f2`.

**Test counts:**
- Unit tests (cross-crate): 7/7 GREEN (`cross_crate_tests` module: 4 tests; `cross_crate_termination_tests` module: 3 tests)
- Integration tests (new): 4/4 GREEN (`test_cross_crate_scc_detection_reports_members`, `test_cross_crate_termination_decreasing_verifies_unsat`, `test_cross_crate_termination_non_decreasing_produces_sat`, `test_single_crate_recursion_regression`)
- Pre-existing tests: all GREEN (0 regressions)
- Clippy: zero warnings on `rust-fv-analysis`

---

_Verified: 2026-03-01_
_Verifier: Claude (gsd-verifier)_
