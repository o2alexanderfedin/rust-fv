---
phase: 26-wmm03-race-detection-fix
verified: 2026-02-22T00:00:00Z
status: passed
score: 5/5 must-haves verified
re_verification: false
---

# Phase 26: WMM-03 Weak Memory Race Detection Fix — Verification Report

**Phase Goal:** Fix the WMM-03 soundness gap — WeakMemoryRace VC body in rc11.rs emits a SAT-returning formula so Relaxed data races are correctly detected and surfaced through the driver pipeline.
**Verified:** 2026-02-22
**Status:** passed
**Re-verification:** No — initial verification

---

## Goal Achievement

### Observable Truths

| #   | Truth                                                                                                              | Status     | Evidence                                                                                                       |
| --- | ------------------------------------------------------------------------------------------------------------------ | ---------- | -------------------------------------------------------------------------------------------------------------- |
| 1   | WeakMemoryRace VC script is SAT-returning (Z3 finds a model, not UNSAT)                                           | VERIFIED   | rc11.rs line 576: `Command::Assert(Term::BoolLit(true))` + mo_cmds + rf_cmds in Step J                        |
| 2   | test_relaxed_data_race_detected calls Z3 and asserts SolverResult::Sat                                            | VERIFIED   | weak_memory_litmus.rs line 1531: `assert!(matches!(result, SolverResult::Sat(_)), ...)` — test passes in 0.03s |
| 3   | Two Relaxed writes to same location from different threads produce WeakMemoryRace VC with mo_cmds and rf_cmds     | VERIFIED   | rc11.rs lines 571-577: `script.extend(mo_cmds.clone()); script.extend(rf_cmds.clone()); Assert(BoolLit(true))`|
| 4   | Users see actionable help text when a weak memory data race error is reported                                     | VERIFIED   | diagnostics.rs line 530-534: `VcKind::WeakMemoryRace => Some("Weak memory data race: use Release/Acquire...")`|
| 5   | End-to-end driver pipeline: two Relaxed atomic stores → verify_functions_parallel returns verified:false          | VERIFIED   | wmm_race_e2e.rs test_relaxed_race_surfaces_as_driver_failure — passes in 0.03s with Z3                         |

**Score:** 5/5 truths verified

---

### Required Artifacts

| Artifact                                               | Expected                                                            | Status     | Details                                                                                 |
| ------------------------------------------------------ | ------------------------------------------------------------------- | ---------- | --------------------------------------------------------------------------------------- |
| `crates/analysis/src/concurrency/rc11.rs`              | WeakMemoryRace VC with Assert(BoolLit(true)) + mo_cmds + rf_cmds   | VERIFIED   | Lines 570-577: preamble + mo_cmds + rf_cmds + Assert(BoolLit(true)) + CheckSat         |
| `crates/analysis/tests/weak_memory_litmus.rs`          | Z3 SAT check for WeakMemoryRace VC                                  | VERIFIED   | Lines 1487-1535: solver_or_skip() + check_sat_raw + assert SolverResult::Sat(_)        |
| `crates/driver/src/diagnostics.rs`                     | suggest_fix() arm + bounded concurrency warning for WeakMemoryRace  | VERIFIED   | Line 530: suggest_fix arm; Line 203: `\|\| failure.vc_kind == VcKind::WeakMemoryRace` |
| `crates/driver/tests/wmm_race_e2e.rs`                  | E2E driver integration test proving race surfaces through pipeline  | VERIFIED   | Full file: verify_functions_parallel + assert race_failures non-empty                  |

All four artifacts exist, are substantive (no stubs, no placeholder return values), and are wired into the test execution path.

---

### Key Link Verification

| From                                      | To                              | Via                                                              | Status  | Details                                                                                      |
| ----------------------------------------- | ------------------------------- | ---------------------------------------------------------------- | ------- | -------------------------------------------------------------------------------------------- |
| rc11.rs generate_rc11_vcs() Step J        | Z3 solver                       | preamble + mo_cmds + rf_cmds + Assert(BoolLit(true)) + CheckSat | WIRED   | Lines 570-577 confirmed — no BoolLit(false) stub present                                    |
| test_relaxed_data_race_detected            | Z3Solver.check_sat_raw          | solver_or_skip() + race_vcs[0].script.to_string()               | WIRED   | Lines 1488, 1526-1529 confirmed — solver called, result asserted                            |
| wmm_race_e2e.rs                           | verify_functions_parallel       | VerificationTask with ConcurrencyConfig.verify_concurrency=true | WIRED   | Lines 19, 136: import + call confirmed                                                      |
| verify_functions_parallel SAT result      | VerificationResult { verified: false } | parallel.rs SAT handling                                  | WIRED   | Test asserts `!r.verified && r.vc_location.vc_kind == VcKind::WeakMemoryRace` — passes     |

---

### Requirements Coverage

| Requirement | Source Plans    | Description                                                            | Status    | Evidence                                                                                          |
| ----------- | --------------- | ---------------------------------------------------------------------- | --------- | ------------------------------------------------------------------------------------------------- |
| WMM-03      | 26-01, 26-02    | Data race detection extends to cover weak memory orderings (not SeqCst)| SATISFIED | rc11.rs SAT-returning WeakMemoryRace VC + Z3 SAT test + E2E driver failure test all pass         |

REQUIREMENTS.md traceability row: `WMM-03 | Phase 26 (gap closure) | Complete`

No orphaned requirements — WMM-03 is the only requirement mapped to Phase 26 in REQUIREMENTS.md, and both plans (26-01, 26-02) claim it.

---

### Anti-Patterns Found

None detected. Specific checks performed:

- rc11.rs Step J: no `Assert(BoolLit(false))` — the stub is gone, replaced by substantive constraints
- weak_memory_litmus.rs test_relaxed_data_race_detected: no empty handler, no `return null`, solver is actually called
- diagnostics.rs WeakMemoryRace arm: returns actionable `Some(...)` string, not `None` or empty
- wmm_race_e2e.rs: no Z3 skip-by-default logic (only skips if Z3 binary missing from PATH)

---

### Test Execution Results

```
cargo test -p rust-fv-analysis --test weak_memory_litmus
  test result: ok. 9 passed; 0 failed; 0 ignored  (0.03s)
  Included: test_relaxed_data_race_detected ... ok

cargo test -p rust-fv-driver --test wmm_race_e2e
  test result: ok. 1 passed; 0 failed; 0 ignored  (0.03s)
  Included: test_relaxed_race_surfaces_as_driver_failure ... ok

cargo clippy -p rust-fv-analysis -p rust-fv-driver
  (no errors output)
```

---

### Human Verification Required

None. All observable behaviors are programmatically verifiable:

- The SAT/UNSAT outcome is directly asserted in tests
- The pipeline failure propagation is asserted via `!r.verified`
- The diagnostic text is a string literal (no visual rendering needed)
- No external services beyond Z3 (already required and verified present)

---

### Commit Verification

All commits documented in SUMMARYs confirmed present in git log:

| Commit  | Description                                        | Plan  |
| ------- | -------------------------------------------------- | ----- |
| cf9a02a | fix(26-01): fix WeakMemoryRace VC to emit SAT-returning formula (WMM-03) | 26-01 |
| 96938b6 | feat(26-02): add WeakMemoryRace UX to diagnostics  | 26-02 |
| 3805445 | feat(26-02): add E2E driver integration test for WMM-03 weak memory race | 26-02 |

---

## Summary

Phase 26 fully achieves its goal. The WMM-03 soundness gap is closed:

1. **Root cause fixed:** `rc11.rs` Step J WeakMemoryRace VC no longer contains `Assert(BoolLit(false))` (the UNSAT stub that silently hid all Relaxed data races). It now emits `preamble + mo_cmds + rf_cmds + Assert(BoolLit(true)) + CheckSat`, which Z3 evaluates as SAT — correctly signaling a race exists.

2. **Analysis-level proof:** `test_relaxed_data_race_detected` in `weak_memory_litmus.rs` calls Z3 via `solver_or_skip()` and asserts `SolverResult::Sat(_)` on the WeakMemoryRace VC. Test passes in 0.03s.

3. **Driver-level proof:** `wmm_race_e2e.rs::test_relaxed_race_surfaces_as_driver_failure` exercises the full pipeline — IR function with two concurrent Relaxed stores → `verify_functions_parallel` → result with `verified=false` and `vc_kind=VcKind::WeakMemoryRace`. Test passes in 0.03s.

4. **UX completeness:** `diagnostics.rs` has a `WeakMemoryRace` arm in `suggest_fix()` with actionable help text, and the bounded concurrency warning condition includes `WeakMemoryRace`.

5. **Zero regressions:** All 9 litmus tests (CoRR, CoRW, CoWR, CoWW, SB, LB, MP, IRIW, Race) pass. Clippy reports 0 errors.

---

_Verified: 2026-02-22_
_Verifier: Claude (gsd-verifier)_
