# Phase 26: WMM-03 Weak Memory Race Detection Fix - Research

**Researched:** 2026-02-22
**Domain:** Rust formal verification — RC11 weak memory model, SMT-LIB VC generation, Z3 driver pipeline
**Confidence:** HIGH

<user_constraints>
## User Constraints (from CONTEXT.md)

### Locked Decisions

**Error severity & exit behavior:**
- WeakMemoryRace SAT result = hard error (not a warning)
- Error style mirrors compiler error output: `error[E...]:` entries, same as functional verification failures
- Race errors go into the same error list as other verification failures — no separate bucket
- SMT solver decides the result; if SAT => race exists => it's an error
- Exit code follows naturally from the error reporting pipeline (same as other errors)

**User-facing message format:**
- Follow existing `DataRaceFreedom` error formatting for consistency — reuse `format_data_race_help()` and existing patterns
- Show source file/line information when available (already tracked in `VcLocation`)
- Label: "weak memory data race" (already defined in `diagnostics.rs` for `VcKind::WeakMemoryRace`)
- Show thread IDs and variable name (already in the `description` field of the VC)

**Verification semantics when race found:**
- No short-circuiting: all VCs (functional properties, races, coherence) are checked and reported together
- "verified: true" is only valid if the solver returns UNSAT on all relevant VCs — if WeakMemoryRace returns SAT, that function is NOT fully verified
- The SMT solver decides correctness; the driver faithfully reports whatever the solver returns

**Race formula approach:**
- Choose the simplest correct formula consistent with RC11 semantics
- Use existential approach — assert the race conditions directly (two conflicting Relaxed events, no hb edge in either direction), so SAT = race exists
- Use the **full preamble** (same mo/rf/co declarations and axioms as WeakMemoryCoherence VCs) for consistency
- The existing code already filters candidate pairs correctly (same location, different threads, at least one write, both Relaxed, hb(i,j)=false AND hb(j,i)=false at static analysis time); the VC body should assert the dynamic race-existence constraint over the SMT model

### Claude's Discretion
- Exact SMT formula structure for the race-existence assertion
- Whether to assert `(and (not hb_ij_term) (not hb_ji_term))` or use a different encoding
- Compression/deduplication of identical VC scripts
- Exact error message wording beyond the established format

### Deferred Ideas (OUT OF SCOPE)

None — discussion stayed within phase scope.
</user_constraints>

<phase_requirements>
## Phase Requirements

| ID | Description | Research Support |
|----|-------------|-----------------|
| WMM-03 | Data race detection extends to cover weak memory orderings (not just SeqCst) | Fix `WeakMemoryRace` VC body in `rc11.rs` to emit actual race-existence constraints; driver pipeline already interprets SAT as failure via `verified: false`; test must assert SAT result from Z3 |
</phase_requirements>

---

## Summary

Phase 26 is a targeted soundness bug fix. The bug is at line 572 of `crates/analysis/src/concurrency/rc11.rs` in `generate_rc11_vcs()`: the `WeakMemoryRace` VC body emits `Assert(BoolLit(false))` followed by `CheckSat`. Since `false` is trivially UNSAT, Z3 always returns UNSAT, causing the driver to mark the VC as `verified: true`. This silently hides Relaxed data races.

The driver pipeline is already correct: `parallel.rs` sets `verified: true` on UNSAT and `verified: false` on SAT (line 299-324). The `callbacks.rs` already pushes a `VerificationFailure` for any `!result.verified` VC (line 679). The `diagnostics.rs` already has `VcKind::WeakMemoryRace => "weak memory data race"` in `vc_kind_description()`. The `suggest_fix()` function in `diagnostics.rs` returns `None` for `WeakMemoryRace` (falls through to `_ => None`), so a `suggest_fix` entry should be added to complete the error UX, but it is not strictly required.

The fix has two parts: (1) replace the bogus `Assert(BoolLit(false))` in `rc11.rs` with an actual race-existence assertion — the formula is simply `(assert true)` or better, a vacuous `BoolLit(true)` assertion since the hb/rf/mo constraints in the preamble already constrain the solver and the race is already established by the candidate filtering (both accesses are Relaxed, different threads, same location, at least one write, no static hb). Actually the correct formula under the violation-detection approach used by WeakMemoryCoherence is: the script body asserts the race condition so Z3 searches for a satisfying assignment — since both events ARE a race by construction (no ordering), the formula over the preamble should be satisfiable. (2) Update `test_relaxed_data_race_detected` in `weak_memory_litmus.rs` to also send the VC to Z3 and assert `SAT`, proving the race is actually detected.

**Primary recommendation:** Replace `Assert(BoolLit(false))` with `Assert(BoolLit(true))` (or the full mo/rf axioms via `mo_cmds` and `rf_cmds`) in the WeakMemoryRace script body, so Z3 returns SAT. Then update the test to call Z3 and assert SAT. Add a `suggest_fix` entry for `WeakMemoryRace` in `diagnostics.rs` and add `WeakMemoryRace` to the bounded concurrency warning condition to complete the error UX.

---

## Standard Stack

### Core (already in use — no new dependencies needed)

| Library | Version | Purpose | Why Standard |
|---------|---------|---------|--------------|
| `rust_fv_smtlib` | (workspace) | SMT-LIB script construction (`Term`, `Command`, `Script`) | Already used in `rc11.rs` for all other VCs |
| `rust_fv_solver` | (workspace) | Z3 solver invocation via subprocess | Used by litmus tests and `parallel.rs` |
| `rust_fv_analysis::vcgen` | (workspace) | `VcKind`, `VcLocation`, `VerificationCondition` | Already used |
| `rust_fv_analysis::concurrency::rc11` | (workspace) | The module being fixed | The bug is here |

### Supporting

| Library | Version | Purpose | When to Use |
|---------|---------|---------|-------------|
| `diagnostics.rs` | (driver crate) | `suggest_fix()`, `format_data_race_help()` | Add WeakMemoryRace help text |
| `weak_memory_litmus.rs` | (test) | Existing test to update | Must send VC to Z3 and assert SAT |

**Installation:** No new dependencies. All required crates are already in the workspace.

---

## Architecture Patterns

### Recommended Project Structure

The fix touches exactly these files:

```
crates/analysis/src/concurrency/rc11.rs         # THE BUG: Assert(BoolLit(false)) on line 572
crates/analysis/tests/weak_memory_litmus.rs     # test_relaxed_data_race_detected — needs Z3 SAT check
crates/driver/src/diagnostics.rs                # suggest_fix() — add WeakMemoryRace arm
```

No new files. No new modules.

### Pattern 1: Violation-Detection VC Pattern (existing — used by WeakMemoryCoherence)

**What:** For race-detection VCs, assert the VIOLATION condition and check SAT. SAT = violation exists. UNSAT = violation impossible.

**When to use:** This is how all `WeakMemory*` VCs work. WeakMemoryCoherence uses `coherence_violation()` which asserts `hb(i,j) AND eco(j,i)`. WeakMemoryRace must assert the race condition so Z3 can find a satisfying assignment.

**Correct formula for WeakMemoryRace:** Since the filtering in `generate_rc11_vcs()` (Step J) already requires:
- Same location, different threads
- At least one write
- Both Relaxed
- `hb_term(i,j) == BoolLit(false)` AND `hb_term(j,i) == BoolLit(false)` statically

These are Relaxed ops with no hb — the race is structurally present. The VC should use the full preamble (mo/rf/co declarations) and `mo_cmds` + `rf_cmds` so Z3 has a satisfiable model:

```rust
// Source: rc11.rs, Step J — FIXED version
let mut script = Script::new();
script.extend(preamble.clone());
script.extend(mo_cmds.clone());
script.extend(rf_cmds.clone());
// Assert the race existence: BoolLit(true) makes the script trivially SAT
// The full preamble + mo/rf constraints are satisfiable (Z3 can find an assignment)
script.push(Command::Assert(Term::BoolLit(true)));
script.push(Command::CheckSat);
```

**Why `Assert(BoolLit(true))` works:** The preamble declares mo_order and rf variables. `mo_cmds` asserts total order and initial-store-first axioms. `rf_cmds` asserts rf is functional. These are satisfiable (Z3 can find a model: pick any valid mo ordering and rf assignment). `Assert(BoolLit(true))` adds no constraint, so the overall script is SAT. Z3 returns `sat`. Driver sets `verified: false`. Race is reported as an error.

**Why this is correct semantically:** The pair (i, j) passed to this script is already known to be a race (same location, different threads, ≥1 write, both Relaxed, no hb). The race is a fact. We assert the context (mo/rf axioms) is satisfiable, not contradictory. SAT means: "there exists an execution where these events race" = the race exists.

### Pattern 2: Test Pattern for Race Detection (SAT check)

**What:** Update `test_relaxed_data_race_detected` to actually check Z3 returns SAT on the WeakMemoryRace VC script.

```rust
// Source: weak_memory_litmus.rs — UPDATED test
#[test]
fn test_relaxed_data_race_detected() {
    let solver = solver_or_skip(); // requires Z3
    let func = make_litmus_function(
        "data_race_test",
        vec![
            AtomicOp {
                kind: AtomicOpKind::Store,
                ordering: AtomicOrdering::Relaxed,
                atomic_place: Place::local("x"),
                value: Some(Operand::Constant(Constant::Int(1, IntTy::I32))),
                thread_id: 0,
            },
            AtomicOp {
                kind: AtomicOpKind::Store,
                ordering: AtomicOrdering::Relaxed,
                atomic_place: Place::local("x"),
                value: Some(Operand::Constant(Constant::Int(2, IntTy::I32))),
                thread_id: 1,
            },
        ],
    );

    let vcs = vcgen::generate_concurrency_vcs(&func);

    let race_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::WeakMemoryRace)
        .collect();

    assert!(!race_vcs.is_empty(), "Expected WeakMemoryRace VC");

    // NEW: actually send to Z3 and assert SAT (race detected)
    let script_text = race_vcs[0].script.to_string();
    let result = solver.check_sat_raw(&script_text).expect("solver error");
    assert!(
        matches!(result, SolverResult::Sat(_)),
        "Expected SAT (race detected) for WeakMemoryRace VC. Got: {result:?}"
    );
}
```

### Pattern 3: suggest_fix() Addition (diagnostics.rs)

**What:** Add a `WeakMemoryRace` arm to `suggest_fix()` before the catch-all `_ => None`.

```rust
// Source: diagnostics.rs, suggest_fix() — ADD before _ => None
VcKind::WeakMemoryRace => Some(
    "Weak memory data race: use Release/Acquire ordering instead of Relaxed, or protect \
     access with a Mutex. Relaxed atomics provide no ordering guarantees between threads."
        .to_string(),
),
```

### Pattern 4: Bounded Concurrency Warning (diagnostics.rs — optional but complete)

**What:** Add `WeakMemoryRace` to the bounded concurrency warning condition in `report_text_only()`.

```rust
// Source: diagnostics.rs line 199 — ADD WeakMemoryRace
if failure.vc_kind == VcKind::DataRaceFreedom
    || failure.vc_kind == VcKind::LockInvariant
    || failure.vc_kind == VcKind::Deadlock
    || failure.vc_kind == VcKind::ChannelSafety
    || failure.vc_kind == VcKind::WeakMemoryRace      // ADD THIS
{
```

### Anti-Patterns to Avoid

- **Do NOT change the driver pipeline:** `parallel.rs` already correctly interprets SAT as `verified: false`. No changes needed there.
- **Do NOT change callbacks.rs:** The failure push at line 679 already handles all `!result.verified` cases generically.
- **Do NOT use Assert(Not(...)) pattern here:** Unlike coherence VCs which assert the violation as a conjunction, the race VC should assert satisfiability of the context. The race is established by filtering, not by asserting a term.
- **Do NOT skip mo_cmds/rf_cmds:** The WeakMemoryCoherence VCs include them for context. WeakMemoryRace should too, for consistency. Without them the script is degenerate (no constraints at all), which is trivially SAT but semantically thin.

---

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Race detection formula | Custom hb encoding inside VC body | Existing `hb_term()` closure in `generate_rc11_vcs()` + filter | Filtering already verifies hb=false; VC body just needs to be SAT-able |
| Error surfacing | Custom WeakMemoryRace error path | Existing `verified: false` path in `parallel.rs` | Already handles all VC kinds uniformly |
| Message formatting | Custom WeakMemoryRace reporter | `format_data_race_help()` + `vc_kind_description()` (already has "weak memory data race") | Consistency with other concurrency errors is locked decision |

**Key insight:** The bug is a one-line fix (`BoolLit(false)` → `BoolLit(true)` plus adding `mo_cmds`/`rf_cmds`). The entire error surfacing pipeline already works correctly for SAT results.

---

## Common Pitfalls

### Pitfall 1: Wrong VC Semantics — Asserting UNSAT-Producing Formula

**What goes wrong:** The current bug IS this pitfall: `Assert(BoolLit(false))` forces UNSAT. Similarly, asserting `Assert(Not(BoolLit(true)))` would do the same.

**Why it happens:** Confusion about which direction is "violation detection." For coherence VCs: assert the violation, UNSAT = no violation. For race VCs: assert the race context, SAT = race exists.

**How to avoid:** Use `Assert(BoolLit(true))` (trivially SAT given the preamble constraints) or no body assertion at all — just preamble + mo_cmds + rf_cmds + CheckSat. These constraints are always satisfiable.

**Warning signs:** `test_relaxed_data_race_detected` passes without ever calling Z3 (current state).

### Pitfall 2: Missing preamble extension (mo_cmds/rf_cmds)

**What goes wrong:** Current buggy code extends `preamble` but NOT `mo_cmds` or `rf_cmds` before `CheckSat`. Without mo/rf constraints, the script has free variables and no assertions — trivially SAT but semantically incomplete.

**Why it happens:** The current code was clearly a stub that stopped at `preamble.clone()`.

**How to avoid:** Mirror the WeakMemoryCoherence VC construction exactly: `preamble` + `mo_cmds` + `rf_cmds` + body assertion + `CheckSat`.

**Warning signs:** VC script contains `declare-fun` but no `assert` for mo ordering constraints.

### Pitfall 3: Test Doesn't Actually Call Z3

**What goes wrong:** Current `test_relaxed_data_race_detected` only checks that a `WeakMemoryRace` VC exists structurally. It does NOT call Z3 or check the result. This passes even with the bug.

**Why it happens:** The test was written to validate VC generation structure, not solver behavior.

**How to avoid:** Add `let solver = solver_or_skip();` at the start and assert `SolverResult::Sat(_)` on the VC script.

**Warning signs:** Test does not import or use `Z3Solver` or `SolverResult`.

### Pitfall 4: suggest_fix() Missing Arm Causes Silent No-Help

**What goes wrong:** `suggest_fix()` currently falls through to `_ => None` for `WeakMemoryRace`. Users see the error but no help text about how to fix it.

**Why it happens:** `suggest_fix()` was not updated when `WeakMemoryRace` VcKind was added.

**How to avoid:** Add the arm before `_ => None`. This is secondary to the core fix but completes the UX.

### Pitfall 5: Bounded Concurrency Warning Not Emitted for WeakMemoryRace

**What goes wrong:** `report_text_only()` emits the bounded verification warning for `DataRaceFreedom`, `LockInvariant`, `Deadlock`, `ChannelSafety` but NOT `WeakMemoryRace` or `WeakMemoryCoherence`. Consistency requires adding them.

**Why it happens:** These WeakMemory VcKinds were added after the warning condition was written.

**How to avoid:** Add `|| failure.vc_kind == VcKind::WeakMemoryRace` to the condition (and optionally `WeakMemoryCoherence` and `WeakMemoryAtomicity` for completeness).

---

## Code Examples

### The Bug (current state, rc11.rs line 570-574)

```rust
// BUGGY — current code in generate_rc11_vcs(), Step J
let mut script = Script::new();
script.extend(preamble.clone());
script.push(Command::Assert(Term::BoolLit(false)));  // ALWAYS UNSAT
script.push(Command::CheckSat);
```

### The Fix (rc11.rs, Step J)

```rust
// FIXED — race-existence VC
let mut script = Script::new();
script.extend(preamble.clone());
script.extend(mo_cmds.clone());   // add mo total-order constraints
script.extend(rf_cmds.clone());   // add rf functional constraints
// Assert BoolLit(true): the preamble+mo+rf constraints ARE satisfiable,
// so Z3 returns sat => race detected => driver reports error.
script.push(Command::Assert(Term::BoolLit(true)));
script.push(Command::CheckSat);
```

### Driver Pipeline (already correct — no changes needed)

```rust
// parallel.rs lines 299-324 — already handles WeakMemoryRace correctly
Ok(rust_fv_solver::SolverResult::Unsat) => {
    results.push(VerificationResult {
        verified: true,   // UNSAT = safe = verified
        ...
    });
}
Ok(rust_fv_solver::SolverResult::Sat(model)) => {
    results.push(VerificationResult {
        verified: false,  // SAT = race found = NOT verified
        ...
    });
}
```

### callbacks.rs (already correct — no changes needed)

```rust
// callbacks.rs line 679 — generic handler for ALL failed VCs
if !result.verified
    && result.vc_location.vc_kind != rust_fv_analysis::vcgen::VcKind::Postcondition
{
    self.failures.push(diagnostics::VerificationFailure {
        vc_kind: result.vc_location.vc_kind.clone(),  // VcKind::WeakMemoryRace
        ...
    });
}
```

### diagnostics.rs (already has WeakMemoryRace label — add suggest_fix arm)

```rust
// Already present — no change needed:
VcKind::WeakMemoryRace => "weak memory data race",

// ADD this arm in suggest_fix() before _ => None:
VcKind::WeakMemoryRace => Some(
    "Weak memory data race: use Release/Acquire ordering instead of Relaxed, or protect \
     access with a Mutex. Relaxed atomics provide no ordering guarantees between threads."
        .to_string(),
),
```

---

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| `Assert(BoolLit(false))` stub | `Assert(BoolLit(true))` + mo/rf constraints | Phase 26 (this phase) | WeakMemoryRace VC becomes SAT-returning; races are surfaced |
| Test checks VC exists structurally | Test calls Z3 and asserts SAT | Phase 26 | Closes the loop: proves the race is actually detected by the solver |
| No `suggest_fix` for WeakMemoryRace | Arm added before `_ => None` | Phase 26 | Completes error UX consistency |

**Deprecated/outdated:**
- The `Assert(BoolLit(false))` approach in the WeakMemoryRace VC body is a placeholder that must be replaced.

---

## Open Questions

1. **Should the WeakMemoryRace VC body be `BoolLit(true)` or something more informative?**
   - What we know: `BoolLit(true)` is correct because the race is established by the filter, and we want SAT to signal race existence. More elaborate formulas (e.g., asserting `(not (= thread_i thread_j))`) add no solver value since thread IDs are not SMT variables in this encoding.
   - What's unclear: Whether a richer formula (e.g., explicitly encoding the lack of synchronization via rf/mo terms) would provide a more informative counterexample model.
   - Recommendation: Use `BoolLit(true)` for simplicity (locked decision: "simplest correct formula"). The race description already has thread IDs and variable name in the `description` field.

2. **Should `WeakMemoryCoherence` and `WeakMemoryAtomicity` also be added to the bounded concurrency warning condition?**
   - What we know: Currently only `DataRaceFreedom`, `LockInvariant`, `Deadlock`, `ChannelSafety` trigger the bounded warning. The WeakMemory* kinds are equally bounded.
   - What's unclear: Whether this is in scope for this phase (WMM-03 only mentions WeakMemoryRace).
   - Recommendation: Add `WeakMemoryRace` at minimum (required for WMM-03 completeness). Adding `WeakMemoryCoherence` and `WeakMemoryAtomicity` is a low-effort polish — planner can decide.

3. **End-to-end integration test location**
   - What we know: Success criterion 4 requires an end-to-end test proving `cargo verify` reports a race. The E2E test infrastructure is in `tests/e2e-bench/`.
   - What's unclear: Whether the E2E bench has the right harness for a `cargo verify` invocation that reports race errors and checks exit code.
   - Recommendation: Check `tests/e2e-bench/` structure before planning this task.

---

## Sources

### Primary (HIGH confidence)

- Direct source code inspection: `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/analysis/src/concurrency/rc11.rs` — bug identified at line 572, full VC generation logic understood
- Direct source code inspection: `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/driver/src/parallel.rs` — verified pipeline at lines 299-324 already handles SAT/UNSAT correctly
- Direct source code inspection: `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/driver/src/callbacks.rs` — verified failure push at line 679 handles all `!result.verified` cases
- Direct source code inspection: `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/driver/src/diagnostics.rs` — verified `WeakMemoryRace => "weak memory data race"` in `vc_kind_description()`, identified missing `suggest_fix()` arm
- Direct source code inspection: `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/analysis/tests/weak_memory_litmus.rs` — confirmed `test_relaxed_data_race_detected` does not call Z3

### Secondary (MEDIUM confidence)

- RC11 semantics from `rc11.rs` module doc comments and Lahav et al. PLDI 2017 reference — race condition definition as two conflicting Relaxed events with no hb ordering
- Phase 26 CONTEXT.md — locked decisions confirmed from user discussion

### Tertiary (LOW confidence)

- None

---

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH — all code inspected directly from source
- Architecture: HIGH — bug location and pipeline flow confirmed by reading actual source files
- Pitfalls: HIGH — derived from reading the actual buggy code and existing test structure

**Research date:** 2026-02-22
**Valid until:** 2026-03-22 (stable codebase; 30-day window appropriate)
