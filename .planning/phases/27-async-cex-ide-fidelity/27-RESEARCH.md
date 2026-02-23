# Phase 27: Async Counterexample IDE Fidelity - Research

**Researched:** 2026-02-23
**Domain:** Rust async counterexample extraction + TypeScript VSCode interface synchronization
**Confidence:** HIGH

<phase_requirements>
## Phase Requirements

| ID | Description | Research Support |
|----|-------------|-----------------|
| ASY-02 | User can write `#[state_invariant]` to specify invariants that must hold at every `.await` suspension point in an `async fn` | Counterexample IDE rendering pipeline: populate `poll_iteration` from Z3 model's `poll_iter` constant, infer `await_side` from `VcKind`, add TypeScript interface fields |
</phase_requirements>

## Summary

Phase 27 closes a doubly-incomplete async counterexample gap: the Rust side never populates `poll_iteration` and `await_side` fields in `JsonCounterexample`, and the TypeScript side never declared those fields in the `JsonCounterexample` interface. Both fields were added to the Rust `json_output.rs` struct (lines 59-67 of `json_output.rs`) but left as `None` placeholders in `build_counterexample_v2()` (lines 414-415 of `parallel.rs`).

The fix has three specific parts: (1) in `parallel.rs::build_counterexample_v2()`, scan `cx_pairs` for a `("poll_iter", value)` pair and parse the value as `usize`; (2) look at `vc_location.vc_kind` and map `VcKind::AsyncStateInvariantSuspend` → `"pre_await"` and `VcKind::AsyncStateInvariantResume` → `"post_await"`; (3) add `poll_iteration?: number` and `await_side?: string` to the `JsonCounterexample` TypeScript interface in `vscode-extension/src/verifier.ts`. There is no logic change required in `async_vcgen.rs` — the SMT scripts already declare and pin `poll_iter` correctly.

Optionally, `outputPanel.ts` can render those two new fields (e.g. "Poll iteration 2, pre-await") in the structured channel for richer UX. This is a small, self-contained single-plan phase with clear, already-tested integration points.

**Primary recommendation:** Follow the exact TDD + E2E pattern from Phase 26 (`wmm_race_e2e.rs`): write a failing unit test for `build_counterexample_v2` first, wire the extraction, then add a TypeScript compile check (`npx tsc --noEmit`), then optionally augment `outputPanel.ts` rendering.

## Standard Stack

### Core
| Library / Crate | Version | Purpose | Why Standard |
|-----------------|---------|---------|--------------|
| `rust_fv_driver::parallel` | workspace | Hosts `build_counterexample_v2()` — the only Rust change site | All counterexample assembly happens here |
| `rust_fv_analysis::vcgen::VcKind` | workspace | Enum with `AsyncStateInvariantSuspend` / `AsyncStateInvariantResume` variants | Already imported in `parallel.rs` |
| `rust_fv_driver::json_output::JsonCounterexample` | workspace | Target struct with `poll_iteration: Option<usize>` and `await_side: Option<String>` | Fields exist but always `None` |
| TypeScript 5.3 | ^5.3.0 | VSCode extension language | Declared in `vscode-extension/package.json` |
| `npx tsc --noEmit` | via `package.json` | TypeScript compile check | Standard CI gate |

### Supporting
| Library / Crate | Version | Purpose | When to Use |
|-----------------|---------|---------|-------------|
| `rust_fv_solver::SolverResult::Sat(model)` | workspace | Z3 model providing `cx_pairs` | Context for `build_counterexample_v2` call |
| `vscode-extension/src/outputPanel.ts` | - | Optional: render `poll_iteration` and `await_side` in structured output | If planner includes optional UX task |

### Alternatives Considered
| Instead of | Could Use | Tradeoff |
|------------|-----------|----------|
| Parsing `poll_iter` from `cx_pairs` | Re-querying Z3 | cx_pairs already contains the model assignments; re-querying adds complexity with no benefit |
| Mapping VcKind to `await_side` in `build_counterexample_v2` | Mapping in `json_output.rs` | `build_counterexample_v2` already has access to `vc_location.vc_kind`; cleaner to do it there |

## Architecture Patterns

### Recommended Project Structure
```
crates/driver/src/
├── parallel.rs          # build_counterexample_v2() — ONLY change site in Rust
├── json_output.rs       # JsonCounterexample struct — fields already declared, no change
vscode-extension/src/
├── verifier.ts          # JsonCounterexample interface — add 2 optional fields
├── outputPanel.ts       # formatFailedFunction() — optional: render async context
```

### Pattern 1: Extract poll_iter from cx_pairs
**What:** `cx_pairs` is `&[(String, String)]` — pairs of `(name, value)` from the Z3 model. The async VCs declare `(declare-const poll_iter Int)` and pin it to the state id. When the VC is SAT, the Z3 model will include `("poll_iter", "<integer>")`.

**When to use:** Only inside `build_counterexample_v2()`, gated on `vc_location.vc_kind` being an async kind.

**Example:**
```rust
// Source: crates/driver/src/parallel.rs — build_counterexample_v2()
// After the existing variables/failing_location construction:

let poll_iteration = if matches!(
    vc_location.vc_kind,
    VcKind::AsyncStateInvariantSuspend
        | VcKind::AsyncStateInvariantResume
        | VcKind::AsyncPostcondition
) {
    pairs
        .iter()
        .find(|(name, _)| name == "poll_iter")
        .and_then(|(_, val)| val.trim().parse::<usize>().ok())
} else {
    None
};

let await_side = match vc_location.vc_kind {
    VcKind::AsyncStateInvariantSuspend => Some("pre_await".to_string()),
    VcKind::AsyncStateInvariantResume  => Some("post_await".to_string()),
    _ => None,
};
```

### Pattern 2: TypeScript interface extension
**What:** Add two optional fields to `JsonCounterexample` in `verifier.ts`. Fields must use `?:` (optional) because they are `skip_serializing_if = "Option::is_none"` on the Rust side — they will be absent for non-async VCs.

**Example:**
```typescript
// Source: vscode-extension/src/verifier.ts
/** Structured counterexample with typed variables and metadata (v2 schema). */
export interface JsonCounterexample {
  variables: JsonCexVariable[];
  failing_location: JsonLocation;
  vc_kind: string;
  violated_spec?: string;
  /** For async VCs: which poll iteration (0-based state_id) triggered the violation. */
  poll_iteration?: number;
  /** For async VCs: "pre_await" (suspension) or "post_await" (resumption) side. */
  await_side?: string;
}
```

### Pattern 3: TDD unit test for build_counterexample_v2
**What:** The existing `parallel.rs` test module already has a `test_verification_task_result_with_timing` test. Add a new test that calls `build_counterexample_v2` directly with async-typed cx_pairs containing `("poll_iter", "2")` and asserts the returned `JsonCounterexample` has `poll_iteration = Some(2)` and `await_side = Some("pre_await")` (for `AsyncStateInvariantSuspend`).

**Example pattern:**
```rust
#[test]
fn test_build_counterexample_v2_async_fields() {
    let cx_pairs = Some(vec![
        ("poll_iter".to_string(), "2".to_string()),
        ("counter".to_string(), "0".to_string()),
    ]);
    let vc_location = VcLocation {
        vc_kind: VcKind::AsyncStateInvariantSuspend,
        // ... other fields
    };
    let ir_func = make_minimal_async_func(); // reuse pattern from async_vcgen.rs tests
    let cex = build_counterexample_v2(cx_pairs.as_deref(), &vc_location, &ir_func).unwrap();
    assert_eq!(cex.poll_iteration, Some(2));
    assert_eq!(cex.await_side.as_deref(), Some("pre_await"));
}
```

### Pattern 4: E2E driver test for async counterexample population
**What:** Following `wmm_race_e2e.rs` pattern — build a minimal async `Function` with `coroutine_info`, run `verify_functions_parallel()`, assert the failing result has `counterexample_v2` with non-None `poll_iteration` and `await_side`.

**Key construction:** Use `make_async_func()` pattern from `async_vcgen.rs` tests: `CoroutineInfo { states: vec![yield_state(0, 0)], persistent_fields: vec![("counter", Ty::Int(...))] }` plus a falsifiable `state_invariant` (e.g. `"counter >= 1"` while counter defaults to 0).

### Anti-Patterns to Avoid
- **Changing `async_vcgen.rs`:** No change needed — SMT scripts already declare `poll_iter` correctly. The gap is purely in the extraction side.
- **Changing `json_output.rs`:** The struct fields `poll_iteration: Option<usize>` and `await_side: Option<String>` already exist with correct serde attributes. No change needed.
- **Making `await_side` depend on model pairs:** `await_side` is deterministically inferred from `vc_kind` — it is not a Z3 model value. Using cx_pairs for this would be wrong.
- **Adding `await_side` for `AsyncPostcondition`:** That VC kind has no await-side semantics — it fires at `Poll::Ready`. Only `Suspend`/`Resume` get `await_side`.

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Z3 model integer parsing | Custom parser | `str::parse::<usize>()` | Z3 outputs clean decimal integers for `Int` sort constants |
| VcKind string matching | String comparison | `matches!` macro on `VcKind` enum | Type-safe, exhaustive, compiler-checked |
| TypeScript compile verification | Custom check | `npx tsc --noEmit` in `vscode-extension/` | Already in project tooling |

**Key insight:** Both fields (`poll_iteration`, `await_side`) are trivially derivable from existing data — no new infrastructure needed.

## Common Pitfalls

### Pitfall 1: poll_iter absent in non-async Z3 models
**What goes wrong:** `cx_pairs.iter().find(|(name, _)| name == "poll_iter")` returns `None` for non-async VCs — which is correct behavior. But calling without the `VcKind` guard means non-async failures silently get `poll_iteration: None` (acceptable) rather than confusing `Some(0)` from an accidental match.
**Why it happens:** The `poll_iter` constant name could theoretically appear in non-async models.
**How to avoid:** Guard extraction with `matches!(vc_location.vc_kind, VcKind::AsyncStateInvariantSuspend | VcKind::AsyncStateInvariantResume | VcKind::AsyncPostcondition)`.
**Warning signs:** Test asserting `poll_iteration.is_none()` for non-async VCs fails.

### Pitfall 2: TypeScript interface missing optional marker
**What goes wrong:** Declaring `poll_iteration: number` (not `poll_iteration?: number`) causes TypeScript compile errors when consuming code doesn't provide the field, and causes runtime errors when deserializing non-async JSON (the field will be absent).
**Why it happens:** Forgetting `?` on optional fields.
**How to avoid:** Both fields MUST use `?:` — they are `skip_serializing_if = "Option::is_none"` on the Rust side.
**Warning signs:** `npx tsc --noEmit` produces errors at `counterexample_v2` usage sites.

### Pitfall 3: await_side string values must match spec
**What goes wrong:** Using `"suspension"` / `"resumption"` (the internal SMT encoding strings) instead of `"pre_await"` / `"post_await"` (the public API strings specified in the success criteria).
**Why it happens:** The `generate_invariant_vc()` function in `async_vcgen.rs` uses `side = "suspension"` / `"resumption"` internally. The JSON output uses different, user-facing strings.
**How to avoid:** Map `AsyncStateInvariantSuspend` → `"pre_await"` and `AsyncStateInvariantResume` → `"post_await"` as specified in Phase 27 success criteria. Do NOT reuse the internal strings.
**Warning signs:** E2E test asserting `await_side == "pre_await"` fails.

### Pitfall 4: build_counterexample_v2 is private — test must be in same module
**What goes wrong:** Trying to call `build_counterexample_v2` from an integration test in `crates/driver/tests/` fails because the function is `fn` (not `pub fn`).
**Why it happens:** The function was intentionally kept private.
**How to avoid:** Unit tests go in `parallel.rs`'s `#[cfg(test)] mod tests { ... }` block. The E2E test that validates async field propagation through the full pipeline goes in a new `crates/driver/tests/async_cex_e2e.rs`.
**Warning signs:** `error[E0603]: function 'build_counterexample_v2' is private` in test file.

### Pitfall 5: E2E test needs falsifiable state_invariant
**What goes wrong:** Using `"counter >= 0"` with counter default 0 produces UNSAT (verified) — no counterexample is generated, so `counterexample_v2` is None.
**Why it happens:** A satisfiable assertion (always-true invariant) won't trigger SAT from Z3.
**How to avoid:** Use a spec that is falsifiable given the default SMT model — e.g. `"counter >= 1"` while `counter` has no lower bound constraint, or `"_0 >= 10"` with `_0` unconstrained.
**Warning signs:** E2E test asserting `counterexample_v2.is_some()` fails.

## Code Examples

### How cx_pairs arrive in build_counterexample_v2
```rust
// Source: crates/driver/src/parallel.rs lines 309-315
Ok(rust_fv_solver::SolverResult::Sat(model)) => {
    let cx_pairs = model.map(|m| m.assignments);  // Vec<(String, String)>
    let counterexample_v2 =
        build_counterexample_v2(cx_pairs.as_deref(), &vc.location, &task.ir_func);
    // ...
}
```

### How poll_iter is declared in the SMT script (async_vcgen.rs)
```rust
// Source: crates/analysis/src/async_vcgen.rs lines 224-228
// For state invariant VCs — poll_iter is PINNED to state.state_id
script.push(Command::DeclareConst("poll_iter".to_string(), Sort::Int));
script.push(Command::Assert(Term::Eq(
    Box::new(Term::Const("poll_iter".to_string())),
    Box::new(Term::IntLit(state.state_id as i128)),
)));

// For async postcondition VCs — poll_iter is bounded but not pinned
script.push(Command::DeclareConst("poll_iter".to_string(), Sort::Int));
// assert 0 <= poll_iter < state_count
```

### Existing parallel.rs test module pattern
```rust
// Source: crates/driver/src/parallel.rs lines 419-445
#[cfg(test)]
mod tests {
    use super::*;
    // ... existing tests ...

    // New test to add:
    #[test]
    fn test_build_counterexample_v2_async_fields_suspension() {
        // ... uses build_counterexample_v2 directly (same module = access OK)
    }
}
```

### TypeScript interface current state vs target
```typescript
// CURRENT (verifier.ts lines 39-44) — missing async fields:
export interface JsonCounterexample {
  variables: JsonCexVariable[];
  failing_location: JsonLocation;
  vc_kind: string;
  violated_spec?: string;
  // poll_iteration and await_side NOT declared here — GAP
}

// TARGET after phase 27:
export interface JsonCounterexample {
  variables: JsonCexVariable[];
  failing_location: JsonLocation;
  vc_kind: string;
  violated_spec?: string;
  poll_iteration?: number;    // new — for async VCs only
  await_side?: string;        // new — "pre_await" | "post_await" | undefined
}
```

### Optional outputPanel.ts rendering
```typescript
// outputPanel.ts — in formatFailedFunction(), after the counterexample block
if (failure.counterexample_v2?.poll_iteration !== undefined) {
  const side = failure.counterexample_v2.await_side ?? 'unknown';
  channel.appendLine(
    `    Async context: poll iteration ${failure.counterexample_v2.poll_iteration}, ${side}`
  );
}
```

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| `poll_iteration: None` (Phase 23 placeholder) | Extract from cx_pairs `poll_iter` constant | Phase 27 | Async counterexamples show which await point failed |
| TypeScript `JsonCounterexample` missing async fields | Add `poll_iteration?: number`, `await_side?: string` | Phase 27 | TypeScript interface matches Rust struct exactly |

**Deprecated/outdated:**
- The `poll_iteration: None` / `await_side: None` placeholder pattern in `build_counterexample_v2` is replaced by real extraction.

## Open Questions

1. **Should outputPanel.ts rendering be in the single plan or treated as a bonus task?**
   - What we know: The success criteria does not mandate `outputPanel.ts` changes — it says "optional outputPanel.ts rendering" in the roadmap.
   - What's unclear: Whether rendering the async context line in the structured panel is worth a separate task.
   - Recommendation: Include as a task in the single plan (it's ~5 lines of TypeScript) — low risk, high UX value.

2. **Does `poll_iter` appear in the Z3 model for AsyncPostcondition VCs when SAT?**
   - What we know: `generate_async_postcondition_vc()` declares `poll_iter` with `0 <= poll_iter < state_count` constraint but does NOT pin it. When SAT, Z3 will assign it some value in range.
   - What's unclear: Whether Z3 always includes `poll_iter` in the model output when it's declared but not pinned.
   - Recommendation: The extraction code `pairs.iter().find(...)` handles absence gracefully (returns `None`). No special casing needed. Verify in unit test.

## Validation Architecture

**Note:** `workflow.nyquist_validation` is not set in `.planning/config.json` (field absent). Applying standard validation architecture for the project.

### Test Framework
| Property | Value |
|----------|-------|
| Framework | Rust `cargo test` + TypeScript `tsc --noEmit` |
| Config file | `Cargo.toml` (workspace) + `vscode-extension/tsconfig.json` |
| Quick run command | `cargo test -p rust-fv-driver -- parallel 2>&1 \| tail -20` |
| Full suite command | `cargo test -p rust-fv-driver && cd vscode-extension && npx tsc --noEmit` |
| Estimated runtime | ~15 seconds (Rust unit tests) + ~5 seconds (tsc) |

### Phase Requirements → Test Map
| Req ID | Behavior | Test Type | Automated Command | File Exists? |
|--------|----------|-----------|-------------------|-------------|
| ASY-02 | `poll_iteration` extracted from Z3 model `poll_iter` constant | unit | `cargo test -p rust-fv-driver test_build_counterexample_v2_async_fields -- --nocapture` | ❌ Wave 0 gap |
| ASY-02 | `await_side` inferred from `VcKind::AsyncStateInvariantSuspend` → `"pre_await"` | unit | `cargo test -p rust-fv-driver test_build_counterexample_v2_async_fields -- --nocapture` | ❌ Wave 0 gap |
| ASY-02 | `await_side` inferred from `VcKind::AsyncStateInvariantResume` → `"post_await"` | unit | `cargo test -p rust-fv-driver test_build_counterexample_v2_await_side_resume -- --nocapture` | ❌ Wave 0 gap |
| ASY-02 | TypeScript `JsonCounterexample` declares `poll_iteration?: number` and `await_side?: string` | compile | `cd vscode-extension && npx tsc --noEmit` | ❌ Wave 0 gap (fields absent) |
| ASY-02 | E2E: driver pipeline produces `counterexample_v2` with populated async fields | integration | `cargo test -p rust-fv-driver async_cex_e2e -- --nocapture` | ❌ Wave 0 gap |

### Nyquist Sampling Rate
- **Minimum sample interval:** After every committed task → run: `cargo test -p rust-fv-driver -- parallel 2>&1 | tail -20`
- **Full suite trigger:** Before merging final task of plan 27-01
- **Phase-complete gate:** Full suite green (`cargo test` + `npx tsc --noEmit`) before `/gsd:verify-work` runs
- **Estimated feedback latency per task:** ~15 seconds

### Wave 0 Gaps (must be created before implementation)
- [ ] Unit tests in `crates/driver/src/parallel.rs` `#[cfg(test)]` block — covers poll_iteration and await_side extraction
- [ ] `crates/driver/tests/async_cex_e2e.rs` — E2E driver integration test for async counterexample field population
- [ ] TypeScript interface update in `vscode-extension/src/verifier.ts` — prerequisite for `tsc --noEmit` to pass

*(The Rust test framework and TypeScript toolchain are fully configured — no framework install needed.)*

## Sources

### Primary (HIGH confidence)
- Direct code read: `crates/driver/src/parallel.rs` lines 362-417 — `build_counterexample_v2()` implementation, `poll_iteration: None` placeholder confirmed
- Direct code read: `crates/driver/src/json_output.rs` lines 52-67 — `JsonCounterexample` struct with `poll_iteration: Option<usize>` and `await_side: Option<String>` already declared
- Direct code read: `vscode-extension/src/verifier.ts` lines 38-44 — `JsonCounterexample` TypeScript interface missing `poll_iteration` and `await_side` fields confirmed
- Direct code read: `crates/analysis/src/async_vcgen.rs` lines 223-228 — `poll_iter` constant declared and pinned in state invariant VCs
- Direct code read: `crates/analysis/src/vcgen.rs` lines 136-141 — `AsyncStateInvariantSuspend`, `AsyncStateInvariantResume`, `AsyncPostcondition` VcKind variants

### Secondary (MEDIUM confidence)
- Direct code read: `crates/driver/tests/wmm_race_e2e.rs` — E2E test pattern (VerificationTask construction, `verify_functions_parallel`, result assertion)
- Direct code read: `crates/driver/tests/ghost_predicate_e2e.rs` — Alternative E2E test pattern with `make_ghost_test_func`
- Direct code read: `crates/analysis/tests/async_verification.rs` — Async function construction patterns for tests
- Direct code read: `.planning/STATE.md` — Phase 23 decision: "poll_iteration + await_side on JsonCounterexample with skip_serializing_if for backward compat" confirms the tech debt origin

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH — all crates and files verified by direct read
- Architecture: HIGH — exact change sites identified, no ambiguity
- Pitfalls: HIGH — derived from actual code structure and test patterns in the codebase
- TypeScript compile check: HIGH — `npx tsc --noEmit` pattern confirmed from Phase 25 success criteria

**Research date:** 2026-02-23
**Valid until:** 2026-03-25 (stable internal codebase — no external dependencies)
