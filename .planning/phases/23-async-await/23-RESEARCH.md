# Phase 23: Async/Await Verification - Research

**Researched:** 2026-02-22
**Domain:** Rust async/coroutine MIR verification — SMT encoding of coroutine state machines
**Confidence:** HIGH (based on direct codebase analysis + official rustc nightly docs)

<user_constraints>
## User Constraints (from CONTEXT.md)

### Locked Decisions

- **Supported async patterns**: `async fn` with `.await`, nested `async fn` calls, `async {}` blocks — IN SCOPE. `Pin<Box<dyn Future>>`, combinators, async traits — OUT OF SCOPE.
- **`select!` macro**: IN SCOPE with conservative over-approximation — modeled as non-deterministic branch choice (boolean SMT variable for branch).
- **`join!` macro**: IN SCOPE with conservative over-approximation — modeled as sequential execution (left branch then right branch).
- **`#[state_invariant]` scope**: Can reference all of — function-local variables, variables captured from enclosing scope, values reachable through function arguments (e.g. fields of `&mut State`).
- **`#[state_invariant]` must hold at BOTH sides of every `.await`**: at suspension (just before yielding) AND at resumption (just after control returns from the awaited future).
- **`#[state_invariant]` at resumption can reference the awaited expression result** — e.g. `awaited_result >= 0`.
- **Failure reporting**: Report BOTH the annotation location (which invariant) AND the specific `.await` expression that triggered the failure (suspension or resumption side).
- **Counterexample**: variable values at point of violation (typed Rust values, consistent with Phase 19/25 format) PLUS which poll iteration (1st, 2nd, …) triggered the violation under sequential polling.
- **Cross-`.await` references**: YES — `#[requires]` and `#[ensures]` can reference any local variable visible at the annotation site, including locals set before or after `.await` boundaries.
- **Dual-source SMT**: callee AST constraints (Set A) + annotation constraints (Set B) concatenated — no deduplication (standard architecture).
- **Nested async fn calls**: callee SMT constraints generated from both its code AST (Set A) and annotations (Set B), no special trust boundary.

### Claude's Discretion

- Exact timing model for `#[requires]` (call site vs. first poll)
- Exact timing model for `#[ensures]` (final resolution vs. each `Poll::Ready`)
- IDE counterexample surface implementation (reuse Phase 25 infrastructure)
- Internal encoding of coroutine state machine (how MIR coroutine states map to SMT variables across suspension points)

### Deferred Ideas (OUT OF SCOPE)

- None — discussion stayed within phase scope
</user_constraints>

<phase_requirements>
## Phase Requirements

| ID | Description | Research Support |
|----|-------------|-----------------|
| ASY-01 | User can annotate `async fn` with `#[requires]`/`#[ensures]` and have functional properties verified under sequential polling model | Driver coroutine detection via `body.coroutine`, IR `CoroutineInfo` struct, `async_vcgen.rs` module for postcondition at `Poll::Ready`; timing: `#[requires]` at call site, `#[ensures]` at final resolution |
| ASY-02 | User can write `#[state_invariant]` to specify invariants that must hold at every `.await` suspension point in an `async fn` | New `#[state_invariant]` macro (same `spec_attribute` pattern); `Contracts.state_invariant` field; `async_vcgen.rs` generates per-`Yield`-terminator VCs checking invariant at suspension and resumption; `VcKind::AsyncStateInvariant` |
</phase_requirements>

---

## Summary

Phase 23 adds SMT verification of `async fn` code under a **sequential polling model**. The key abstraction is that an `async fn` compiles to a coroutine MIR body — rustc represents each `.await` suspension point as a `TerminatorKind::Yield` in the pre-transform MIR. The verification approach splits an `async fn` into coroutine states (code segments between `Yield` terminators), generates SMT VCs per-state, and checks that `#[requires]`/`#[ensures]` hold at call site and final resolution, plus that `#[state_invariant]` holds at both sides of every `Yield`.

The existing architecture handles this cleanly: coroutine detection happens in `driver/src/mir_converter.rs` (already has rustc API access via `body.coroutine`), the stable IR gets two new additive fields (`CoroutineInfo` on `Function`, `state_invariant` on `Contracts`), and a new `analysis/src/async_vcgen.rs` module generates the VCs (parallel to the existing `hof_vcgen.rs` pattern for HOF). The `#[state_invariant]` macro follows the existing `spec_attribute` pattern and requires zero changes to macro infrastructure.

The sequential polling model means: each `Yield` is treated as a state boundary; variables persisted across `.await` become `CoroutineState` field names in the SMT encoding; the invariant is an SMT assertion checked at each `Yield` site (both before and after). The poll iteration counter is an integer SMT constant bounded by the state count; the counterexample reports which state (poll iteration) triggered the violation. The existing `cex_render.rs` and `JsonCounterexample` infrastructure is extended with a `poll_iteration: Option<usize>` field.

**Primary recommendation:** Add `CoroutineInfo` to `ir::Function`, add `state_invariant` to `ir::Contracts`, add `#[state_invariant]` macro, add `VcKind::AsyncStateInvariant` and `VcKind::AsyncPostcondition`, and implement `async_vcgen.rs` following the `hof_vcgen.rs` pattern — dispatched from `generate_vcs_with_db` when `func.coroutine_info.is_some()`.

---

## Standard Stack

### Core (already in codebase — no new dependencies needed)

| Library | Version | Purpose | Why Standard |
|---------|---------|---------|--------------|
| `rust_fv_smtlib` | workspace | SMT-LIB2 AST construction | Existing. `Term::Forall`, `Term::And`, `Term::ITE`, `Term::Eq` sufficient for all async VCs |
| `rust_fv_solver` | workspace | Z3 process interface | Existing. `Z3Solver::check_sat_raw` works unchanged |
| `rustc_middle::mir` | nightly-2026-02-11 | MIR body, `CoroutineInfo`, `TerminatorKind::Yield` | Existing driver already imports these |

### New IR Constructs (additive to existing `ir.rs`)

```rust
// Add to analysis/src/ir.rs

/// Coroutine state machine derived from an async fn.
/// Present when the function was compiled from `async fn` or `async {}`.
#[derive(Debug, Clone)]
pub struct CoroutineInfo {
    /// Each entry is a (state_id, await_point_description) pair.
    /// state_id 0 = code before first .await
    /// state_id N = code after N-th .await resumes
    pub states: Vec<CoroutineState>,
    /// Locals that persist across .await boundaries (coroutine struct fields).
    /// Each is (smt_name, Ty).
    pub persistent_fields: Vec<(String, Ty)>,
}

#[derive(Debug, Clone)]
pub struct CoroutineState {
    /// 0-based state index (== poll iteration that runs this segment)
    pub state_id: usize,
    /// IR basic block index range for this state's code
    pub entry_block: BlockId,
    /// Where control leaves this state (Yield or Return)
    pub exit_kind: CoroutineExitKind,
    /// Source location of the .await that ended this state (for diagnostics)
    pub await_source_line: Option<u32>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum CoroutineExitKind {
    /// Suspends at .await (TerminatorKind::Yield)
    Yield,
    /// Returns Poll::Ready (TerminatorKind::Return)
    Return,
}

// Add field to Contracts:
pub struct Contracts {
    // ... existing fields ...
    /// #[state_invariant(...)] — must hold at every .await suspension AND resumption.
    pub state_invariant: Option<SpecExpr>,
}

// Add field to Function:
pub struct Function {
    // ... existing fields ...
    /// Present when function is an async fn or async block.
    pub coroutine_info: Option<CoroutineInfo>,
}
```

### New VcKind Variants (additive to existing `VcKind` enum)

```rust
pub enum VcKind {
    // ... existing ...
    /// #[state_invariant] check at .await suspension point
    AsyncStateInvariantSuspend,
    /// #[state_invariant] check at .await resumption point
    AsyncStateInvariantResume,
    /// #[ensures] check at Poll::Ready (async fn postcondition)
    AsyncPostcondition,
}
```

### New Module

```
analysis/src/async_vcgen.rs   (NEW, ~300 lines)
    pub fn generate_async_vcs(func: &Function) -> Vec<VerificationCondition>
```

### New Macro

```rust
// crates/macros/src/lib.rs — add #[state_invariant]
#[proc_macro_attribute]
pub fn state_invariant(attr: TokenStream, item: TokenStream) -> TokenStream {
    spec_attribute("state_invariant", attr, item)  // ZERO new infrastructure
}
```

**Installation:** No new `Cargo.toml` dependencies. All within existing workspace crates.

---

## Architecture Patterns

### Recommended Project Structure (changes only)

```
crates/
├── analysis/src/
│   ├── ir.rs                  # MODIFY: add CoroutineInfo, CoroutineState, CoroutineExitKind
│   │                          #         add state_invariant to Contracts
│   │                          #         add coroutine_info to Function
│   ├── vcgen.rs               # MODIFY: dispatch to async_vcgen when coroutine_info.is_some()
│   │                          #         add VcKind::AsyncStateInvariantSuspend/Resume/AsyncPostcondition
│   └── async_vcgen.rs         # NEW: generate per-state VCs for async fn
│
├── driver/src/
│   └── mir_converter.rs       # MODIFY: detect body.coroutine, populate CoroutineInfo
│                              #         extract Yield terminators as state boundaries
│                              #         extract persistent_fields from coroutine_layout
│
└── macros/src/
    └── lib.rs                 # MODIFY: add #[state_invariant] proc_macro_attribute
```

### Pattern 1: Coroutine Detection in MIR Converter (driver crate)

**What:** Check `body.coroutine` to detect async fn; extract `Yield` terminators as state boundaries.

**When to use:** In `convert_mir()` in `mir_converter.rs`, after building `basic_blocks`.

**Key rustc API (confirmed nightly):**

```rust
// Source: https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/struct.CoroutineInfo.html
if let Some(coro_info) = &body.coroutine {
    // coroutine_kind distinguishes async fn from gen fn:
    use rustc_hir::CoroutineKind;
    let is_async = matches!(
        coro_info.coroutine_kind,
        CoroutineKind::Desugared(rustc_hir::CoroutineDesugaring::Async, _)
    );

    if is_async {
        let coroutine_info = extract_coroutine_states(body);
        // attach to ir::Function
    }
}
```

**Yield terminator extraction:**

```rust
// Source: https://doc.rust-lang.org/beta/nightly-rustc/rustc_middle/mir/enum.TerminatorKind.html
// TerminatorKind::Yield { value, resume, resume_arg, drop }
fn extract_coroutine_states(body: &mir::Body<'_>) -> ir::CoroutineInfo {
    let mut states = Vec::new();
    let mut state_id = 0usize;

    for (bb_idx, bb_data) in body.basic_blocks.iter_enumerated() {
        if let Some(term) = &bb_data.terminator {
            if let mir::TerminatorKind::Yield { resume, resume_arg, .. } = &term.kind {
                states.push(ir::CoroutineState {
                    state_id,
                    entry_block: bb_idx.as_usize(),
                    exit_kind: ir::CoroutineExitKind::Yield,
                    await_source_line: term.source_info.span
                        .lo()
                        .to_u32()
                        .into(), // approximate line from span
                });
                state_id += 1;
            }
        }
    }

    // Final state (after last resume, runs to Return)
    states.push(ir::CoroutineState {
        state_id,
        entry_block: 0, // placeholder — the last resume basic block
        exit_kind: ir::CoroutineExitKind::Return,
        await_source_line: None,
    });

    // Persistent fields from coroutine_layout (populated after state transform)
    let persistent_fields = extract_persistent_fields(body);

    ir::CoroutineInfo { states, persistent_fields }
}
```

**WARNING (from STATE.md blocker):** "Async coroutine MIR shape may have changed post-PR#145330 — validate with `RUSTFLAGS="-Zunpretty=mir"` before Phase 23." The MIR shape must be validated on `nightly-2026-02-11` before implementing state extraction.

### Pattern 2: Async VC Generation (`async_vcgen.rs`)

**What:** For each coroutine state, generate VCs for `#[state_invariant]` at suspension and resumption.

**When to use:** Dispatched from `generate_vcs_with_db` when `func.coroutine_info.is_some()`.

**Example dispatch in `vcgen.rs`:**

```rust
// In generate_vcs_with_db, after HOF VCs (following hof_vcgen pattern):

// ASY-01 / ASY-02: Generate async VCs if this is a coroutine
if func.coroutine_info.is_some() {
    let async_vcs = crate::async_vcgen::generate_async_vcs(func);
    conditions.extend(async_vcs);
}
```

**SMT encoding for `#[state_invariant]` at each `.await`:**

The sequential polling model means all locals are SSA-versioned across states. The invariant is checked at two points per `Yield` state:

1. **Suspension check**: `(assert (not INVARIANT_at_yield))` → UNSAT = invariant holds before yield
2. **Resumption check**: `(assert (not INVARIANT_after_resume))` → UNSAT = invariant holds after resume

Variables visible across `.await` are the `persistent_fields` (coroutine struct fields); they are declared as SMT constants once and referenced in both suspension and resumption checks.

**SMT script structure for a 2-await async fn with `#[state_invariant(x >= 0)]`:**

```smt2
(set-logic QF_LIA)
; Coroutine persistent fields (cross-await locals)
(declare-const x Int)
(declare-const awaited_result_1 Int)   ; result of 1st .await

; Poll iteration counter (for counterexample)
(declare-const poll_iter Int)
(assert (>= poll_iter 0))
(assert (<= poll_iter 2))   ; bounded by state count

; State 0 code constraints (before 1st .await)
(assert (= x initial_value))  ; code constraints for state 0

; Suspension check at 1st .await (poll_iter = 1)
(assert (= poll_iter 1))
(assert (not (>= x 0)))    ; negated invariant
(check-sat)                ; SAT => invariant violated at suspension
```

### Pattern 3: `#[requires]`/`#[ensures]` Timing for Async (Claude's Discretion)

**Recommendation based on standard functional verification semantics:**

- **`#[requires]`**: Checked at call site (synchronous, before `Future` is first polled). This is consistent with existing sync contract semantics — the precondition is the caller's obligation at the moment `async fn` is called and the `Future` is created. Implementation: emit precondition VC in state 0 declarations (before first `Yield`).

- **`#[ensures]`**: Checked at final `Poll::Ready` resolution — i.e., at the `TerminatorKind::Return` of the last coroutine state. This is `AsyncPostcondition` VcKind. The `result` variable in `#[ensures]` refers to `Future::Output` value (the return local `_0`).

**Rationale:** This matches how tools like Prusti and Kani handle async — pre at creation, post at resolution — and is the "semantically cleanest" model consistent with sync contract semantics as the CONTEXT.md requests.

### Pattern 4: `select!` Encoding (locked decision)

**What:** Model `select!` as a non-deterministic branch choice.

**SMT encoding:**

```rust
// In async_vcgen.rs — when a select! macro site is detected:
// Introduce a boolean SMT variable for branch choice, generate constraints
// for both branches, assert (or branch_a branch_b) — solver explores both.

// (declare-const select_branch_0 Bool)
// Branch A constraints under (assert select_branch_0)
// Branch B constraints under (assert (not select_branch_0))
```

**Detection:** `select!` expands to a match on `Poll` results with nested futures. In MIR this appears as multiple `Call` terminators with multiple potential resume paths in a single state. Detection: look for `::tokio::select` or `::futures::select` in function call names, OR look for the `SwitchInt` on multiple `Poll::Pending`/`Poll::Ready` targets within a single coroutine state. Conservative: if uncertain, treat as non-deterministic.

### Pattern 5: `join!` Encoding (locked decision)

**What:** Model `join!` as sequential left-then-right.

**Implementation:** `join!` desugars to polling both futures in order. In the sequential model this is: State N awaits left future to completion, State N+1 awaits right future to completion. The MIR contains two consecutive `Yield` terminators (one per future). The existing state extraction loop handles this naturally — each `Yield` becomes a separate state. No special handling needed.

### Pattern 6: Counterexample with Poll Iteration

**What:** Extend `JsonCounterexample` with async-specific metadata.

**Extension to `json_output.rs`:**

```rust
pub struct JsonCounterexample {
    pub variables: Vec<JsonCexVariable>,
    pub failing_location: JsonLocation,
    pub vc_kind: String,
    pub violated_spec: Option<String>,
    /// Present only for async VCs — which poll iteration (0-based) triggered the violation
    #[serde(skip_serializing_if = "Option::is_none")]
    pub poll_iteration: Option<usize>,
    /// Present only for async VCs — "suspension" or "resumption"
    #[serde(skip_serializing_if = "Option::is_none")]
    pub await_side: Option<String>,
}
```

**Reuse Phase 25 infrastructure:** The VSCode extension's `renderCounterexampleLines` helper in `diagnostics.ts` is already generic. The output panel `outputPanel.ts` already consumes `counterexample_v2`. Only add `poll_iteration` and `await_side` to the TypeScript interfaces to surface the new fields.

### Anti-Patterns to Avoid

- **Do NOT detect coroutines in the analysis crate**: Analysis crate is rustc-free. Coroutine detection MUST happen in `driver/src/mir_converter.rs`.
- **Do NOT add a new SMT logic**: Existing `QF_LIA` / `QF_BV` suffice. Async does NOT require quantifiers unless referencing cross-state locals with `forall`.
- **Do NOT model coroutine scheduling**: The sequential polling model means no scheduler, no fairness, no concurrent interleaving. One future polls to completion before the next begins.
- **Do NOT use mutable global for coroutine state**: Carry `CoroutineInfo` as a field on `ir::Function`. The parallel executor runs functions concurrently — global state would data-race.
- **Do NOT try to extract `coroutine_layout` before the state transform pass**: `coroutine_layout` is `None` before the coroutine lowering pass. Extract persistent fields from local_decls instead (locals with internal names `__awaitee`, `__coroutine_field_N`, etc.) or use `vars_and_temps_iter` and filter to those that span multiple states.

---

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Counterexample rendering | Custom async renderer | Extend existing `cex_render::render_counterexample` + `JsonCounterexample` with `poll_iteration` field | Phase 19/25 infrastructure handles all typed value rendering; only need to add two optional fields |
| SMT term construction | Custom async term builders | Existing `Term::And`, `Term::Not`, `Term::ITE`, `Term::Eq`, `Term::IntLe` | All invariant checks are just boolean assertions — same terms as loop invariants |
| HOF dispatch pattern | New entry point in vcgen | Copy `hof_vcgen` pattern: `if func.coroutine_info.is_some() { ... }` | HOF already established the "sub-module per feature" dispatch pattern in vcgen.rs |
| Macro infrastructure | New macro parser | `spec_attribute("state_invariant", attr, item)` — ZERO new code | Existing helper already handles any keyword → doc attribute |
| Coroutine state persistence | Custom field tracking | Use `body.local_decls` + var_debug_info filtering for cross-await locals | MIR already tracks which locals survive across yield points |

**Key insight:** The hardest part of async verification is encoding the sequential polling semantics — not the SMT queries. The SMT queries themselves are simpler than loop invariant queries (no induction, just bounded state enumeration).

---

## Common Pitfalls

### Pitfall 1: Coroutine MIR Shape May Have Changed (Pre-Validated Risk)

**What goes wrong:** The MIR structure of coroutine bodies post-PR#145330 (tracked in STATE.md) may differ from what the research architecture assumed. Specifically, the `TerminatorKind::Yield` locations and state discriminant structure may be different in `nightly-2026-02-11`.

**Why it happens:** Rustc's coroutine lowering pass is actively evolving. The shape of pre-transform coroutine MIR (which is what `after_analysis` sees) can change between nightly versions.

**How to avoid:** Before implementing state extraction, validate the actual MIR shape with:
```bash
RUSTFLAGS="-Zunpretty=mir" cargo check --manifest-path /path/to/test/Cargo.toml 2>&1 | grep -A 20 "async fn"
```
Confirm that `TerminatorKind::Yield` is present in the pre-transform body and that the state discriminant `SwitchInt` is visible.

**Warning signs:** If coroutine detection returns `false` for a known `async fn`, or if `Yield` terminators are missing, the pass ordering is wrong — verify `after_analysis` is the right hook.

### Pitfall 2: Persistent Field Extraction Before `coroutine_layout` Is Populated

**What goes wrong:** Attempting to extract persistent fields from `body.coroutine.coroutine_layout` fails because `coroutine_layout` is `None` in the pre-lowering MIR body seen at `after_analysis`.

**Why it happens:** `coroutine_layout` is populated by the MIR coroutine lowering pass, which runs AFTER `after_analysis`.

**How to avoid:** Extract persistent fields from `body.local_decls` directly — look for locals whose `source_info` spans multiple basic blocks including Yield terminators, OR use the names produced by `var_debug_info` to identify which named locals persist across states. Alternatively, conservatively treat ALL locals in the function as persistent (sound but over-approximate).

**Warning signs:** `body.coroutine.as_ref().unwrap().coroutine_layout.is_none()` returns true — use alternative extraction strategy.

### Pitfall 3: `.await` Desugaring Creates Intermediate States

**What goes wrong:** Each `.await expr` in Rust desugars to a loop that polls until `Poll::Ready`. This creates multiple MIR basic blocks and potentially multiple `Yield` terminators per source-level `.await`. Counting `Yield` terminators != counting source `.await` points.

**Why it happens:** The desugaring of `.await` generates a polling loop:
```rust
loop {
    match future.poll(cx) {
        Poll::Ready(v) => break v,
        Poll::Pending => yield,  // <- one Yield per poll attempt
    }
}
```

**How to avoid:** Group consecutive `Yield` terminators that share the same awaited future (same source span) into a single logical suspension point. Under the sequential polling model, treat each source `.await` as a single state transition regardless of how many poll iterations it takes. The poll_iteration counter in the counterexample is per source-level `.await`, not per MIR `Yield`.

**Warning signs:** State count in `CoroutineInfo` is much larger than the number of `.await` expressions in the source.

### Pitfall 4: `select!` / `join!` Detection Is Fragile

**What goes wrong:** Detecting `select!` and `join!` macros by looking for their expanded MIR form is brittle — macro expansion depends on the tokio/futures version and can change.

**Why it happens:** `select!` from tokio and `select!` from futures crate expand differently. Name-based detection of `::tokio::select` is insufficient.

**How to avoid:** For this phase, use a conservative heuristic: if the same coroutine state contains multiple Yield terminators with different resume basic blocks (indicating multi-future polling), treat it as a `select!`-like construct and apply the non-deterministic branch encoding. For `join!`, detect two consecutive Yield terminators where the first resumes to the second — treat as sequential.

**Warning signs:** Counterexample says "no invariant violation found" for a function that clearly has one — likely a false negative from missed `select!` detection.

### Pitfall 5: `#[state_invariant]` Extraction from HIR

**What goes wrong:** The `state_invariant` doc attribute is emitted by the macro but not extracted in `callbacks.rs::extract_contracts()`.

**Why it happens:** `extract_contracts()` currently only scans for `requires`, `ensures`, `invariant`, `decreases`, `fn_spec`, etc. — it has no case for `state_invariant`.

**How to avoid:** Add `"state_invariant"` to the doc attribute scanning pattern in `callbacks.rs`. The attribute format will be `rust_fv::state_invariant::EXPR_STRING` following the existing `spec_attribute` convention. This is a one-liner addition to the existing scan.

**Warning signs:** `func.contracts.state_invariant.is_none()` even when `#[state_invariant]` is on the function.

---

## Code Examples

Verified patterns from codebase + official docs:

### Coroutine Detection in `mir_converter.rs`

```rust
// Source: https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/struct.CoroutineInfo.html
// Source: direct codebase inspection of convert_mir() in driver/src/mir_converter.rs

pub fn convert_mir(
    tcx: TyCtxt<'_>,
    local_def_id: LocalDefId,
    body: &mir::Body<'_>,
    contracts: ir::Contracts,
) -> ir::Function {
    // ... existing code ...

    // Detect async fn / coroutine (NEW)
    let coroutine_info = body.coroutine.as_ref().and_then(|coro| {
        use rustc_hir::{CoroutineDesugaring, CoroutineKind};
        let is_async = matches!(
            coro.coroutine_kind,
            CoroutineKind::Desugared(CoroutineDesugaring::Async, _)
        );
        if is_async {
            Some(extract_coroutine_info(body))
        } else {
            None
        }
    });

    ir::Function {
        // ... existing fields ...
        coroutine_info,
    }
}
```

### Dispatch in `vcgen.rs`

```rust
// In generate_vcs_with_db(), after HOF section:
// Source: hof_vcgen dispatch pattern (line 735-739 in vcgen.rs)

// ASY-01 / ASY-02: Generate async VCs if this is a coroutine
if func.coroutine_info.is_some() {
    let async_vcs = crate::async_vcgen::generate_async_vcs(func);
    conditions.extend(async_vcs);
}
```

### Macro Addition (`macros/src/lib.rs`)

```rust
// Source: existing spec_attribute pattern (line 285-300 in macros/src/lib.rs)

/// Attach a state invariant to an async function.
///
/// The invariant must hold at every `.await` suspension point —
/// both when yielding (suspension) and when resuming (resumption).
///
/// # Example
///
/// ```ignore
/// #[state_invariant(x >= 0)]
/// async fn increment_async(x: &mut i32) {
///     some_future().await;
///     *x += 1;
/// }
/// ```
#[proc_macro_attribute]
pub fn state_invariant(attr: TokenStream, item: TokenStream) -> TokenStream {
    spec_attribute("state_invariant", attr, item)
}
```

### Contract Extraction in `callbacks.rs`

```rust
// Extend extract_contracts() to scan for state_invariant:
// Source: existing pattern in callbacks.rs (doc attr scanning)

if doc_value.starts_with("rust_fv::state_invariant::") {
    let expr_str = &doc_value["rust_fv::state_invariant::".len()..];
    contracts.state_invariant = Some(SpecExpr {
        expr: expr_str.to_string(),
        // ... span info ...
    });
}
```

### `async_vcgen.rs` Structure

```rust
// Source: hof_vcgen.rs pattern (crates/analysis/src/hof_vcgen.rs)

pub fn generate_async_vcs(func: &Function) -> Vec<VerificationCondition> {
    let Some(coro_info) = &func.coroutine_info else {
        return vec![];
    };

    let mut vcs = Vec::new();

    // ASY-01: Postcondition VC (at Poll::Ready / Return state)
    if !func.contracts.ensures.is_empty() {
        vcs.push(generate_async_postcondition_vc(func));
    }

    // ASY-02: State invariant VCs (per Yield state)
    if let Some(invariant) = &func.contracts.state_invariant {
        for state in &coro_info.states {
            if state.exit_kind == CoroutineExitKind::Yield {
                // Suspension check
                vcs.push(generate_invariant_vc(func, state, invariant, AwaitSide::Suspension));
                // Resumption check
                vcs.push(generate_invariant_vc(func, state, invariant, AwaitSide::Resumption));
            }
        }
    }

    vcs
}
```

---

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| Generators (RFC 2033, unstable) | Coroutines (stabilized Rust 1.75) | Late 2023 | `body.coroutine` field replaces `body.generator_kind` |
| `TerminatorKind::GeneratorDrop` | `TerminatorKind::Yield` with drop block field | Rust 1.75 | Yield terminator carries resume and drop targets |
| `CoroutineKind::Async(_)` naming | `CoroutineKind::Desugared(CoroutineDesugaring::Async, _)` | Approx 2024 | More precise variant matching needed |

**Deprecated/outdated:**
- `body.generator_kind()`: Replaced by `body.coroutine.as_ref().map(|c| c.coroutine_kind)`. Do not use the old generator API.

---

## Open Questions

1. **Exact MIR shape in `nightly-2026-02-11` for Yield terminators**
   - What we know: `TerminatorKind::Yield { value, resume, resume_arg, drop }` exists per official nightly docs
   - What's unclear: Whether the `after_analysis` hook sees pre-transform or post-transform coroutine MIR; whether `Yield` terminators are present or have been lowered to state discriminant switches
   - Recommendation: First task in Phase 23 MUST be a validation step: write a minimal `async fn` test, run `RUSTFLAGS="-Zunpretty=mir"` and inspect the output. If Yield is absent, use the `SwitchInt` on coroutine discriminant instead.

2. **`select!` macro detection strategy**
   - What we know: `select!` is out of tokio/futures and expands differently per crate; non-deterministic branch encoding is locked
   - What's unclear: Whether to detect `select!` by call graph (looking for known symbol names) or by MIR pattern (multiple Yield with same resume target)
   - Recommendation: Use conservative approach — if any `SwitchInt` within a coroutine state leads to a `Yield` terminator, treat as `select!`-like and apply non-deterministic encoding. Emit a diagnostic note "select! detected — using conservative non-deterministic model".

3. **Persistent field identification without `coroutine_layout`**
   - What we know: `coroutine_layout` is None pre-lowering; `var_debug_info` carries source names; locals spanning multiple BB ranges persist
   - What's unclear: Reliable way to identify which MIR locals are coroutine struct fields (persisted) vs. temporaries (state-local)
   - Recommendation: Conservative fallback — treat ALL named locals (those with source names in `var_debug_info`) as persistent. This is sound (over-approximates state) but may produce larger SMT queries.

---

## Sources

### Primary (HIGH confidence)
- Direct codebase analysis of `crates/analysis/src/ir.rs`, `vcgen.rs`, `hof_vcgen.rs`, `driver/src/mir_converter.rs`, `callbacks.rs`, `cex_render.rs`, `json_output.rs`, `macros/src/lib.rs` — confirms all integration points, existing patterns, and data structures
- `https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/struct.CoroutineInfo.html` — confirms `body.coroutine`, `coroutine_kind`, `coroutine_layout` fields and lifecycle
- `https://doc.rust-lang.org/beta/nightly-rustc/rustc_middle/mir/enum.TerminatorKind.html` — confirms `TerminatorKind::Yield { value, resume, resume_arg, drop }` structure

### Secondary (MEDIUM confidence)
- `.planning/research/ARCHITECTURE.md` v0.4 research — confirms async feature integration plan, component boundaries, `CoroutineInfo` struct design, anti-patterns
- `https://doc.rust-lang.org/nightly/nightly-rustc/rustc_mir_transform/coroutine/struct.SuspensionPoint.html` — confirms `SuspensionPoint` with state discriminant in coroutine transform pass
- STATE.md blocker note — confirms MIR shape may have changed post-PR#145330, validates the shape-check as a required first step

### Tertiary (LOW confidence — flag for validation)
- `CoroutineKind::Desugared(CoroutineDesugaring::Async, _)` variant naming — from WebSearch/WebFetch of nightly docs, confirmed as current but exact enum structure should be verified against `nightly-2026-02-11` specifically
- `select!` MIR detection heuristic — no official documentation; heuristic derived from understanding of macro expansion semantics

---

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH — all components exist in codebase; only additive changes needed; no new deps
- Architecture: HIGH — `hof_vcgen.rs` pattern is proven; `CoroutineInfo` integration is clean additive field
- Coroutine detection API: MEDIUM — `body.coroutine` confirmed by docs, but exact variant names for `nightly-2026-02-11` must be validated
- Pitfalls: HIGH — MIR shape risk is pre-identified in STATE.md; persistent field extraction pitfall is well-understood

**Research date:** 2026-02-22
**Valid until:** 2026-03-08 (14 days — nightly-specific APIs can shift)
