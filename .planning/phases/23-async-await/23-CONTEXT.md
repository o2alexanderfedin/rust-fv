# Phase 23: Async/Await Verification - Context

**Gathered:** 2026-02-22
**Status:** Ready for planning

<domain>
## Phase Boundary

Add verification support for `async fn` — developers annotate async functions with `#[requires]`, `#[ensures]`, and `#[state_invariant]`, and `cargo verify` proves those contracts hold under a **sequential polling model**. This phase does NOT add concurrent scheduling awareness, a new async runtime, or support for async traits.

</domain>

<decisions>
## Implementation Decisions

### Supported async patterns
- `async fn` with `.await` expressions: **in scope**
- Nested `async fn` calls (async fn calling another async fn): **in scope** — callee's SMT constraints are generated from both its code AST (Set A) and its annotations (Set B), concatenated into the solver per the dual-source architecture (no special trust boundary)
- `async {}` blocks appearing inside a verified `async fn` body: **in scope**
- `select!` macro: **in scope** with conservative over-approximation — modeled as non-deterministic branch choice
- `join!` macro: **in scope** with conservative over-approximation — modeled as sequential execution (left branch then right branch)
- `Pin<Box<dyn Future>>`, combinators (`.map()`, `.then()`), async traits: **out of scope** for this phase

### State invariant semantics
- `#[state_invariant]` can reference **all** of: function-local variables, variables captured from enclosing scope (async closure captures), and values reachable through function arguments (e.g., fields of `&mut State`)
- The invariant must hold at **both** sides of every `.await` point: at suspension (just before yielding) AND at resumption (just after control returns from the awaited future)
- The invariant at resumption **can reference the result of the awaited expression** (the value that `.await` produced), allowing expressions like `awaited_result >= 0`

### Verification failure reporting
- When a `#[state_invariant]` is violated, report **both**: the annotation location (which invariant) AND the specific `.await` expression that triggered the failure (suspension or resumption side)
- Counterexample includes: **variable values at the point of violation** (typed Rust values, consistent with Phase 19/25 counterexample format) **plus which poll iteration** (1st, 2nd, …) triggered the violation under sequential polling
- IDE surface: Claude's discretion — reuse existing Phase 25 VSCode counterexample infrastructure (inline diagnostic on the `.await` line + output panel)

### Contract interaction with async
- `#[requires]` and `#[ensures]` timing: Claude's discretion — pick the semantically cleanest model consistent with existing sync contract semantics
- `#[ensures]` timing: Claude's discretion — pick standard functional verification semantics (expected: at final `Poll::Ready` resolution)
- Cross-await references: **YES** — `#[requires]` and `#[ensures]` can reference any local variable visible at the annotation site, including locals set before or after `.await` boundaries, because the sequential polling model makes all locals traceable across suspension points

### Claude's Discretion
- Exact timing model for `#[requires]` (call site vs first poll)
- Exact timing model for `#[ensures]` (final resolution vs each `Poll::Ready`)
- IDE counterexample surface implementation (reuse Phase 25 infrastructure)
- Internal encoding of coroutine state machine (how MIR coroutine states map to SMT variables across suspension points)

</decisions>

<specifics>
## Specific Ideas

- SMT constraint generation follows the dual-source architecture: code AST generates Set A constraints, annotations generate Set B constraints, both concatenated as-is to the solver — no deduplication, no client-side contradiction checking (solver handles this)
- `select!` non-deterministic model: introduce a boolean SMT variable representing the branch choice, generate constraints for both branches, let solver explore both paths
- `join!` sequential model: treat as sequential `.await` on left then `.await` on right — conservative but sound under the sequential polling assumption

</specifics>

<deferred>
## Deferred Ideas

- None — discussion stayed within phase scope

</deferred>

---

*Phase: 23-async-await*
*Context gathered: 2026-02-22*
