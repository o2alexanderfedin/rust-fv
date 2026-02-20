# Phase 22: Higher-Order Closures - Context

**Gathered:** 2026-02-20
**Status:** Ready for planning

<domain>
## Phase Boundary

Developers can specify and verify higher-order functions (HOFs) taking closure arguments with precise pre/postconditions. The verifier proves closure specs at every call site and tracks environment mutation for FnMut closures via SSA-versioned snapshots. This phase does NOT add new Rust language features, richer type inference, or loop-based closure calls beyond what inference can handle.

</domain>

<decisions>
## Implementation Decisions

### fn_spec annotation syntax
- Closure argument referenced by name (e.g., `fn_spec(f, |x| ...)`) — Claude's discretion on exact ergonomics
- Multiple closures covered in a single `fn_spec` call: `fn_spec(f => |x| ..., g => |y| ...)`
- Pre/postcondition delimiter: Claude's discretion (follow most readable form; `|x| pre => post` is the roadmap reference)
- Placement and form of `fn_spec`: follow the existing spec annotation convention already established in Phases 1–21 (read codebase to determine)

### FnMut mutation modeling
- SSA environment snapshots named semantically: `env_before` / `env_after` (not numeric indices)
- All captured variables included in the environment snapshot (not just those referenced in the spec)
- Loop calls: prefer inference-based approach (e.g., loop invariant inference) for safety and precision; avoid requiring the developer to manually annotate invariants when possible
- Unprovable FnMut postconditions: follow the existing pattern for unproven obligations in Phases 1–21

### Error reporting
- Primary error location: call site (where closure is passed to HOF)
- Secondary note: points to the specific fn_spec clause that failed
- Counterexamples: always show when available (extract concrete values from Z3 model)
- FnMut errors: show full `env_before` and `env_after` side-by-side (not diff only)
- Pre vs post distinction: follow the existing pre/post error distinction in the codebase

### Closure trait coverage
- All three traits in scope: `Fn`, `FnMut`, `FnOnce`
- Generic closure bounds: monomorphize at each call site (each concrete closure generates its own VC)
- FnOnce encoding: Claude's discretion (single-call VC with no repeated env tracking is preferred for soundness)
- Trait coercion (FnMut passed where Fn expected): Claude's discretion — follow Rust semantics and soundness requirements

### Claude's Discretion
- Exact `fn_spec` syntax form (name vs positional, delimiter style)
- FnOnce encoding details
- Trait coercion handling
- Loop invariant inference depth/strategy
- Exact `fn_spec` placement convention (determined by reading existing codebase)

</decisions>

<specifics>
## Specific Ideas

- Roadmap reference syntax: `fn_spec(f, |x| pre => post)` — use as the design anchor
- SSA naming from roadmap: `env_v0 → env_v1` pattern replaced by semantic `env_before`/`env_after` names per user decision
- Safety and precision preferred over simplicity when making inference trade-offs (user explicitly requested this for loop handling)
- Developer unavailability assumption: inference is preferred over requiring manual annotations wherever feasible

</specifics>

<deferred>
## Deferred Ideas

None — discussion stayed within phase scope.

</deferred>

---

*Phase: 22-higher-order-closures*
*Context gathered: 2026-02-20*
