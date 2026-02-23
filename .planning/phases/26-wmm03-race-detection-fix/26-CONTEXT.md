# Phase 26: WMM-03 Weak Memory Race Detection Fix - Context

**Gathered:** 2026-02-22
**Status:** Ready for planning

<domain>
## Phase Boundary

Fix the soundness bug in `WeakMemoryRace` VC generation: `rc11.rs` currently emits `Assert(BoolLit(false))` which is always UNSAT, causing the driver to silently report Relaxed data races as safe. This phase fixes the VC body to emit actual race-existence constraints so Z3 can return SAT when a race genuinely exists, and fixes the driver pipeline to interpret SAT on a `WeakMemoryRace` VC as a race error surfaced to the user.

Scope: `rc11.rs` VC formula + driver result interpretation + test updates. New concurrency features are out of scope.

</domain>

<decisions>
## Implementation Decisions

### Error severity & exit behavior
- WeakMemoryRace SAT result = hard error (not a warning)
- Error style mirrors compiler error output: `error[E...]:` entries, same as functional verification failures
- Race errors go into the same error list as other verification failures — no separate bucket
- SMT solver decides the result; if SAT → race exists → it's an error
- Exit code follows naturally from the error reporting pipeline (same as other errors)

### User-facing message format
- Follow existing `DataRaceFreedom` error formatting for consistency — reuse `format_data_race_help()` and existing patterns
- Show source file/line information when available (already tracked in `VcLocation`)
- Label: "weak memory data race" (already defined in `diagnostics.rs` for `VcKind::WeakMemoryRace`)
- Show thread IDs and variable name (already in the `description` field of the VC)

### Verification semantics when race found
- No short-circuiting: all VCs (functional properties, races, coherence) are checked and reported together
- "verified: true" is only valid if the solver returns UNSAT on all relevant VCs — if WeakMemoryRace returns SAT, that function is NOT fully verified
- The SMT solver decides correctness; the driver faithfully reports whatever the solver returns

### Race formula approach
- **Claude's Discretion**: Choose the simplest correct formula consistent with RC11 semantics
  - Guidance: use existential approach — assert the race conditions directly (two conflicting Relaxed events, no hb edge in either direction), so SAT = race exists
  - Use the **full preamble** (same mo/rf/co declarations and axioms as WeakMemoryCoherence VCs) for consistency
  - The existing code already filters candidate pairs correctly (same location, different threads, at least one write, both Relaxed, hb(i,j)=false AND hb(j,i)=false at static analysis time); the VC body should assert the dynamic race-existence constraint over the SMT model

### Claude's Discretion
- Exact SMT formula structure for the race-existence assertion
- Whether to assert `(and (not hb_ij_term) (not hb_ji_term))` or use a different encoding
- Compression/deduplication of identical VC scripts
- Exact error message wording beyond the established format

</decisions>

<specifics>
## Specific Ideas

- User emphasized: "SMT solver should decide — we just provide SMT constraints." This means the formula must faithfully encode race-existence so Z3 can determine it, rather than pre-computing the result in Rust and hardcoding it.
- Error should feel like a compiler error (`error[E...]:`) not a linter warning.
- Full preamble on the VC gives Z3 the full context (mo/rf/co axioms) even if not all of it is strictly needed for the race pair — ensures soundness.

</specifics>

<deferred>
## Deferred Ideas

None — discussion stayed within phase scope.

</deferred>

---

*Phase: 26-wmm03-race-detection-fix*
*Context gathered: 2026-02-22*
