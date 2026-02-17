# Phase 18: bv2int Optimization - Context

**Gathered:** 2026-02-16
**Status:** Ready for planning

<domain>
## Phase Boundary

Enable bv2int optimization for arithmetic-heavy formal verification with proven equivalence and performance measurement. Developers can opt-in to replace bitvector SMT encoding with integer arithmetic encoding for eligible functions, gaining significant speedup on arithmetic-heavy proofs while maintaining soundness.

</domain>

<decisions>
## Implementation Decisions

### Activation & Controls
- Both CLI flag (--bv2int) and environment variable (RUST_FV_BV2INT=1) supported, CLI takes precedence
- Global enable with per-function opt-out via #[fv::no_bv2int] attribute
- Auto-detect eligible functions and suggest bv2int candidates in output (user enables manually)
- When enabled globally, warn per ineligible function explaining why bv2int was skipped (not silent fallback)

### Equivalence Reporting
- Divergence between bitvector and bv2int encodings reported as error with counterexample showing specific input
- Equivalence testing runs automatically on first use of bv2int for a function
- Results cached per function content hash — only re-check when function changes
- Always show timing comparison: both encoding times and speedup factor (e.g., "bitvector: 1.2s, bv2int: 0.3s (4x faster)")

### Applicability Boundaries
- Eligibility excludes only bitwise operations (&, |, ^, <<, >>) — most permissive approach (arithmetic + comparisons allowed)
- Mixed expressions: Claude's discretion toward safety and precision (conservative approach for soundness)
- Overflow semantics: Claude's discretion toward safety and precision (sound approach based on SMT semantics)
- Rejection messages: Claude's discretion toward safety and precision (detailed enough for developer action)

### Performance Feedback
- Regression detection uses stored bitvector baseline, compares against bv2int run
- Summary report mode: rust-fv --bv2int-report showing table of all functions with encoding, time, speedup
- Slowdown warning threshold is configurable via env var or CLI flag (default 2x)
- Auto-detect suggestions: Claude's discretion — no speculative estimates, candidate list based on static analysis

### Claude's Discretion
- Mixed expression handling strategy (entire function vs per-expression) — lean toward safety
- Overflow guard implementation for wrapping arithmetic — choose sound approach
- Rejection message detail level — provide actionable information
- Auto-detect suggestion format — practical without speculative speedup estimates
- Baseline storage format and location — consistent with incremental verification cache (Phase 14)

</decisions>

<specifics>
## Specific Ideas

- User consistently prefers "safety and precision" as the guiding principle for boundary decisions
- Equivalence caching should integrate with the existing incremental verification infrastructure from Phase 14
- The --bv2int-report mode suggests treating this as a first-class analysis tool, not just an optimization toggle
- Warning-per-function on fallback indicates preference for transparency over silence

</specifics>

<deferred>
## Deferred Ideas

None — discussion stayed within phase scope

</deferred>

---

*Phase: 18-bv2int-optimization*
*Context gathered: 2026-02-16*
