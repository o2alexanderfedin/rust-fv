# Phase 14: Incremental Verification - Context

**Gathered:** 2026-02-15
**Status:** Ready for planning

<domain>
## Phase Boundary

Modified function re-verifies in <1s via enhanced dependency tracking and MIR-hash caching. Cache verification results per-function with sound invalidation through transitive dependency graphs. Enable real-time IDE feedback through fast incremental re-verification. Full re-verification and cache management commands available.

</domain>

<decisions>
## Implementation Decisions

### Cache granularity
- Per-function caching — each function's verification result cached independently
- Separate MIR hash and contract hash per function — body change re-verifies self only, contract change re-verifies self + transitive dependents
- Transitive invalidation on contract changes — all functions transitively depending on a changed contract get re-verified (soundness requirement)
- Cache VC results only (sat/unsat outcomes) — no persistent Z3 solver state across runs

### Developer feedback
- Show every function with status: verified / skipped (cached) / failed — full per-function visibility
- Timing: total time by default, --verbose adds per-function timing breakdown
- Show invalidation reason when re-verifying: "Re-verifying foo: contract of bar changed"
- Two cache-bypass mechanisms:
  - `--fresh` flag for one-off full re-verification (ignores cache for this run)
  - `cargo verify clean` subcommand to clear cache permanently

### Persistence & storage
- Cache location: `target/verify-cache/` — inside Cargo's target directory, cleaned by `cargo clean`
- Cache format: JSON — human-readable and debuggable
- Age-based eviction: entries older than 30 days automatically evicted
- No size limit — rely on age-based eviction + manual `cargo verify clean`

### Benchmark & measurement
- Benchmark suite: synthetic codebase (controlled, reproducible) + real-world samples (representative)
- Metrics: both wall-clock ratio (full/incremental time) and cache hit rate (skipped/total functions)
- CI integration: nightly benchmark runs to catch performance regressions
- Target sizes: <1s at 1,000 lines (success criteria), also measure at 10,000 lines to understand scaling

### Claude's Discretion
- Dependency graph data structure and traversal algorithm
- MIR hashing implementation details (what exactly constitutes the hash input)
- JSON cache schema design
- Synthetic benchmark codebase generation approach
- Eviction implementation (lazy on access vs. periodic cleanup)

</decisions>

<specifics>
## Specific Ideas

- Cache lives in `target/verify-cache/` to follow Rust ecosystem conventions (cleaned by `cargo clean`)
- Invalidation reasons shown always (not behind verbose flag) — helps developers understand cascade effects
- Two-hash approach (MIR + contract) gives precise invalidation: editing a function body doesn't force re-verifying callers if the contract hasn't changed

</specifics>

<deferred>
## Deferred Ideas

None — discussion stayed within phase scope

</deferred>

---

*Phase: 14-incremental-verification*
*Context gathered: 2026-02-15*
