# Phase 5: Performance and Polish - Context

**Gathered:** 2026-02-11
**Status:** Ready for planning

<domain>
## Phase Boundary

Make verification fast enough for interactive development (sub-1s simple, sub-5s complex), add VC caching to skip unchanged functions, parallelize solver execution across functions, simplify formulas to reduce solver time, and polish error messages to guide developers to fixes. No new verification capabilities — this phase optimizes and polishes what exists.

</domain>

<decisions>
## Implementation Decisions

### Benchmark strategy
- Both existing E2E test programs (as regression baselines) AND synthetic stress tests (for scalability limits)
- Latency targets: sub-1s for single-function verification, sub-5s for loops + inter-procedural calls
- Formula simplification measured via A/B comparison: run each benchmark with and without simplification, report % reduction in solver time
- Benchmarks are developer-only, not CI-gated (consistent with existing 01-03 decision)

### Caching behavior
- Per-function cache granularity: if function body + contracts unchanged, skip re-verification
- Cache stored in target/rust-fv-cache/ directory (cleaned by cargo clean, standard Rust convention)
- Conservative invalidation: hash of all contracts + all function bodies — any change re-verifies everything
- Add --fresh flag to cargo verify to force re-verification (useful for debugging or after solver upgrades)

### Parallelism model
- Per-function parallelism: verify multiple functions simultaneously, each function's VCs run sequentially
- Process-based parallelism via subprocess solver instances (supports multi-solver future: Z3, CVC5, etc.)
- Default to cores/2 parallel instances, configurable via --jobs N flag (like cargo build -j N)
- Topological verification order: build call graph, verify leaf functions first (ensures callee contracts are checked before use)

### Error message design
- Rustc-style error format: source file + line number, colored arrows pointing to failing spec, counterexample below
- Suggest fixes for common patterns when obvious: "add overflow check", "strengthen precondition", "add loop invariant"
- Add --output-format json flag for structured JSON output (enables IDE/rust-analyzer integration)

### Claude's Discretion
- Counterexample display format (variable assignments vs execution trace — pick based on implementation feasibility)
- Exact formula simplification passes (constant folding, dead code elimination, CSE — pick based on measured impact)
- Thread management for process pool (tokio, std::thread, or simple subprocess spawning)
- JSON output schema design

</decisions>

<specifics>
## Specific Ideas

- Multi-solver support anticipated (Z3, CVC5, etc.) — parallelism design should not assume Z3-only
- Error format should feel familiar to Rust developers (rustc, clippy style)
- --jobs N flag mirrors cargo build convention for discoverability

</specifics>

<deferred>
## Deferred Ideas

None — discussion stayed within phase scope

</deferred>

---

*Phase: 05-performance-and-polish*
*Context gathered: 2026-02-11*
