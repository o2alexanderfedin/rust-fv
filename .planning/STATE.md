# Project State: rust-fv

**Last updated:** 2026-02-14

## Project Reference

**Core Value:** Sound, automated verification of Rust code properties with minimal developer burden -- if the tool says "verified", it must be mathematically correct; if a developer can write a spec, the tool should prove it automatically 80-90% of the time for safe Rust.

**Current Milestone:** v0.3 Production Usability

**Current Focus:** Defining requirements

## Current Position

Phase: Not started (defining requirements)
Plan: —
Status: Defining requirements
Last activity: 2026-02-14 — Milestone v0.3 started

### Shipped Milestones

- **v0.1** (2026-02-12): 5 phases, 17 plans, 1,741 tests, 43,621 LOC
- **v0.2** (2026-02-14): 7 phases, 21 plans, 2,264 tests, 66,133 LOC

## Accumulated Context

- 5-crate workspace: macros/, smtlib/, solver/, analysis/, driver/
- Nightly Rust required for rustc_private
- Z3 subprocess + native API backends
- Hidden doc attributes for spec transport through compilation
- Contract-based modular verification (no callee inlining)
- petgraph for SCC analysis (recursion + deadlock)

## Blockers

None.

---
*STATE.md reset: 2026-02-14 for v0.3 milestone*
