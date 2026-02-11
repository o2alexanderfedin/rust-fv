# Project State

## Project Reference

See: .planning/PROJECT.md (updated 2026-02-10)

**Core value:** Sound, automated verification of Rust code properties with minimal developer burden
**Current focus:** Phase 2 - Table Stakes Completion

## Current Position

Phase: 2 of 5 (Table Stakes Completion)
Plan: 5 of 5 in current phase
Status: In progress - loop invariant verification complete
Last activity: 2026-02-11 -- Completed 02-02: Loop invariant verification (3-VC approach)

Progress: [████████████████    ] 80% (Phase 2: plans 02-01, 02-02, 02-04 complete; 02-03, 02-05 remain)

## What Exists (v0.1.0)

- 5-crate workspace: macros/, smtlib/, solver/, analysis/, driver/
- 363+ tests passing (76 analysis unit + 8 aggregate E2E + 10 loop E2E + 10 e2e + 22 soundness + 22 completeness + 108 smtlib + 63 solver + rest), zero warnings
- End-to-end pipeline: annotation -> MIR -> VC -> SMT -> Z3 -> result
- Proc macro contracts: `#[requires]`, `#[ensures]`, `#[pure]`, `#[invariant]`
- Bitvector encoding for all integer types (i8-i128, u8-u128, isize, usize)
- Arithmetic overflow detection (add/sub/mul/div/rem/shl/shr) -- audited against Rust semantics
- **Z3 native API backend (02-01)**: SolverBackend trait with subprocess and z3-crate backends, ~50ms overhead eliminated
- **Structured tracing (02-01)**: RUST_LOG-based pipeline debugging with info/debug/trace levels
- Counterexample extraction from SAT results
- **Aggregate type encoding (02-04)**: SMT datatypes for structs/tuples/enums, field selector and constructor encoding, result.field specs verified by Z3
- **Loop invariant verification (02-02)**: Classical 3-VC approach (init/preserve/exit), DFS back-edge detection, next-state variable encoding

## What Must Be Fixed First

- ~~SSA violation in VCGen: linear block-walking is unsound for branches/loops~~ (FIXED in 01-01)
- ~~Variable shadowing produces incorrect verification for multi-path control flow~~ (FIXED in 01-01)
- ~~Arithmetic overflow encoding needs systematic audit against Rust semantics~~ (FIXED in 01-02)

## Performance Metrics

**Velocity:**
- Total plans completed: 6
- Average duration: ~14 min
- Total execution time: ~83 min

**By Phase:**

| Phase | Plans | Total | Avg/Plan |
|-------|-------|-------|----------|
| 01-soundness-foundation | 3/3 | ~21 min | ~7 min |
| 02-table-stakes-completion | 3/5 | ~62 min | ~21 min |

*Updated after each plan completion*

## Accumulated Context

### Decisions

Decisions are logged in PROJECT.md Key Decisions table.
Recent decisions affecting current work:

- [Init]: SMT-based verification via Z3 subprocess (proven by Verus/Prusti/Creusot/Kani)
- [Init]: Proc macros for specs (stable API, no compiler fork)
- [Init]: Bitvector theory for exact integer overflow semantics
- [Init]: 5-crate workspace isolating nightly dependency to driver/
- [01-01]: Path-sensitive encoding over SSA phi-nodes for simpler handling of early returns and match arms
- [01-01]: Common-prefix detection via branch_depth to prevent circular path-condition constraints
- [01-01]: Comparison operand-type inference for correct signed/unsigned bitvector operations
- [01-03]: Criterion 0.5 for benchmarks (stable, html_reports, widely adopted in Rust)
- [01-03]: Benchmarks are developer-only, not CI gate (avoid flaky perf failures)
- [01-03]: Complex benchmark uses clamp function with 5 basic blocks for realistic coverage
- [01-02]: Signed Rem gets same overflow check as Div (INT_MIN % -1 panics in Rust)
- [01-02]: Test suites use self-contained helpers for test independence
- [01-02]: VCGen lacks intra-block SSA renaming (known Phase 2 concern)
- [02-01]: System Z3 over bundled feature (faster builds, smaller disk footprint, already available)
- [02-01]: z3 crate 0.19 global context model (simpler than explicit lifetimes)
- [02-01]: SolverBackend trait for backend abstraction (zero-cost via feature flags)
- [02-01]: Tracing at info/debug/trace levels (avoids noise, RUST_LOG controls verbosity)
- [02-04]: QF_UFBVDT logic for datatypes+bitvectors (QF_UFDT lacks bitvectors, QF_BV lacks datatypes)
- [02-04]: Selector naming convention: {TypeName}-{field_name} for global uniqueness
- [02-04]: Constructor naming: mk-{TypeName} for structs/tuples, mk-{VariantName} for enum variants
- [02-04]: Signedness inference from struct/tuple field types for correct comparison in specs
- [02-02]: Next-state variables (_var_next) for preservation VC to avoid SMT constant reuse conflicts
- [02-02]: Header statement encoding in exit VC to establish condition-variable relationship
- [02-02]: Body-only assignments in preservation VC (header stmts encoded separately)
- [02-02]: Loops without invariants skip verification with tracing::warn

### Pending Todos

None yet.

### Blockers/Concerns

- Nightly toolchain pinned (nightly-2026-02-11) -- resolved by 01-03

## Session Continuity

Last session: 2026-02-11
Stopped at: Completed 02-02-PLAN.md (Loop invariant verification)
Resume file: None
Next step: Continue with remaining Phase 2 plans (02-03 assertions/panic, 02-05 spec parser + cargo verify)
