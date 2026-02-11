# Project State

## Project Reference

See: .planning/PROJECT.md (updated 2026-02-10)

**Core value:** Sound, automated verification of Rust code properties with minimal developer burden
**Current focus:** Phase 3 - Modular Verification -- COMPLETE

## Current Position

Phase: 3 of 5 (Modular Verification) -- COMPLETE
Plan: 2 of 2 in current phase -- 03-02 complete
Status: Phase 3 complete -- ownership-aware inter-procedural verification
Last activity: 2026-02-11 -- Completed 03-02-PLAN.md (ownership classification + E2E tests)

Progress: [############░░░░░░░░] 60% (Phase 3: 2 of 2 complete)

## What Exists (v0.1.0)

- 5-crate workspace: macros/, smtlib/, solver/, analysis/, driver/
- 243+ tests passing (113 analysis unit + 36 spec_parser + 8 aggregate E2E + 10 loop E2E + 11 assertion E2E + 10 e2e + 10 interprocedural E2E + 12 ownership E2E + 22 soundness + 22 completeness + 108 smtlib + 63 solver + rest), zero warnings
- **Inter-procedural verification (03-01)**: ContractDatabase, call-site encoding (assert-pre/havoc/assume-post), modular verification of call chains
- **Ownership-aware verification (03-02)**: OwnershipKind classification, pre-call snapshot constraints for SharedBorrow/Copied, havoc for MutableBorrow
- End-to-end pipeline: annotation -> MIR -> VC -> SMT -> Z3 -> result
- Proc macro contracts: `#[requires]`, `#[ensures]`, `#[pure]`, `#[invariant]`
- Bitvector encoding for all integer types (i8-i128, u8-u128, isize, usize)
- Arithmetic overflow detection (add/sub/mul/div/rem/shl/shr) -- audited against Rust semantics
- **Z3 native API backend (02-01)**: SolverBackend trait with subprocess and z3-crate backends, ~50ms overhead eliminated
- **Structured tracing (02-01)**: RUST_LOG-based pipeline debugging with info/debug/trace levels
- Counterexample extraction from SAT results
- **Aggregate type encoding (02-04)**: SMT datatypes for structs/tuples/enums, field selector and constructor encoding, result.field specs verified by Z3
- **Loop invariant verification (02-02)**: Classical 3-VC approach (init/preserve/exit), DFS back-edge detection, next-state variable encoding
- **Assertion and panic detection (02-03)**: AssertKind enum for 9 panic variants, specific error messages per kind
- **Full spec parser (02-05)**: syn-based expression parser with old() operator, field access, backward-compatible fallback
- **cargo verify subcommand (02-05)**: Colored per-function output (OK/FAIL/TIMEOUT), --help, --timeout, exit codes

## What Must Be Fixed First

- ~~SSA violation in VCGen: linear block-walking is unsound for branches/loops~~ (FIXED in 01-01)
- ~~Variable shadowing produces incorrect verification for multi-path control flow~~ (FIXED in 01-01)
- ~~Arithmetic overflow encoding needs systematic audit against Rust semantics~~ (FIXED in 01-02)

## Performance Metrics

**Velocity:**
- Total plans completed: 10
- Average duration: ~12 min
- Total execution time: ~120 min

**By Phase:**

| Phase | Plans | Total | Avg/Plan |
|-------|-------|-------|----------|
| 01-soundness-foundation | 3/3 | ~21 min | ~7 min |
| 02-table-stakes-completion | 5/5 | ~78 min | ~16 min |
| 03-modular-verification | 2/2 | ~21 min | ~11 min |

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
- [02-03]: AssertKind enum with 9 variants covering common Rust panic sources
- [02-03]: classify_assert_kind maps rustc MIR AssertKind to IR AssertKind
- [02-03]: AssertKind-based VCs complement (not replace) existing overflow VCs
- [02-05]: syn 2.0 with full+parsing features for complete Rust expression parsing in specs
- [02-05]: parse_spec fallback: try syn parser first, fall back to parse_simple_spec
- [02-05]: old(expr) via in_old flag propagation through recursive expression tree
- [02-05]: Skip cargo_metadata: read Cargo.toml directly to minimize dependencies
- [02-05]: colored 3.1 for output (lightweight, simple API)
- [02-05]: Dual binary targets (rust-fv-driver + cargo-verify) sharing main.rs
- [03-01]: Optional ContractDatabase parameter for backward-compatible inter-procedural verification
- [03-01]: CallSiteInfo recorded inline during traverse_block (not separate pass)
- [03-01]: Callee postconditions asserted positively as assumptions in caller postcondition VCs
- [03-01]: build_callee_func_context from FunctionSummary for spec parsing in caller context
- [03-01]: normalize_callee_name: trim -> strip "const " -> take last :: segment
- [03-02]: Param type takes precedence over operand kind for ownership classification
- [03-02]: Pre-call snapshot via DeclareConst + assertion pairs for value preservation
- [03-02]: No driver changes needed: ownership analysis driven by VCGen from ContractDatabase param types
- [03-02]: Bounded callee return contracts in tests to prevent bitvector overflow

### Pending Todos

None yet.

### Blockers/Concerns

- Nightly toolchain pinned (nightly-2026-02-11) -- resolved by 01-03

## Session Continuity

Last session: 2026-02-11
Stopped at: Phase 3 verified complete (4/4 success criteria met, 469 tests)
Resume file: None
Next step: Plan Phase 4 via /gsd:plan-phase 4
