# Project State

## Project Reference

See: .planning/PROJECT.md (updated 2026-02-10)

**Core value:** Sound, automated verification of Rust code properties with minimal developer burden
**Current focus:** Phase 5 - Performance and Polish

## Current Position

Phase: 5 of 5 (Performance and Polish) -- IN PROGRESS
Plan: 3 of 3 in current phase -- COMPLETE
Status: 05-01 (simplification), 05-02 (caching and parallelism), 05-03 (diagnostics) complete
Last activity: 2026-02-12 -- 05-02 caching and parallel verification

Progress: [████████████████████] 100% (Phase 5: 3/3 plans complete)

## What Exists (v0.1.0)

- 5-crate workspace: macros/, smtlib/, solver/, analysis/, driver/
- 498+ tests passing (137 analysis unit + 42 spec_parser + 17 e2e + 10 loop E2E + 11 assertion E2E + 10 interprocedural E2E + 12 ownership E2E + 22 soundness + 22 completeness + 112 smtlib + 63 solver + 12 macros + rest), zero warnings
- **Inter-procedural verification (03-01)**: ContractDatabase, call-site encoding (assert-pre/havoc/assume-post), modular verification of call chains
- **Ownership-aware verification (03-02)**: OwnershipKind classification, pre-call snapshot constraints for SharedBorrow/Copied, havoc for MutableBorrow
- **Unbounded integers (04-01)**: SpecInt/SpecNat types, `as int` cast syntax, Bv2Int/Int2Bv terms, `#[ghost]` macro (Z3 bv2int integration deferred)
- **Quantifiers and triggers (04-02)**: forall/exists specs with automatic trigger inference, Term::Annotated for :pattern, implies() function, verified by Z3
- **Generic function verification (04-04)**: Monomorphization with MonomorphizationRegistry, per-instantiation VC generation, concrete type substitution, verified max<T: Ord> for i32/u64
- **Prophecy variables (04-03)**: ProphecyInfo for &mut param tracking, spec parser *expr and final_value() operators, prophecy declarations/resolutions (encoding limitation documented for future SSA work)
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
- **Formula simplification (05-01)**: Simplify module with 8 algebraic rules, recursive term rewriting, ~30% SMT size reduction
- **VC caching and parallel verification (05-02)**: SHA-256 hash-based per-function caching in target/rust-fv-cache/, Rayon parallelism (cores/2 default), topological ordering via call graph, --fresh and --jobs flags
- **Enhanced diagnostics (05-03)**: VcKind classification (10 categories), ariadne-based error reporting, fix suggestions, counterexample formatting
- **JSON output (05-03)**: Structured JSON output via --output-format json for IDE/rust-analyzer integration

## What Must Be Fixed First

- ~~SSA violation in VCGen: linear block-walking is unsound for branches/loops~~ (FIXED in 01-01)
- ~~Variable shadowing produces incorrect verification for multi-path control flow~~ (FIXED in 01-01)
- ~~Arithmetic overflow encoding needs systematic audit against Rust semantics~~ (FIXED in 01-02)

## Performance Metrics

**Velocity:**
- Total plans completed: 18
- Average duration: ~12.9 min
- Total execution time: ~232 min

**By Phase:**

| Phase | Plans | Total | Avg/Plan |
|-------|-------|-------|----------|
| 01-soundness-foundation | 3/3 | ~21 min | ~7 min |
| 02-table-stakes-completion | 5/5 | ~78 min | ~16 min |
| 03-modular-verification | 2/2 | ~21 min | ~11 min |
| 04-differentiation | 4/4 | ~83 min | ~21 min |
| 05-performance-and-polish | 3/3 | ~29 min | ~10 min |

*Updated after each plan completion*
| Phase 05 P03 | 12 | 2 tasks | 5 files |
| Phase 05 P02 | 10 | 2 tasks | 7 files |

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
- [04-01]: SpecInt/SpecNat for unbounded mathematical integers in specifications
- [04-01]: `as int` cast produces Bv2Int wrapper (not int-mode for inner expr)
- [04-01]: ALL logic when Int theory needed (bv2int requires Z3 extensions)
- [04-01]: is_ghost field on Local (false default, backward compatible)
- [04-01]: Z3 bv2int integration deferred - requires version/config research
- [04-02]: implies(a, b) function call syntax (valid Rust, vs ==> operator requiring pre-processing)
- [04-02]: Conservative trigger inference: first function app covering all bound vars
- [04-02]: Automatic annotation in parse_spec (all quantified specs benefit automatically)
- [04-02]: Warn on missing trigger but don't fail (incomplete instantiation better than rejection)
- [04-02]: ALL logic for quantified specs (Z3 auto-detects theories)
- [04-04]: Monomorphization strategy mirrors Rust's (separate VCs per concrete type instantiation)
- [04-04]: MonomorphizationRegistry tracks instantiations per function name
- [04-04]: substitute_generics replaces Ty::Generic recursively throughout Function IR
- [04-04]: encode_type panics on Ty::Generic to enforce monomorphization-first
- [04-04]: generate_vcs_monomorphized wraps generate_vcs for backward compatibility
- [04-03]: final_value(x) function call syntax for prophecy variables (valid Rust, self-documenting)
- [04-03]: ProphecyInfo metadata struct for &mut param tracking
- [04-03]: Prophecy variables in base declarations alongside regular variables
- [04-03]: Initial value capture via SMT assertion (documented encoding limitation with direct param assignment)
- [05-01]: AST-level simplification over Z3 built-in API (backend-agnostic, zero overhead)
- [05-01]: A/B benchmarks for both regression tests and synthetic stress tests (measure real-world + scalability)
- [05-03]: Ariadne 0.4 for rustc-style diagnostics (mature, well-documented library)
- [05-03]: VcKind classification with 10 categories for error categorization
- [05-03]: JSON to stdout, all other output to stderr (IDE integration best practice)
- [05-03]: Fallback text diagnostics when source location unavailable (ariadne requires source file access)
- [05-03]: Fix suggestions for common patterns (overflow, precondition, postcondition, loop invariants, division-by-zero)
- [Phase 05-02]: Per-function caching with SHA-256 hash keys (conservative invalidation)
- [Phase 05-02]: Subprocess-based Z3 instances per thread for isolation
- [Phase 05-02]: Topological ordering via call graph (leaf functions first)

### Pending Todos

- **Improve test coverage to 85%+** (area: testing) - Prioritize lowest coverage files first: encode_term.rs (73.88%), macros/lib.rs (73.33%), cargo_verify.rs (78.19%), vcgen.rs (79.38%), simplify.rs (79.91%)

### Blockers/Concerns

- Z3 bv2int function availability: requires Z3 4.8.10+ or alternative encoding (04-01 deferred)
- Prophecy encoding limitation: Direct &mut param reassignment creates conflicting SMT constraints; requires SSA for parameters (04-03 infrastructure complete, encoding deferred to future work)

## Session Continuity

Last session: 2026-02-12
Stopped at: Completed 05-02 (VC caching and parallel verification)
Resume file: None
Next step: Continue Phase 5 with remaining plans (documentation, performance optimization, or additional polish features)
