# Phase 00: milestone-uat - Research

**Researched:** 2026-02-25
**Domain:** UAT document authoring for milestones v0.4 (phases 19-27) and v0.5 (phases 28-29)
**Confidence:** HIGH

<user_constraints>
## User Constraints (from CONTEXT.md)

### Locked Decisions

#### Coverage scope
- Cover both v0.4 (phases 19-27) and v0.5 (phases 28-29) in one combined UAT file
- File name: `v0.4-v0.5-UAT.md` in `.planning/phases/00-milestone-uat/`
- 1-2 test items per phase (phases 19-29 = ~22-44 total tests)

#### Test derivation
- Derive test cases from each phase's SUMMARY.md `provides` clauses — ensures coverage of every declared deliverable
- Each test's `expected` field: concrete observable behavior ("Running X produces Y") — testable by running commands
- Include specific `cargo test` names as evidence hints in each test item

#### Evidence standard
- Run full suite: `cargo test --workspace` — capture overall pass count and zero failures
- Run targeted subsets per UAT item (e.g., `cargo test vcgen`, `cargo test separation_logic`) — specific proof per item
- Clippy check required: `cargo clippy --workspace` must produce zero warnings

#### Failure policy
- Blocking: a `fail` result stops UAT and milestone completion is blocked until fixed
- When a failure occurs: capture exact commands run, full output, minimal reproduction case, and root cause hypothesis
- Diagnosis goes in the UAT item's `result`/`evidence` fields with `status: diagnosed`

### Claude's Discretion
- Exact ordering of test items within the document
- How to group phases 19-27 vs 28-29 within the file (sections or flat list)
- Whether to include a summary table at the top

### Deferred Ideas (OUT OF SCOPE)

None — discussion stayed within phase scope.
</user_constraints>

## Summary

This phase produces a single UAT document `v0.4-v0.5-UAT.md` that validates milestones v0.4 (phases 19-27) and v0.5 (phases 28-29). The document follows the exact format established by `milestone-UAT.md` and `v0.3-UAT.md`, using YAML front-matter and a `### N. Test Name` structure with `expected:`, `result:`, and `evidence:` fields.

The test suite is currently fully healthy: all 1,300+ tests pass with zero failures and zero clippy warnings across the workspace. This means UAT execution should proceed without blockers.

Each phase from 19-29 has clear, concrete deliverables documented in their SUMMARY.md `provides` clauses. These map directly to observable behaviors testable via `cargo test` commands. The research has catalogued specific test names and filter patterns for each phase.

**Primary recommendation:** Write `v0.4-v0.5-UAT.md` with two sections (v0.4: phases 19-27, v0.5: phases 28-29), derive 2 tests per phase (~22 total), use `cargo test <filter>` evidence commands, include a summary table at the top.

## Standard Stack

### Core
| Tool | Version | Purpose | Why Standard |
|------|---------|---------|--------------|
| cargo test | workspace | Execute all Rust unit and integration tests | Built into Rust toolchain |
| cargo clippy | workspace | Lint for zero warnings | Enforced by pre-commit hook |
| cargo test --test <name> | per-phase | Run specific integration test files | Targeted evidence per UAT item |

### Supporting
| Tool | Version | Purpose | When to Use |
|------|---------|---------|-------------|
| cargo test -- <filter> | ad-hoc | Filter tests by name substring | Evidence for specific capabilities |
| cargo test -p <crate> | per-crate | Scope test run to one crate | Faster targeted checks |

## Architecture Patterns

### Existing UAT File Format
```markdown
---
status: complete
phase: milestone-vX.Y
source: NN-NN-SUMMARY.md, ...
started: 2026-02-NNT00:00:00Z
updated: 2026-02-NNT00:00:00Z
---

## Current Test

[testing complete]

## Tests

### N. Test Name
expected: <concrete observable behavior>
result: pass|fail|diagnosed
evidence: <specific commands and output observed>

## Summary

total: N
passed: N
issues: 0
pending: 0
skipped: 0

## Gaps

[none]
```

### Test Item Derivation Pattern
**What:** Each phase's SUMMARY.md `provides:` clause becomes 1-2 UAT test items.
**When to use:** For every phase in scope (19-29).
**Rule:** `expected:` must describe a concrete observable behavior (e.g., "Running `cargo test sep_logic` passes N tests"); avoid abstract descriptions.

### Anti-Patterns to Avoid
- **Vague expected clauses:** "The feature works" — use "Running `cargo test hof_closures` completes with 6 passed, 0 failed" instead.
- **Missing evidence commands:** Every `result: pass` must cite the exact command run and key output observed.
- **Testing future scope:** Only validate what phases 19-29 declared as `provides`, not what was deferred.

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Test discovery | Don't grep test names manually | `cargo test -- --list \| grep <pattern>` | Authoritative, always current |
| Coverage checking | Don't count files manually | `cargo test --workspace` total count | Single source of truth |

## Common Pitfalls

### Pitfall 1: Testing the Wrong Thing
**What goes wrong:** UAT item tests a behavior that was actually from a prior phase, not the v0.4/v0.5 phase being validated.
**Why it happens:** Phases build on each other; easy to attribute a capability to the wrong phase.
**How to avoid:** Always trace each test to a specific `provides` clause from the correct phase's SUMMARY.md.
**Warning signs:** If you can't find the `provides` clause in the target phase's SUMMARY.md, reassign or drop the test.

### Pitfall 2: Ignored Tests Masking Gaps
**What goes wrong:** `cargo test --workspace` passes but some tests are `#[ignore]`d.
**Why it happens:** Phase 29 has one intentionally ignored test (`vcgen_06_set_discriminant_assertion`). The v0.3 UAT documented a similar known gap.
**How to avoid:** Run `cargo test --workspace` and note the "ignored" count; document known ignores explicitly in UAT Gaps section.
**Warning signs:** Test count lower than expected; `ignored` count in `cargo test` output.

### Pitfall 3: Cargo Test Filter Too Broad
**What goes wrong:** A filter like `cargo test vcgen` matches hundreds of tests, making evidence unwieldy.
**Why it happens:** Short filter strings match many test names.
**How to avoid:** Use more specific filter strings (e.g., `cargo test vcgen_completeness28`, `cargo test sep_logic_integration`).

### Pitfall 4: Missing GetModel vs CheckSat (Phase 27 insight)
**What goes wrong:** async VC tests pass but counterexample_v2 is None.
**Why it happens:** async_vcgen uses `check_sat_raw` which does NOT auto-append `(get-model)`.
**How to avoid:** Evidence for Phase 27 should verify the `GetModel` fix — run `cargo test async_cex_e2e` to confirm counterexample fields populate.

## Code Examples

### UAT Evidence Command Patterns

```bash
# Full suite (mandatory for any UAT)
cargo test --workspace

# Phase-specific integration test files
cargo test -p rust-fv-analysis --test sep_logic_integration
cargo test -p rust-fv-analysis --test weak_memory_litmus
cargo test -p rust-fv-analysis --test hof_closures
cargo test -p rust-fv-analysis --test async_verification
cargo test -p rust-fv-driver --test ghost_predicate_e2e
cargo test -p rust-fv-driver --test wmm_race_e2e
cargo test -p rust-fv-driver --test async_cex_e2e
cargo test -p rust-fv-analysis --test vcgen_completeness28
cargo test -p rust-fv-analysis --test vcgen_completeness29

# Unit test filters
cargo test -p rust-fv-driver -- cex_render
cargo test -p rust-fv-analysis -- hof_vcgen
cargo test -p rust-fv-analysis -- sep_logic
cargo test -p rust-fv-analysis -- async_vcgen
cargo test -p rust-fv-analysis -- ghost_predicate_db

# Clippy (mandatory)
cargo clippy --workspace
```

### Phase-by-Phase Test Catalog (from provides clauses)

**Phase 19 — Counterexample Generation (CEX-01, CEX-02, CEX-03)**
- `VcOutcome::Sat` carries `Vec<(String,String)>` structured model pairs (not flat string)
- `ir::Function.source_names` maps SSA names to Rust source names via `var_debug_info`
- `render_counterexample()` in `cex_render.rs` produces typed `CexVariable` list
- ariadne multi-label rendering at actual source spans
- `counterexample_v2` JSON schema with typed variables in `JsonFailure`

Test commands:
```bash
cargo test -p rust-fv-driver -- cex_render  # 30 unit tests
cargo test -p rust-fv-driver -- json_output # 18 tests
```

**Phase 20 — Separation Logic (SEP-01, SEP-02, SEP-03, SEP-04)**
- `sep_logic::encode_pts_to()` wired in spec_parser
- `pts_to(p,x) * pts_to(q,y)` separating conjunction
- Frame axiom with E-matching trigger
- Ghost predicate bounded inlining to depth 3

Test commands:
```bash
cargo test -p rust-fv-analysis --test sep_logic_integration  # 4 E2E tests
cargo test -p rust-fv-analysis -- sep_logic                   # unit tests
```

**Phase 21 — Weak Memory Models (WMM-01, WMM-02, WMM-03, WMM-04)**
- `rc11.rs` with `generate_rc11_vcs()` and 11 RC11 primitives
- 9 canonical litmus tests (MP, SB, LB, IRIW, CoRR, CoRW, CoWR, CoWW, Race)
- `has_non_seqcst_atomics()` gate in vcgen.rs

Test commands:
```bash
cargo test -p rust-fv-analysis --test weak_memory_litmus  # 9 litmus tests
cargo test -p rust-fv-analysis -- rc11                    # unit tests
```

**Phase 22 — Higher-Order Closures (HOF-01, HOF-02)**
- `fn_spec` proc macro with `#[fn_spec(f, |x| pre => post)]`
- `hof_vcgen.rs` with `generate_fn_spec_vcs()` emitting AUFLIA-logic SMT
- 6 Z3 UNSAT/SAT entailment tests for Fn, FnMut, FnOnce

Test commands:
```bash
cargo test -p rust-fv-analysis --test hof_closures  # 6 Z3 tests
cargo test -p rust-fv-analysis -- hof_vcgen         # 10 unit tests
```

**Phase 23 — Async/Await Verification (ASY-01, ASY-02)**
- `CoroutineInfo/CoroutineState/CoroutineExitKind` IR types
- `#[state_invariant(expr)]` proc macro
- `async_vcgen.rs` with `generate_async_vcs()` emitting QF_LIA scripts
- 6 Z3 integration tests for postcondition and state invariant verification

Test commands:
```bash
cargo test -p rust-fv-analysis --test async_verification  # 6 tests
cargo test -p rust-fv-analysis -- async_vcgen             # 8 unit tests
```

**Phase 24 — SEP-04 Ghost Predicate Wiring (SEP-04)**
- `generate_vcs_with_db()` threaded through `VerificationTask`
- E2E driver integration test validates ghost predicate expansion end-to-end

Test commands:
```bash
cargo test -p rust-fv-driver --test ghost_predicate_e2e  # 2 tests
cargo test -p rust-fv-analysis -- ghost_predicate_db     # 3 tests
```

**Phase 25 — VSCode Counterexample v2 (CEX-02, CEX-04)**
- `renderCounterexampleLines()` in `diagnostics.ts` uses `counterexample_v2` typed schema
- `outputPanel.ts` `formatFailedFunction()` uses typed rendering

Test commands: TypeScript compiler only
```bash
cd vscode-extension && npx tsc --noEmit
```

**Phase 26 — WMM-03 Race Detection Fix (WMM-03)**
- WeakMemoryRace VC fixed from `Assert(BoolLit(false))` to `Assert(BoolLit(true))` with mo+rf context
- E2E driver test confirms Relaxed race surfaces as failure

Test commands:
```bash
cargo test -p rust-fv-analysis --test weak_memory_litmus -- test_relaxed_data_race_detected
cargo test -p rust-fv-driver --test wmm_race_e2e
```

**Phase 27 — Async Counterexample IDE Fidelity (ASY-02)**
- `poll_iteration` and `await_side` extracted from model in `build_counterexample_v2()`
- `JsonCounterexample` TypeScript interface has `poll_iteration?: number` and `await_side?: string`
- E2E test confirms async fields populated end-to-end

Test commands:
```bash
cargo test -p rust-fv-driver --test async_cex_e2e
cargo test -p rust-fv-driver -- test_build_counterexample_v2_async_fields
```

**Phase 28 — SMT VCGen Completeness (VCGEN-01..04)**
- `encode_int_to_int_cast()` with sign-extend/zero-extend/extract
- `Rvalue::Discriminant` emits `Term::App("discriminant-{local}", ...)`
- `generate_index_bounds_vcs()` + `Rvalue::Len` as named SMT constant
- `trait_bounds_as_smt_assumptions()` + `Ty::Generic -> Sort::Uninterpreted`

Test commands:
```bash
cargo test -p rust-fv-analysis --test vcgen_completeness28  # 10 tests all GREEN
```

**Phase 29 — Fix Identified SMT VCGen Gaps (MIRCONV-01, MIRCONV-02, VCGEN-05, VCGEN-06)**
- CastKind exhaustive match in `mir_converter.rs` (MIRCONV-01)
- `encode_float_to_int_cast` using `fp.to_sbv`/`fp.to_ubv` with RTZ (VCGEN-05)
- `AggregateKind::Adt` + `SetDiscriminant` + `Assume` in MIR converter (MIRCONV-02)
- `TyKind::Param -> Ty::Generic` fix + `Rvalue::Repeat`/`CopyForDeref`/`RawPtr` (MIRCONV-01)
- Projected LHS struct field mutation produces `mk-StructName` functional update (VCGEN-06)

Test commands:
```bash
cargo test -p rust-fv-analysis --test vcgen_completeness29  # 9 active + 1 ignored
```

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| Flat string model in VcOutcome::Sat | Vec<(String,String)> structured pairs | Phase 19 | Enables typed counterexample rendering |
| No separation logic | pts_to + frame rule + AUFBV | Phase 20 | Heap ownership specs possible |
| No weak memory model | RC11 axiomatic with QF_LIA | Phase 21 | Detects Relaxed data races |
| WeakMemoryRace VC was BoolLit(false) stub | BoolLit(true) with mo+rf context | Phase 26 | WMM-03 soundness gap closed |
| Ty::Generic panicked in encode_sort | Sort::Uninterpreted | Phase 28 | Parametric VCGen enabled |
| Float-to-int used Term::Extract (type error) | fp.to_sbv/fp.to_ubv with RTZ | Phase 29 | SMT-LIB2 type soundness restored |
| All casts hardcoded as IntToInt | Exhaustive CastKind match | Phase 29 | FloatToInt/IntToFloat kinds correct |

## Open Questions

1. **TypeScript compiler check (Phase 25 and 27)**
   - What we know: `npx tsc --noEmit` is the UAT evidence command for VSCode changes
   - What's unclear: Whether the TypeScript toolchain is available in the current environment
   - Recommendation: Run `cd vscode-extension && npx tsc --noEmit` early; if unavailable, note as "TypeScript compiler not available in test environment" and mark evidence as manual-only

2. **vcgen_06_set_discriminant_assertion is #[ignore]d**
   - What we know: Phase 29 Plan 05 explicitly left this test ignored — SetDiscriminant VCGen encoding is deferred
   - What's unclear: Whether the UAT should call this out as a known gap
   - Recommendation: Document in UAT Gaps section as known tech debt analogous to the Phase 13 doc-test gap in v0.3-UAT.md

## Sources

### Primary (HIGH confidence)
- All SUMMARY.md files for phases 19-29 — read directly from filesystem
- `milestone-UAT.md` — exact UAT format specification verified
- `v0.3-UAT.md` — additional format reference for multi-phase UAT
- `00-CONTEXT.md` — user decisions lock format, scope, and evidence standard
- `cargo test --workspace` — live test suite health confirmed (0 failures)

### Secondary (MEDIUM confidence)
- `.planning/config.json` — nyquist_validation not present (key absent = skip Validation Architecture section)

## Metadata

**Confidence breakdown:**
- UAT format: HIGH — copied from two existing UAT files in the repo
- Phase deliverables: HIGH — read directly from each phase's SUMMARY.md provides clauses
- Test commands: HIGH — verified against live `cargo test` output and `--list` output
- Test suite health: HIGH — executed `cargo test --workspace` and confirmed 0 failures, 0 clippy warnings

**Research date:** 2026-02-25
**Valid until:** 2026-03-27 (30 days; test suite is stable, no external deps changed)
