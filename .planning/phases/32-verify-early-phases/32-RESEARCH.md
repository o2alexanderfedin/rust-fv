# Phase 32: Formal Verification Docs for Early Phases - Research

**Researched:** 2026-02-26
**Domain:** Retrospective documentation — creating VERIFICATION.md files for 7 unverified early phases
**Confidence:** HIGH

<user_constraints>
## User Constraints (from CONTEXT.md)

### Locked Decisions

**Verification approach**
- Method: Code inspection + `cargo test` run for each phase
- Primary evidence: Goal-backward analysis — start from phase goal in ROADMAP.md, trace backward through implementation to confirm delivery
- Depth: Full code review per phase — thorough analysis of every changed file
- Scope: Holistic — verify the phase goal AND flag any obvious issues in surrounding/adjacent code encountered during review

**Content depth & rigor**
- Sections per VERIFICATION.md: Goal, Evidence, Tests (full `cargo test` output), Assessment, Notes — plus a Code Quality / Technical Debt section
- Goal achievement documentation: Both — prose narrative summary + itemized bullet checklist of deliverables
- Test evidence: Paste complete `cargo test` output verbatim into VERIFICATION.md
- File traceability: List key source files changed by each phase to make verification traceable

**Gap / failure handling**
- If gaps found: Document in VERIFICATION.md + create a new fix phase in the roadmap automatically for significant gaps
- Verdict vocabulary: **PASS** / **PASS WITH NOTES** / **FAIL**
- If tests fail: Investigate root cause first (confirm it's a real failure vs environment issue) before issuing verdict
- Fix phase creation: Any FAIL or PASS WITH NOTES requiring code changes gets a new fix phase added to the roadmap

**Template & format**
- Base format: Match existing VERIFICATION.md structure from recent phases (28, 29, 30, 31) exactly
- Retrospective marker: Add a `Retrospective: true` flag in frontmatter + a date note clarifying when verification was created vs when phase ran
- File location: Canonical copy in each phase's own directory (e.g., `.planning/phases/05-.../`); also referenced from Phase 32 directory
- Summary document: Phase 32 produces a `SUMMARY.md` listing all 7 phases with their verdicts and key notes

### Claude's Discretion
- Exact cargo test invocation flags (workspace vs per-crate)
- How to determine which files belong to which early phase (use git log / PLAN.md)
- Structure of the Phase 32 SUMMARY.md
- Order in which phases are processed within each plan

### Deferred Ideas (OUT OF SCOPE)
None — discussion stayed within phase scope
</user_constraints>

## Summary

Phase 32 is a documentation completeness phase. The 7 early phases (05, 06, 07, 08, 11, 13, 17) were executed and shipped across milestones v0.1–v0.3 before the GSD verification step was established. Each phase has PLAN.md and SUMMARY.md files confirming what was done, but no VERIFICATION.md. The Phase 00 UAT (22/22 PASS) provides indirect functional coverage, and the workspace has 3,148 passing tests with 0 failures, confirming these phases are working correctly.

The task is purely retrospective: read each phase's PLAN.md and all SUMMARY.md files, run `cargo test` to collect current evidence, trace key files in git, and produce a VERIFICATION.md that follows the format established in phases 28–31. No new code is written. The primary evidence pattern is goal-backward: start from the phase goal stated in ROADMAP.md, confirm that deliverables listed in SUMMARY files are present in the codebase, and verify tests pass.

The 3 plans split 7 phases naturally: Plan 01 covers phases 05/06/07 (v0.1 POC + v0.2 start), Plan 02 covers phases 08/11 (v0.2), and Plan 03 covers phases 13/17 (v0.3). Each plan will produce 2-3 VERIFICATION.md files. The Phase 32 SUMMARY.md (produced at the end of the last plan) provides a verdict table across all 7 phases.

**Primary recommendation:** Work goal-backward from ROADMAP.md phase goals through SUMMARY.md deliverable lists to code presence checks, collect `cargo test` output verbatim, and produce VERIFICATION.md files that follow the phases 28–31 format with `Retrospective: true` in frontmatter.

## Phase Knowledge Base

### Phase 05: Performance and Polish

**Goal:** Production-ready cargo verify with formula simplification, benchmarks, and diagnostics

**Milestone:** v0.1 POC (shipped 2026-02-12)

**Plans/Deliverables (from SUMMARY files):**
- **05-01:** `crates/analysis/src/simplify.rs` (formula simplification: constant folding, identity elimination, double negation), `crates/analysis/tests/simplify_tests.rs`, benchmark suite extension. Files: simplify.rs, lib.rs, vcgen_bench.rs, stress_bench.rs, simplify_tests.rs
- **05-02:** (Based on SUMMARY context: Criterion A/B benchmarks with simplification impact)
- **05-03:** Ariadne-based diagnostics with VcKind classification (10 categories: Precondition/Postcondition/Overflow/DivisionByZero/ShiftBounds/Assertion/LoopInvariantInit/Preserve/Exit/PanicFreedom), JSON output module, `--output-format` flag. Key files: `crates/driver/src/diagnostics.rs`, `crates/driver/src/json_output.rs`

**Key commits:** 27abf6c, 328f7a4 (05-03)

**Test coverage:** `cargo test -p rust-fv-analysis --test simplify_tests`, integration via `cargo test --workspace`

**What to verify:**
- `crates/analysis/src/simplify.rs` exists with `simplify_term()` and `simplify_script()` functions
- `crates/driver/src/diagnostics.rs` exists with VcKind classification and `report_verification_failure()`
- `crates/driver/src/json_output.rs` exists with `JsonVerificationReport` schema
- Benchmarks compile: `cargo bench -p rust-fv-analysis -- --test`
- All tests pass: `cargo test --workspace`

### Phase 06: Recursive Functions

**Goal:** Recursive functions with termination proofs via `#[decreases(n)]` clause and SCC-based call graph analysis

**Milestone:** v0.2 Advanced Verification (shipped 2026-02-14)

**Plans/Deliverables:**
- **06-01:** `#[decreases(expr)]` proc macro (in crates/macros/src/lib.rs), `Contracts.decreases: Option<SpecExpr>` field, `VcKind::Termination` variant, `RecursiveGroup` type, `CallGraph::detect_recursion()` via petgraph tarjan_scc. petgraph 0.8 added to Cargo.toml
- **06-02:** `crates/analysis/src/recursion.rs` — `encode_recursive_function()` with forall axioms, `check_missing_decreases()`, `generate_termination_vcs()`
- **06-03:** `crates/analysis/tests/recursion_verification.rs` (8 E2E tests via Z3), termination diagnostic helpers `format_missing_decreases_help()` and `format_termination_counterexample()` in `crates/driver/src/diagnostics.rs`. 1,788 tests passing.

**Key commits:** cf71433, 2cd1428 (06-03)

**Requirements:** REC-01 through REC-05, INF-01 (petgraph)

**What to verify:**
- `crates/macros/src/lib.rs` has `pub fn decreases` proc macro
- `crates/analysis/src/ir.rs` has `Contracts.decreases` field
- `crates/analysis/src/vcgen.rs` has `VcKind::Termination` variant
- `crates/analysis/src/call_graph.rs` has `tarjan_scc` usage and `RecursiveGroup` struct
- `crates/analysis/src/recursion.rs` exists
- `crates/analysis/tests/recursion_verification.rs` exists
- `cargo test -p rust-fv-analysis --test recursion_verification` passes

### Phase 07: Closures

**Goal:** Fn/FnMut/FnOnce closure verification via defunctionalization

**Milestone:** v0.2 (shipped 2026-02-14)

**Plans/Deliverables:**
- **07-01:** Closure IR and analysis infrastructure — `ClosureTrait`, `ClosureInfo`, `closure_analysis` module, SMT encoding (closure environment as datatype, `declare-fun` for closure_impl)
- **07-02:** `crates/analysis/src/defunctionalize.rs` — `defunctionalize_closure_call()`, `encode_closure_call_term()`, FnOnce validation, closure spec references in `spec_parser.rs`
- **07-03:** `crates/analysis/tests/closure_verification.rs` (10 E2E tests), `format_closure_contract_help()` and `format_fnonce_double_call_help()` in diagnostics.rs. Key commits: f8fe6ca, ec0769b. 1,843 workspace tests.

**Requirements:** CLO-01 through CLO-06

**What to verify:**
- `crates/analysis/tests/closure_verification.rs` exists (10 tests)
- `crates/analysis/src/defunctionalize.rs` exists
- `crates/analysis/src/closure_analysis.rs` exists (or equivalent)
- `crates/driver/src/diagnostics.rs` has `format_closure_contract_help` and `format_fnonce_double_call_help`
- `cargo test -p rust-fv-analysis --test closure_verification` passes

### Phase 08: Trait Objects

**Goal:** Trait-level contracts with behavioral subtyping, dynamic dispatch, and sealed traits

**Milestone:** v0.2 (shipped 2026-02-14)

**Plans/Deliverables:**
- **08-01:** `TraitDef`, `TraitMethod`, `TraitImpl`, `VcKind::BehavioralSubtyping`, `TraitDatabase` in IR
- **08-02:** `crates/analysis/src/behavioral_subtyping.rs` — `generate_subtyping_vcs()`, sealed trait sum type encoding, trait method call recognition
- **08-03:** `crates/analysis/tests/trait_verification.rs` (10 E2E tests), diagnostic helpers `parse_behavioral_subtyping_message`, `format_precondition_weakening_help`, `format_postcondition_strengthening_help`. Key commits: 777680e, c463799. 1,919 workspace tests.

**Requirements:** TRT-01 through TRT-05

**What to verify:**
- `crates/analysis/tests/trait_verification.rs` exists (10 tests)
- `crates/analysis/src/behavioral_subtyping.rs` exists
- `crates/analysis/src/ir.rs` has `VcKind::BehavioralSubtyping` and `TraitDef`/`TraitImpl`/`TraitMethod`/`TraitDatabase`
- `cargo test -p rust-fv-analysis --test trait_verification` passes

### Phase 11: Floating-Point Verification

**Goal:** IEEE 754 floating-point verification with NaN/Inf VCs and performance warnings

**Milestone:** v0.2 (shipped 2026-02-14)

**Plans/Deliverables:**
- **11-01:** FP terms in SMT-LIB AST — `Sort::FloatingPoint`, `Term::FpLit`, float rounding modes in `crates/smtlib/src/`
- **11-02:** `crates/analysis/src/float_verification.rs` — `generate_float_vcs()`, `encode_float_sort()`, VcKind::FloatingPointNaN, `crates/analysis/src/encode_sort.rs` updates
- **11-03:** `crates/analysis/tests/float_verification.rs` (16 E2E tests), `emit_float_verification_warning()` in diagnostics.rs with AtomicBool one-time warning. Key commits: 0c59924, 98ab12a. 2,149 workspace tests.

**Requirements:** FPV-01 through FPV-06, INF-02

**Note:** Tests validate VC structure (not Z3 SAT/UNSAT) because float_verification VCs use placeholder terms ("lhs", "rhs", "result") — this is intentional by design.

**What to verify:**
- `crates/analysis/tests/float_verification.rs` exists (16 tests)
- `crates/analysis/src/float_verification.rs` exists
- `crates/driver/src/diagnostics.rs` has `emit_float_verification_warning`
- `cargo test -p rust-fv-analysis --test float_verification` passes

### Phase 13: Standard Library Contracts

**Goal:** Preloaded contracts for Vec, Option, Result, HashMap, Iterator with oracle validation

**Milestone:** v0.3 Production Usability (shipped 2026-02-17)

**Plans/Deliverables:**
- **13-01 through 13-04:** `StdlibContractRegistry`, `load_default_contracts()`, per-type contracts (Vec/Option/Result/HashMap/Iterator/String), `ContractDatabase` merge, CLI `--no-stdlib` override
- **13-05:** `crates/analysis/tests/oracle_tests.rs` + oracle/ directory (37 proptest tests), `crates/analysis/tests/e2e_stdlib.rs` (10 E2E tests), proptest-1.6 added. Key commits: db7fc37, 6a02ca0.

**Requirements:** Tier 1 stdlib contracts (Vec, Option, Result, HashMap, Iterator)

**What to verify:**
- `crates/analysis/tests/oracle_tests.rs` exists
- `crates/analysis/tests/oracle/` directory exists with vec_oracle.rs, hashmap_oracle.rs, option_result_oracle.rs, iterator_oracle.rs
- `crates/analysis/tests/e2e_stdlib.rs` exists (10 tests)
- `cargo test -p rust-fv-analysis --test oracle_tests` passes (37 tests × 256 cases)
- `cargo test -p rust-fv-analysis --test e2e_stdlib` passes (10 tests)
- `crates/analysis/Cargo.toml` has proptest dev-dependency

### Phase 17: rust-analyzer Integration

**Goal:** rust-analyzer flycheck integration with auto-configured overrideCommand and diagnostic-based gutter decorations

**Milestone:** v0.3 (shipped 2026-02-17)

**Plans/Deliverables:**
- **17-01:** `--message-format=json` flag outputting rustc-compatible JSON diagnostics from the driver
- **17-02:** `vscode-extension/src/raMode.ts` (mode detection, overrideCommand config, RaModeCallbacks), config.ts updates, package.json settings (`rust-analyzer.rustfv.enable`, `autoVerifyOnSave`), extension.ts RA lifecycle, gutterDecorations.ts `updateGutterDecorationsFromDiagnostics`. Key commits: 3d34c08, ade5793.

**Requirements:** IDE-04 (RA flycheck integration), IDE-05 (deduplication)

**What to verify:**
- `vscode-extension/src/raMode.ts` exists
- `vscode-extension/package.json` has `rust-analyzer.rustfv.enable` setting
- `crates/driver` has `--message-format` flag support
- TypeScript compiles: `npx tsc --noEmit` in vscode-extension/
- `cargo test --workspace` passes (driver tests cover JSON diagnostic output)

## Architecture Patterns

### VERIFICATION.md Structure (from phases 28–31)

```
---
phase: {phase-slug}
verified: {ISO-8601-timestamp}
status: passed | gaps_found | failed
score: N/M must-haves verified
re_verification: false
retrospective: true          # ADD THIS for Phase 32 work
---

# Phase N: {Name} — Verification Report

**Phase Goal:** {from ROADMAP.md}
**Verified:** {timestamp}
**Status:** PASS | PASS WITH NOTES | FAIL
**Retrospective:** Yes — verification document created {date}; phase executed {original date}

## Goal Achievement

### Observable Truths

| # | Truth | Status | Evidence |
|---|-------|--------|----------|
| 1 | {truth} | VERIFIED / NOT VERIFIED | {code location or test evidence} |

**Score:** N/M truths verified

### Required Artifacts

| Artifact | Expected | Status | Details |
|----------|----------|--------|---------|
| `path/to/file` | {what it provides} | VERIFIED / MISSING | {details} |

### Key Link Verification

| From | To | Via | Status | Details |
|------|----|-----|--------|---------|

### Requirements Coverage

| Requirement | Source Plan | Description | Status | Evidence |
|-------------|------------|-------------|--------|----------|

### Code Quality / Technical Debt

| File | Pattern | Severity | Impact |
|------|---------|----------|--------|

### Human Verification Required

{List items needing manual check, or "None"}

### Gaps Summary

{Description of gaps, or "No gaps."}

---

## Verification Evidence Log

```
{cargo test output — verbatim}
```

---

## Retrospective Note

Phase {N} was executed on {original date} and shipped in milestone {v0.x}. This VERIFICATION.md was
created retrospectively on 2026-02-26 as part of Phase 32 audit closure. The phase is covered
by Phase 00 UAT (22/22 PASS) providing indirect functional coverage.

---

_Verified: {timestamp}_
_Verifier: Claude (gsd-verifier)_
```

### Cargo Test Invocations

| Scope | Command | Use Case |
|-------|---------|---------|
| Workspace-wide | `cargo test --workspace` | Collect full suite output |
| Per-crate | `cargo test -p rust-fv-analysis` | Analysis crate tests |
| Per integration test | `cargo test -p rust-fv-analysis --test {name}` | Specific test files |
| Driver tests | `cargo test -p rust-fv-driver` | Driver/diagnostics tests |
| Macros | `cargo test -p rust-fv-macros` | Macro tests |

**Decision:** Use per-crate invocations for targeted evidence, then include workspace summary. Phases 28–31 paste the relevant test binary output, not the entire workspace output.

### Goal-Backward Verification Flow

```
1. Read ROADMAP.md phase goal (one sentence)
2. Read all SUMMARY.md files for the phase
3. Extract deliverables list from SUMMARY frontmatter (key_files.created, key_files.modified)
4. Check each file exists: ls / Glob / Read
5. Check key code patterns: Grep for function names, type names from SUMMARY
6. Run cargo test (crate-scoped) → paste output verbatim
7. Map deliverables → requirements (from PLAN.md must_haves)
8. Assign PASS / PASS WITH NOTES / FAIL
```

### Anti-Patterns to Avoid

- **Verdict before evidence:** Write Observable Truths table first, score last
- **Vague evidence:** Always cite specific file + line number, not just "file exists"
- **Skipping test output:** Test Evidence section requires verbatim `cargo test` output
- **Wrong frontmatter:** Must include `retrospective: true` and both verification date and phase execution date
- **Single file check:** Use Grep to verify internal patterns, not just file existence

## Common Pitfalls

### Pitfall 1: Placeholder Terms in Float Tests
**What goes wrong:** Phase 11's `float_verification.rs` generates VCs with placeholder terms (`lhs`, `rhs`, `result`) not proper SMT encoding. Tests validate VC structure, not Z3 SAT/UNSAT.
**How to avoid:** Document this intentional design choice in Phase 11 VERIFICATION.md. Mark as PASS (by design, not a gap).
**Warning signs:** If Z3 reports "unknown constant lhs" — this is expected.

### Pitfall 2: Phase 05 Plan Numbers in ROADMAP vs Files
**What goes wrong:** ROADMAP.md lists Phase 5 plans as "05-01: Incremental caching and parallel verification", "05-02: Ariadne diagnostics and JSON output", "05-03: cargo verify CLI". But SUMMARY files show 05-03 is "Enhanced Diagnostics and JSON Output" (diagnostics + JSON) and 05-01 is "Formula simplification". The ROADMAP labels are illustrative, not canonical — trust SUMMARY files over ROADMAP for what was actually built.
**How to avoid:** Always read all SUMMARY.md files, not just ROADMAP.md descriptions.

### Pitfall 3: VcKind Exhaustive Match
**What goes wrong:** Phases 06+ add new VcKind variants (Termination, ClosureContract, BehavioralSubtyping, FloatingPointNaN). If verifying that these exist, also check that `diagnostics.rs` handles them in the match arm.
**How to avoid:** Grep for VcKind enum definition AND all match sites.

### Pitfall 4: Retrospective Date Framing
**What goes wrong:** Confusing when the phase ran vs when the verification is being created.
**How to avoid:** Frontmatter has `verified: 2026-02-26T...Z` (when Phase 32 runs it) and a note `phase_executed: 2026-02-12` (when the original phase ran). The Retrospective Note section explicitly calls this out.

### Pitfall 5: Current Test Count Differs from SUMMARY
**What goes wrong:** SUMMARYs report test counts from when phases ran (e.g., "1,788 tests passing"). Current workspace has 3,148 tests. Evidence tables should cite current run counts.
**How to avoid:** Always run fresh `cargo test` — cite current counts in the Evidence Log.

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| File existence check | Custom shell script | Read tool + Grep | Faster, direct evidence |
| Commit history reconstruction | Manual log search | `git log --oneline --grep="phase-slug"` | Definitive, traceable |
| Test run formatting | Custom parser | Paste verbatim cargo test output | Matches established pattern |
| Phase goal text | Paraphrase | Copy from ROADMAP.md verbatim | Traceability |
| Deliverable list | Reconstruct from code | Read from SUMMARY.md files | Already documented |

## Code Examples

### Observable Truths Pattern (from Phase 28)

```markdown
### Observable Truths

| # | Truth | Status | Evidence |
|---|-------|--------|----------|
| 1 | `simplify_term()` and `simplify_script()` public API exist in simplify.rs | VERIFIED | crates/analysis/src/simplify.rs lines X-Y: `pub fn simplify_term(term: &Term) -> Term` and `pub fn simplify_script(script: &Script) -> Script` |
| 2 | Constant folding: `And(BoolLit(true), x) -> x` and `BvAdd(BitVecLit(0,w), x) -> x` | VERIFIED | simplify_tests.rs: test_constant_folding passes |
```

### Retrospective Frontmatter (new for Phase 32)

```yaml
---
phase: 05-performance-and-polish
verified: 2026-02-26T00:00:00Z
status: passed
score: N/M must-haves verified
re_verification: false
retrospective: true
phase_executed: "2026-02-11 to 2026-02-12"
milestone: "v0.1 POC (shipped 2026-02-12)"
---
```

### Cargo Test Evidence Section

```markdown
## Verification Evidence Log

\`\`\`
cargo test -p rust-fv-analysis --test simplify_tests
  running N tests
  test test_constant_fold_and_true ... ok
  ...
  test result: ok. N passed; 0 failed; 0 ignored

cargo test --workspace (summary)
  test result: ok. NNNN passed; 0 failed; N ignored
\`\`\`
```

## Plan-to-Phase Mapping

| Plan | Phases | Strategy |
|------|--------|----------|
| 32-01 | 05, 06, 07 | v0.1 POC polish + v0.2 recursive + v0.2 closures |
| 32-02 | 08, 11 | v0.2 traits + v0.2 floating-point |
| 32-03 | 13, 17 | v0.3 stdlib contracts + v0.3 IDE integration |

**Phase 32 SUMMARY.md structure:** Quick-reference verdict table with columns: Phase #, Name, Verdict, Key Notes. Produced at end of Plan 32-03.

## Verification Context

**Current test suite status:** The workspace currently has approximately 3,148+ passing tests with 0 failures (from v0.1-MILESTONE-AUDIT.md: "3,148 tests pass, 0 failures" as of 2026-02-26). This provides strong baseline evidence for all early phases being functional.

**UAT coverage:** Phase 00 UAT covers 22 test items across phases 01–27 (all PASS). This provides indirect behavioral coverage for phases 05–17.

**Key verification insight:** Since these phases all passed before (evidenced by SUMMARY.md Self-Check sections all reporting "PASSED"), the expected verdict is PASS for all 7. The verification task is to document the evidence formally — not to discover new failures. However, any actual gaps or tech debt encountered should be documented per the CONTEXT.md gap-handling rules.

## Sources

### Primary (HIGH confidence)
- `.planning/phases/32-verify-early-phases/32-CONTEXT.md` — User decisions, locked approach
- `.planning/phases/05-*/0N-SUMMARY.md` through `.planning/phases/17-*/17-02-SUMMARY.md` — Definitive record of what each phase built (read directly)
- `.planning/phases/28-31/XX-VERIFICATION.md` — Canonical format templates (read directly)
- `.planning/v0.1-MILESTONE-AUDIT.md` — Authoritative list of which 7 phases are unverified and why

### Secondary (MEDIUM confidence)
- `.planning/ROADMAP.md` — Phase goals (use verbatim for "Phase Goal:" field in VERIFICATION.md)
- Git log `--grep="0N-"` — Commit traceability for each phase

### Tertiary (LOW confidence)
- PLAN.md files — List of must_haves (use for Observable Truths construction; treat as planned not confirmed)

## Open Questions

1. **Phase 05 plan numbering discrepancy**
   - What we know: ROADMAP.md describes Plan 01 as "Incremental caching and parallel verification" but SUMMARY shows Plan 01 as "Formula simplification". The actual content differs from roadmap labels.
   - What's unclear: Whether there are overlapping features (caching may have moved to a different plan)
   - Recommendation: Trust SUMMARY.md content over ROADMAP labels; read all 3 SUMMARY files before writing Phase 05 VERIFICATION.md

2. **Float verification placeholder terms**
   - What we know: Phase 11 tests intentionally avoid Z3 submission due to placeholder "lhs"/"rhs" terms
   - What's unclear: Whether Phase 11's `float_verification.rs` was ever fully wired to produce proper SMT (or if it remains infrastructure-only)
   - Recommendation: Document the current state honestly; this is a known design choice from the SUMMARY, not a gap to fix

3. **Phase 17 TypeScript compilation**
   - What we know: Phase 17 modifies vscode-extension TypeScript files; Phase 00 UAT confirmed `npx tsc --noEmit` exits 0
   - What's unclear: Whether to re-run TypeScript compilation as part of Phase 17 verification evidence
   - Recommendation: Yes — include `npx tsc --noEmit` output as evidence for Phase 17, consistent with Phase 00 UAT approach

## Metadata

**Confidence breakdown:**
- Phase knowledge base: HIGH — directly read from SUMMARY.md files (authoritative records)
- VERIFICATION.md format: HIGH — directly read from phases 28, 29, 30, 31 (recent canonical examples)
- Cargo test strategy: HIGH — established pattern confirmed in phases 28–31
- Gap probability: HIGH (expected PASS) — all 7 phases had Self-Check: PASSED in their SUMMARY files; workspace has 3,148 passing tests

**Research date:** 2026-02-26
**Valid until:** 2026-03-28 (30 days — stable documentation domain)
