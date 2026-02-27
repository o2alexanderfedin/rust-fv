# Phase 33: v0.1 Tech Debt Resolution - Context

**Gathered:** 2026-02-26
**Status:** Ready for planning

<domain>
## Phase Boundary

Resolve all 5 tech debt items from the v0.1 milestone audit. Each item has a specific resolution path. Completing this phase allows the v0.1 milestone to move from `tech_debt` → `passed` status and enables archiving.

Items in scope:
1. **Phase 14** — Run E2E incremental performance benchmarks (environment constraint)
2. **Phase 18** — Create `docs/bv2int.md` user-facing documentation (product decision)
3. **Phase 10** — Fix raw pointer aliasing edge cases (12 DEBTLINES)
4. **Phase 15** — Add E2E tests for trigger edge cases with complex quantifier schemas (9 DEBTLINES)
5. **Phase 11** — Replace float VC placeholder terms with real IEEE 754 assertions

</domain>

<decisions>
## Implementation Decisions

### Phase 14 — E2E Benchmark Execution
- Run the `#[ignore]`d E2E performance tests locally using the live Rust toolchain + Z3
- Command: `cargo test -p rust-fv-driver --test e2e_performance -- --ignored --nocapture`
- Remove `#[ignore]` from tests once they pass
- **Acceptance criteria:** <1s re-verification time AND 99%+ cache hit rate when no changes (as specified in the audit)
- **On failure:** Diagnose root cause and fix the performance issue — no adjusting thresholds, no keeping `#[ignore]`
- **Completion signal:** Phase 14 `VERIFICATION.md` updated from `human_needed` to `passed`; milestone audit item closed

### Phase 18 — bv2int Documentation
- Create **both** `docs/bv2int.md` (standalone user-facing) AND improve inline docs
- `docs/bv2int.md` must cover: when to use bv2int (use cases), known limitations and edge cases, environment variables/configuration, performance characteristics
- **Depth:** Short reference format (1-2 pages), practical and scannable — not a tutorial
- Inline docs: expand `--help` text in `cargo_verify.rs` and module doc comments in `bv2int.rs`
- **Completion signal:** Phase 18 `VERIFICATION.md` updated from `human_needed` to `passed` (score 5/5); milestone audit item closed

### Phase 10 — Raw Pointer Aliasing Edge Cases
- Add targeted E2E tests covering the 12 DEBTLINE scenarios in `10-VERIFICATION.md`
- If tests expose actual bugs in the raw pointer aliasing detector: **fix them** — no known bugs should remain
- **Completion signal:** DEBTLINES removed from `10-VERIFICATION.md` (tests pass + any bugs fixed)

### Phase 15 — Trigger Edge Cases with Complex Quantifier Schemas
- Same approach as Phase 10: add E2E tests covering the 9 DEBTLINE scenarios
- If tests expose bugs in trigger/quantifier schema interaction: **fix them**
- **Completion signal:** DEBTLINES removed from `15-VERIFICATION.md`

### Phase 11 — Float VC Placeholder Terms
- **Replace placeholder terms (`lhs`/`rhs`/`result`) with real IEEE 754 assertions** — not just documentation
- **Target scope:** All float operations including basic ops (+, -, *, /), comparisons (fp.eq/lt/gt), casts (f32↔f64), and special values (NaN, Inf)
- **Process:** TDD — write failing tests that expect real IEEE 754 SMT assertions first, then implement the encoding in `encode_term.rs`
- **Completion signal:** Phase 11 `VERIFICATION.md` upgraded from `passed with notes` to `passed` (clean); milestone audit item closed

### Post-Phase Completion
- After all 5 items resolved: update `v0.1-MILESTONE-AUDIT.md` status from `tech_debt` to `passed`
- Then run `/gsd:complete-milestone v0.1`

### Claude's Discretion
- Specific SMT formula structure for IEEE 754 operations (fp.add etc. with rounding modes)
- Test case selection for the 12 + 9 DEBTLINE scenarios — derive from DEBTLINE descriptions
- Order of execution for the 5 items (can be parallelized or sequenced)
- Whether to create a `docs/` directory if it doesn't exist

</decisions>

<specifics>
## Specific Ideas

- Phase 14 test command is known: `cargo test -p rust-fv-driver --test e2e_performance -- --ignored --nocapture`
- Phase 11 encoding infrastructure already exists in `encode_term.rs` — extend it rather than rewrite
- DEBTLINES in VERIFICATION.md files are the authoritative list of what needs addressing for Ph10 and Ph15

</specifics>

<deferred>
## Deferred Ideas

None — discussion stayed within phase scope.

</deferred>

---

*Phase: 33-v0-1-tech-debt-resolution*
*Context gathered: 2026-02-26*
