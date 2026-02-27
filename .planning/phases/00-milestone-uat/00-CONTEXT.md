# Phase 00: milestone-uat - Context

**Gathered:** 2026-02-25
**Status:** Ready for planning

<domain>
## Phase Boundary

Create and execute a UAT document validating that milestones v0.4 (phases 19-27) and v0.5 (phases 28-29) work correctly end-to-end. Neither milestone has a UAT file yet. This phase closes that gap with one combined UAT document following the existing `milestone-UAT.md` / `v0.3-UAT.md` pattern.

Creating new verification tests or fixing bugs is out of scope — this phase only validates what was shipped.

</domain>

<decisions>
## Implementation Decisions

### Coverage scope
- Cover both v0.4 (phases 19-27) and v0.5 (phases 28-29) in one combined UAT file
- File name: `v0.4-v0.5-UAT.md` in `.planning/phases/00-milestone-uat/`
- 1–2 test items per phase (phases 19-29 = ~22-44 total tests)

### Test derivation
- Derive test cases from each phase's SUMMARY.md `provides` clauses — ensures coverage of every declared deliverable
- Each test's `expected` field: concrete observable behavior ("Running X produces Y") — testable by running commands
- Include specific `cargo test` names as evidence hints in each test item

### Evidence standard
- Run full suite: `cargo test --workspace` — capture overall pass count and zero failures
- Run targeted subsets per UAT item (e.g., `cargo test vcgen`, `cargo test separation_logic`) — specific proof per item
- Clippy check required: `cargo clippy --workspace` must produce zero warnings

### Failure policy
- Blocking: a `fail` result stops UAT and milestone completion is blocked until fixed
- When a failure occurs: capture exact commands run, full output, minimal reproduction case, and root cause hypothesis
- Diagnosis goes in the UAT item's `result`/`evidence` fields with `status: diagnosed`

### Claude's Discretion
- Exact ordering of test items within the document
- How to group phases 19-27 vs 28-29 within the file (sections or flat list)
- Whether to include a summary table at the top

</decisions>

<specifics>
## Specific Ideas

- Follow the exact YAML front-matter format from `milestone-UAT.md` (status, phase, source, started, updated fields)
- Test format: `### N. Test Name` with `expected:`, `result:`, `evidence:` fields — matches existing UAT style
- The `source` field should list all SUMMARY.md files from phases 19-29

</specifics>

<deferred>
## Deferred Ideas

None — discussion stayed within phase scope.

</deferred>

---

*Phase: 00-milestone-uat*
*Context gathered: 2026-02-25*
