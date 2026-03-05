# Phase 45: Quick Wins & Pattern Integration - Context

**Gathered:** 2026-03-04
**Status:** Ready for planning

<domain>
## Phase Boundary

Fix 8 RED regression tests across for-loop VCGen, SetDiscriminant, ghost locals, and spec-int routing. Add 4 pattern matching integration tests (let-else, slice patterns, range patterns, @ bindings). All success criteria are binary: tests pass or they don't. No new verification capabilities are introduced — this phase validates and hardens existing implementations.

</domain>

<decisions>
## Implementation Decisions

### Regression fix approach (COMPL-19..22)
- Fix the underlying VCGen/encoding code to match test expectations — do NOT weaken tests
- The 8 RED unit tests in `vcgen_completeness29_1.rs` define the target behavior; implementation must satisfy them
- SetDiscriminant E2E test (COMPL-20): must produce a verified-or-counterexample result, not silent no-op
- Ghost local guard (COMPL-21): `encode_assignment()` must check `is_ghost` flag and skip ghost locals in SMT encoding
- Spec-int routing (COMPL-22): `uses_spec_int_types()` must scan spec expression strings for `as int`/`as nat` patterns, not just IR types

### Pattern test strategy (PAT-01..04)
- Use real Rust test programs compiled through the full `cargo verify` E2E pipeline
- Each pattern construct gets at least one positive test (correct VC generated) and one negative test (violation detected)
- Test programs should be minimal — smallest possible Rust function exercising the pattern construct
- Verify VCs are correct, not just that the pipeline doesn't crash

### Test organization
- Create one new combined integration test file: `crates/driver/tests/pattern_matching_e2e.rs` for PAT-01..04
- SetDiscriminant E2E test (COMPL-20) goes in `crates/driver/tests/` as appropriate for E2E scope
- COMPL-19 fixes go into existing `crates/analysis/` code to make `vcgen_completeness29_1.rs` tests pass
- COMPL-21 and COMPL-22 regression tests live in `crates/analysis/tests/vcgen_completeness29.rs` (already written, need code fixes)

### Claude's Discretion
- Exact implementation details for fixing each RED test
- Whether pattern tests use `#[requires]`/`#[ensures]` annotations or just verify VC generation
- Helper function structure for pattern test fixtures
- Order of fixing the 8 RED tests (can be parallelized)

</decisions>

<specifics>
## Specific Ideas

No specific requirements — open to standard approaches. Phase is pure regression/test work with binary success criteria defined in ROADMAP.md.

</specifics>

<code_context>
## Existing Code Insights

### Reusable Assets
- `make_func()` helper (vcgen_completeness29.rs:16-49): IR function builder for unit tests
- `make_for_loop_func()` helper (vcgen_completeness29_1.rs:156-200): For-loop IR builder
- `script_to_text()` (vcgen_completeness29.rs:72-176): SMT rendering utility for assertions
- `for_loop_vcgen.rs` module: Complete for-loop VCGen with range/slice/enumerate/conservative paths
- `vcgen.rs:1464-1499`: `generate_set_discriminant_vcs()` function already exists
- `ir.rs:403-430`: `Local` struct with `is_ghost: bool` field and `Local::ghost()` constructor

### Established Patterns
- Unit tests build synthetic IR functions and assert on generated SMT text
- E2E tests in `crates/driver/tests/` compile real Rust programs through the full pipeline
- Test naming convention: `vcgen_XX_description()` for unit tests, descriptive names for E2E
- VCGen completeness tests are grouped by phase in `vcgen_completeness{phase}.rs` files

### Integration Points
- `generate_vcs_with_db()` in vcgen.rs calls `generate_for_loop_vcs()` (line 761)
- `encode_assignment()` in vcgen.rs is where ghost local filtering must happen
- `uses_spec_int_types()` is called during solver/logic selection
- Pattern matching desugars to MIR SwitchInt/discriminant checks — tests exercise existing MIR converter

</code_context>

<deferred>
## Deferred Ideas

None — discussion stayed within phase scope.

</deferred>

---

*Phase: 45-quick-wins-pattern-integration*
*Context gathered: 2026-03-04*
