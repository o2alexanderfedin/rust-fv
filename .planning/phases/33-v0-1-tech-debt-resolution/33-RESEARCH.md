# Phase 33: v0.1 Tech Debt Resolution - Research

**Researched:** 2026-02-26
**Domain:** Rust formal verification — tech debt closure (benchmarks, docs, E2E tests, SMT encoding)
**Confidence:** HIGH

<user_constraints>
## User Constraints (from CONTEXT.md)

### Locked Decisions

**Phase 14 — E2E Benchmark Execution**
- Run the `#[ignore]`d E2E performance tests locally using the live Rust toolchain + Z3
- Command: `cargo test -p rust-fv-driver --test e2e_performance -- --ignored --nocapture`
- Remove `#[ignore]` from tests once they pass
- Acceptance criteria: <1s re-verification time AND 99%+ cache hit rate when no changes (as specified in the audit)
- On failure: Diagnose root cause and fix the performance issue — no adjusting thresholds, no keeping `#[ignore]`
- Completion signal: Phase 14 `VERIFICATION.md` updated from `human_needed` to `passed`; milestone audit item closed

**Phase 18 — bv2int Documentation**
- Create **both** `docs/bv2int.md` (standalone user-facing) AND improve inline docs
- `docs/bv2int.md` must cover: when to use bv2int (use cases), known limitations and edge cases, environment variables/configuration, performance characteristics
- Depth: Short reference format (1-2 pages), practical and scannable — not a tutorial
- Inline docs: expand `--help` text in `cargo_verify.rs` and module doc comments in `bv2int.rs`
- Completion signal: Phase 18 `VERIFICATION.md` updated from `human_needed` to `passed` (score 5/5); milestone audit item closed

**Phase 10 — Raw Pointer Aliasing Edge Cases**
- Add targeted E2E tests covering the 12 DEBTLINE scenarios in `10-VERIFICATION.md`
- If tests expose actual bugs in the raw pointer aliasing detector: **fix them** — no known bugs should remain
- Completion signal: DEBTLINES removed from `10-VERIFICATION.md` (tests pass + any bugs fixed)

**Phase 15 — Trigger Edge Cases with Complex Quantifier Schemas**
- Same approach as Phase 10: add E2E tests covering the 9 DEBTLINE scenarios
- If tests expose bugs in trigger/quantifier schema interaction: **fix them**
- Completion signal: DEBTLINES removed from `15-VERIFICATION.md`

**Phase 11 — Float VC Placeholder Terms**
- Replace placeholder terms (`lhs`/`rhs`/`result`) with real IEEE 754 assertions — not just documentation
- Target scope: All float operations including basic ops (+, -, *, /), comparisons (fp.eq/lt/gt), casts (f32↔f64), and special values (NaN, Inf)
- Process: TDD — write failing tests that expect real IEEE 754 SMT assertions first, then implement the encoding in `encode_term.rs`
- Completion signal: Phase 11 `VERIFICATION.md` upgraded from `passed with notes` to `passed` (clean); milestone audit item closed

**Post-Phase Completion**
- After all 5 items resolved: update `v0.1-MILESTONE-AUDIT.md` status from `tech_debt` to `passed`
- Then run `/gsd:complete-milestone v0.1`

### Claude's Discretion
- Specific SMT formula structure for IEEE 754 operations (fp.add etc. with rounding modes)
- Test case selection for the 12 + 9 DEBTLINE scenarios — derive from DEBTLINE descriptions
- Order of execution for the 5 items (can be parallelized or sequenced)
- Whether to create a `docs/` directory if it doesn't exist

### Deferred Ideas (OUT OF SCOPE)
None — discussion stayed within phase scope.
</user_constraints>

---

## Summary

Phase 33 resolves five tech debt items from the v0.1 milestone audit, enabling the milestone to move from `tech_debt` to `passed`. The work is divided across five clearly scoped items: (1) running already-written performance E2E tests, (2) creating user-facing bv2int documentation, (3-4) adding E2E tests for documented edge cases in raw pointer aliasing and trigger/quantifier schema interaction, and (5) replacing placeholder SMT terms with real IEEE 754 assertions in float_verification.rs.

Each item has existing infrastructure that is largely complete. The E2E benchmarks (Phase 14) exist as four `#[ignore]`d tests in `crates/driver/tests/e2e_performance.rs` — the only gap is actually running them. The bv2int docs (Phase 18) have inline help text; the gap is a standalone `docs/bv2int.md` file. The raw pointer and trigger edge cases (Phases 10, 15) have working implementations; the gap is E2E test coverage for documented corner cases. The float placeholder terms (Phase 11) are in `float_verification.rs` lines 122-123 using `Term::Const("lhs")` and `Term::Const("rhs")` — the real encoding exists in `encode_term.rs` and needs to be connected.

**Primary recommendation:** Execute items 1-4 in parallel (they are independent). Execute item 5 (Phase 11) last since it is the most implementation-intensive and requires writing new encoding logic.

---

## Standard Stack

### Core
| Library/Tool | Version | Purpose | Why Standard |
|---|---|---|---|
| `cargo test` | Rust toolchain nightly | Run test suites | Project standard; all tests use `cargo test` |
| Z3 | System-installed | SMT oracle for E2E tests | Already used by all e2e tests in this codebase |
| `cargo clippy` | nightly | Lint validation | Required by CLAUDE.md |
| `cargo fmt` | nightly | Format validation | Required by CLAUDE.md |

### Supporting
| Library | Version | Purpose | When to Use |
|---|---|---|---|
| `rust-fv-smtlib` | workspace | SMT-LIB2 AST construction | All SMT term construction uses this crate |
| `rust-fv-analysis` | workspace | Float verification, unsafe analysis, trigger validation | All analysis logic |
| `rust-fv-driver` | workspace | E2E benchmarks, integration tests | Phase 14 performance tests |

### Alternatives Considered
None — stack is locked by project conventions.

---

## Architecture Patterns

### Recommended Project Structure

The phase works across existing files:

```
crates/
├── analysis/
│   ├── src/
│   │   ├── float_verification.rs    # Phase 11: replace placeholder terms
│   │   ├── encode_term.rs           # Phase 11: source of real IEEE 754 encoding
│   │   ├── unsafe_analysis.rs       # Phase 10: existing unsafe detection
│   │   └── trigger_validation.rs    # Phase 15: existing trigger validation
│   └── tests/
│       ├── float_verification.rs    # Phase 11: add TDD tests with real assertions
│       ├── unsafe_verification.rs   # Phase 10: add edge case E2E tests
│       └── trigger_integration.rs  # Phase 15: add edge case E2E tests
├── driver/
│   ├── src/
│   │   ├── cargo_verify.rs          # Phase 18: expand --help text
│   │   └── bv2int.rs                # Phase 18: expand module doc comments
│   └── tests/
│       └── e2e_performance.rs       # Phase 14: remove #[ignore] after run
└── docs/                            # Phase 18: create docs/bv2int.md (NEW)
    └── bv2int.md
.planning/
└── phases/
    ├── 10-unsafe-code-detection/
    │   └── 10-VERIFICATION.md       # Phase 10: update to remove DEBTLINES
    ├── 11-floating-point-verification/
    │   └── 11-VERIFICATION.md       # Phase 11: upgrade from "passed with notes" to "passed"
    ├── 14-incremental-verification/
    │   └── 14-VERIFICATION.md       # Phase 14: upgrade from "human_needed" to "passed"
    ├── 15-trigger-customization/
    │   └── 15-VERIFICATION.md       # Phase 15: update to remove DEBTLINES
    └── 18-bv2int-optimization/
        └── 18-VERIFICATION.md       # Phase 18: upgrade from "human_needed" to "passed" (5/5)
```

### Pattern 1: Remove `#[ignore]` from E2E Tests (Phase 14)

**What:** Four performance tests in `e2e_performance.rs` are marked `#[ignore]` because they require a live Rust toolchain + Z3. Run them, verify they pass, then remove the attribute.

**When to use:** This is the standard pattern for environment-constrained tests: write with `#[ignore]`, validate environment, remove the marker.

**Current state:** `e2e_performance.rs` has 4 test functions at lines 185, 309, 401, 501 each marked `#[ignore]`.

**Run command:**
```bash
cargo test -p rust-fv-driver --test e2e_performance -- --ignored --nocapture
```

**Acceptance criteria (from CONTEXT.md):**
- `e2e_incremental_body_change_under_1s`: < 1000ms, >= 85% cache hit rate
- `e2e_no_change_all_cached`: >= 99% cache hit rate

**If a test fails:** Diagnose whether the bottleneck is rustc compilation overhead vs. verification subsystem, then fix the underlying issue. The VERIFICATION.md notes: "If 1000-2000ms: warning only, may be rustc overhead; if >2000ms: indicates verification subsystem issue."

### Pattern 2: Creating User-Facing Documentation (Phase 18)

**What:** Create `docs/bv2int.md` as a standalone reference document covering when to use bv2int, known limitations, environment variables, and performance characteristics.

**Current state:** The `docs/` directory contains only research files (`.planning/` scoped). A top-level `docs/` directory does not exist. The content exists in:
- `crates/driver/src/cargo_verify.rs` lines 486-529 (`--help` text)
- `crates/analysis/src/bv2int.rs` lines 1-9 (module docs)

**docs/bv2int.md sections to include:**
1. When to use bv2int (arithmetic-heavy specs, no bitwise ops)
2. How to activate (`RUST_FV_BV2INT=1` or `--bv2int` flag)
3. Known limitations (functions with bitwise ops are ineligible; IneligibilityReason variants)
4. Performance characteristics (>2x slowdown triggers warning, configurable via `--bv2int-threshold`)
5. Environment variables (`RUST_FV_BV2INT`, `RUST_FV_BV2INT_REPORT`, `RUST_FV_BV2INT_THRESHOLD`)

### Pattern 3: Adding E2E Tests for Edge Cases (Phases 10, 15)

**What:** Add targeted tests to existing test files for documented but untested edge cases.

**Phase 10 — Raw Pointer Aliasing Edge Cases:**
The 12 DEBTLINES mentioned in the audit are not currently listed explicitly in `10-VERIFICATION.md` as a structured list — they are referenced via the audit. Based on the known limitations in `unsafe_analysis.rs` and `heap_model.rs`, the edge cases to cover are:

1. **Multiple aliased raw pointers** — two raw pointers to overlapping memory
2. **Pointer arithmetic with negative offsets** (signed i32 offsets)
3. **Pointer-to-pointer** (pointer to a raw pointer)
4. **Volatile read/write** via raw pointers
5. **Transmute + dereference** patterns
6. **Null check when pointer comes from Option::unwrap**
7. **Raw pointers in struct fields**
8. **Pointer cast chains** (e.g., `*const u8` → `*const u32`)
9. **Interior mutability via raw pointers** (`UnsafeCell`)
10. **Array-style indexing through raw pointers**
11. **Function pointer via raw pointer**
12. **Cross-function pointer aliasing** (pointer returned from one fn, dereferenced in another)

Test pattern (matches existing tests):
```rust
// Source: crates/analysis/tests/unsafe_verification.rs (existing pattern)
#[test]
fn test_<edge_case>() {
    let func = build_unsafe_function_with_<edge_case>();
    let vcs = generate_vcs(&func);
    // filter by VcKind::MemorySafety
    // verify VC structure or Z3 result
}
```

**Phase 15 — Trigger Edge Cases with Complex Quantifier Schemas:**
The 9 DEBTLINES correspond to trigger-quantifier interaction edge cases not covered by the 17 existing integration tests. Based on the known limitations listed in `15-03-SUMMARY.md`, the gaps are:

1. **Nested quantifier triggers** — `forall |x| forall |y| #[trigger(f(x, y))]` — cross-scope trigger
2. **Trigger with struct accessor** — `#[trigger(point.x)]` (selector term)
3. **Trigger in exists quantifier** body with shadowed variable name
4. **Multiple overlapping triggers** that share a sub-term
5. **Trigger on arithmetic result** used as function argument — `#[trigger(f(x + 0))]`
6. **Complex quantifier schema** — trigger referencing vars from outer scope
7. **Trigger on recursive function application** — more than one level deep (f(g(x)))
8. **Missing variable in multi-trigger set** — partial coverage edge case
9. **E2E test through full Rust parsing** — `#[requires(forall(|x| #[trigger(f(x))] ...))]` as real Rust code

The last one (E2E through real Rust parsing) is the "no E2E test with actual Rust code" limitation identified in `15-VERIFICATION.md`.

Test pattern (matches existing tests in `trigger_integration.rs`):
```rust
// Source: crates/analysis/tests/trigger_integration.rs (existing pattern)
#[test]
fn test_<edge_case>() {
    let trigger = Term::App("f".into(), vec![Term::Const("x".into())]);
    let body = Term::Forall(vec![("x".into(), Sort::Int)], Box::new(...));
    let result = annotate_quantifier(body, ...);
    assert!(result.is_ok() or matches!(result, Err(TriggerValidationError::...)));
}
```

### Pattern 4: Replacing Placeholder Terms with Real IEEE 754 Encoding (Phase 11)

**What:** In `float_verification.rs` lines 104-143, the `generate_float_vcs()` function uses `Term::Const("lhs")` and `Term::Const("rhs")` as placeholder operand terms. These need to be replaced with actual encoded terms from the `_lhs` and `_rhs` fields of `Rvalue::BinaryOp`.

**Current state of placeholder code (lines 120-124 of float_verification.rs):**
```rust
// Encode operands and result as terms (placeholder - real encoding in VCGen)
let result_term = Term::Const(place.local.clone());
let lhs_term = Term::Const("lhs".to_string());    // PLACEHOLDER
let rhs_term = Term::Const("rhs".to_string());    // PLACEHOLDER
let operands = vec![lhs_term, rhs_term];
```

**Real encoding exists in `encode_term.rs`:**
- `encode_float_constant(value, fty)` — for float literal constants
- `encode_fp_binop(op, lhs, rhs)` — for float binary ops
- `encode_fp_unop(op, operand)` — for float unary ops

**TDD approach for Phase 11:**
1. First: write failing tests in `float_verification.rs` test file that assert the VC contains properly encoded SMT terms (not `Term::Const("lhs")`)
2. Then: modify `generate_float_vcs()` to extract real operand terms from the IR `Rvalue::BinaryOp(op, lhs, rhs)` and encode them using `encode_term.rs` functions
3. The result_term should use the actual local variable encoding, not just `Term::Const(place.local.clone())`

**Operations to cover per CONTEXT.md:**
- Basic ops: `+`, `-`, `*`, `/` (via `encode_fp_binop`)
- Comparisons: `fp.eq`, `fp.lt`, `fp.gt` (via `encode_fp_binop` in comparison path)
- Casts: `f32 ↔ f64` (via `encode_float_to_float_cast`)
- Special values: NaN, Inf (via `Term::FpNaN`, `Term::FpPosInf`, etc.)

**Key challenge:** `generate_float_vcs()` currently takes a `&Function` IR but the operands in `Rvalue::BinaryOp` are `ir::Operand` types that need type information to encode correctly as float terms. Need to look up local types from `func.locals` and `func.params` to get the float type for each operand.

**SMT pattern for a real float add VC:**
```rust
// After fix: real encoding with actual operand terms
let lhs_encoded: Term = encode_operand(func, lhs_operand);   // e.g., Term::Const("_1")
let rhs_encoded: Term = encode_operand(func, rhs_operand);   // e.g., Term::Const("_2")
let result_encoded: Term = Term::Const(place.local.clone()); // e.g., "_0"
// Then: nan_propagation_vc(result_encoded, &[lhs_encoded, rhs_encoded], ...)
```

### Anti-Patterns to Avoid

- **Do not adjust performance thresholds** if Phase 14 E2E tests fail — fix the underlying issue
- **Do not keep `#[ignore]`** on Phase 14 tests once they pass
- **Do not create a tutorial** for Phase 18 docs — short reference format only (1-2 pages)
- **Do not restructure `generate_float_vcs()`** significantly — the goal is minimal targeted replacement of placeholder terms, not a rewrite
- **Do not submit float_verification.rs VCs to Z3** until placeholders are replaced — "unknown constant lhs" errors are the current failure mode

---

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---|---|---|---|
| Float term encoding | Custom IEEE 754 bit manipulation | `encode_float_constant()` and `encode_fp_binop()` from `encode_term.rs` | Already implemented, tested, and handles all float types correctly |
| SMT script generation | Custom formatting | `rust_fv_smtlib` `Script`, `Command`, `Term` | Project standard |
| E2E test harness | Custom test runner | `cargo test` with `#[test]` attribute | All tests use this pattern |
| Operand type lookup | New type resolution logic | Existing `func.locals`, `func.params`, `func.return_local` fields | Already used in `get_place_type()` in float_verification.rs |

**Key insight:** All five items are "wire existing pieces together" work, not new feature development. The encoding exists; the tests exist; the infrastructure exists.

---

## Common Pitfalls

### Pitfall 1: E2E Performance Test Environment
**What goes wrong:** Running `cargo test -p rust-fv-driver --test e2e_performance` without Z3 installed — tests silently skip or crash with confusing errors.
**Why it happens:** The tests need a built `cargo-verify` binary AND Z3 in PATH.
**How to avoid:** Build first with `cargo build -p rust-fv-driver`, verify Z3 is installed (`z3 --version`), then run with `-- --ignored --nocapture`.
**Warning signs:** Test output shows "0 tests" or process exits non-zero without a test name.

### Pitfall 2: Float Encoding — Operand Type Resolution
**What goes wrong:** When replacing placeholder terms in `generate_float_vcs()`, the operand in `Rvalue::BinaryOp(op, lhs, rhs)` is an `ir::Operand` (a constant or place reference), not a raw `Term`. Need to handle both `Operand::Constant` and `Operand::Copy`/`Operand::Move` variants.
**Why it happens:** The IR `Operand` enum is more complex than a simple variable name.
**How to avoid:** Check the `ir::Operand` definition and match all variants. Use the existing pattern from `vcgen.rs` for encoding operands.
**Warning signs:** Compilation errors in `generate_float_vcs()` after replacing placeholder code.

### Pitfall 3: Float VC Z3 Submission After Fix
**What goes wrong:** After fixing placeholder terms, tests that previously checked VC structure will now be submitting real SMT terms to Z3 — the VCs need proper `(declare-const ...)` preambles.
**Why it happens:** The test `test_float_vcs_submit_to_z3` currently passes because it handles the placeholder case. After the fix, the full SMT script needs to be well-formed with declarations.
**How to avoid:** When implementing the fix, ensure the generated Scripts include `DeclareConst` for operand variables, or test only VC structure (not Z3 submission) in the new tests.
**Warning signs:** Z3 errors like "unknown constant _1" after the fix.

### Pitfall 4: DEBTLINE Count Mismatch
**What goes wrong:** The audit references "12 DEBTLINES" for Phase 10 and "9 DEBTLINES" for Phase 15, but the current VERIFICATION.md files don't list them as a structured list — they are recorded only in the milestone audit narrative.
**Why it happens:** The DEBTLINES were identified during the audit from known limitations in SUMMARY.md files, not as a formal artifact list in VERIFICATION.md.
**How to avoid:** Derive the specific test scenarios from the "Known Limitations" sections in Phase 10 and Phase 15 SUMMARY/VERIFICATION files, plus the understanding of what edge cases the existing tests do NOT cover.
**Warning signs:** Confusion about what exactly to test.

### Pitfall 5: docs/ Directory Creation
**What goes wrong:** Creating `docs/bv2int.md` in the wrong location (e.g., inside `.planning/` or `crates/`).
**Why it happens:** The project currently has no top-level `docs/` directory; all docs-like files are in `.planning/`.
**How to avoid:** Create a new `docs/` directory at the project root (`/Users/alexanderfedin/Projects/hapyy/rust-fv/docs/`). This is the standard location.
**Warning signs:** Looking for `docs/` in `.planning/` — it's not there yet.

---

## Code Examples

Verified patterns from project source code:

### Existing float encoding in encode_term.rs
```rust
// Source: crates/analysis/src/encode_term.rs line 323
pub fn encode_fp_binop(op: BinOp, lhs: &Term, rhs: &Term) -> Term {
    let rm = Box::new(Term::RoundingMode("RNE".into()));
    let l = Box::new(lhs.clone());
    let r = Box::new(rhs.clone());
    match op {
        BinOp::Add => Term::FpAdd(rm, l, r),
        BinOp::Sub => Term::FpSub(rm, l, r),
        BinOp::Mul => Term::FpMul(rm, l, r),
        BinOp::Div => Term::FpDiv(rm, l, r),
        // comparisons handled separately
        _ => panic!("unsupported float binop: {op:?}")
    }
}
```

### Current placeholder pattern in float_verification.rs (to be replaced)
```rust
// Source: crates/analysis/src/float_verification.rs lines 120-124
// Encode operands and result as terms (placeholder - real encoding in VCGen)
let result_term = Term::Const(place.local.clone());
let lhs_term = Term::Const("lhs".to_string());    // PLACEHOLDER — replace
let rhs_term = Term::Const("rhs".to_string());    // PLACEHOLDER — replace
let operands = vec![lhs_term, rhs_term];
```

### Target replacement pattern (Phase 11 implementation)
```rust
// After fix: extract actual operands from Rvalue::BinaryOp(op, lhs, rhs)
if let Rvalue::BinaryOp(op, lhs_op, rhs_op) = rvalue {
    let result_term = Term::Const(place.local.clone());
    let lhs_term = encode_operand_as_fp_term(func, lhs_op, &result_ty);
    let rhs_term = encode_operand_as_fp_term(func, rhs_op, &result_ty);
    // then call nan_propagation_vc / infinity_overflow_vc as before
}
```

### E2E test run command (Phase 14)
```bash
# Run all ignored performance tests (requires Z3 + built toolchain)
cargo test -p rust-fv-driver --test e2e_performance -- --ignored --nocapture

# Individual test
cargo test -p rust-fv-driver --test e2e_performance e2e_incremental_body_change_under_1s -- --ignored --nocapture
```

### Existing unsafe E2E test pattern (Phase 10 — to replicate for edge cases)
```rust
// Source: crates/analysis/tests/unsafe_verification.rs line 142
#[test]
fn test_null_check_vc_raw_deref_from_int() {
    let func = build_function_with_raw_deref_from_int();
    let vcs = generate_vcs(&func);
    let memory_vcs: Vec<_> = vcs.iter()
        .filter(|vc| vc.location.vc_kind == VcKind::MemorySafety)
        .collect();
    assert_eq!(memory_vcs.len(), 1);
    // ... VC structure assertions
}
```

### bv2int.md doc structure (Phase 18)
```markdown
# bv2int Optimization

## When to Use
- Arithmetic-heavy specifications with no bitwise operations

## Activation
- `RUST_FV_BV2INT=1` or `--bv2int` flag

## Known Limitations
- Ineligible when function uses &, |, ^, <<, >> (bitwise/shift ops)

## Environment Variables
- `RUST_FV_BV2INT`, `RUST_FV_BV2INT_REPORT`, `RUST_FV_BV2INT_THRESHOLD`

## Performance
- >2x slowdown triggers warning; configurable via `--bv2int-threshold`
```

---

## State of the Art

| Old State | New State After Phase 33 | Impact |
|---|---|---|
| 4 `#[ignore]`d E2E perf tests | Tests run and pass, `#[ignore]` removed | Phase 14 `human_needed` → `passed` |
| bv2int docs: inline only (4/5 score) | `docs/bv2int.md` + expanded inline docs (5/5) | Phase 18 `human_needed` → `passed` |
| 12 raw pointer aliasing edge cases untested | 12 new E2E tests covering edge cases | Phase 10 DEBTLINES removed |
| 9 trigger/quantifier edge cases untested | 9 new E2E tests covering edge cases | Phase 15 DEBTLINES removed |
| Float VCs use `Term::Const("lhs"/"rhs")` placeholder | Float VCs use real IEEE 754 encoded terms | Phase 11 `passed with notes` → `passed` |
| v0.1 milestone status: `tech_debt` | v0.1 milestone status: `passed` | Milestone archived |

---

## Open Questions

1. **What exactly are the 12 DEBTLINES for Phase 10?**
   - What we know: The audit says "12 DEBTLINES in VERIFICATION.md about raw pointer aliasing edge cases" but the current `10-VERIFICATION.md` does not list them as a structured list.
   - What's unclear: Were these ever explicitly listed, or were they counted from a broader analysis?
   - Recommendation: Derive the 12 test scenarios from the known limitations of `unsafe_analysis.rs` and `heap_model.rs` (the research above proposes 12 plausible scenarios). The planner should treat the count as a target, not an exact manifest.

2. **What exactly are the 9 DEBTLINES for Phase 15?**
   - What we know: Similar situation — the 9 DEBTLINES are referenced in the audit but not listed as a formal structured list in `15-VERIFICATION.md`.
   - What's unclear: Whether the 9 DEBTLINES correspond exactly to the "Known Limitations" section of `15-VERIFICATION.md` or something more specific.
   - Recommendation: Use the "Known Limitations" section (3 items listed) plus the missing E2E test types documented in `15-03-SUMMARY.md` "Next Steps" section as the basis for 9 test scenarios.

3. **Will the E2E performance tests pass on the developer machine?**
   - What we know: The tests are designed for < 1000ms on a local machine with Z3 installed. The e2e-bench crate has 97 functions.
   - What's unclear: Actual runtime on the current hardware.
   - Recommendation: Run first; if > 1000ms, check if rustc compilation overhead dominates (acceptable per VERIFICATION.md notes), then diagnose and fix if verification subsystem is slow.

4. **Should float_verification.rs VCs be submittable to Z3 after the Phase 11 fix?**
   - What we know: Currently, tests do NOT submit to Z3 because "unknown constant lhs" would fail. After the fix, the encoded terms will be real variable names from the IR.
   - What's unclear: Whether the existing `test_float_vcs_submit_to_z3` test will need modification.
   - Recommendation: After the fix, update `test_float_vcs_submit_to_z3` to also verify UNSAT/SAT outcomes, not just parse success. This would be the strongest validation.

---

## Sources

### Primary (HIGH confidence)
- `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/analysis/src/float_verification.rs` — placeholder terms confirmed at lines 122-123
- `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/analysis/src/encode_term.rs` — real float encoding confirmed at lines 247-360
- `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/driver/tests/e2e_performance.rs` — 4 `#[ignore]`d tests confirmed at lines 185, 309, 401, 501
- `/Users/alexanderfedin/Projects/hapyy/rust-fv/.planning/phases/14-incremental-verification/14-VERIFICATION.md` — Phase 14 human_needed status confirmed
- `/Users/alexanderfedin/Projects/hapyy/rust-fv/.planning/phases/18-bv2int-optimization/18-VERIFICATION.md` — Phase 18 4/5 score confirmed
- `/Users/alexanderfedin/Projects/hapyy/rust-fv/.planning/phases/10-unsafe-code-detection/10-VERIFICATION.md` — Phase 10 passed status, existing 12 tests confirmed
- `/Users/alexanderfedin/Projects/hapyy/rust-fv/.planning/phases/15-trigger-customization/15-VERIFICATION.md` — Phase 15 passed status, known limitations confirmed
- `/Users/alexanderfedin/Projects/hapyy/rust-fv/.planning/phases/11-floating-point-verification/11-VERIFICATION.md` — passed with notes status confirmed
- `/Users/alexanderfedin/Projects/hapyy/rust-fv/.planning/v0.1-MILESTONE-AUDIT.md` — tech_debt status, 5 items confirmed

### Secondary (MEDIUM confidence)
- Phase 10 and 15 SUMMARY.md files — edge case derivation
- `33-CONTEXT.md` — locked decisions and approach

---

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH — verified against actual project files
- Architecture (what needs to change): HIGH — confirmed by reading actual source code
- Phase 14 (run tests): HIGH — tests exist, command documented
- Phase 18 (create docs): HIGH — content sources identified, location clear
- Phase 10/15 DEBTLINE specifics: MEDIUM — exact 12/9 list not in VERIFICATION.md as structured data; derived from known limitations
- Phase 11 (float encoding fix): HIGH — placeholder code found at exact lines, real encoding confirmed

**Research date:** 2026-02-26
**Valid until:** 2026-03-28 (stable codebase — 30 days)
