# Phase 30: SetDiscriminant VCGen Implementation - Research

**Researched:** 2026-02-26
**Domain:** Rust formal verification — IR statement extension + SMT VC emission
**Confidence:** HIGH

<user_constraints>
## User Constraints (from CONTEXT.md)

### Locked Decisions

**Discriminant VC assertion form:**
- Integer equality form: `discriminant(place) == variant_index` (not symbolic/typed)
- Emitted as an inline assertion VC at the SetDiscriminant statement site
- Hard assert (checked VC — must prove discriminant is set correctly), not an assumption
- `variant_index` uses the raw integer index from MIR (`VariantIdx` as integer), not symbolic variant names

**Test coverage breadth:**
- Un-ignore `vcgen_06_set_discriminant_assertion` only — sufficient for phase closure per ROADMAP
- TDD RED test in plan 30-01: write BOTH a unit test (IR construction) AND an integration test (full MIR→IR→VCGen pipeline)
- Test assertions use contains-check: verify VC output contains `discriminant` and the variant index (not exact string match)

**Edge case handling:**
- Unit variants (no fields): handle in-scope — same VCGen path applies
- Single-variant ADTs: handle in-scope — integer equality VC applies naturally, no special-casing
- Out-of-range variant_index: `panic!` / `unreachable!` — IR is internal, malformed IR is a compiler bug
- Nested discriminants (place projections): handle in-scope if they arise naturally from MIR lowering; do not artificially block

**IR variant fields:**
- Current ir.rs already has `SetDiscriminant(Place, usize)` — this is the correct form
- `AdtDef` from CONTEXT.md discussion applies only to driver crate context; analysis IR must remain TyCtxt-free
- Use `usize` (already in place) as variant index — no newtype wrapper
- `derive(Debug)` already on `Statement` enum via existing derive

**Claude's Discretion:**
- Exact `Display` format string
- Whether to add a Display impl for SetDiscriminant specifically
- Exact test fixture construction for the RED test
- How to insert the new `generate_set_discriminant_vcs` call into `generate_vcs_with_db`

### Deferred Ideas (OUT OF SCOPE)

None — discussion stayed within phase scope
</user_constraints>

<phase_requirements>
## Phase Requirements

| ID | Description | Research Support |
|----|-------------|-----------------|
| VCGEN-06 | Projected LHS mutation + SetDiscriminant assertion VC emission | VCGen generator pattern documented below; `discriminant-{local}` Term::App encoding verified in codebase |
| MIRCONV-02 | Aggregate conversion + `ir::Statement::SetDiscriminant` fully wired | IR variant already exists at ir.rs:608; mir_converter.rs:184-190 already converts MIR SetDiscriminant; gap is only VCGen emission |
</phase_requirements>

---

## Summary

Phase 30 is a targeted gap-closure phase. The `ir::Statement::SetDiscriminant(Place, usize)` variant already exists in the analysis IR (added in Phase 29 Plan 03) and `mir_converter.rs` already converts MIR `SetDiscriminant` to it. The gap is purely in VCGen: `vcgen.rs` currently treats `SetDiscriminant` as a no-op (no VC emitted). The test `vcgen_06_set_discriminant_assertion` is `#[ignore]`d with a `todo!()` body.

The work breaks into three plans matching the ROADMAP: (1) write TDD RED tests — a unit test for IR construction and an integration test checking VCGen pipeline, both intentionally failing; (2) implement `generate_set_discriminant_vcs()` in `vcgen.rs` following the `generate_index_bounds_vcs` pattern, emitting a `discriminant(place) == variant_index` assertion VC per statement site; (3) fill in the `vcgen_06_set_discriminant_assertion` test body and remove `#[ignore]`, confirm full suite GREEN.

The discriminant encoding follows the established pattern from Phase 28: `Rvalue::Discriminant` already uses `Term::App("discriminant-{local}", [Term::Const(local)])`. The SetDiscriminant VC should assert `discriminant-{place.local}(place) == variant_index` using `Term::Eq` over the app term and an integer literal. The SMT script uses `QF_BV` logic (or `QF_UFBVDT` if datatype declarations are present) via `base_script()`.

**Primary recommendation:** Add `generate_set_discriminant_vcs(func, datatype_declarations, declarations)` in `generate_vcs_with_db` immediately after `generate_index_bounds_vcs`, following the identical call pattern. The function iterates blocks/statements, matches `Statement::SetDiscriminant(place, idx)`, and emits one `VerificationCondition` per site with `VcKind::Assertion`.

---

## Standard Stack

### Core (project-specific, no external additions needed)

| Component | Location | Purpose | Status |
|-----------|----------|---------|--------|
| `ir::Statement::SetDiscriminant` | `crates/analysis/src/ir.rs:608` | IR variant already exists as `SetDiscriminant(Place, usize)` | Already present |
| `mir_converter::convert_statement` | `crates/driver/src/mir_converter.rs:184-190` | MIR→IR conversion already wired | Already present |
| `vcgen::generate_vcs_with_db` | `crates/analysis/src/vcgen.rs:235` | Entry point where new generator call is added | Needs `generate_set_discriminant_vcs` call |
| `Term::App` / `Term::Eq` / `Term::IntLit` | `rust_fv_smtlib` crate | SMT term construction | Available |
| `VcKind::Assertion` | `crates/analysis/src/vcgen.rs:104` | Correct kind for hard-assert VCs | Available |
| `base_script()` | `crates/analysis/src/vcgen.rs:1491` | Script setup with correct logic selection | Available |

### No New Dependencies

This phase requires zero new Cargo dependencies. All building blocks exist in the codebase.

---

## Architecture Patterns

### Recommended File Changes

```
crates/analysis/src/vcgen.rs          — add generate_set_discriminant_vcs() + wire into generate_vcs_with_db
crates/analysis/tests/vcgen_completeness29.rs  — fill vcgen_06_set_discriminant_assertion + add RED unit/integration tests
```

### Pattern 1: Statement-Level VC Generator (Template from generate_index_bounds_vcs)

**What:** A free function that iterates all blocks/statements, matches a specific `Statement` variant, and emits one `VerificationCondition` per matching site.

**When to use:** Any time a statement-level IR construct needs a VCGen VC (not path-based).

**Example (generate_index_bounds_vcs pattern — source: vcgen.rs:1374):**

```rust
// Source: crates/analysis/src/vcgen.rs:1374
fn generate_index_bounds_vcs(
    func: &Function,
    datatype_declarations: &[Command],
    declarations: &[Command],
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    for (block_idx, bb) in func.basic_blocks.iter().enumerate() {
        for (stmt_idx, stmt) in bb.statements.iter().enumerate() {
            let index_operand = match stmt {
                Statement::Assign(_, Rvalue::Use(op)) => extract_index_operand(op),
                _ => None,
            };

            if let Some((arr_local, idx_local)) = index_operand {
                // ... build script, push assertion, push VerificationCondition
                vcs.push(VerificationCondition {
                    description: desc,
                    script,
                    location: VcLocation {
                        function: func.name.clone(),
                        block: block_idx,
                        statement: stmt_idx,
                        source_file: None,
                        source_line: None,
                        source_column: None,
                        contract_text: Some(...),
                        vc_kind: VcKind::MemorySafety,
                    },
                });
            }
        }
    }
    vcs
}
```

**SetDiscriminant adaptation:**

```rust
fn generate_set_discriminant_vcs(
    func: &Function,
    datatype_declarations: &[Command],
    declarations: &[Command],
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    for (block_idx, bb) in func.basic_blocks.iter().enumerate() {
        for (stmt_idx, stmt) in bb.statements.iter().enumerate() {
            if let Statement::SetDiscriminant(place, variant_idx) = stmt {
                // discriminant-{local}({local}) == variant_idx
                let disc_fn = format!("discriminant-{}", place.local);
                let disc_term = Term::App(disc_fn, vec![Term::Const(place.local.clone())]);
                let idx_term = Term::IntLit(*variant_idx as i64);
                let assertion = Term::Eq(Box::new(disc_term), Box::new(idx_term));

                let mut script = base_script(
                    datatype_declarations,
                    declarations,
                    uses_spec_int_types(func),
                );

                let desc = format!(
                    "{}: discriminant of `{}` == {} at block {}",
                    func.name, place.local, variant_idx, block_idx
                );
                script.push(Command::Comment(desc.clone()));
                // Negate: UNSAT = assertion holds
                script.push(Command::Assert(Term::Not(Box::new(assertion))));
                script.push(Command::CheckSat);
                script.push(Command::GetModel);

                vcs.push(VerificationCondition {
                    description: desc,
                    script,
                    location: VcLocation {
                        function: func.name.clone(),
                        block: block_idx,
                        statement: stmt_idx,
                        source_file: None,
                        source_line: None,
                        source_column: None,
                        contract_text: Some(format!(
                            "discriminant({}) == {}",
                            place.local, variant_idx
                        )),
                        vc_kind: VcKind::Assertion,
                    },
                });
            }
        }
    }
    vcs
}
```

**Wire into generate_vcs_with_db (after generate_index_bounds_vcs call, ~line 321):**

```rust
// Generate discriminant assertion VCs for SetDiscriminant statements (VCGEN-06).
let mut disc_vcs = generate_set_discriminant_vcs(func, &datatype_declarations, &declarations);
conditions.append(&mut disc_vcs);
```

### Pattern 2: Discriminant Term Encoding (established in Phase 28)

**What:** `Rvalue::Discriminant` encoding uses `Term::App("discriminant-{local}", [Term::Const(local)])` — an uninterpreted function application. SetDiscriminant VC reuses this same naming convention.

**Source:** `crates/analysis/src/vcgen.rs:1659-1667`

```rust
// Source: vcgen.rs:1659
Rvalue::Discriminant(disc_place) => {
    let disc_fn = format!("discriminant-{}", disc_place.local);
    Term::App(disc_fn, vec![Term::Const(disc_place.local.clone())])
}
```

The SetDiscriminant VC **must use the same naming convention** so that SMT assertions about the discriminant are consistent whether read via `Rvalue::Discriminant` or set via `Statement::SetDiscriminant`.

### Pattern 3: TDD RED Tests in vcgen_completeness29.rs

**What:** Tests written before implementation that will fail (RED) until the implementation is complete.

**Pattern observed:**

```rust
// Unit test: IR construction — RED because VCGen returns 0 VCs for SetDiscriminant
#[test]
fn vcgen_06_set_discriminant_assertion_unit() {
    let blocks = vec![BasicBlock {
        statements: vec![Statement::SetDiscriminant(Place::local("_1"), 1)],
        terminator: Terminator::Return,
    }];
    let func = make_func("set_disc_vc", Ty::Int(IntTy::I32), vec![], vec![], blocks);
    let vcs = vcgen::generate_vcs(&func, None);

    assert!(
        !vcs.conditions.is_empty(),
        "VCGEN-06: expected VC for SetDiscriminant, got 0"
    );

    let all_smt: String = vcs
        .conditions
        .iter()
        .map(|vc| script_to_text(&vc.script))
        .collect::<Vec<_>>()
        .join("\n");

    assert!(
        all_smt.contains("discriminant"),
        "VCGEN-06: expected 'discriminant' in SMT output but got:\n{all_smt}"
    );
    assert!(
        all_smt.contains('1'),
        "VCGEN-06: expected variant index '1' in SMT output but got:\n{all_smt}"
    );
}
```

### Anti-Patterns to Avoid

- **Using `Term::BitVecLit` for variant_index:** The discriminant function is uninterpreted (Sort::Int implied), so use `Term::IntLit` not `Term::BitVecLit`. The SMT sort must be consistent with how `Rvalue::Discriminant` is declared.
- **Adding a full `DeclareFun` for discriminant:** Phase 28 decision (STATE.md:161) confirmed Z3 accepts `Term::App` without explicit `declare-fun` — do NOT add one.
- **Using `VcKind::MemorySafety`:** SetDiscriminant is a correctness assertion (discriminant is set correctly), not a memory safety check. Use `VcKind::Assertion`.
- **Modifying the existing `Statement::SetDiscriminant(Place, usize)` tuple variant:** The current form is correct and already used in monomorphize.rs and borrow_conflict.rs. Do NOT change to struct syntax or add fields — it would require updating those callers.
- **Emitting an assumption (not assertion):** CONTEXT.md locked: hard assert, not an assumption.

---

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Script construction | Custom Script builder | `base_script(datatype_declarations, declarations, uses_spec_int_types(func))` | Already handles logic selection (QF_BV vs QF_UFBVDT vs ALL) |
| Discriminant term naming | Custom naming scheme | `format!("discriminant-{}", place.local)` | Must match Rvalue::Discriminant encoding (vcgen.rs:1666) for SMT consistency |
| VC accumulation pattern | Custom merge | `conditions.append(&mut disc_vcs)` | Matches all other generator call sites in generate_vcs_with_db |
| Test body structure | New helpers | `make_func()` + `script_to_text()` already in vcgen_completeness29.rs | Reuse existing test infrastructure |

**Key insight:** This phase is almost entirely wiring existing building blocks. The SMT encoding, test helpers, VC structure, and IR variant all exist. The only new code is `generate_set_discriminant_vcs()` (~30 lines) and the test body (~20 lines).

---

## Common Pitfalls

### Pitfall 1: Wrong SMT Sort for Variant Index

**What goes wrong:** Using `Term::BitVecLit(idx as i128, 32)` for the variant index comparison.

**Why it happens:** Other VCGen places use BitVec for integer comparisons.

**How to avoid:** The discriminant function is uninterpreted and Z3 infers its sort. Use `Term::IntLit` (integer, not bitvec). If Z3 rejects, fall back to `Term::BitVecLit(idx as i128, 32)` — but start with IntLit for consistency with how `Rvalue::Discriminant` is used in SwitchInt.

**Warning signs:** SMT parse error mentioning sort mismatch or "ambiguous sort".

### Pitfall 2: Existing mirconv_02_set_discriminant Test Breakage

**What goes wrong:** The `mirconv_02_set_discriminant` test at line 384 expects `vcgen::generate_vcs` to **not panic** and previously expected 0 VCs (implicit). After plan 30-02, VCGen will emit VCs for SetDiscriminant.

**Why it happens:** The test only asserts the call succeeds (no panic), not VC count. The new VCs do not break this assertion.

**How to avoid:** Read the test: it calls `let _vcs = vcgen::generate_vcs(&func, None)` with no assertion on `_vcs.conditions.is_empty()`. The test will still pass after plan 30-02 — no change needed.

**Warning signs:** If someone added a `assert!(vcs.conditions.is_empty())` — but they did not; the test comment says "vcgen must not panic; SetDiscriminant is a no-op for now" and the `_vcs` is intentionally unused.

### Pitfall 3: Forgetting the #[ignore] Comment Must Change

**What goes wrong:** Removing `#[ignore]` but leaving the `todo!()` body unchanged.

**Why it happens:** Two separate changes needed in plan 30-03: remove the attribute AND replace the body.

**How to avoid:** Plan 30-03 must replace the entire test body with a real assertion, not just remove the `#[ignore]` line.

### Pitfall 4: SMT Logic Mismatch

**What goes wrong:** `base_script` selects `QF_BV` but the discriminant function uses integer sort — Z3 might reject in pure bitvector logic.

**Why it happens:** `base_script` selects QF_BV when there are no datatype declarations. `Term::App` for uninterpreted functions may require UF (uninterpreted functions) theory.

**How to avoid:** Pass the `datatype_declarations` correctly. If the function has enum types (datatype declarations), `base_script` will use `QF_UFBVDT` which supports UF. For a pure no-enum test fixture, you may need to check if QF_BV is sufficient for uninterpreted function apps. Phase 28 (STATE.md:161) confirmed Z3 accepts this. Use `QF_UFBVDT` explicitly if QF_BV tests fail, OR pass a non-empty `datatype_declarations` slice.

**Warning signs:** Z3 returns `unknown` or parse error mentioning UF.

---

## Code Examples

### Current State: SetDiscriminant in ir.rs

```rust
// Source: crates/analysis/src/ir.rs:600-611
/// A MIR statement.
#[derive(Debug, Clone)]
pub enum Statement {
    /// `place = rvalue`
    Assign(Place, Rvalue),
    /// No-op (padding, debug info, etc.)
    Nop,
    /// Set enum variant discriminant (tag).
    SetDiscriminant(Place, usize),
    /// Inject an assumption premise.
    Assume(Operand),
}
```

### Current State: mir_converter.rs (already wired)

```rust
// Source: crates/driver/src/mir_converter.rs:184-190
mir::StatementKind::SetDiscriminant {
    place,
    variant_index,
} => Some(ir::Statement::SetDiscriminant(
    convert_place(place),
    variant_index.as_usize(),
)),
```

### Current State: VCGen (no-op, must be fixed in Plan 30-02)

```rust
// Source: vcgen.rs:1184-1212 — all statement loops use if-let on Statement::Assign only
// SetDiscriminant is silently skipped — no VC emitted
for (stmt_idx, stmt) in block.statements.iter().enumerate() {
    if let Statement::Assign(place, rvalue) = stmt {
        // ... only Assign handled
    }
    // SetDiscriminant, Assume, Nop — all skipped (no-op)
}
```

### Target: Wire in generate_vcs_with_db

```rust
// Source: vcgen.rs:321 (after generate_index_bounds_vcs call)
let mut index_vcs = generate_index_bounds_vcs(func, &datatype_declarations, &declarations);
conditions.append(&mut index_vcs);

// ADD AFTER:
let mut disc_vcs = generate_set_discriminant_vcs(func, &datatype_declarations, &declarations);
conditions.append(&mut disc_vcs);
```

### Target: vcgen_06_set_discriminant_assertion Test Body (Plan 30-03)

```rust
// Un-ignore and fill in — contains-check per CONTEXT.md decision
#[test]
fn vcgen_06_set_discriminant_assertion() {
    use rust_fv_analysis::ir::IntTy;
    let blocks = vec![BasicBlock {
        statements: vec![Statement::SetDiscriminant(Place::local("_1"), 2)],
        terminator: Terminator::Return,
    }];
    let func = make_func("set_disc", Ty::Int(IntTy::I32), vec![], vec![], blocks);
    let vcs = vcgen::generate_vcs(&func, None);

    assert!(
        !vcs.conditions.is_empty(),
        "VCGEN-06c: expected at least one VC for SetDiscriminant, got 0"
    );

    let all_smt: String = vcs
        .conditions
        .iter()
        .map(|vc| script_to_text(&vc.script))
        .collect::<Vec<_>>()
        .join("\n");

    assert!(
        all_smt.contains("discriminant"),
        "VCGEN-06c: expected 'discriminant' in SMT, got:\n{all_smt}"
    );
    assert!(
        all_smt.contains('2'),
        "VCGEN-06c: expected variant index '2' in SMT, got:\n{all_smt}"
    );
}
```

---

## State of the Art

| Old State | Current State | Introduced | Impact |
|-----------|---------------|------------|--------|
| `Statement::SetDiscriminant` absent from IR | `SetDiscriminant(Place, usize)` in ir.rs:608 | Phase 29 Plan 03 | IR variant exists; monomorphize.rs and borrow_conflict.rs already handle it |
| `mirconv_02_set_discriminant` was `#[ignore]` | Test is GREEN (no-op assertion passes) | Phase 29 Plan 03 | MIR→IR conversion verified; VCGen still treats as no-op |
| `vcgen_06_set_discriminant_assertion` is `#[ignore]` with `todo!()` | Must become GREEN | Phase 30 Plan 03 | Requires Plan 30-02 to emit the VC |
| VCGen treats SetDiscriminant as no-op | Must emit `discriminant(p)==idx` assertion VC | Phase 30 Plan 02 | Closes VCGEN-06 partial gap |

**Key fact (from STATE.md:161):** Phase 28 confirmed `Task 2 (SMT DeclareFun for discriminant) skipped — vcgen_02 tests pass after Task 1 alone; Z3 accepts Term::App without explicit declare-fun`. This means the SetDiscriminant VC can use `Term::App` directly without adding a `DeclareFun` command.

---

## Open Questions

1. **SMT sort of discriminant function in pure QF_BV context**
   - What we know: Phase 28 confirmed Z3 accepts `Term::App("discriminant-{local}", ...)` without `declare-fun` in `QF_UFBVDT` context. The `mirconv_02_set_discriminant` test uses a function with no datatype declarations, so `base_script` will select `QF_BV`.
   - What's unclear: Will `Term::App` (UF) be accepted in a strict `QF_BV` logic context without explicit declaration?
   - Recommendation: For the RED test in Plan 30-01, use a test fixture with an enum type (so `datatype_declarations` is non-empty and `QF_UFBVDT` is selected). If sort issues arise in Plan 30-02, add a `Command::DeclareFun` for the discriminant function — but try without first per the Phase 28 precedent.

---

## Sources

### Primary (HIGH confidence)

- `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/analysis/src/ir.rs` — Statement enum, SetDiscriminant(Place, usize) at line 608
- `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/analysis/src/vcgen.rs` — generate_vcs_with_db (235), generate_index_bounds_vcs (1374), generate_assert_terminator_vcs (1789), base_script (1491), VcKind enum (86), Rvalue::Discriminant encoding (1659)
- `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/driver/src/mir_converter.rs` — MIR SetDiscriminant conversion at lines 184-190
- `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/analysis/tests/vcgen_completeness29.rs` — vcgen_06_set_discriminant_assertion at line 600, mirconv_02_set_discriminant at line 384
- `/Users/alexanderfedin/Projects/hapyy/rust-fv/.planning/STATE.md` — Phase 28 decision on discriminant Term::App without declare-fun (line 161), Phase 29-03 decision on SetDiscriminant/Assume as no-ops (line 173)
- `/Users/alexanderfedin/Projects/hapyy/rust-fv/.planning/v0.1-MILESTONE-AUDIT.md` — VCGEN-06 and MIRCONV-02 gap evidence (lines 12-25)

### Secondary (MEDIUM confidence)

- `/Users/alexanderfedin/Projects/hapyy/rust-fv/.planning/phases/30-set-discriminant-vcgen/30-CONTEXT.md` — Locked decisions on VC form, test breadth, edge cases

---

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH — all components verified directly in source code
- Architecture patterns: HIGH — exact function signatures and call patterns read from vcgen.rs
- Pitfalls: HIGH — sourced from STATE.md decisions and direct test analysis
- IR state: HIGH — verified SetDiscriminant(Place, usize) exists at ir.rs:608

**Research date:** 2026-02-26
**Valid until:** 2026-03-28 (stable — internal codebase, no external dependencies changing)
