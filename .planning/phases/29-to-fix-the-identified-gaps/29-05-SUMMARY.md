---
phase: 29-to-fix-the-identified-gaps
plan: "05"
subsystem: vcgen
tags: [smt, vcgen, functional-update, struct-mutation, downcast, projection]

requires:
  - phase: 29-02
    provides: fp.to_sbv/fp.to_ubv float-to-int SMT encoding (VCGEN-05)
  - phase: 29-03
    provides: AggregateKind::Adt MIR converter + SetDiscriminant/Assume IR variants
  - phase: 29-04
    provides: TyKind::Param->Generic fix + Rvalue::Repeat IR variant + CopyForDeref/RawPtr/Repeat arms
provides:
  - "encode_assignment: projected LHS struct field mutation produces mk-StructName functional update"
  - "encode_rvalue_for_assignment: Use/BinaryOp/UnaryOp rvalues supported as functional update RHS"
  - "encode_place_with_type: Projection::Downcast narrows type to variant's fields using Cow<Ty>"
  - "VCGEN-06 requirement satisfied"
affects:
  - phase-30-and-beyond
  - any future work on MIR-to-SMT encoding

tech-stack:
  added: []
  patterns:
    - "Functional record update: (= s (mk-Name new_f0 (Name-f1 s) ...)) for struct field mutation"
    - "Cow<Ty> for mixed borrowed/owned type in projection traversal loop"
    - "let-chain syntax for collapsible-if cleanup in nested projection matching"

key-files:
  created: []
  modified:
    - crates/analysis/src/vcgen.rs
    - crates/analysis/src/encode_term.rs

key-decisions:
  - "Functional update uses mk-StructName with ALL fields in arity order — changed field gets new_val, others get selector(base)"
  - "Cow<Ty> used in encode_place_with_type so Downcast can produce an owned variant-struct Ty alongside borrowed Tys from find_local_type"
  - "encode_rvalue_for_assignment is a term-returning helper (not Command) reusing encode_binop/encode_unop for non-Use rvalues"

patterns-established:
  - "Struct mutation pattern: single Projection::Field + Ty::Struct -> mk-constructor functional update"
  - "Downcast type narrowing: Ty::Enum + variant_idx -> ad-hoc Ty::Struct for variant's fields"

requirements-completed: [VCGEN-06]

duration: 4min
completed: 2026-02-24
---

# Phase 29 Plan 05: Functional Record Update for Struct Field Mutation (VCGEN-06) Summary

**Projected LHS struct field mutation (`s.field = expr`) now produces SMT functional update `(= s (mk-Point new_x (Point-y s)))` via encode_assignment, with Downcast type narrowing in encode_place_with_type using `Cow<Ty>`**

## Performance

- **Duration:** 4 min
- **Started:** 2026-02-24T~06:52Z
- **Completed:** 2026-02-24T~06:56Z
- **Tasks:** 1
- **Files modified:** 2

## Accomplishments
- `encode_assignment` detects single-level `Projection::Field` on struct base and emits `mk-StructName` functional update with correct arity (all fields)
- `encode_rvalue_for_assignment` helper returns a `Term` (not `Command`) for `Use`/`BinaryOp`/`UnaryOp` rvalues as the new field value
- `encode_place_with_type` changed `current_ty` from `&Ty` to `Cow<'_, Ty>` so `Projection::Downcast` can synthesize an owned variant-struct type without lifetime conflicts
- All 9 active Phase 29 tests GREEN, all 10 Phase 28 tests GREEN, full suite clean

## Task Commits

1. **Task 1: Functional record update + Downcast type narrowing** - `77aba84` (fix)

## Files Created/Modified
- `crates/analysis/src/vcgen.rs` - encode_assignment projected LHS + encode_rvalue_for_assignment helper
- `crates/analysis/src/encode_term.rs` - encode_place_with_type Downcast narrowing using Cow<Ty>

## Decisions Made
- `Cow<Ty>` chosen over cloning the full current type at each projection step — only the Downcast arm pays the allocation cost; Field/Index/Deref remain zero-copy borrows
- Functional update always emits ALL fields using `fields.iter().enumerate()` — correct SMT constructor arity guaranteed by construction
- `encode_rvalue_for_assignment` returns `Option<Term>` with `?` propagation so the outer `encode_assignment` can short-circuit cleanly when a rvalue type is not yet supported

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Fixed Cow<Ty> type mismatch in encode_place_with_type**
- **Found during:** Task 1 (compile step)
- **Issue:** Plan's Downcast code assigned owned `Ty` to `&Ty` variable — E0308 mismatched types
- **Fix:** Changed `current_ty: &Ty` to `Cow<'_, Ty>`, updated all arms to use `Cow::Borrowed`/`Cow::Owned` and `.as_ref()` for derefs
- **Files modified:** crates/analysis/src/encode_term.rs
- **Verification:** cargo build clean, tests GREEN
- **Committed in:** 77aba84 (task commit)

**2. [Rule 1 - Bug] Fixed collapsible-if clippy lints**
- **Found during:** Task 1 (clippy step)
- **Issue:** Nested `if let` blocks in both vcgen.rs and encode_term.rs triggered `-D clippy::collapsible-if`
- **Fix:** Collapsed to let-chain syntax (`if cond && let Pat = expr`)
- **Files modified:** crates/analysis/src/vcgen.rs, crates/analysis/src/encode_term.rs
- **Verification:** clippy clean
- **Committed in:** 77aba84 (task commit)

---

**Total deviations:** 2 auto-fixed (2 bugs — compile error + clippy)
**Impact on plan:** Both fixes required for correctness and compliance. No scope creep.

## Issues Encountered
None beyond the auto-fixed compile error and clippy issues above.

## Next Phase Readiness
- All 4 Phase 29 requirements satisfied: MIRCONV-01, MIRCONV-02, VCGEN-05, VCGEN-06
- Phase 29 complete — ready for Phase 30 or any subsequent work
- `vcgen_06_set_discriminant_assertion` test remains `#[ignore]` (SetDiscriminant VCGen encoding deferred, annotated in test)

## Self-Check: PASSED

- FOUND: crates/analysis/src/vcgen.rs (contains `mk-` functional update)
- FOUND: crates/analysis/src/encode_term.rs (contains Downcast Cow<Ty> narrowing)
- FOUND: 77aba84 — fix(29-05): functional record update commit
- All Phase 28 tests: 10/10 GREEN
- All Phase 29 active tests: 9/9 GREEN (1 ignored)
- clippy clean, rustfmt clean, full build clean

---
*Phase: 29-to-fix-the-identified-gaps*
*Completed: 2026-02-24*
