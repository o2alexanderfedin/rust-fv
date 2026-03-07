---
phase: 51-core-language-features-i
plan: 01
subsystem: analysis
tags: [const-generics, smt-encoding, ir, monomorphization, spec-parser, vcgen]

# Dependency graph
requires:
  - phase: 50-stdlib-ptr-mem-unsafe-boundary
    provides: MaybeUninit ghost state pattern, Function struct with ghost state fields
provides:
  - Ty::ConstGeneric(String, Box<Ty>) IR variant for const generic parameters
  - Ty::Union(String, Vec<(String, Ty)>) IR variant for union types
  - VcKind::UnionAccess, VcKind::DropOrder, VcKind::PinSafety verification condition kinds
  - GenericParam.is_const and const_ty fields for const generic detection
  - UnionGhostState, PinGhostState, DropLocalInfo structs on Function
  - SMT sort encoding for ConstGeneric (Int/Bool) and Union (BitVec) types
  - MIR extraction of GenericParamDefKind::Const from rustc
  - Monomorphization substitution for Ty::ConstGeneric and Ty::Union
  - Spec parser resolution of const generic names in requires/ensures expressions
  - VCGen declare-const emission for const generic parameters
affects: [51-02-union-field-tracking, 51-03-drop-pin-verification, 52-advanced-type-system]

# Tech tracking
tech-stack:
  added: []
  patterns: [const-generic-smt-encoding, ghost-state-struct-fields, int-mode-spec-parsing]

key-files:
  created:
    - crates/analysis/tests/const_generic_tests.rs
  modified:
    - crates/analysis/src/ir.rs
    - crates/analysis/src/vcgen.rs
    - crates/analysis/src/encode_sort.rs
    - crates/analysis/src/monomorphize.rs
    - crates/analysis/src/spec_parser.rs
    - crates/driver/src/mir_converter.rs
    - crates/driver/src/diagnostics.rs
    - crates/driver/src/callbacks.rs
    - crates/driver/src/cex_render.rs

key-decisions:
  - "Const generics declared as Sort::Int in SMT regardless of underlying integer type for unbounded symbolic reasoning"
  - "Removed Hash derive from GenericParam since Ty does not implement Hash and no code uses GenericParam as hash key"
  - "Auto-enable int_mode in spec parser when function has const generic params to avoid BV/Int sort mismatch"
  - "Union types encoded as BitVec of max field size in bits for overlapping storage semantics"

patterns-established:
  - "Const generic SMT encoding: declare-const N Int in VCGen preamble for each is_const generic param"
  - "Int mode auto-detection: spec parser switches to Int operators when const generics present"

requirements-completed: [LANG-01]

# Metrics
duration: 43min
completed: 2026-03-07
---

# Phase 51 Plan 01: Const Generic Parameter Verification Summary

**Full const generic pipeline: MIR extraction of GenericParamDefKind::Const through IR Ty::ConstGeneric to SMT declare-const with spec parser resolution and monomorphization substitution**

## Performance

- **Duration:** 43 min
- **Started:** 2026-03-07T03:20:56Z
- **Completed:** 2026-03-07T04:04:13Z
- **Tasks:** 2
- **Files modified:** 81

## Accomplishments
- Const generic parameters (`const N: usize`) are extracted from MIR, represented as `Ty::ConstGeneric` in IR, encoded as `Sort::Int` in SMT, and declared as `declare-const N Int` in VCGen preamble
- Spec expressions like `#[requires(N > 0)]` resolve const generic names as SMT integer constants with auto int-mode detection
- Monomorphization substitutes `Ty::ConstGeneric("N", _)` with concrete types at call sites
- IR foundations for Plans 02 and 03: `Ty::Union`, `VcKind::UnionAccess/DropOrder/PinSafety`, `UnionGhostState`, `PinGhostState`, `DropLocalInfo` structs
- 19 new integration tests covering all const generic functionality end-to-end
- All 1273 lib tests + 259 driver tests + 19 new tests passing, clippy clean on both crates

## Task Commits

Each task was committed atomically:

1. **Task 1: IR type extensions + const generic MIR extraction** - `17e05c2` (feat)
2. **Task 2: Const generic monomorphization + spec parser + VCGen wiring** - `4559a5e` (feat)

## Files Created/Modified
- `crates/analysis/tests/const_generic_tests.rs` - 19 integration tests for const generic verification pipeline
- `crates/analysis/src/ir.rs` - Added Ty::ConstGeneric, Ty::Union, GenericParam.is_const/const_ty, UnionGhostState, PinGhostState, DropLocalInfo
- `crates/analysis/src/vcgen.rs` - VcKind::UnionAccess/DropOrder/PinSafety, declare-const emission for const generics
- `crates/analysis/src/encode_sort.rs` - Sort encoding for ConstGeneric (Int/Bool) and Union (BitVec)
- `crates/analysis/src/monomorphize.rs` - Ty::ConstGeneric and Ty::Union substitution in substitute_ty
- `crates/analysis/src/spec_parser.rs` - Const generic name resolution in resolve_variable_name, auto int_mode
- `crates/driver/src/mir_converter.rs` - GenericParamDefKind::Const extraction in convert_generic_params
- `crates/driver/src/diagnostics.rs` - V130/V140/V150 diagnostic codes and severity for new VcKind variants
- `crates/driver/src/callbacks.rs` - vc_kind_to_string mappings for union_access/drop_order/pin_safety
- `crates/driver/src/cex_render.rs` - ty_name_string for ConstGeneric and Union variants
- 71 additional files updated with new Function struct fields (union_ghost_states, pin_ghost_states, drop_locals)

## Decisions Made
- **Const generics as Sort::Int:** All integer const generics use `Sort::Int` (unbounded) rather than fixed-width bitvectors, enabling symbolic reasoning without overflow concerns
- **Removed Hash from GenericParam:** Adding `const_ty: Option<Ty>` broke Hash derive since Ty doesn't implement Hash; no code uses GenericParam as hash key
- **Auto int-mode in spec parser:** When a function has const generic params, spec parser auto-enables `in_int_mode` to produce `IntGt`/`IntLt` instead of `BvSgt`/`BvSlt` for correct sort matching
- **Union as BitVec:** Union types encoded as `BitVec(max_field_bits)` matching their overlapping storage semantics

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] GenericParam Hash derive removed**
- **Found during:** Task 1 (IR type extensions)
- **Issue:** GenericParam derived Hash but Ty does not implement Hash; adding const_ty: Option<Ty> broke compilation
- **Fix:** Removed Hash from GenericParam's derive list
- **Files modified:** crates/analysis/src/ir.rs
- **Verification:** cargo build succeeds, no code uses GenericParam as hash key
- **Committed in:** 17e05c2

**2. [Rule 1 - Bug] Sort mismatch for const generic spec expressions**
- **Found during:** Task 2 (spec parser + VCGen wiring)
- **Issue:** Const generics declared as Int in SMT but spec parser defaulted to BV mode, producing BvSgt instead of IntGt for N > 0 comparisons
- **Fix:** Auto-enable in_int_mode in parse_spec_expr_with_depth when function has const generic params
- **Files modified:** crates/analysis/src/spec_parser.rs
- **Verification:** Tests pass with correct Int sort operations in SMT output
- **Committed in:** 4559a5e

**3. [Rule 1 - Bug] Tests used wrong SpecExpr constructor**
- **Found during:** Task 2 (test writing)
- **Issue:** Tests used SpecExpr::Expr("N > 0") but SpecExpr is a struct with raw field, not an enum
- **Fix:** Changed to SpecExpr { raw: "N > 0".to_string() }
- **Files modified:** crates/analysis/tests/const_generic_tests.rs
- **Verification:** Tests compile and pass
- **Committed in:** 4559a5e

**4. [Rule 1 - Bug] VCGen requires ensures clause to generate postcondition VCs**
- **Found during:** Task 2 (VCGen wiring tests)
- **Issue:** Tests expected VCs from #[requires(N > 0)] alone, but requires clauses are assumptions, not provable VCs
- **Fix:** Added ensures clauses to test functions to trigger postcondition VC generation
- **Files modified:** crates/analysis/tests/const_generic_tests.rs
- **Verification:** VCs generated with N references in SMT script
- **Committed in:** 4559a5e

---

**Total deviations:** 4 auto-fixed (4 bugs via Rule 1)
**Impact on plan:** All fixes necessary for correctness. No scope creep.

## Issues Encountered
- Updating 78+ files with new Function struct fields required sed scripting + Python scripting + manual fixes for edge cases (files using variable names instead of vec![] literals, doc comments containing struct syntax)
- Pre-commit hooks required multiple rounds of rustfmt and clippy fixes before successful commits

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- IR foundations complete for Plans 02 (union field tracking) and 03 (drop/pin verification)
- Ty::Union, UnionGhostState, VcKind::UnionAccess ready for Plan 02
- PinGhostState, DropLocalInfo, VcKind::DropOrder/PinSafety ready for Plan 03
- All 81 files updated with new Function fields, no further structural changes needed

## Self-Check: PASSED

- All 7 key source files: FOUND
- Commit 17e05c2 (Task 1): FOUND
- Commit 4559a5e (Task 2): FOUND
- SUMMARY.md: FOUND

---
*Phase: 51-core-language-features-i*
*Completed: 2026-03-07*
