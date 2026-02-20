---
phase: 20-separation-logic
plan: 03
subsystem: formal-verification
tags: [separation-logic, smt, spec-parser, vcgen, frame-rule, ghost-predicates]

# Dependency graph
requires:
  - phase: 20-01
    provides: sep_logic.rs with declare_sep_heap, encode_pts_to, extract_pts_to_footprint
  - phase: 20-02
    provides: GhostPredicateDatabase, ghost_predicate proc-macro, callbacks.rs extraction

provides:
  - "build_frame_axiom() with :pattern trigger annotation for E-matching efficiency"
  - "is_sep_logic_formula() syntactic detection of pts_to/ghost-pred calls"
  - "parse_spec_expr_with_db() public API for ghost predicate expansion"
  - "Separating conjunction H1 * H2 encoded as Term::And (not BvMul)"
  - "Ghost predicate bounded inlining to depth 3 with BoolLit(false) at depth 0"
  - "Frame axiom emission at call sites with pts_to in callee contracts"
  - "SMT logic upgrade: QF_BV -> AUFBV (call-site with frame forall) / QF_AUFBV (postcond)"
  - "sep_heap declarations prepended to VCs with sep-logic contracts"

affects:
  - phase-20-04
  - future sep-logic SMT solving
  - vcgen call-site verification

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "Syntactic sep-conj detection before expression conversion (check raw Expr not converted Term)"
    - "Ghost predicate expansion: bounded depth, depth=0 => BoolLit(false) conservative"
    - "Frame axiom with :pattern E-matching trigger to prevent quantifier looping"
    - "SMT logic upgrade via replace_script_logic() post-construction"
    - "sep_heap_pre snapshot declared at call site for frame rule pre/post comparison"

key-files:
  created: []
  modified:
    - crates/analysis/src/sep_logic.rs
    - crates/analysis/src/spec_parser.rs
    - crates/analysis/src/vcgen.rs

key-decisions:
  - "Syntactic sep-conj detection: check Expr::Binary with Mul before converting operands, not after"
  - "convert_expr_with_db() as the core internal entry point; convert_expr_with_bounds() delegates to it with empty DB for backward compat"
  - "replace_whole_word() helper for ghost pred param substitution (not regex, simple byte scan)"
  - "Frame axiom uses :pattern ((select sep_heap _sep_frame_addr)) trigger to guide Z3 E-matching"
  - "has_sep_logic_spec() is a cheap syntactic substring check (pts_to() in raw string)"
  - "prepend_sep_heap_decls() inserts declarations after SetLogic command (first command in script)"
  - "Frame forall at call sites -> AUFBV; postcondition VCs -> QF_AUFBV (no frame forall)"

patterns-established:
  - "Ghost predicate expansion: thread ghost_pred_db + depth through convert_expr_with_db chain"
  - "Backward compat: new public functions (parse_spec_expr_with_db) alongside unchanged parse_spec_expr"
  - "Sep-logic upgrade in vcgen: detect -> prepend decls -> snapshot -> emit frame -> upgrade logic"

requirements-completed: [SEP-02, SEP-03, SEP-04]

# Metrics
duration: 15min
completed: 2026-02-20
---

# Phase 20 Plan 03: Sep-conj, Ghost Predicates, Frame Rule Summary

**Separating conjunction via `H1 * H2` syntactic detection, ghost predicate bounded inlining to depth 3, frame axiom emission with E-matching trigger, and AUFBV/QF_AUFBV logic selection in vcgen call-site VCs**

## Performance

- **Duration:** ~15 min
- **Started:** 2026-02-20T03:51:26Z
- **Completed:** 2026-02-20T04:06:00Z
- **Tasks:** 2
- **Files modified:** 3

## Accomplishments
- sep_logic.rs: `build_frame_axiom()` emits universally-quantified heap-frame invariant with `:pattern` E-matching trigger to prevent quantifier looping in Z3
- spec_parser.rs: `pts_to(p,v) * pts_to(q,w)` now produces `Term::And([pts_to_enc, pts_to_enc])` not `BvMul`; ghost predicate calls expand to body at depth 1-3, return `BoolLit(false)` at depth 0
- vcgen.rs: call-site VCs for callees with `pts_to` in `requires` now include sep_heap declarations, sep_heap_pre snapshot, frame axiom, and use AUFBV logic; postcondition VCs with sep-logic contracts use QF_AUFBV

## Task Commits

1. **Task 1: Sep-conj detection, ghost pred expansion, build_frame_axiom** - `f06ba8a` (feat)
2. **Task 2: Frame rule emission + AUFBV logic selection in vcgen.rs** - `1f2d07f` (feat)

## Files Created/Modified
- `crates/analysis/src/sep_logic.rs` - Added `build_frame_axiom()` with trigger annotation; 3 new tests
- `crates/analysis/src/spec_parser.rs` - Added `parse_spec_expr_with_db()`, `is_sep_logic_formula()`, `convert_expr_with_db()`, `convert_call_with_db()`, `replace_whole_word()`; 3 new tests for sep-conj, mul-not-sep, ghost-depth-zero
- `crates/analysis/src/vcgen.rs` - Added `has_sep_logic_spec()`, `prepend_sep_heap_decls()`, frame axiom emission, AUFBV logic selection; 1 new test

## Decisions Made
- Syntactic sep-conj detection at `Expr::Binary` level before operand conversion: the `is_sep_logic_formula()` check must happen on the raw `syn::Expr` (not after Term conversion) to correctly intercept `*` between heap predicates
- `convert_expr_with_bounds()` kept unchanged as a backward-compatible wrapper delegating to `convert_expr_with_db()` with an empty DB — preserves all 1148+ existing call sites
- `replace_whole_word()` implemented as a simple byte-scan rather than regex (no additional deps, sufficient for Phase 20 ghost predicate parameter substitution with simple variable args)
- Frame axiom trigger `:pattern ((select sep_heap _sep_frame_addr))` — reuses the post-call heap select term as the pattern so Z3 only instantiates the forall when reasoning about a specific heap address

## Deviations from Plan

None - plan executed exactly as written. The only structural choice was placing `convert_expr_with_db` as a new private function rather than modifying the existing `convert_expr_with_bounds` signature, which better preserves backward compatibility.

## Issues Encountered
- `syn::Expr` does not implement `Debug`, so `format!("{expr:?}")` failed for `expr_to_arg_str()`. Fixed by using a pattern-match based approach returning identifier names for path exprs and literal strings for int/bool literals, returning empty string for complex expressions.
- `convert_expr` became dead code after all callers were updated to use `parse_spec_expr_with_depth` directly. Removed to fix clippy `-D dead-code` error.

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- All SEP-02, SEP-03, SEP-04 requirements satisfied
- Phase 20 Plan 04 (integration tests + end-to-end sep-logic verification) can proceed
- The sep-logic pipeline is now complete: pts_to encoding (Plan 01) → ghost predicates (Plan 02) → sep-conj + frame rule + ghost expansion (Plan 03) → integration (Plan 04)

---
*Phase: 20-separation-logic*
*Completed: 2026-02-20*
