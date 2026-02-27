---
phase: 20-separation-logic
verified: 2026-02-19T00:00:00Z
status: passed
score: 7/7 must-haves verified
re_verification: false
---

# Phase 20: Separation Logic Verification Report

**Phase Goal:** Developers can prove aliasing freedom and heap ownership properties for raw pointer code using separation logic predicates
**Verified:** 2026-02-19
**Status:** passed
**Re-verification:** No — initial verification

## Goal Achievement

### Observable Truths

| #  | Truth                                                                                              | Status     | Evidence                                                                                     |
|----|-----------------------------------------------------------------------------------------------------|------------|----------------------------------------------------------------------------------------------|
| 1  | Developer writes pts_to(p, v) in #[requires]/#[ensures] and the spec parser produces a well-typed SMT term | VERIFIED | `parse_spec_expr("pts_to(p, v)", &func)` returns `Some(Term::And([Select(perm,p), Eq(...)]))` — test `test_pts_to_parse_basic` passes |
| 2  | pts_to(p, v) emits And([Select(perm,p), Eq(heapval_as_bvN(Select(sep_heap,p)), v)]) to Z3         | VERIFIED   | `encode_pts_to()` in `sep_logic.rs` produces exactly this structure; `test_encode_pts_to_structure` passes; Z3 returns `sat` in `sep_01_pts_to_ownership` |
| 3  | sep_heap and perm arrays are declared in any VC script that contains pts_to                         | VERIFIED   | `has_sep_logic_spec()` in `vcgen.rs` detects pts_to; `insert_sep_heap_decls()` prepends declarations; `test_sep_logic_call_site_vc_uses_aufbv` confirms `sep_heap` in script |
| 4  | H1 * H2 where both sides are pts_to() calls is encoded as separating conjunction, not BvMul         | VERIFIED   | `is_sep_logic_formula()` + Mul branch in `spec_parser.rs` routes to `Term::And`; `test_sep_conj_pts_to_star_pts_to` and `sep_02_separating_conjunction` pass |
| 5  | A function with pts_to in requires gets a frame axiom asserting sep_heap unchanged outside footprint | VERIFIED   | `build_frame_axiom()` in `sep_logic.rs` + vcgen.rs call-site emission; `sep_03_frame_rule` confirms `forall` in script and Z3 returns `unsat` for negation |
| 6  | VCs containing sep-logic terms use AUFBV or QF_AUFBV logic (not QF_BV)                             | VERIFIED   | `sep_logic_smt_logic()` returns `AUFBV`/`QF_AUFBV`; `replace_set_logic()` used in vcgen.rs; call-site VCs confirmed to contain `AUFBV` |
| 7  | Developer writes linked_list(p, n) in a spec and the verifier inlines the body to depth 3           | VERIFIED   | `parse_spec_expr_with_db()` + ghost predicate expansion in `convert_call`; `sep_04_ghost_predicate_unfold` passes: depth-3 expansion works, recursive pred returns `BoolLit(false)` at depth 0 |

**Score:** 7/7 truths verified

### Required Artifacts

| Artifact                                              | Expected                                               | Status     | Details                                                              |
|-------------------------------------------------------|--------------------------------------------------------|------------|----------------------------------------------------------------------|
| `crates/analysis/src/sep_logic.rs`                    | 5 public functions: declare_sep_heap, declare_heapval_accessor, encode_pts_to, sep_logic_smt_logic, extract_pts_to_footprint, build_frame_axiom | VERIFIED   | All 6 functions present and substantive (315 lines); 5 unit tests pass |
| `crates/analysis/src/spec_parser.rs`                  | pts_to recognized in convert_call; sep-conj detection; ghost pred expansion; parse_spec_expr_with_db | VERIFIED   | pts_to arm at line 678; is_sep_logic_formula at line 237; ghost pred expansion at line 737; parse_spec_expr_with_db at line 46 |
| `crates/analysis/src/lib.rs`                          | pub mod sep_logic and pub mod ghost_predicate_db declared | VERIFIED   | Line 22: `pub mod sep_logic`; line 15: `pub mod ghost_predicate_db` |
| `crates/macros/src/lib.rs`                            | #[ghost_predicate] proc-macro attribute                | VERIFIED   | `pub fn ghost_predicate` at line 247; ghost_predicate_impl at line ~506; 2 tests pass |
| `crates/analysis/src/ghost_predicate_db.rs`           | GhostPredicateDatabase with insert/get/contains        | VERIFIED   | Full struct with all methods; 3 unit tests pass |
| `crates/driver/src/callbacks.rs`                      | ghost_pred_db field on AnalysisCallbacks; extraction from doc attrs | VERIFIED   | Field at line 140; extraction function at line 833; insert at line 854 |
| `crates/analysis/src/vcgen.rs`                        | Frame axiom emission; AUFBV logic selection; sep_heap declarations | VERIFIED   | has_sep_logic_spec at line 1910; build_frame_axiom call at line 2062; sep_logic_smt_logic at line 2066 |
| `crates/analysis/tests/sep_logic_integration.rs`      | 4 E2E integration tests for all SEP requirements       | VERIFIED   | All 4 tests (sep_01_pts_to_ownership, sep_02_separating_conjunction, sep_03_frame_rule, sep_04_ghost_predicate_unfold) pass |

### Key Link Verification

| From                          | To                              | Via                                           | Status  | Details                                                                           |
|-------------------------------|---------------------------------|-----------------------------------------------|---------|-----------------------------------------------------------------------------------|
| `spec_parser.rs`              | `sep_logic.rs`                  | `sep_logic::encode_pts_to()` in pts_to arm    | WIRED   | Line 701: `return Some(sep_logic::encode_pts_to(ptr_term, val_term, pointee_bits))` |
| `sep_logic.rs`                | `rust_fv_smtlib`                | `Sort::Array`, `Sort::Uninterpreted`, `Term::*` | WIRED | Uses Sort::Array, Sort::BitVec, Sort::Uninterpreted; imports at top of file       |
| `macros/src/lib.rs`           | `driver/src/callbacks.rs`       | doc format `rust_fv::ghost_predicate::name::params::body` | WIRED | Macro emits format at line 535; callbacks.rs strips prefix at line 842            |
| `callbacks.rs`                | `ghost_predicate_db.rs`         | `GhostPredicateDatabase::insert()` call        | WIRED   | Line 854: `ghost_predicate_db.insert(...)` in extract_ghost_predicates()          |
| `callbacks.rs`                | `vcgen.rs`                      | `ghost_pred_db` field on AnalysisCallbacks     | WIRED   | Field `pub ghost_pred_db: GhostPredicateDatabase` at line 140; populated at line 401 |
| `spec_parser.rs`              | `sep_logic.rs`                  | `sep_logic::extract_pts_to_footprint()`        | WIRED   | Called from vcgen.rs at line 2053 after spec parsing                             |
| `vcgen.rs`                    | `sep_logic.rs`                  | `sep_logic::build_frame_axiom()` and `sep_logic_smt_logic()` | WIRED | Lines 2062 and 2066; `use crate::sep_logic` at line 48                           |
| `tests/sep_logic_integration.rs` | `rust_fv_analysis::vcgen`   | `vcgen::generate_vcs()` call                   | WIRED   | Line 251: `vcgen::generate_vcs(&func, None)`; line 392: with ContractDatabase    |
| `tests/sep_logic_integration.rs` | `rust_fv_smtlib`            | `Script::render` / `solver.check_sat_raw()`    | WIRED   | Z3 calls confirmed working — all 4 E2E tests pass against live Z3                |

### Requirements Coverage

| Requirement | Source Plan | Description                                                                  | Status    | Evidence                                                                          |
|-------------|------------|------------------------------------------------------------------------------|-----------|-----------------------------------------------------------------------------------|
| SEP-01      | 20-01, 20-04 | User can write `pts_to(p, v)` ownership predicate in `#[requires]`/`#[ensures]` | SATISFIED | encode_pts_to() + spec_parser pts_to arm + sep_01_pts_to_ownership integration test passes |
| SEP-02      | 20-03, 20-04 | User can write separating conjunction (H1 * H2) in specs to prove disjoint ownership | SATISFIED | is_sep_logic_formula() + Mul→And routing + sep_02_separating_conjunction passes |
| SEP-03      | 20-03, 20-04 | Frame rule automatically applied during function calls                        | SATISFIED | build_frame_axiom() + vcgen.rs call-site emission + sep_03_frame_rule: Z3 returns UNSAT for negation |
| SEP-04      | 20-02, 20-03, 20-04 | User can define recursive heap predicates via #[ghost_predicate] with depth-3 unfolding | SATISFIED | ghost_predicate proc-macro + GhostPredicateDatabase + ghost pred expansion + sep_04_ghost_predicate_unfold passes |

All four requirements are marked `[x] Complete` in REQUIREMENTS.md. No orphaned requirements found — REQUIREMENTS.md maps exactly SEP-01 through SEP-04 to Phase 20.

### Anti-Patterns Found

None. Scanned `sep_logic.rs`, `ghost_predicate_db.rs`, and `sep_logic_integration.rs` — no TODOs, FIXMEs, placeholders, empty implementations, or console-only handlers found.

### Human Verification Required

None. All checks are programmatically verifiable via the existing test suite. The Z3 integration tests (sep_01 through sep_04) provide live SMT solver confirmation.

### Test Results Summary

```
test ghost_predicate_db::tests::test_empty_db             ... ok
test ghost_predicate_db::tests::test_insert_and_get       ... ok
test ghost_predicate_db::tests::test_multiple_predicates  ... ok
test sep_logic::tests::test_build_frame_axiom_empty_footprint ... ok
test sep_logic::tests::test_build_frame_axiom_multiple_ptrs   ... ok
test sep_logic::tests::test_build_frame_axiom_single_ptr      ... ok
test sep_logic::tests::test_encode_pts_to_structure           ... ok
test sep_logic::tests::test_declare_sep_heap_commands         ... ok
test sep_logic::tests::test_sep_logic_smt_logic               ... ok
test spec_parser::tests::test_ghost_predicate_depth_zero      ... ok
test spec_parser::tests::test_mul_not_sep_conj                ... ok
test spec_parser::tests::test_pts_to_parse_basic              ... ok
test spec_parser::tests::test_pts_to_wrong_arity              ... ok
test spec_parser::tests::test_sep_conj_pts_to_star_pts_to     ... ok
test vcgen::tests::test_sep_logic_call_site_vc_uses_aufbv     ... ok
test sep_01_pts_to_ownership                                  ... ok
test sep_02_separating_conjunction                            ... ok
test sep_03_frame_rule                                        ... ok
test sep_04_ghost_predicate_unfold                            ... ok

Overall: 1149+ tests pass, 0 failed
```

### Gaps Summary

No gaps. All 7 observable truths verified, all 8 artifacts confirmed substantive and wired, all 9 key links confirmed active, all 4 requirements satisfied by passing integration tests against live Z3.

---

_Verified: 2026-02-19_
_Verifier: Claude (gsd-verifier)_
