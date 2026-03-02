---
status: resolved
trigger: "term-app-declare-fun-z3-encoding"
created: 2026-03-02T00:00:00Z
updated: 2026-03-02T00:01:00Z
---

## Current Focus

hypothesis: encode_precondition_weakening_vc and encode_postcondition_strengthening_vc use Term::App to reference uninterpreted predicate functions (e.g., trait_requires_push, trait_ensures_push) without emitting DeclareFun commands for them first, so Z3 rejects the script with an undefined-symbol parse error.
test: Read the code in behavioral_subtyping.rs, verify Term::App usage without DeclareFun, then add DeclareFun for each uninterpreted predicate before the Assert.
expecting: After adding DeclareFun(name, param_sorts, Bool) for each Term::App predicate, the generated SMT-LIB2 will be accepted by Z3 and return UNSAT for the trivially-valid VCs.
next_action: implement fix in behavioral_subtyping.rs

## Symptoms

expected: Z3 receives a well-formed SMT-LIB2 script with all uninterpreted functions declared via (declare-fun ...) before use, yielding UNSAT (contract satisfied) or SAT (violation found).
actual: Z3 rejects the script with a parse error about undefined symbols. The test catches the error and logs "known encoding limitation" — real verification is skipped.
errors: Z3 parse error — function applied before being declared with declare-fun. Seen in crates/analysis/tests/trait_verification.rs around lines 697-715, match arm Err(e).
reproduction: Run the E2E test e2e_behavioral_subtyping_pipeline_correct_impl in crates/analysis/tests/trait_verification.rs. The Err(e) branch will be hit.
started: Introduced in Phase 38.

## Eliminated

(none yet)

## Evidence

- timestamp: 2026-03-02T00:00:00Z
  checked: crates/analysis/src/behavioral_subtyping.rs lines 98-179 (encode_precondition_weakening_vc)
  found: Uses Term::App("trait_requires_{name}", params) without a corresponding Command::DeclareFun. Only Command::DeclareConst for parameters is emitted.
  implication: Z3 sees (trait_requires_push self) but no (declare-fun trait_requires_push (Bool) Bool) — parse error is guaranteed.

- timestamp: 2026-03-02T00:00:00Z
  checked: crates/analysis/src/behavioral_subtyping.rs lines 190-265 (encode_postcondition_strengthening_vc)
  found: Same pattern: Term::App("trait_ensures_{name}", params+result) without DeclareFun.
  implication: Same Z3 parse error for postcondition scripts.

- timestamp: 2026-03-02T00:00:00Z
  checked: crates/smtlib/src/command.rs
  found: Command::DeclareFun(String, Vec<Sort>, Sort) exists — (name, param_sorts, return_sort)
  implication: Fix is straightforward: emit DeclareFun before each Term::App predicate.

- timestamp: 2026-03-02T00:00:00Z
  checked: crates/analysis/src/encode_sort.rs (encode_type)
  found: Ty::Unit encodes to Sort::Bool. Parameters in test use Ty::Unit for "self".
  implication: DeclareFun param sorts can be derived via encode_type on each param.

## Resolution

root_cause: encode_precondition_weakening_vc and encode_postcondition_strengthening_vc emit Term::App for symbolic predicate functions (e.g., trait_requires_push, trait_ensures_push) without preceding Command::DeclareFun declarations. SMT-LIB2 requires every function symbol to be declared before use.
fix: Added Command::DeclareFun(pred_name, param_sorts, Sort::Bool) immediately before each Term::App usage in both encode_precondition_weakening_vc and encode_postcondition_strengthening_vc. For postcondition predicates, the sort list includes both param sorts and return sort. Removed the Err(e) workaround from the test — it now panics on Z3 parse errors, enforcing correctness.
verification: All 13 trait_verification integration tests pass. All 12 behavioral_subtyping unit tests pass. No clippy warnings.
files_changed:
  - crates/analysis/src/behavioral_subtyping.rs
  - crates/analysis/tests/trait_verification.rs
