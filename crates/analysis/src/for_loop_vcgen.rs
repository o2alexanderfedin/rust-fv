//! For-loop VCGen: generates verification conditions for for-loop iterators.
//!
//! This is a stub implementation — all functions panic with `todo!()`.
//! Plan 29.1-02 implements the full logic.
//!
//! RED state: tests in vcgen_completeness29_1.rs import this module and call
//! `generate_for_loop_vcs`, which panics. Tests are RED (fail at runtime).

use crate::ghost_predicate_db::GhostPredicateDatabase;
use crate::ir::Function;
use crate::vcgen::VerificationCondition;

/// Generate verification conditions for all for-loops in a function.
///
/// Returns one or more VCs per classified loop:
/// - `Range`/`RangeInclusive`: quantified AUFLIA VC + bounded QF_LIA VC
/// - `SliceIter`/`VecIter`: VC asserting loop var stays within `{collection}_len`
/// - `Enumerate`: VC declaring both `index_` and `elem_` SMT constants
/// - `Unknown`: single conservative `BoolLit(true)` VC
///
/// # Panics
///
/// This stub always panics with `todo!()`. Implemented in Plan 29.1-02.
pub fn generate_for_loop_vcs(
    _func: &Function,
    _ghost_pred_db: &GhostPredicateDatabase,
) -> Vec<VerificationCondition> {
    todo!("for_loop_vcgen::generate_for_loop_vcs is not yet implemented (Plan 29.1-02)")
}
