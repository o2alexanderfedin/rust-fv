//! RC11 weak memory model SMT encoding.
//!
//! Implements mo (modification order), rf (reads-from), sw (synchronizes-with),
//! fr (from-read), and the four RC11 consistency axioms as bounded QF_LIA SMT
//! formulas. See Lahav et al. PLDI 2017.

use crate::ir::{AtomicOrdering, Function};
use rust_fv_smtlib::command::Command;
use rust_fv_smtlib::sort::Sort;
use rust_fv_smtlib::term::Term;

// ===== Modification Order (mo) declarations =====

/// Declare the modification order position for a store event.
///
/// `mo_order_N` is an integer giving the modification order position of store
/// event N. Stores to the same location are totally ordered by mo; smaller
/// integer = earlier in mo.
pub fn declare_mo_order(event_id: usize) -> Command {
    Command::DeclareFun(format!("mo_order_{event_id}"), vec![], Sort::Int)
}

// ===== Reads-From (rf) declarations =====

/// Declare the reads-from predicate between a load event and a store event.
///
/// `rf_L_S` = true means load event L reads the value written by store event S.
pub fn declare_rf(load_event: usize, store_event: usize) -> Command {
    Command::DeclareFun(format!("rf_{load_event}_{store_event}"), vec![], Sort::Bool)
}

// ===== Modification Order constraints =====

/// Assert that modification order positions are all distinct (strict total order).
///
/// For all pairs (i, j) of store events, asserts `mo_order_i != mo_order_j`,
/// ensuring that the mo relation is a strict total order (no ties).
pub fn assert_mo_total_order(store_events: &[usize]) -> Vec<Command> {
    let mut cmds = Vec::new();
    for i in 0..store_events.len() {
        for j in (i + 1)..store_events.len() {
            let si = store_events[i];
            let sj = store_events[j];
            let distinct = Term::Not(Box::new(Term::Eq(
                Box::new(Term::Const(format!("mo_order_{si}"))),
                Box::new(Term::Const(format!("mo_order_{sj}"))),
            )));
            cmds.push(Command::Assert(distinct));
        }
    }
    cmds
}

// ===== Reads-From constraints =====

/// Assert that the reads-from relation is functional for a load event.
///
/// At-least-one: the load reads from some store (including initial store).
/// At-most-one: the load reads from at most one store.
///
/// `store_events` must include the initial store event if relevant.
pub fn assert_rf_functional(load_event: usize, store_events: &[usize]) -> Vec<Command> {
    let mut cmds = Vec::new();

    if store_events.is_empty() {
        return cmds;
    }

    // At-least-one: load reads from some store
    let rf_terms: Vec<Term> = store_events
        .iter()
        .map(|&s| Term::Const(format!("rf_{load_event}_{s}")))
        .collect();
    let at_least_one = if rf_terms.len() == 1 {
        rf_terms[0].clone()
    } else {
        Term::Or(rf_terms)
    };
    cmds.push(Command::Assert(at_least_one));

    // At-most-one: for each pair (Si, Sj), not both rf_L_Si and rf_L_Sj
    for i in 0..store_events.len() {
        for j in (i + 1)..store_events.len() {
            let si = store_events[i];
            let sj = store_events[j];
            let at_most_one = Term::Not(Box::new(Term::And(vec![
                Term::Const(format!("rf_{load_event}_{si}")),
                Term::Const(format!("rf_{load_event}_{sj}")),
            ])));
            cmds.push(Command::Assert(at_most_one));
        }
    }

    cmds
}

// ===== Ordering predicates =====

/// Returns true if the ordering is a release (or stronger) ordering.
///
/// Under RC11: Release, AcqRel, and SeqCst are release orderings.
pub fn is_release(ordering: AtomicOrdering) -> bool {
    matches!(
        ordering,
        AtomicOrdering::Release | AtomicOrdering::AcqRel | AtomicOrdering::SeqCst
    )
}

/// Returns true if the ordering is an acquire (or stronger) ordering.
///
/// Under RC11: Acquire, AcqRel, and SeqCst are acquire orderings.
pub fn is_acquire(ordering: AtomicOrdering) -> bool {
    matches!(
        ordering,
        AtomicOrdering::Acquire | AtomicOrdering::AcqRel | AtomicOrdering::SeqCst
    )
}

// ===== Synchronizes-With (sw) encoding =====

/// Encode the synchronizes-with predicate for a release-store / acquire-load pair.
///
/// Returns a Term representing `sw(store_event, load_event)`:
/// - `false` if either the store is not a release or the load is not an acquire
/// - `rf_L_S` (the reads-from predicate) otherwise
///
/// Note: AcqRel passes both `is_release` and `is_acquire` — this is correct per RC11.
pub fn encode_sw(
    store_event: usize,
    store_ordering: AtomicOrdering,
    load_event: usize,
    load_ordering: AtomicOrdering,
) -> Term {
    if !is_release(store_ordering) || !is_acquire(load_ordering) {
        Term::BoolLit(false)
    } else {
        Term::Const(format!("rf_{load_event}_{store_event}"))
    }
}

// ===== From-Read (fr) encoding =====

/// Encode the from-read predicate `fr(load_event, store_s2)`.
///
/// `fr(L, S2)` = exists S1. `rf(L, S1)` AND `mo(S1) < mo(S2)`
///
/// This means: L reads from S1, but S2 is modification-ordered after S1,
/// so L "happens before" (in fr) S2 in the sense that L missed the later store.
///
/// Returns the disjunction over all S1 in `store_events` of the conjunction
/// `rf_L_S1 AND mo_order_S1 < mo_order_S2`.
pub fn encode_fr(load_event: usize, store_s2: usize, store_events: &[usize]) -> Term {
    if store_events.is_empty() {
        return Term::BoolLit(false);
    }

    let disjuncts: Vec<Term> = store_events
        .iter()
        .map(|&s1| {
            Term::And(vec![
                Term::Const(format!("rf_{load_event}_{s1}")),
                Term::IntLt(
                    Box::new(Term::Const(format!("mo_order_{s1}"))),
                    Box::new(Term::Const(format!("mo_order_{store_s2}"))),
                ),
            ])
        })
        .collect();

    if disjuncts.len() == 1 {
        disjuncts[0].clone()
    } else {
        Term::Or(disjuncts)
    }
}

// ===== Coherence check =====

/// Assert the RC11 COHERENCE axiom for a pair of events (i, j).
///
/// RC11 COHERENCE: NOT(hb(i, j) AND eco(j, i))
///
/// This asserts that the extended coherence order `eco` (which includes mo, rf,
/// fr, and their compositions) is irreflexive with respect to happens-before.
/// Specifically: if i happens-before j, then j cannot be eco-before i.
pub fn coherence_check(event_i: usize, event_j: usize, hb_i_j: Term, eco_j_i: Term) -> Command {
    let _ = (event_i, event_j); // event ids are encoded in the terms
    Command::Assert(Term::Not(Box::new(Term::And(vec![hb_i_j, eco_j_i]))))
}

// ===== Logic selection =====

/// SMT-LIB logic for weak memory VCs.
///
/// We use QF_LIA (Quantifier-Free Linear Integer Arithmetic) for modification
/// order reasoning. Integer positions avoid the bit-width concerns of QF_BV and
/// are supported by all major SMT solvers.
pub fn weak_memory_smt_logic() -> &'static str {
    "QF_LIA"
}

// ===== Gate function =====

/// Returns true if the function has at least one non-SeqCst atomic operation.
///
/// Functions with only SeqCst atomics are covered by the existing
/// DataRaceFreedom VcKind and do not need RC11 WeakMemory* VCs.
pub fn has_non_seqcst_atomics(func: &Function) -> bool {
    func.atomic_ops
        .iter()
        .any(|op| op.ordering != AtomicOrdering::SeqCst)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{AtomicOpKind, Contracts, Local, Place, Ty};

    fn make_empty_func() -> Function {
        Function {
            name: "test".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            loops: vec![],
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
        }
    }

    // ===== declare_mo_order tests =====

    #[test]
    fn test_declare_mo_order_returns_declare_fun() {
        let cmd = declare_mo_order(3);
        assert!(matches!(cmd, Command::DeclareFun(name, sorts, sort)
            if name == "mo_order_3" && sorts.is_empty() && sort == Sort::Int));
    }

    // ===== declare_rf tests =====

    #[test]
    fn test_declare_rf_returns_declare_fun_bool() {
        let cmd = declare_rf(2, 5);
        assert!(matches!(cmd, Command::DeclareFun(name, sorts, sort)
            if name == "rf_2_5" && sorts.is_empty() && sort == Sort::Bool));
    }

    // ===== assert_mo_total_order tests =====

    #[test]
    fn test_assert_mo_total_order_empty() {
        let cmds = assert_mo_total_order(&[]);
        assert!(cmds.is_empty());
    }

    #[test]
    fn test_assert_mo_total_order_one_event() {
        let cmds = assert_mo_total_order(&[0]);
        assert!(cmds.is_empty());
    }

    #[test]
    fn test_assert_mo_total_order_two_events() {
        let cmds = assert_mo_total_order(&[0, 1]);
        assert_eq!(cmds.len(), 1);
        // Should be Assert(Not(Eq(mo_order_0, mo_order_1)))
        assert!(matches!(&cmds[0], Command::Assert(Term::Not(_))));
    }

    #[test]
    fn test_assert_mo_total_order_three_events() {
        // C(3,2) = 3 pairs
        let cmds = assert_mo_total_order(&[0, 1, 2]);
        assert_eq!(cmds.len(), 3);
    }

    // ===== assert_rf_functional tests =====

    #[test]
    fn test_assert_rf_functional_empty_stores() {
        let cmds = assert_rf_functional(0, &[]);
        assert!(cmds.is_empty());
    }

    #[test]
    fn test_assert_rf_functional_one_store() {
        // At-least-one: 1 cmd; At-most-one: 0 pairs = 0 cmds
        let cmds = assert_rf_functional(0, &[5]);
        assert_eq!(cmds.len(), 1);
        // The single cmd is the at-least-one assertion
        assert!(matches!(&cmds[0], Command::Assert(_)));
    }

    #[test]
    fn test_assert_rf_functional_two_stores() {
        // At-least-one: 1 cmd; At-most-one: 1 pair = 1 cmd; total = 2
        let cmds = assert_rf_functional(0, &[5, 6]);
        assert_eq!(cmds.len(), 2);
    }

    // ===== is_release / is_acquire tests =====

    #[test]
    fn test_is_release() {
        assert!(!is_release(AtomicOrdering::Relaxed));
        assert!(!is_release(AtomicOrdering::Acquire));
        assert!(is_release(AtomicOrdering::Release));
        assert!(is_release(AtomicOrdering::AcqRel));
        assert!(is_release(AtomicOrdering::SeqCst));
    }

    #[test]
    fn test_is_acquire() {
        assert!(!is_acquire(AtomicOrdering::Relaxed));
        assert!(is_acquire(AtomicOrdering::Acquire));
        assert!(!is_acquire(AtomicOrdering::Release));
        assert!(is_acquire(AtomicOrdering::AcqRel));
        assert!(is_acquire(AtomicOrdering::SeqCst));
    }

    // ===== encode_sw tests =====

    #[test]
    fn test_encode_sw_relaxed_relaxed_is_false() {
        let term = encode_sw(0, AtomicOrdering::Relaxed, 1, AtomicOrdering::Relaxed);
        assert_eq!(term, Term::BoolLit(false));
    }

    #[test]
    fn test_encode_sw_release_acquire_is_rf() {
        let term = encode_sw(0, AtomicOrdering::Release, 1, AtomicOrdering::Acquire);
        assert_eq!(term, Term::Const("rf_1_0".to_string()));
    }

    #[test]
    fn test_encode_sw_acqrel_acqrel_is_rf() {
        let term = encode_sw(2, AtomicOrdering::AcqRel, 3, AtomicOrdering::AcqRel);
        assert_eq!(term, Term::Const("rf_3_2".to_string()));
    }

    #[test]
    fn test_encode_sw_release_relaxed_is_false() {
        // Release store but Relaxed load: not acquire, so no sw
        let term = encode_sw(0, AtomicOrdering::Release, 1, AtomicOrdering::Relaxed);
        assert_eq!(term, Term::BoolLit(false));
    }

    #[test]
    fn test_encode_sw_relaxed_acquire_is_false() {
        // Acquire load but Relaxed store: not release, so no sw
        let term = encode_sw(0, AtomicOrdering::Relaxed, 1, AtomicOrdering::Acquire);
        assert_eq!(term, Term::BoolLit(false));
    }

    // ===== encode_fr tests =====

    #[test]
    fn test_encode_fr_empty_stores() {
        let term = encode_fr(0, 1, &[]);
        assert_eq!(term, Term::BoolLit(false));
    }

    #[test]
    fn test_encode_fr_one_store() {
        let term = encode_fr(0, 2, &[1]);
        // Should be And(rf_0_1, mo_order_1 < mo_order_2)
        assert!(matches!(term, Term::And(_)));
    }

    #[test]
    fn test_encode_fr_two_stores() {
        let term = encode_fr(0, 3, &[1, 2]);
        // Should be Or(...)
        assert!(matches!(term, Term::Or(_)));
    }

    // ===== coherence_check tests =====

    #[test]
    fn test_coherence_check_returns_assert_not_and() {
        let hb = Term::BoolLit(true);
        let eco = Term::BoolLit(true);
        let cmd = coherence_check(0, 1, hb, eco);
        assert!(matches!(cmd, Command::Assert(Term::Not(_))));
    }

    // ===== weak_memory_smt_logic tests =====

    #[test]
    fn test_weak_memory_smt_logic() {
        assert_eq!(weak_memory_smt_logic(), "QF_LIA");
    }

    // ===== has_non_seqcst_atomics tests =====

    #[test]
    fn test_has_non_seqcst_atomics_empty() {
        let func = make_empty_func();
        assert!(!has_non_seqcst_atomics(&func));
    }

    #[test]
    fn test_has_non_seqcst_atomics_all_seqcst() {
        use crate::ir::AtomicOp;
        let mut func = make_empty_func();
        func.atomic_ops.push(AtomicOp {
            kind: AtomicOpKind::Load,
            ordering: AtomicOrdering::SeqCst,
            atomic_place: Place::local("x"),
            value: None,
            thread_id: 0,
        });
        assert!(!has_non_seqcst_atomics(&func));
    }

    #[test]
    fn test_has_non_seqcst_atomics_with_relaxed() {
        use crate::ir::AtomicOp;
        let mut func = make_empty_func();
        func.atomic_ops.push(AtomicOp {
            kind: AtomicOpKind::Store,
            ordering: AtomicOrdering::Relaxed,
            atomic_place: Place::local("x"),
            value: None,
            thread_id: 0,
        });
        assert!(has_non_seqcst_atomics(&func));
    }

    #[test]
    fn test_has_non_seqcst_atomics_mixed() {
        use crate::ir::AtomicOp;
        let mut func = make_empty_func();
        func.atomic_ops.push(AtomicOp {
            kind: AtomicOpKind::Load,
            ordering: AtomicOrdering::SeqCst,
            atomic_place: Place::local("x"),
            value: None,
            thread_id: 0,
        });
        func.atomic_ops.push(AtomicOp {
            kind: AtomicOpKind::Store,
            ordering: AtomicOrdering::Release,
            atomic_place: Place::local("x"),
            value: None,
            thread_id: 1,
        });
        assert!(has_non_seqcst_atomics(&func));
    }
}
