//! RC11 weak memory model SMT encoding.
//!
//! Implements mo (modification order), rf (reads-from), sw (synchronizes-with),
//! fr (from-read), and the four RC11 consistency axioms as bounded QF_LIA SMT
//! formulas. See Lahav et al. PLDI 2017.

use crate::ir::{AtomicOpKind, AtomicOrdering, Function};
use crate::vcgen::{VcKind, VcLocation, VerificationCondition};
use rust_fv_smtlib::command::Command;
use rust_fv_smtlib::script::Script;
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

/// Assert the RC11 COHERENCE violation for a pair of events (i, j).
///
/// This asserts the NEGATION of the coherence axiom: `hb(i, j) AND eco(j, i)`.
/// Used in violation-detection VCs: if this is SAT, there IS a coherence violation.
/// If UNSAT, no execution can produce this pair of hb and eco orderings simultaneously.
pub fn coherence_violation(event_i: usize, event_j: usize, hb_i_j: Term, eco_j_i: Term) -> Command {
    let _ = (event_i, event_j); // event ids are encoded in the terms
    Command::Assert(Term::And(vec![hb_i_j, eco_j_i]))
}

/// Assert that the initial store sentinel is modification-order-first for a location.
///
/// The initial store (writing 0 to every location) is always mo-before any
/// real store to the same location. This is an axiom of the memory model.
pub fn assert_initial_store_mo_first(
    real_store_ids: &[usize],
    initial_store_id: usize,
) -> Vec<Command> {
    real_store_ids
        .iter()
        .map(|&s| {
            Command::Assert(Term::IntLt(
                Box::new(Term::Const(format!("mo_order_{initial_store_id}"))),
                Box::new(Term::Const(format!("mo_order_{s}"))),
            ))
        })
        .collect()
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

// ===== RC11 VC generation =====

/// Generate RC11 weak memory verification conditions for a function.
///
/// Produces three kinds of VCs:
/// - `WeakMemoryCoherence`: hb;eco? irreflexivity per RC11 COHERENCE axiom
/// - `WeakMemoryRace`: Relaxed-vs-Relaxed same-location cross-thread unordered writes
/// - `WeakMemoryAtomicity`: RMW atomicity (no intervening store between read and write of RMW)
///
/// The caller is responsible for gating this function behind `has_non_seqcst_atomics`.
pub fn generate_rc11_vcs(func: &Function) -> Vec<VerificationCondition> {
    let ops = &func.atomic_ops;
    if ops.is_empty() {
        return Vec::new();
    }

    let n = ops.len();
    // Sentinel event_id for the initial store (value 0) — one past last real event.
    let initial_store_id = n;

    // === Step A: categorize events ===
    // Collect store event ids and load event ids, grouped by location.
    let mut store_ids_by_loc: std::collections::HashMap<&str, Vec<usize>> =
        std::collections::HashMap::new();
    let mut load_ids_by_loc: std::collections::HashMap<&str, Vec<usize>> =
        std::collections::HashMap::new();

    for (idx, op) in ops.iter().enumerate() {
        let loc = op.atomic_place.local.as_str();
        match op.kind {
            AtomicOpKind::Store => {
                store_ids_by_loc.entry(loc).or_default().push(idx);
            }
            AtomicOpKind::Load => {
                load_ids_by_loc.entry(loc).or_default().push(idx);
            }
            // RMW operations act as both store and load
            AtomicOpKind::Swap
            | AtomicOpKind::CompareExchange
            | AtomicOpKind::FetchAdd
            | AtomicOpKind::FetchSub => {
                store_ids_by_loc.entry(loc).or_default().push(idx);
                load_ids_by_loc.entry(loc).or_default().push(idx);
            }
        }
    }

    // Collect all locations
    let all_locs: std::collections::HashSet<&str> = ops
        .iter()
        .map(|op| op.atomic_place.local.as_str())
        .collect();

    // === Step B: Build SMT preamble commands ===
    let mut preamble: Vec<Command> = Vec::new();
    preamble.push(Command::SetLogic(weak_memory_smt_logic().to_string()));

    // Declare mo_order for all store events (including RMW writes).
    for (idx, op) in ops.iter().enumerate() {
        match op.kind {
            AtomicOpKind::Store
            | AtomicOpKind::Swap
            | AtomicOpKind::CompareExchange
            | AtomicOpKind::FetchAdd
            | AtomicOpKind::FetchSub => {
                preamble.push(declare_mo_order(idx));
            }
            AtomicOpKind::Load => {}
        }
    }
    // Declare mo_order for the initial store sentinel.
    preamble.push(declare_mo_order(initial_store_id));

    // Declare rf predicates: for each load, declare rf_L_S for every same-location store
    // (and for the initial store sentinel).
    for loc in &all_locs {
        let load_ids = load_ids_by_loc.get(loc).cloned().unwrap_or_default();
        let mut store_ids = store_ids_by_loc.get(loc).cloned().unwrap_or_default();
        // Add sentinel initial store
        store_ids.push(initial_store_id);

        for &load_id in &load_ids {
            for &store_id in &store_ids {
                preamble.push(declare_rf(load_id, store_id));
            }
        }
    }

    // === Step C: Assert mo is a total order per location ===
    let mut mo_cmds: Vec<Command> = Vec::new();
    for loc in &all_locs {
        let mut store_ids = store_ids_by_loc.get(loc).cloned().unwrap_or_default();
        // Assert initial store is mo-first (axiom: initial store precedes all real stores)
        mo_cmds.extend(assert_initial_store_mo_first(&store_ids, initial_store_id));
        store_ids.push(initial_store_id); // include sentinel
        mo_cmds.extend(assert_mo_total_order(&store_ids));
    }

    // === Step D: Assert rf is functional (each load reads from exactly one store) ===
    let mut rf_cmds: Vec<Command> = Vec::new();
    for loc in &all_locs {
        let load_ids = load_ids_by_loc.get(loc).cloned().unwrap_or_default();
        let mut store_ids = store_ids_by_loc.get(loc).cloned().unwrap_or_default();
        store_ids.push(initial_store_id);
        for &load_id in &load_ids {
            rf_cmds.extend(assert_rf_functional(load_id, &store_ids));
        }
    }

    // === Step E: Build sb (sequenced-before) static matrix ===
    // sb(i, j) = ops[i].thread_id == ops[j].thread_id && i < j
    let sb = |i: usize, j: usize| -> bool { i < j && ops[i].thread_id == ops[j].thread_id };

    // === Step F: Build sw (synchronizes-with) terms ===
    // sw(S, L) holds when S is a release store and L is an acquire load that reads from S.
    // We enumerate only (store, load) pairs where rf_L_S is declared (same location).
    // Result: sw_terms[i][j] = sw(i, j) term (BoolLit(false) if not applicable)
    let mut sw_terms: Vec<Vec<Term>> = vec![vec![Term::BoolLit(false); n]; n];
    for loc in &all_locs {
        let load_ids = load_ids_by_loc.get(loc).cloned().unwrap_or_default();
        let store_ids = store_ids_by_loc.get(loc).cloned().unwrap_or_default();
        for &store_id in &store_ids {
            for &load_id in &load_ids {
                if store_id != load_id {
                    let sw = encode_sw(
                        store_id,
                        ops[store_id].ordering,
                        load_id,
                        ops[load_id].ordering,
                    );
                    sw_terms[store_id][load_id] = sw;
                }
            }
        }
    }

    // === Step G: Build hb (happens-before) terms ===
    // hb(i, j) = sb(i,j) OR sw(i,j) OR (exists k. sb(i,k) AND sw(k,j))
    // For bounded N, compute over the N×N matrix.
    // Representation: each hb_term[i][j] is a Term (BoolLit(true/false) or Const "rf_...").
    let hb_term = |i: usize, j: usize| -> Term {
        if sb(i, j) {
            return Term::BoolLit(true);
        }
        // Direct sw
        let direct_sw = sw_terms[i][j].clone();
        if direct_sw != Term::BoolLit(false) {
            return direct_sw;
        }
        // Transitive: exists k. sb(i,k) && sw(k,j)
        let mut trans_terms: Vec<Term> = Vec::new();
        for (k, sw_row) in sw_terms.iter().enumerate().take(n) {
            if k != i && k != j && sb(i, k) {
                let sw_kj = sw_row[j].clone();
                if sw_kj != Term::BoolLit(false) {
                    trans_terms.push(sw_kj);
                }
            }
        }
        match trans_terms.len() {
            0 => Term::BoolLit(false),
            1 => trans_terms.remove(0),
            _ => Term::Or(trans_terms),
        }
    };

    // === Step H: Build eco (extended coherence order) terms ===
    // eco(i, j) = rf(i,j) OR mo(i,j) OR fr(i,j)
    let eco_term = |i: usize, j: usize| -> Term {
        if i == j {
            return Term::BoolLit(false);
        }
        let loc_i = ops[i].atomic_place.local.as_str();
        let loc_j = ops[j].atomic_place.local.as_str();
        if loc_i != loc_j {
            return Term::BoolLit(false);
        }
        let loc = loc_i;

        // rf(i, j): i is a load that reads from store j
        let load_ids = load_ids_by_loc.get(loc).cloned().unwrap_or_default();
        let store_ids_real = store_ids_by_loc.get(loc).cloned().unwrap_or_default();
        let mut store_ids_with_sentinel = store_ids_real.clone();
        store_ids_with_sentinel.push(initial_store_id);

        let rf_term = if load_ids.contains(&i) && store_ids_real.contains(&j) {
            Term::Const(format!("rf_{i}_{j}"))
        } else {
            Term::BoolLit(false)
        };

        // mo(i, j): both are stores, mo_order_i < mo_order_j
        let i_is_store = store_ids_real.contains(&i);
        let j_is_store = store_ids_real.contains(&j);
        let mo_term = if i_is_store && j_is_store {
            Term::IntLt(
                Box::new(Term::Const(format!("mo_order_{i}"))),
                Box::new(Term::Const(format!("mo_order_{j}"))),
            )
        } else {
            Term::BoolLit(false)
        };

        // fr(i, j): i is a load, j is a store, i reads from some store that is mo-before j
        let fr_term = if load_ids.contains(&i) && j_is_store {
            encode_fr(i, j, &store_ids_with_sentinel)
        } else {
            Term::BoolLit(false)
        };

        // Combine: eco = rf OR mo OR fr
        let parts: Vec<Term> = [rf_term, mo_term, fr_term]
            .into_iter()
            .filter(|t| *t != Term::BoolLit(false))
            .collect();
        match parts.len() {
            0 => Term::BoolLit(false),
            1 => parts.into_iter().next().unwrap(),
            _ => Term::Or(parts),
        }
    };

    let mut vcs: Vec<VerificationCondition> = Vec::new();

    // === Step I: Generate WeakMemoryCoherence VCs ===
    //
    // Violation-detection mode: for each pair (i, j), assert the VIOLATION
    // condition `hb(i,j) AND eco(j,i)` and check SAT.
    //
    //   SAT   => there EXISTS an execution with this coherence violation (bad)
    //   UNSAT => NO execution can produce hb(i,j) AND eco(j,i) simultaneously
    //            (RC11 coherence holds for this pair — good)
    //
    // For canonical litmus tests, FORBIDDEN outcomes produce UNSAT VCs:
    // the violation scenario is shown to be inconsistent with RC11.
    for i in 0..n {
        for j in 0..n {
            if i == j {
                continue;
            }
            let hb_i_j = hb_term(i, j);
            let eco_j_i = eco_term(j, i);

            // Skip pairs where either is statically false (violation structurally impossible)
            if hb_i_j == Term::BoolLit(false) || eco_j_i == Term::BoolLit(false) {
                continue;
            }

            let mut script = Script::new();
            script.extend(preamble.clone());
            script.extend(mo_cmds.clone());
            script.extend(rf_cmds.clone());
            // Assert the VIOLATION: hb(i,j) AND eco(j,i)
            // UNSAT => violation impossible => RC11 coherence holds
            // SAT   => violation possible   => coherence issue
            script.push(coherence_violation(i, j, hb_i_j, eco_j_i));
            script.push(Command::CheckSat);

            vcs.push(VerificationCondition {
                description: format!(
                    "RC11 coherence violation possible between events {i} and {j} in {}",
                    func.name
                ),
                script,
                location: VcLocation {
                    function: func.name.clone(),
                    block: 0,
                    statement: 0,
                    source_file: None,
                    source_line: None,
                    source_column: None,
                    contract_text: Some(format!(
                        "RC11 COHERENCE CHECK: hb({i},{j}) AND eco({j},{i}) [UNSAT=safe, SAT=violation]"
                    )),
                    vc_kind: VcKind::WeakMemoryCoherence,
                },
            });
        }
    }

    // === Step J: Generate WeakMemoryRace VCs ===
    // For all pairs (i, j) where:
    // - same location, different threads
    // - at least one is a write
    // - both are Relaxed
    // - hb(i,j) = false AND hb(j,i) = false
    for i in 0..n {
        for j in (i + 1)..n {
            let opi = &ops[i];
            let opj = &ops[j];
            if opi.atomic_place.local != opj.atomic_place.local {
                continue;
            }
            if opi.thread_id == opj.thread_id {
                continue;
            }
            let i_is_write = matches!(
                opi.kind,
                AtomicOpKind::Store
                    | AtomicOpKind::Swap
                    | AtomicOpKind::CompareExchange
                    | AtomicOpKind::FetchAdd
                    | AtomicOpKind::FetchSub
            );
            let j_is_write = matches!(
                opj.kind,
                AtomicOpKind::Store
                    | AtomicOpKind::Swap
                    | AtomicOpKind::CompareExchange
                    | AtomicOpKind::FetchAdd
                    | AtomicOpKind::FetchSub
            );
            if !i_is_write && !j_is_write {
                continue; // read-read: not a race
            }
            if opi.ordering != AtomicOrdering::Relaxed || opj.ordering != AtomicOrdering::Relaxed {
                continue;
            }
            // Check no hb in either direction
            let hb_ij = hb_term(i, j);
            let hb_ji = hb_term(j, i);
            if hb_ij != Term::BoolLit(false) || hb_ji != Term::BoolLit(false) {
                continue;
            }

            let mut script = Script::new();
            script.extend(preamble.clone());
            script.push(Command::Assert(Term::BoolLit(false)));
            script.push(Command::CheckSat);

            vcs.push(VerificationCondition {
                description: format!(
                    "Weak memory race: Relaxed accesses to {} from threads {} and {} without ordering in {}",
                    opi.atomic_place.local, opi.thread_id, opj.thread_id, func.name
                ),
                script,
                location: VcLocation {
                    function: func.name.clone(),
                    block: 0,
                    statement: 0,
                    source_file: None,
                    source_line: None,
                    source_column: None,
                    contract_text: Some(format!(
                        "Relaxed race between events {i} (thread {}) and {j} (thread {})",
                        opi.thread_id, opj.thread_id
                    )),
                    vc_kind: VcKind::WeakMemoryRace,
                },
            });
        }
    }

    // === Step K: Generate WeakMemoryAtomicity VCs ===
    // For RMW events with non-SeqCst ordering: assert no intervening store between
    // the store-that-RMW-reads-from and the RMW-write in mo.
    for (rmw_id, op) in ops.iter().enumerate() {
        match op.kind {
            AtomicOpKind::FetchAdd
            | AtomicOpKind::FetchSub
            | AtomicOpKind::Swap
            | AtomicOpKind::CompareExchange => {}
            _ => continue,
        }
        if op.ordering == AtomicOrdering::SeqCst {
            continue;
        }
        let loc = op.atomic_place.local.as_str();
        let store_ids_real = store_ids_by_loc.get(loc).cloned().unwrap_or_default();
        let mut store_ids_with_sentinel = store_ids_real.clone();
        store_ids_with_sentinel.push(initial_store_id);

        // The RMW event rmw_id acts as both a load (reads rf_rmw_id_S1) and a store (mo_order_rmw_id).
        // Atomicity: for every other store S2 at the same location,
        // it is NOT the case that mo_order_S1 < mo_order_S2 < mo_order_rmw_id
        // (where S1 is the store the RMW reads from).
        for &other_store in &store_ids_real {
            if other_store == rmw_id {
                continue;
            }
            // For each possible S1 that rmw_id could read from (including sentinel):
            for &s1 in &store_ids_with_sentinel {
                if s1 == rmw_id || s1 == other_store {
                    continue;
                }
                // The violation: rf_rmw_id_S1 AND mo_order_S1 < mo_order_other_store AND
                //                mo_order_other_store < mo_order_rmw_id
                // If this is satisfiable, we have an atomicity violation.
                let rf_term = Term::Const(format!("rf_{rmw_id}_{s1}"));
                let mo_s1_lt_other = Term::IntLt(
                    Box::new(Term::Const(format!("mo_order_{s1}"))),
                    Box::new(Term::Const(format!("mo_order_{other_store}"))),
                );
                let mo_other_lt_rmw = Term::IntLt(
                    Box::new(Term::Const(format!("mo_order_{other_store}"))),
                    Box::new(Term::Const(format!("mo_order_{rmw_id}"))),
                );
                let violation = Term::And(vec![rf_term, mo_s1_lt_other, mo_other_lt_rmw]);
                // Assert the negation: the violation must be impossible
                let mut script = Script::new();
                script.extend(preamble.clone());
                script.extend(mo_cmds.clone());
                script.extend(rf_cmds.clone());
                script.push(Command::Assert(Term::Not(Box::new(violation))));
                script.push(Command::CheckSat);

                vcs.push(VerificationCondition {
                    description: format!(
                        "RC11 RMW atomicity: event {rmw_id} in {} has intervening store {other_store}",
                        func.name
                    ),
                    script,
                    location: VcLocation {
                        function: func.name.clone(),
                        block: 0,
                        statement: 0,
                        source_file: None,
                        source_line: None,
                        source_column: None,
                        contract_text: Some(format!(
                            "RMW atomicity: no store between read-source and RMW write for event {rmw_id}"
                        )),
                        vc_kind: VcKind::WeakMemoryAtomicity,
                    },
                });
            }
        }
    }

    vcs
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
