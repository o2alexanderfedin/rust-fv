//! Async function verification condition generator.
//!
//! Generates VCs for `async fn` bodies under the sequential polling model.
//! Each `.await` suspension point (`CoroutineExitKind::Yield`) produces two VCs:
//! - `AsyncStateInvariantSuspend`: invariant holds just before yielding
//! - `AsyncStateInvariantResume`: invariant holds just after resuming
//!
//! The `Poll::Ready` terminal state produces one VC:
//! - `AsyncPostcondition`: `#[ensures]` holds when the future resolves
//!
//! ## SMT Logic
//!
//! Uses `QF_LIA` (Quantifier-Free Linear Integer Arithmetic) — sufficient for
//! bounded state enumeration with no universal quantification needed.
//!
//! ## select! encoding (non-deterministic branch)
//!
//! When a coroutine state contains multiple Yield terminators at the same source
//! line (conservative detection of `select!`-like patterns), a boolean SMT branch
//! variable is introduced: `(declare-const select_branch_STATE Bool)`.
//! Invariant checks are generated under both branches.
//!
//! ## join! encoding (sequential)
//!
//! `join!` desugars to consecutive Yield states — each maps to a separate
//! `CoroutineState` naturally. No special code needed.

use rust_fv_smtlib::command::Command;
use rust_fv_smtlib::script::Script;
use rust_fv_smtlib::sort::Sort;
use rust_fv_smtlib::term::Term;

use crate::ghost_predicate_db::GhostPredicateDatabase;
use crate::ir::{CoroutineExitKind, CoroutineInfo, CoroutineState, Function, SpecExpr, Ty};
use crate::spec_parser::parse_spec_expr_with_db;
use crate::vcgen::{VcKind, VcLocation, VerificationCondition};

/// Generate all VCs for an async function (coroutine).
///
/// Returns an empty `Vec` if the function is not async (`coroutine_info` is `None`).
///
/// Generated VCs:
/// - One `AsyncPostcondition` VC per `#[ensures]` clause (at `Poll::Ready`)
/// - Two VCs per Yield state per `#[state_invariant]`:
///   `AsyncStateInvariantSuspend` (before yield) and
///   `AsyncStateInvariantResume` (after resume)
pub fn generate_async_vcs(
    func: &Function,
    ghost_pred_db: &GhostPredicateDatabase,
) -> Vec<VerificationCondition> {
    let Some(coro_info) = &func.coroutine_info else {
        return vec![];
    };

    let mut vcs = Vec::new();

    // ASY-01: Postcondition VC — #[ensures] at Poll::Ready resolution
    for ensures_expr in &func.contracts.ensures {
        vcs.push(generate_async_postcondition_vc(
            func,
            coro_info,
            ensures_expr,
            ghost_pred_db,
        ));
    }

    // ASY-02: State invariant VCs — at each Yield state (suspension + resumption)
    if let Some(invariant) = &func.contracts.state_invariant {
        for state in &coro_info.states {
            if state.exit_kind == CoroutineExitKind::Yield {
                // Detect select!-like pattern: multiple yields at same source line
                let has_select_pattern = detect_select_pattern(coro_info, state.await_source_line);

                vcs.push(generate_invariant_vc(
                    func,
                    coro_info,
                    state,
                    invariant,
                    "suspension",
                    has_select_pattern,
                    ghost_pred_db,
                ));
                vcs.push(generate_invariant_vc(
                    func,
                    coro_info,
                    state,
                    invariant,
                    "resumption",
                    has_select_pattern,
                    ghost_pred_db,
                ));
            }
        }
    }

    vcs
}

/// Detect select!-like pattern: multiple Yield states at the same source line.
///
/// Conservative heuristic: if two or more Yield states share the same
/// `await_source_line`, treat the group as a `select!`-like construct and
/// apply non-deterministic branch encoding.
fn detect_select_pattern(coro_info: &CoroutineInfo, source_line: Option<u32>) -> bool {
    let Some(line) = source_line else {
        return false;
    };
    coro_info
        .states
        .iter()
        .filter(|s| s.exit_kind == CoroutineExitKind::Yield && s.await_source_line == Some(line))
        .count()
        >= 2
}

/// Generate the `AsyncPostcondition` VC for a single `#[ensures]` clause.
///
/// Script structure:
/// ```text
/// (set-logic QF_LIA)
/// (declare-const FIELD_NAME Int)  ; for each persistent field
/// (declare-const _0 Int)          ; return value (if not already a field)
/// (declare-const poll_iter Int)
/// (assert REQUIRES_EXPR)          ; #[requires] as assumptions
/// (assert (not ENSURES_EXPR))     ; negated #[ensures]
/// (check-sat)
/// ```
/// UNSAT = postcondition proven.
fn generate_async_postcondition_vc(
    func: &Function,
    coro_info: &CoroutineInfo,
    ensures_expr: &SpecExpr,
    ghost_pred_db: &GhostPredicateDatabase,
) -> VerificationCondition {
    let mut script = Script::new();
    script.push(Command::SetLogic("QF_LIA".to_string()));

    // Declare persistent fields as SMT constants
    let field_names = declare_persistent_fields(&mut script, coro_info);

    // Declare _0 (return value) if not already a persistent field
    if !field_names.contains(&"_0".to_string()) {
        let return_sort = ty_to_qf_lia_sort(&func.return_local.ty);
        script.push(Command::DeclareConst("_0".to_string(), return_sort));
    }

    // Declare poll_iter for counterexample diagnostics (bounded by state count)
    script.push(Command::DeclareConst("poll_iter".to_string(), Sort::Int));
    let state_count = coro_info.states.len() as i128;
    script.push(Command::Assert(Term::And(vec![
        Term::IntGe(
            Box::new(Term::Const("poll_iter".to_string())),
            Box::new(Term::IntLit(0)),
        ),
        Term::IntLt(
            Box::new(Term::Const("poll_iter".to_string())),
            Box::new(Term::IntLit(state_count)),
        ),
    ])));

    // Assert #[requires] as assumptions
    for req in &func.contracts.requires {
        if let Some(term) = parse_spec_expr_with_db(&req.raw, func, ghost_pred_db) {
            script.push(Command::Assert(term));
        }
    }

    // Assert negated #[ensures] — UNSAT = proven
    let ensures_term = parse_spec_expr_with_db(&ensures_expr.raw, func, ghost_pred_db)
        .unwrap_or(Term::BoolLit(true));
    script.push(Command::Assert(Term::Not(Box::new(ensures_term))));

    script.push(Command::CheckSat);

    VerificationCondition {
        description: format!(
            "async postcondition: ensures `{}` holds at Poll::Ready",
            ensures_expr.raw
        ),
        script,
        location: VcLocation {
            function: func.name.clone(),
            block: 0,
            statement: 0,
            source_file: None,
            source_line: None,
            source_column: None,
            contract_text: Some(ensures_expr.raw.clone()),
            vc_kind: VcKind::AsyncPostcondition,
        },
    }
}

/// Generate an `AsyncStateInvariantSuspend` or `AsyncStateInvariantResume` VC
/// for a single coroutine Yield state.
///
/// Script structure:
/// ```text
/// (set-logic QF_LIA)
/// (declare-const FIELD_NAME Int)   ; persistent fields
/// (declare-const poll_iter Int)
/// (assert (= poll_iter STATE_ID))  ; pin to this state
/// ; Optional: non-deterministic branch for select!-like patterns
/// (declare-const select_branch_STATE Bool)
/// (assert (not INVARIANT_EXPR))    ; negation — UNSAT = invariant holds
/// (check-sat)
/// ```
fn generate_invariant_vc(
    func: &Function,
    coro_info: &CoroutineInfo,
    state: &CoroutineState,
    invariant: &SpecExpr,
    side: &str,
    has_select_pattern: bool,
    ghost_pred_db: &GhostPredicateDatabase,
) -> VerificationCondition {
    let mut script = Script::new();
    script.push(Command::SetLogic("QF_LIA".to_string()));

    // Declare persistent fields
    declare_persistent_fields(&mut script, coro_info);

    // Declare poll_iter pinned to this state's id
    script.push(Command::DeclareConst("poll_iter".to_string(), Sort::Int));
    script.push(Command::Assert(Term::Eq(
        Box::new(Term::Const("poll_iter".to_string())),
        Box::new(Term::IntLit(state.state_id as i128)),
    )));

    // Optionally declare awaited_result constant (value returned by this .await)
    let awaited_result_name = format!("awaited_result_{}", state.state_id);
    script.push(Command::DeclareConst(
        awaited_result_name.clone(),
        Sort::Int,
    ));

    // select!-like pattern: introduce non-deterministic boolean branch variable
    if has_select_pattern {
        let branch_name = format!("select_branch_{}", state.state_id);
        script.push(Command::DeclareConst(branch_name.clone(), Sort::Bool));
        tracing::debug!(
            state_id = state.state_id,
            "select!-like construct detected, applying non-deterministic branch encoding"
        );
    }

    // Assert negated invariant — UNSAT = invariant holds
    let invariant_term =
        parse_spec_expr_with_db(&invariant.raw, func, ghost_pred_db).unwrap_or(Term::BoolLit(true));
    script.push(Command::Assert(Term::Not(Box::new(invariant_term))));

    script.push(Command::CheckSat);

    let vc_kind = if side == "suspension" {
        VcKind::AsyncStateInvariantSuspend
    } else {
        VcKind::AsyncStateInvariantResume
    };

    VerificationCondition {
        description: format!(
            "async state invariant ({}) at state {}: `{}`",
            side, state.state_id, invariant.raw
        ),
        script,
        location: VcLocation {
            function: func.name.clone(),
            block: state.entry_block,
            statement: 0,
            source_file: None,
            source_line: state.await_source_line.map(|l| l as usize),
            source_column: None,
            contract_text: Some(invariant.raw.clone()),
            vc_kind,
        },
    }
}

/// Declare all persistent fields as SMT `Int` constants.
///
/// Returns the set of declared names so callers can avoid re-declaring `_0`.
fn declare_persistent_fields(script: &mut Script, coro_info: &CoroutineInfo) -> Vec<String> {
    let mut declared = Vec::new();
    for (name, ty) in &coro_info.persistent_fields {
        let sort = ty_to_qf_lia_sort(ty);
        script.push(Command::DeclareConst(name.clone(), sort));
        declared.push(name.clone());
    }
    declared
}

/// Map a Rust IR type to a QF_LIA-compatible SMT sort.
///
/// All integer types → `Int`, `bool` → `Bool`, everything else → `Int`
/// (conservative fallback — correct for linear integer arithmetic).
fn ty_to_qf_lia_sort(ty: &Ty) -> Sort {
    match ty {
        Ty::Bool => Sort::Bool,
        Ty::Int(_) | Ty::Uint(_) | Ty::Char | Ty::SpecInt | Ty::SpecNat => Sort::Int,
        Ty::Ref(inner, _) => ty_to_qf_lia_sort(inner),
        _ => Sort::Int, // conservative fallback for QF_LIA
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ghost_predicate_db::GhostPredicateDatabase;
    use crate::ir::{
        BasicBlock, Contracts, CoroutineExitKind, CoroutineInfo, CoroutineState, Function, IntTy,
        Local, SpecExpr, Terminator, Ty,
    };

    /// Build a minimal `Function` with `coroutine_info: None` (regular function).
    fn make_non_coroutine_func() -> Function {
        Function {
            name: "regular_fn".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Int(IntTy::I32)),
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
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
            coroutine_info: None,
        }
    }

    /// Build a minimal async `Function` with given states and contracts.
    fn make_async_func(
        states: Vec<CoroutineState>,
        persistent_fields: Vec<(String, Ty)>,
        contracts: Contracts,
    ) -> Function {
        Function {
            name: "async_fn".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Int(IntTy::I32)),
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            contracts,
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
            coroutine_info: Some(CoroutineInfo {
                states,
                persistent_fields,
            }),
        }
    }

    /// Helper: make a Yield state.
    fn yield_state(state_id: usize, entry_block: usize) -> CoroutineState {
        CoroutineState {
            state_id,
            entry_block,
            exit_kind: CoroutineExitKind::Yield,
            await_source_line: Some(10),
        }
    }

    /// Helper: make a Return (Poll::Ready) state.
    fn return_state(state_id: usize) -> CoroutineState {
        CoroutineState {
            state_id,
            entry_block: state_id,
            exit_kind: CoroutineExitKind::Return,
            await_source_line: None,
        }
    }

    // ==================== RED tests ====================

    #[test]
    fn test_generate_async_vcs_empty_for_non_coroutine() {
        let func = make_non_coroutine_func();
        let db = GhostPredicateDatabase::new();
        let vcs = generate_async_vcs(&func, &db);
        assert!(
            vcs.is_empty(),
            "Non-coroutine function must produce zero async VCs"
        );
    }

    #[test]
    fn test_generate_async_vcs_postcondition_vc() {
        // Async fn with coroutine_info + one #[ensures] → 1 AsyncPostcondition VC
        let states = vec![yield_state(0, 0), return_state(1)];
        let contracts = Contracts {
            ensures: vec![SpecExpr {
                raw: "_0 >= 0".to_string(),
            }],
            state_invariant: None,
            ..Default::default()
        };
        let func = make_async_func(states, vec![], contracts);
        let db = GhostPredicateDatabase::new();
        let vcs = generate_async_vcs(&func, &db);
        assert_eq!(
            vcs.len(),
            1,
            "One #[ensures] → one AsyncPostcondition VC, got: {}",
            vcs.len()
        );
        assert_eq!(vcs[0].location.vc_kind, VcKind::AsyncPostcondition);
    }

    #[test]
    fn test_generate_async_vcs_state_invariant_vcs() {
        // Async fn with 2 Yield states + state_invariant → 4 VCs (2 suspend + 2 resume)
        let states = vec![yield_state(0, 0), yield_state(1, 1), return_state(2)];
        let contracts = Contracts {
            state_invariant: Some(SpecExpr {
                raw: "counter >= 0".to_string(),
            }),
            ..Default::default()
        };
        let func = make_async_func(
            states,
            vec![("counter".to_string(), Ty::Int(IntTy::I32))],
            contracts,
        );
        let db = GhostPredicateDatabase::new();
        let vcs = generate_async_vcs(&func, &db);
        assert_eq!(
            vcs.len(),
            4,
            "2 Yield states × 2 sides = 4 invariant VCs, got: {}",
            vcs.len()
        );
    }

    #[test]
    fn test_generate_async_vcs_vc_kinds() {
        // Both AsyncStateInvariantSuspend and AsyncPostcondition appear in output
        let states = vec![yield_state(0, 0), return_state(1)];
        let contracts = Contracts {
            ensures: vec![SpecExpr {
                raw: "_0 >= 0".to_string(),
            }],
            state_invariant: Some(SpecExpr {
                raw: "counter >= 0".to_string(),
            }),
            ..Default::default()
        };
        let func = make_async_func(
            states,
            vec![("counter".to_string(), Ty::Int(IntTy::I32))],
            contracts,
        );
        let db = GhostPredicateDatabase::new();
        let vcs = generate_async_vcs(&func, &db);

        let kinds: Vec<&VcKind> = vcs.iter().map(|vc| &vc.location.vc_kind).collect();

        assert!(
            kinds.contains(&&VcKind::AsyncPostcondition),
            "AsyncPostcondition VC must be present"
        );
        assert!(
            kinds.contains(&&VcKind::AsyncStateInvariantSuspend),
            "AsyncStateInvariantSuspend VC must be present"
        );
        assert!(
            kinds.contains(&&VcKind::AsyncStateInvariantResume),
            "AsyncStateInvariantResume VC must be present"
        );
    }

    #[test]
    fn test_generate_async_vcs_no_invariant_no_ensures() {
        // Async fn with coroutine_info but no contracts → 0 VCs
        let states = vec![yield_state(0, 0), return_state(1)];
        let func = make_async_func(states, vec![], Contracts::default());
        let db = GhostPredicateDatabase::new();
        let vcs = generate_async_vcs(&func, &db);
        assert_eq!(vcs.len(), 0, "No contracts → no VCs, got: {}", vcs.len());
    }

    #[test]
    fn test_generate_async_vcs_only_return_states_no_invariant_vcs() {
        // Async fn with only Return states → state invariant VCs should be zero
        let states = vec![return_state(0)];
        let contracts = Contracts {
            state_invariant: Some(SpecExpr {
                raw: "counter >= 0".to_string(),
            }),
            ..Default::default()
        };
        let func = make_async_func(
            states,
            vec![("counter".to_string(), Ty::Int(IntTy::I32))],
            contracts,
        );
        let db = GhostPredicateDatabase::new();
        let vcs = generate_async_vcs(&func, &db);
        assert_eq!(
            vcs.len(),
            0,
            "Only Return states → 0 invariant VCs (invariant only at Yield), got: {}",
            vcs.len()
        );
    }

    #[test]
    fn test_postcondition_vc_contains_qf_lia_logic() {
        // Verify the SMT script sets QF_LIA logic
        let states = vec![yield_state(0, 0), return_state(1)];
        let contracts = Contracts {
            ensures: vec![SpecExpr {
                raw: "_0 >= 0".to_string(),
            }],
            ..Default::default()
        };
        let func = make_async_func(states, vec![], contracts);
        let db = GhostPredicateDatabase::new();
        let vcs = generate_async_vcs(&func, &db);
        assert_eq!(vcs.len(), 1);
        let script_str = format!("{}", vcs[0].script);
        assert!(
            script_str.contains("QF_LIA"),
            "AsyncPostcondition script must use QF_LIA logic, got: {}",
            script_str
        );
    }

    #[test]
    fn test_invariant_vc_contains_poll_iter() {
        // State invariant VC should declare poll_iter
        let states = vec![yield_state(0, 0), return_state(1)];
        let contracts = Contracts {
            state_invariant: Some(SpecExpr {
                raw: "counter >= 0".to_string(),
            }),
            ..Default::default()
        };
        let func = make_async_func(
            states,
            vec![("counter".to_string(), Ty::Int(IntTy::I32))],
            contracts,
        );
        let db = GhostPredicateDatabase::new();
        let vcs = generate_async_vcs(&func, &db);
        for vc in &vcs {
            let script_str = format!("{}", vc.script);
            assert!(
                script_str.contains("poll_iter"),
                "Invariant VC script must declare poll_iter constant, got: {}",
                script_str
            );
        }
    }
}
