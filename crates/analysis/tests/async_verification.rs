//! TDD integration test suite for ASY-01 and ASY-02 requirements.
//!
//! Validates that `generate_async_vcs()` produces QF_LIA SMT scripts that:
//! - Return UNSAT when the async postcondition or state invariant is provably satisfied
//! - Return SAT when the postcondition or state invariant can be violated
//!
//! ## Test matrix
//!
//! | Test | Requirement | Axiom / constraint | Expected |
//! |------|-------------|-------------------|----------|
//! | async_postcondition_verified | ASY-01 | code path: result = x + 1 | UNSAT |
//! | async_postcondition_violated | ASY-01 | code path: result = x * 2 | SAT |
//! | async_requires_precondition | ASY-01 | with / without x >= 0 | UNSAT / SAT |
//! | async_state_invariant_verified | ASY-02 | counter = 5, only +1 | UNSAT ×4 |
//! | async_state_invariant_violated_at_suspension | ASY-02 | counter may be 0 | SAT |
//! | async_state_invariant_resumption_references_await_result | ASY-02 | awaited_result unconstrained | SAT |
//!
//! ## Axiom injection technique (same as hof_closures.rs)
//!
//! `generate_async_vcs()` produces a Script ending with `(check-sat)`.
//! For verified cases we clone commands (excluding `check-sat`), inject
//! code-path constraints, then append `(check-sat)`.
//!
//! ## SMT encoding reminder
//!
//! Each VC asserts the NEGATION of the property.
//! - UNSAT means the negation is unsatisfiable ↔ property is proven.
//! - SAT means the negation is satisfiable ↔ a counterexample exists.

use rust_fv_analysis::async_vcgen::generate_async_vcs;
use rust_fv_analysis::ghost_predicate_db::GhostPredicateDatabase;
use rust_fv_analysis::ir::{
    BasicBlock, Contracts, CoroutineExitKind, CoroutineInfo, CoroutineState, Function, IntTy,
    Local, SpecExpr, Terminator, Ty,
};
use rust_fv_analysis::vcgen::VcKind;
use rust_fv_smtlib::command::Command;
use rust_fv_smtlib::script::Script;
use rust_fv_smtlib::sort::Sort;
use rust_fv_smtlib::term::Term;
use rust_fv_solver::{SolverResult, Z3Solver};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Return a `Z3Solver` or panic with a clear skip message if Z3 is unavailable.
fn solver_or_skip() -> Z3Solver {
    match Z3Solver::with_default_config() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Skipping async test — Z3 not available: {e}");
            panic!("Z3_NOT_AVAILABLE");
        }
    }
}

/// Format a Script to SMT-LIB2 text for error message clarity.
fn script_to_smtlib(script: &Script) -> String {
    script
        .commands()
        .iter()
        .map(|cmd| format!("{cmd}"))
        .collect::<Vec<_>>()
        .join("\n")
}

/// Build a Script from a list of commands.
fn build_script(cmds: Vec<Command>) -> Script {
    let mut s = Script::new();
    for c in cmds {
        s.push(c);
    }
    s
}

/// Clone all commands from a Script except the trailing `(check-sat)`.
fn commands_without_check_sat(script: &Script) -> Vec<Command> {
    let cmds = script.commands();
    let last_check = cmds
        .iter()
        .rposition(|c| matches!(c, Command::CheckSat))
        .unwrap_or(cmds.len());
    cmds[..last_check].to_vec()
}

/// Build a minimal async `Function` with the given coroutine states and contracts.
///
/// The function has one `i32` parameter `x` and returns `i32` via `_0`.
/// Persistent fields are provided for the coroutine state machine.
fn make_async_func(
    name: &str,
    params: Vec<(&str, Ty)>,
    persistent_fields: Vec<(String, Ty)>,
    states: Vec<CoroutineState>,
    contracts: Contracts,
) -> Function {
    let ir_params: Vec<Local> = params
        .into_iter()
        .map(|(n, ty)| Local::new(n, ty))
        .collect();

    Function {
        name: name.to_string(),
        params: ir_params,
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

/// Build a Yield coroutine state.
fn yield_state(state_id: usize) -> CoroutineState {
    CoroutineState {
        state_id,
        entry_block: state_id,
        exit_kind: CoroutineExitKind::Yield,
        await_source_line: Some((10 + state_id * 5) as u32),
    }
}

/// Build a Return (Poll::Ready) coroutine state.
fn return_state(state_id: usize) -> CoroutineState {
    CoroutineState {
        state_id,
        entry_block: state_id,
        exit_kind: CoroutineExitKind::Return,
        await_source_line: None,
    }
}

// ---------------------------------------------------------------------------
// ASY-01 Test 1: async_postcondition_verified
//
// async fn increment(x: i32) -> i32 with #[ensures(result == x + 1)]
// Code path constraint: _0 = x + 1 (the actual implementation)
// Expected: UNSAT (postcondition proven from code constraint)
//
// SMT reasoning:
//   (assert (= _0 (+ x 1)))          ; code path
//   (assert (not (= _0 (+ x 1))))    ; negated postcondition
//   → contradiction → UNSAT
// ---------------------------------------------------------------------------

#[test]
fn async_postcondition_verified() {
    let solver = solver_or_skip();
    let db = GhostPredicateDatabase::new();

    let states = vec![yield_state(0), return_state(1)];
    let contracts = Contracts {
        ensures: vec![SpecExpr {
            raw: "_0 == x + 1".to_string(),
        }],
        ..Default::default()
    };
    let func = make_async_func(
        "increment",
        vec![("x", Ty::Int(IntTy::I32))],
        vec![("x".to_string(), Ty::Int(IntTy::I32))],
        states,
        contracts,
    );

    let vcs = generate_async_vcs(&func, &db);
    assert_eq!(vcs.len(), 1, "One #[ensures] → one AsyncPostcondition VC");

    let vc = &vcs[0];
    assert_eq!(
        vc.location.vc_kind,
        VcKind::AsyncPostcondition,
        "VC must be AsyncPostcondition kind"
    );

    // Inject code path constraint: _0 = x + 1 (the implementation is correct)
    let mut cmds = commands_without_check_sat(&vc.script);
    cmds.push(Command::Assert(Term::Eq(
        Box::new(Term::Const("_0".to_string())),
        Box::new(Term::IntAdd(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::IntLit(1)),
        )),
    )));
    cmds.push(Command::CheckSat);

    let augmented_script = build_script(cmds);
    let result = solver.check_sat(&augmented_script).unwrap_or_else(|e| {
        panic!(
            "Z3 failed: {e}\nSMT:\n{}",
            script_to_smtlib(&augmented_script)
        )
    });

    assert!(
        matches!(result, SolverResult::Unsat),
        "async_postcondition_verified: code path `_0 = x+1` makes `ensures(_0 == x+1)` provable (UNSAT). \
         Got: {result:?}\nSMT:\n{}",
        script_to_smtlib(&augmented_script)
    );
}

// ---------------------------------------------------------------------------
// ASY-01 Test 2: async_postcondition_violated
//
// async fn bad_double(x: i32) -> i32 with #[ensures(result == x * 3)]
// Code actually computes: _0 = x * 2 (wrong)
// Expected: SAT (postcondition violated — counterexample exists)
//
// SMT reasoning:
//   (assert (= _0 (* x 2)))           ; actual code
//   (assert (not (= _0 (* x 3))))     ; negated postcondition
//   → satisfiable (e.g., x=1, _0=2)  → SAT
// ---------------------------------------------------------------------------

#[test]
fn async_postcondition_violated() {
    let solver = solver_or_skip();
    let db = GhostPredicateDatabase::new();

    let states = vec![yield_state(0), return_state(1)];
    let contracts = Contracts {
        ensures: vec![SpecExpr {
            raw: "_0 == x * 3".to_string(),
        }],
        ..Default::default()
    };
    let func = make_async_func(
        "bad_double",
        vec![("x", Ty::Int(IntTy::I32))],
        vec![("x".to_string(), Ty::Int(IntTy::I32))],
        states,
        contracts,
    );

    let vcs = generate_async_vcs(&func, &db);
    assert_eq!(vcs.len(), 1, "One #[ensures] → one AsyncPostcondition VC");

    let vc = &vcs[0];
    assert_eq!(
        vc.location.vc_kind,
        VcKind::AsyncPostcondition,
        "VC must be AsyncPostcondition kind"
    );

    // Inject code path: _0 = x * 2 (wrong implementation — violates x * 3 postcondition)
    let mut cmds = commands_without_check_sat(&vc.script);
    cmds.push(Command::Assert(Term::Eq(
        Box::new(Term::Const("_0".to_string())),
        Box::new(Term::IntMul(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::IntLit(2)),
        )),
    )));
    cmds.push(Command::CheckSat);

    let augmented_script = build_script(cmds);
    let result = solver.check_sat(&augmented_script).unwrap_or_else(|e| {
        panic!(
            "Z3 failed: {e}\nSMT:\n{}",
            script_to_smtlib(&augmented_script)
        )
    });

    assert!(
        matches!(result, SolverResult::Sat(_)),
        "async_postcondition_violated: code `_0 = x*2` violates `ensures(_0 == x*3)` (SAT). \
         Got: {result:?}\nSMT:\n{}",
        script_to_smtlib(&augmented_script)
    );
}

// ---------------------------------------------------------------------------
// ASY-01 Test 3: async_requires_precondition
//
// async fn sqrt_approx(x: i32) -> i32
//   with #[requires(x >= 0)] #[ensures(result >= 0)]
// Code: _0 = x (identity — trivially non-negative when x >= 0)
//
// With precondition as assumption + code path constraint:
//   UNSAT (requires x>=0, code gives _0=x, so _0>=0 provable)
//
// Without precondition (direct script without requires, but with code):
//   SAT (x may be negative, then _0=x<0 violates ensures)
// ---------------------------------------------------------------------------

#[test]
fn async_requires_precondition() {
    let solver = solver_or_skip();
    let db = GhostPredicateDatabase::new();

    let states = vec![yield_state(0), return_state(1)];
    let contracts = Contracts {
        requires: vec![SpecExpr {
            raw: "x >= 0".to_string(),
        }],
        ensures: vec![SpecExpr {
            raw: "_0 >= 0".to_string(),
        }],
        ..Default::default()
    };
    let func = make_async_func(
        "sqrt_approx",
        vec![("x", Ty::Int(IntTy::I32))],
        vec![("x".to_string(), Ty::Int(IntTy::I32))],
        states,
        contracts,
    );

    let vcs = generate_async_vcs(&func, &db);
    assert_eq!(vcs.len(), 1, "One #[ensures] → one AsyncPostcondition VC");

    let vc = &vcs[0];

    // --- With precondition ---
    // The VC script already asserts `(assert (>= x 0))` as the requires assumption.
    // Inject code path: _0 = x
    // With x>=0 and _0=x: NOT(_0 >= 0) is UNSAT
    let mut cmds_with = commands_without_check_sat(&vc.script);
    cmds_with.push(Command::Assert(Term::Eq(
        Box::new(Term::Const("_0".to_string())),
        Box::new(Term::Const("x".to_string())),
    )));
    cmds_with.push(Command::CheckSat);

    let script_with = build_script(cmds_with);
    let result_with = solver.check_sat(&script_with).unwrap_or_else(|e| {
        panic!(
            "Z3 failed (with precondition): {e}\nSMT:\n{}",
            script_to_smtlib(&script_with)
        )
    });

    assert!(
        matches!(result_with, SolverResult::Unsat),
        "With x>=0 precondition and _0=x: ensures(_0>=0) must be proven (UNSAT). \
         Got: {result_with:?}\nSMT:\n{}",
        script_to_smtlib(&script_with)
    );

    // --- Without precondition ---
    // Build a fresh script: QF_LIA, declare x and _0, inject _0=x (code), assert NOT(_0 >= 0)
    // No requires assumption → x is free → x may be negative → SAT
    let mut cmds_without = Script::new();
    cmds_without.push(Command::SetLogic("QF_LIA".to_string()));
    cmds_without.push(Command::DeclareConst("x".to_string(), Sort::Int));
    cmds_without.push(Command::DeclareConst("_0".to_string(), Sort::Int));
    // Code path: _0 = x
    cmds_without.push(Command::Assert(Term::Eq(
        Box::new(Term::Const("_0".to_string())),
        Box::new(Term::Const("x".to_string())),
    )));
    // Negated ensures: NOT(_0 >= 0)
    cmds_without.push(Command::Assert(Term::Not(Box::new(Term::IntGe(
        Box::new(Term::Const("_0".to_string())),
        Box::new(Term::IntLit(0)),
    )))));
    cmds_without.push(Command::CheckSat);

    let result_without = solver
        .check_sat(&cmds_without)
        .unwrap_or_else(|e| panic!("Z3 failed (without precondition): {e}"));

    assert!(
        matches!(result_without, SolverResult::Sat(_)),
        "Without x>=0 precondition and _0=x: ensures(_0>=0) can be violated (SAT). \
         Got: {result_without:?}"
    );
}

// ---------------------------------------------------------------------------
// ASY-02 Test 4: async_state_invariant_verified
//
// async fn process(counter: i32) with #[state_invariant(counter >= 0)]
// 2 .await points → 2 Yield states → 4 VCs (Suspend + Resume per state)
//
// Code constraints: counter initialized to 5, only incremented
// All 4 VCs: inject (counter >= 5) as assumption → UNSAT for all
//
// SMT reasoning (per invariant VC):
//   (assert (>= counter 5))          ; code constraint (counter always positive)
//   (assert (not (>= counter 0)))    ; negated invariant
//   → contradiction → UNSAT
// ---------------------------------------------------------------------------

#[test]
fn async_state_invariant_verified() {
    let solver = solver_or_skip();
    let db = GhostPredicateDatabase::new();

    let states = vec![yield_state(0), yield_state(1), return_state(2)];
    let contracts = Contracts {
        state_invariant: Some(SpecExpr {
            raw: "counter >= 0".to_string(),
        }),
        ..Default::default()
    };
    let func = make_async_func(
        "process",
        vec![("counter", Ty::Int(IntTy::I32))],
        vec![("counter".to_string(), Ty::Int(IntTy::I32))],
        states,
        contracts,
    );

    let vcs = generate_async_vcs(&func, &db);
    assert_eq!(
        vcs.len(),
        4,
        "2 Yield states × 2 sides = 4 invariant VCs, got: {}",
        vcs.len()
    );

    // Confirm all VCs are either Suspend or Resume
    for vc in &vcs {
        assert!(
            matches!(
                vc.location.vc_kind,
                VcKind::AsyncStateInvariantSuspend | VcKind::AsyncStateInvariantResume
            ),
            "Expected AsyncStateInvariant* kind, got: {:?}",
            vc.location.vc_kind
        );
    }

    // For each VC: inject (counter >= 5) — counter initialized to 5, only incremented
    // NOT(counter >= 0) cannot hold when counter >= 5 → UNSAT
    for (i, vc) in vcs.iter().enumerate() {
        let mut cmds = commands_without_check_sat(&vc.script);
        cmds.push(Command::Assert(Term::IntGe(
            Box::new(Term::Const("counter".to_string())),
            Box::new(Term::IntLit(5)),
        )));
        cmds.push(Command::CheckSat);

        let augmented = build_script(cmds);
        let result = solver.check_sat(&augmented).unwrap_or_else(|e| {
            panic!(
                "Z3 failed (VC {i}): {e}\nSMT:\n{}",
                script_to_smtlib(&augmented)
            )
        });

        assert!(
            matches!(result, SolverResult::Unsat),
            "async_state_invariant_verified: VC {i} ({:?}) — counter>=5 makes invariant provable (UNSAT). \
             Got: {result:?}\nSMT:\n{}",
            vc.location.vc_kind,
            script_to_smtlib(&augmented)
        );
    }
}

// ---------------------------------------------------------------------------
// ASY-02 Test 5: async_state_invariant_violated_at_suspension
//
// async fn process(counter: i32) with #[state_invariant(counter > 0)]
// Code can set counter = 0 before the first .await
// Expected: SAT for AsyncStateInvariantSuspend VC for state 0
//           (counterexample: counter = 0 at suspension)
// ---------------------------------------------------------------------------

#[test]
fn async_state_invariant_violated_at_suspension() {
    let solver = solver_or_skip();
    let db = GhostPredicateDatabase::new();

    let states = vec![yield_state(0), return_state(1)];
    let contracts = Contracts {
        state_invariant: Some(SpecExpr {
            raw: "counter > 0".to_string(),
        }),
        ..Default::default()
    };
    let func = make_async_func(
        "process_bad",
        vec![("counter", Ty::Int(IntTy::I32))],
        vec![("counter".to_string(), Ty::Int(IntTy::I32))],
        states,
        contracts,
    );

    let vcs = generate_async_vcs(&func, &db);
    // 1 Yield state → 2 VCs (Suspend + Resume)
    assert_eq!(vcs.len(), 2, "1 Yield state → 2 invariant VCs");

    // Find the Suspend VC for state 0
    let suspend_vc = vcs
        .iter()
        .find(|vc| vc.location.vc_kind == VcKind::AsyncStateInvariantSuspend)
        .expect("Must have an AsyncStateInvariantSuspend VC");

    // Run the Suspend VC as-is (no additional constraints).
    // The script only declares `counter` as a free Int and asserts NOT(counter > 0).
    // Z3 can freely set counter = 0 → SAT
    let result = solver.check_sat(&suspend_vc.script).unwrap_or_else(|e| {
        panic!(
            "Z3 failed: {e}\nSMT:\n{}",
            script_to_smtlib(&suspend_vc.script)
        )
    });

    assert!(
        matches!(result, SolverResult::Sat(_)),
        "async_state_invariant_violated_at_suspension: counter can be 0 at suspension (SAT). \
         Got: {result:?}\nSMT:\n{}",
        script_to_smtlib(&suspend_vc.script)
    );

    // Confirm poll_iteration is tracked (poll_iter constant in SMT script)
    let script_str = script_to_smtlib(&suspend_vc.script);
    assert!(
        script_str.contains("poll_iter"),
        "Suspend VC must include poll_iter to identify which state failed. SMT:\n{script_str}"
    );

    // Confirm the VC kind is the suspension side
    assert_eq!(
        suspend_vc.location.vc_kind,
        VcKind::AsyncStateInvariantSuspend
    );
}

// ---------------------------------------------------------------------------
// ASY-02 Test 6: async_state_invariant_resumption_references_await_result
//
// async fn fetch(base: i32) with #[state_invariant(awaited_result_0 >= 0)]
//
// The invariant references awaited_result_0 (result returned by the .await expression).
// awaited_result_0 is declared as an unconstrained SMT constant.
// Running the resumption VC as-is: Z3 can set awaited_result_0 = -1 → SAT
//
// This validates the CONTEXT.md decision: invariant CAN reference the awaited result.
// ---------------------------------------------------------------------------

#[test]
fn async_state_invariant_resumption_references_await_result() {
    let solver = solver_or_skip();
    let db = GhostPredicateDatabase::new();

    let states = vec![yield_state(0), return_state(1)];
    // The invariant references awaited_result_0, which is declared per-state in the SMT script
    let contracts = Contracts {
        state_invariant: Some(SpecExpr {
            raw: "awaited_result_0 >= 0".to_string(),
        }),
        ..Default::default()
    };
    let func = make_async_func(
        "fetch",
        vec![("base", Ty::Int(IntTy::I32))],
        vec![("base".to_string(), Ty::Int(IntTy::I32))],
        states,
        contracts,
    );

    let vcs = generate_async_vcs(&func, &db);
    // 1 Yield state → 2 VCs
    assert_eq!(vcs.len(), 2, "1 Yield state → 2 invariant VCs");

    // Find the Resumption VC for state 0
    let resume_vc = vcs
        .iter()
        .find(|vc| vc.location.vc_kind == VcKind::AsyncStateInvariantResume)
        .expect("Must have an AsyncStateInvariantResume VC");

    // Confirm the VC script declares awaited_result_0
    let script_str = script_to_smtlib(&resume_vc.script);
    assert!(
        script_str.contains("awaited_result_0"),
        "Resumption VC must declare awaited_result_0 constant. SMT:\n{script_str}"
    );

    // Run as-is: awaited_result_0 is a free unconstrained constant.
    // Z3 can choose awaited_result_0 = -1 → NOT(awaited_result_0 >= 0) is satisfiable → SAT
    let result = solver.check_sat(&resume_vc.script).unwrap_or_else(|e| {
        panic!(
            "Z3 failed: {e}\nSMT:\n{}",
            script_to_smtlib(&resume_vc.script)
        )
    });

    assert!(
        matches!(result, SolverResult::Sat(_)),
        "async_state_invariant_resumption_references_await_result: \
         awaited_result_0 is unconstrained — invariant `awaited_result_0 >= 0` can be violated (SAT). \
         Got: {result:?}\nSMT:\n{}",
        script_to_smtlib(&resume_vc.script)
    );
}
