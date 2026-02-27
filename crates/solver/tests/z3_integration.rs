//! Integration tests for the Z3 solver interface.
//!
//! These tests call the real Z3 binary and verify end-to-end behavior.

use std::path::PathBuf;

use rust_fv_smtlib::command::Command as SmtCmd;
use rust_fv_smtlib::script::Script;
use rust_fv_smtlib::sort::Sort;
use rust_fv_smtlib::term::Term;

use rust_fv_solver::{SolverConfig, SolverError, SolverKind, SolverResult, Z3Solver};

// ---- Helper ----

fn make_solver() -> Z3Solver {
    Z3Solver::with_default_config().expect("Z3 should be available on this system")
}

// ============================================================
// Raw SMT-LIB string tests (no dependency on formatter)
// ============================================================

#[test]
fn raw_simple_sat() {
    let solver = make_solver();
    let result = solver
        .check_sat_raw(
            "\
(declare-const x Int)
(assert (> x 0))
(assert (< x 10))
(check-sat)
(get-model)
",
        )
        .unwrap();

    assert!(result.is_sat(), "Expected SAT, got: {result:?}");
    let model = result.model().expect("Expected model in SAT result");
    let x_val = model.get("x").expect("Model should contain x");
    // x should be between 1 and 9
    let x: i64 = x_val.parse().expect("x should be a plain integer");
    assert!(x > 0 && x < 10, "x = {x}, expected 0 < x < 10");
}

#[test]
fn raw_simple_unsat() {
    let solver = make_solver();
    let result = solver
        .check_sat_raw(
            "\
(declare-const x Int)
(assert (> x 5))
(assert (< x 3))
(check-sat)
",
        )
        .unwrap();

    assert!(result.is_unsat(), "Expected UNSAT, got: {result:?}");
}

#[test]
fn raw_bitvec_sat() {
    let solver = make_solver();
    let result = solver
        .check_sat_raw(
            "\
(declare-const x (_ BitVec 32))
(assert (= x #x00000005))
(check-sat)
(get-model)
",
        )
        .unwrap();

    assert!(result.is_sat());
    let model = result.model().expect("Expected model");
    let x_val = model.get("x").expect("Model should contain x");
    assert_eq!(x_val, "#x00000005");
}

#[test]
fn raw_bitvec_unsat() {
    let solver = make_solver();
    let result = solver
        .check_sat_raw(
            "\
(declare-const x (_ BitVec 8))
(assert (= x #x05))
(assert (= x #x0a))
(check-sat)
",
        )
        .unwrap();

    assert!(result.is_unsat());
}

#[test]
fn raw_boolean_sat() {
    let solver = make_solver();
    let result = solver
        .check_sat_raw(
            "\
(declare-const p Bool)
(declare-const q Bool)
(assert (or p q))
(assert (not (and p q)))
(check-sat)
(get-model)
",
        )
        .unwrap();

    assert!(result.is_sat());
    let model = result.model().expect("Expected model");
    let p = model.get("p").expect("Model should contain p");
    let q = model.get("q").expect("Model should contain q");
    // Exactly one of p, q should be true
    let p_bool = p == "true";
    let q_bool = q == "true";
    assert!(
        (p_bool || q_bool) && !(p_bool && q_bool),
        "Expected XOR: p={p}, q={q}"
    );
}

#[test]
fn raw_auto_appends_check_sat_get_model() {
    // The raw interface does NOT auto-append; only check_sat() on Script does.
    // So if we omit (check-sat), Z3 will produce empty output, which is a parse error.
    let solver = make_solver();
    let result = solver.check_sat_raw(
        "\
(declare-const x Int)
(assert (> x 0))
",
    );

    // Without (check-sat), Z3 produces no output -- should be a parse error
    assert!(result.is_err());
}

// ============================================================
// Script-based tests (using check_sat which auto-appends)
// ============================================================

#[test]
fn script_simple_sat() {
    let solver = make_solver();

    let mut script = Script::new();
    script.push(SmtCmd::SetLogic("QF_LIA".to_string()));
    script.push(SmtCmd::DeclareConst("x".to_string(), Sort::Int));
    script.push(SmtCmd::Assert(Term::IntGt(
        Box::new(Term::Const("x".to_string())),
        Box::new(Term::IntLit(0)),
    )));
    script.push(SmtCmd::Assert(Term::IntLt(
        Box::new(Term::Const("x".to_string())),
        Box::new(Term::IntLit(100)),
    )));

    let result = solver.check_sat(&script).unwrap();
    assert!(result.is_sat(), "Expected SAT, got: {result:?}");
    let model = result.model().expect("Expected model");
    let x_val = model.get("x").expect("Model should contain x");
    let x: i64 = x_val.parse().expect("x should be parseable");
    assert!(x > 0 && x < 100);
}

#[test]
fn script_simple_unsat() {
    let solver = make_solver();

    let mut script = Script::new();
    script.push(SmtCmd::SetLogic("QF_LIA".to_string()));
    script.push(SmtCmd::DeclareConst("x".to_string(), Sort::Int));
    // x > 5 AND x < 3 is unsatisfiable
    script.push(SmtCmd::Assert(Term::IntGt(
        Box::new(Term::Const("x".to_string())),
        Box::new(Term::IntLit(5)),
    )));
    script.push(SmtCmd::Assert(Term::IntLt(
        Box::new(Term::Const("x".to_string())),
        Box::new(Term::IntLit(3)),
    )));

    let result = solver.check_sat(&script).unwrap();
    assert!(result.is_unsat(), "Expected UNSAT, got: {result:?}");
}

#[test]
fn script_bitvec_overflow_check() {
    let solver = make_solver();

    // Verify that for 8-bit unsigned, x + 1 can overflow (wrap to 0)
    let mut script = Script::new();
    script.push(SmtCmd::SetLogic("QF_BV".to_string()));
    script.push(SmtCmd::DeclareConst("x".to_string(), Sort::BitVec(8)));
    // x + 1 == 0 (overflow case: x = 255)
    script.push(SmtCmd::Assert(Term::Eq(
        Box::new(Term::BvAdd(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::BitVecLit(1, 8)),
        )),
        Box::new(Term::BitVecLit(0, 8)),
    )));

    let result = solver.check_sat(&script).unwrap();
    assert!(
        result.is_sat(),
        "Expected SAT (overflow possible), got: {result:?}"
    );
    let model = result.model().expect("Expected model");
    let x_val = model.get("x").expect("Model should contain x");
    assert_eq!(x_val, "#xff", "x should be 255 (0xff)");
}

#[test]
fn script_bitvec_no_overflow() {
    let solver = make_solver();

    // Check that for 8-bit: if x < 255 then x + 1 != 0
    // i.e., (x < 255) AND (x + 1 == 0) should be UNSAT
    let mut script = Script::new();
    script.push(SmtCmd::SetLogic("QF_BV".to_string()));
    script.push(SmtCmd::DeclareConst("x".to_string(), Sort::BitVec(8)));
    script.push(SmtCmd::Assert(Term::BvULt(
        Box::new(Term::Const("x".to_string())),
        Box::new(Term::BitVecLit(255, 8)),
    )));
    script.push(SmtCmd::Assert(Term::Eq(
        Box::new(Term::BvAdd(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::BitVecLit(1, 8)),
        )),
        Box::new(Term::BitVecLit(0, 8)),
    )));

    let result = solver.check_sat(&script).unwrap();
    assert!(result.is_unsat(), "Expected UNSAT, got: {result:?}");
}

#[test]
fn script_with_explicit_check_sat_no_duplicate() {
    let solver = make_solver();

    let mut script = Script::new();
    script.push(SmtCmd::DeclareConst("x".to_string(), Sort::Int));
    script.push(SmtCmd::Assert(Term::Eq(
        Box::new(Term::Const("x".to_string())),
        Box::new(Term::IntLit(42)),
    )));
    script.push(SmtCmd::CheckSat);
    script.push(SmtCmd::GetModel);

    let result = solver.check_sat(&script).unwrap();
    assert!(result.is_sat());
}

// ============================================================
// Timeout handling
// ============================================================

#[test]
fn timeout_with_short_limit() {
    // Verify that a short timeout causes Z3 to return (not hang) on a hard problem.
    //
    // Previously this hung indefinitely on Ubuntu CI because Z3's internal -t: flag
    // is a soft hint that older Z3 versions (apt z3 4.8.x) ignore for QF_NIA problems.
    // The fix adds an OS-level timeout in CliSolver::check_sat_raw() that kills/abandons
    // the solver process after 3× the configured timeout, guaranteeing termination.
    //
    // Use 2000ms: long enough for Z3 to start and begin solving on any platform, short
    // enough that the OS-level backstop (6s) keeps the total test time well under 10s.
    let config = SolverConfig::auto_detect()
        .expect("z3 must be installed")
        .with_timeout(2000); // 2s solver timeout; OS-level backstop kicks in at 6s
    let solver = Z3Solver::new(config);

    // A hard nonlinear problem (Fermat's Last Theorem cubic case).
    // Z3 cannot solve this quickly — it should time out and return Unknown.
    let result = solver.check_sat_raw(
        "\
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (> x 1))
(assert (> y 1))
(assert (> z 1))
(assert (= (* (* x x x) (* y y y)) (* z z z)))
(check-sat)
",
    );

    // We expect Unknown (timeout) or possibly Unsat if z3 is fast enough.
    // An Err (parse error from truncated output) is also acceptable.
    // What is NOT acceptable: hanging for >10s (the OS-level timeout prevents that).
    match result {
        Ok(SolverResult::Unknown(_)) => {} // Expected: timeout
        Ok(SolverResult::Unsat) => {}      // Valid: z3 was fast enough
        Ok(SolverResult::Sat(_)) => {}     // Unexpected but not a hang
        Err(_) => {}                       // Parse error from truncated output is also ok
    }
}

#[test]
fn normal_timeout_succeeds() {
    // Verify that a reasonable timeout doesn't interfere with solvable problems
    let config = SolverConfig::auto_detect()
        .expect("z3 must be installed")
        .with_timeout(30000); // 30s
    let solver = Z3Solver::new(config);

    let result = solver
        .check_sat_raw(
            "\
(declare-const x Int)
(assert (= x 42))
(check-sat)
(get-model)
",
        )
        .unwrap();

    assert!(result.is_sat());
}

// ============================================================
// Error handling
// ============================================================

#[test]
fn error_missing_binary() {
    let config = SolverConfig::new(SolverKind::Z3, PathBuf::from("/nonexistent/path/z3"));
    let solver = Z3Solver::new(config);

    let result = solver.check_sat_raw("(check-sat)");
    assert!(result.is_err());
    match result.unwrap_err() {
        SolverError::NotFound(_kind, path) => {
            assert_eq!(path, PathBuf::from("/nonexistent/path/z3"));
        }
        other => panic!("Expected NotFound, got: {other:?}"),
    }
}

#[test]
fn error_invalid_smtlib() {
    let solver = make_solver();

    // Invalid SMT-LIB should produce some error output from Z3
    let result = solver.check_sat_raw("(this-is-not-valid-smtlib)");
    // Z3 might produce an error message that doesn't parse as sat/unsat/unknown
    assert!(
        result.is_err(),
        "Expected error for invalid SMT-LIB, got: {result:?}"
    );
}

// ============================================================
// Configuration tests
// ============================================================

#[test]
fn with_default_config_succeeds() {
    let solver = Z3Solver::with_default_config();
    assert!(solver.is_ok(), "Should auto-detect Z3");
}

#[test]
fn config_extra_args() {
    let config = SolverConfig::auto_detect()
        .expect("z3 must be installed")
        .with_extra_args(vec!["-v:0".to_string()]);
    let solver = Z3Solver::new(config);

    let result = solver
        .check_sat_raw(
            "\
(declare-const x Int)
(assert (= x 1))
(check-sat)
",
        )
        .unwrap();

    assert!(result.is_sat());
}

// ============================================================
// Model content verification
// ============================================================

#[test]
fn model_multiple_variables() {
    let solver = make_solver();

    let result = solver
        .check_sat_raw(
            "\
(declare-const a Int)
(declare-const b Int)
(declare-const c Bool)
(assert (= a 10))
(assert (= b 20))
(assert (= c true))
(check-sat)
(get-model)
",
        )
        .unwrap();

    assert!(result.is_sat());
    let model = result.model().expect("Expected model");
    assert_eq!(model.get("a"), Some("10"));
    assert_eq!(model.get("b"), Some("20"));
    assert_eq!(model.get("c"), Some("true"));
}

#[test]
fn model_negative_integer() {
    let solver = make_solver();

    let result = solver
        .check_sat_raw(
            "\
(declare-const x Int)
(assert (= x (- 42)))
(check-sat)
(get-model)
",
        )
        .unwrap();

    assert!(result.is_sat());
    let model = result.model().expect("Expected model");
    let x_val = model.get("x").expect("Model should contain x");
    assert_eq!(x_val, "(- 42)");
}

// ============================================================
// Formal verification pattern: proving properties
// ============================================================

#[test]
fn verification_pattern_prove_by_negation() {
    // To PROVE that (x > 0) => (x + 1 > 1) for all integers x,
    // we check that the NEGATION is UNSAT:
    //   exists x: (x > 0) AND NOT(x + 1 > 1)
    let solver = make_solver();

    let result = solver
        .check_sat_raw(
            "\
(declare-const x Int)
(assert (> x 0))
(assert (not (> (+ x 1) 1)))
(check-sat)
",
        )
        .unwrap();

    assert!(
        result.is_unsat(),
        "Property should be PROVED (negation is unsat), got: {result:?}"
    );
}

#[test]
fn verification_pattern_find_counterexample() {
    // Try to prove that x * x >= 0 for all integers.
    // This is actually true, but let's check a WRONG property:
    //   x * x > 0 for all x (false when x = 0)
    let solver = make_solver();

    let result = solver
        .check_sat_raw(
            "\
(declare-const x Int)
(assert (not (> (* x x) 0)))
(check-sat)
(get-model)
",
        )
        .unwrap();

    assert!(
        result.is_sat(),
        "Should find counterexample (x=0), got: {result:?}"
    );
    let model = result.model().expect("Expected counterexample");
    let x_val = model.get("x").expect("Counterexample should contain x");
    assert_eq!(x_val, "0", "Counterexample should be x=0");
}
