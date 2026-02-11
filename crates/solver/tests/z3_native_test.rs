//! Integration tests for Z3 native backend.
//!
//! These tests verify that the native Z3 API backend produces identical
//! results to the subprocess backend, ensuring correctness of the translation
//! layer from SMT-LIB AST to z3 crate API.

#![cfg(feature = "z3-native")]

use rust_fv_smtlib::command::Command as SmtCmd;
use rust_fv_smtlib::script::Script;
use rust_fv_smtlib::sort::Sort;
use rust_fv_smtlib::term::Term;
use rust_fv_solver::{SolverBackend, SolverResult, Z3Solver};

#[cfg(feature = "z3-native")]
use rust_fv_solver::z3_native::Z3NativeSolver;

/// Helper to run a script on both backends and compare results.
fn test_equivalence(script: Script, expected_result: fn(&SolverResult) -> bool) {
    // Test subprocess backend
    let subprocess = Z3Solver::with_default_config().expect("Z3 not found");
    let subprocess_result = subprocess.check_sat(&script).expect("subprocess failed");
    assert!(
        expected_result(&subprocess_result),
        "Subprocess backend produced unexpected result: {:?}",
        subprocess_result
    );

    // Test native backend
    let native = Z3NativeSolver::new();
    let native_result = native.check_sat(&script).expect("native failed");
    assert!(
        expected_result(&native_result),
        "Native backend produced unexpected result: {:?}",
        native_result
    );

    // Verify both backends agree
    match (&subprocess_result, &native_result) {
        (SolverResult::Sat(_), SolverResult::Sat(_)) => { /* OK */ }
        (SolverResult::Unsat, SolverResult::Unsat) => { /* OK */ }
        (SolverResult::Unknown(_), SolverResult::Unknown(_)) => { /* OK */ }
        _ => panic!(
            "Backends disagree! Subprocess: {:?}, Native: {:?}",
            subprocess_result, native_result
        ),
    }
}

#[test]
fn test_basic_sat_with_model() {
    let mut script = Script::new();
    script.push(SmtCmd::SetLogic("QF_BV".to_string()));
    script.push(SmtCmd::DeclareConst("x".to_string(), Sort::BitVec(32)));
    script.push(SmtCmd::Assert(Term::BvUGt(
        Box::new(Term::Const("x".to_string())),
        Box::new(Term::BitVecLit(0, 32)),
    )));
    script.push(SmtCmd::Assert(Term::BvULt(
        Box::new(Term::Const("x".to_string())),
        Box::new(Term::BitVecLit(10, 32)),
    )));

    test_equivalence(script, |r| r.is_sat() && r.model().is_some());
}

#[test]
fn test_basic_unsat() {
    let mut script = Script::new();
    script.push(SmtCmd::SetLogic("QF_BV".to_string()));
    script.push(SmtCmd::DeclareConst("x".to_string(), Sort::BitVec(32)));
    script.push(SmtCmd::Assert(Term::BvUGt(
        Box::new(Term::Const("x".to_string())),
        Box::new(Term::BitVecLit(0, 32)),
    )));
    script.push(SmtCmd::Assert(Term::BvULt(
        Box::new(Term::Const("x".to_string())),
        Box::new(Term::BitVecLit(0, 32)),
    )));

    test_equivalence(script, |r| r.is_unsat());
}

#[test]
fn test_bitvector_overflow_sat() {
    let mut script = Script::new();
    script.push(SmtCmd::SetLogic("QF_BV".to_string()));
    script.push(SmtCmd::DeclareConst("x".to_string(), Sort::BitVec(8)));
    script.push(SmtCmd::DeclareConst("y".to_string(), Sort::BitVec(8)));

    // x = 200, y = 100, x + y = 44 (overflow in 8-bit)
    script.push(SmtCmd::Assert(Term::Eq(
        Box::new(Term::Const("x".to_string())),
        Box::new(Term::BitVecLit(200, 8)),
    )));
    script.push(SmtCmd::Assert(Term::Eq(
        Box::new(Term::Const("y".to_string())),
        Box::new(Term::BitVecLit(100, 8)),
    )));
    script.push(SmtCmd::Assert(Term::Eq(
        Box::new(Term::BvAdd(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::Const("y".to_string())),
        )),
        Box::new(Term::BitVecLit(44, 8)),
    )));

    test_equivalence(script, |r| r.is_sat());
}

#[test]
fn test_bitvector_overflow_unsat() {
    let mut script = Script::new();
    script.push(SmtCmd::SetLogic("QF_BV".to_string()));
    script.push(SmtCmd::DeclareConst("x".to_string(), Sort::BitVec(8)));

    // x + 1 > x should be UNSAT when x = 255 (overflow wraps to 0)
    script.push(SmtCmd::Assert(Term::Eq(
        Box::new(Term::Const("x".to_string())),
        Box::new(Term::BitVecLit(255, 8)),
    )));
    script.push(SmtCmd::Assert(Term::BvUGt(
        Box::new(Term::BvAdd(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::BitVecLit(1, 8)),
        )),
        Box::new(Term::Const("x".to_string())),
    )));

    test_equivalence(script, |r| r.is_unsat());
}

#[test]
fn test_signed_comparison() {
    let mut script = Script::new();
    script.push(SmtCmd::SetLogic("QF_BV".to_string()));
    script.push(SmtCmd::DeclareConst("x".to_string(), Sort::BitVec(8)));

    // x = 0xFF (255 unsigned, -1 signed)
    // x <s 0 (signed less than 0)
    script.push(SmtCmd::Assert(Term::Eq(
        Box::new(Term::Const("x".to_string())),
        Box::new(Term::BitVecLit(0xFF, 8)),
    )));
    script.push(SmtCmd::Assert(Term::BvSLt(
        Box::new(Term::Const("x".to_string())),
        Box::new(Term::BitVecLit(0, 8)),
    )));

    test_equivalence(script, |r| r.is_sat());
}

#[test]
fn test_bitwise_operations() {
    let mut script = Script::new();
    script.push(SmtCmd::SetLogic("QF_BV".to_string()));
    script.push(SmtCmd::DeclareConst("x".to_string(), Sort::BitVec(8)));

    // x & 0x0F = 0x05, x | 0xF0 = 0xF5 => x = 0x05
    script.push(SmtCmd::Assert(Term::Eq(
        Box::new(Term::BvAnd(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::BitVecLit(0x0F, 8)),
        )),
        Box::new(Term::BitVecLit(0x05, 8)),
    )));
    script.push(SmtCmd::Assert(Term::Eq(
        Box::new(Term::BvOr(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::BitVecLit(0xF0, 8)),
        )),
        Box::new(Term::BitVecLit(0xF5, 8)),
    )));

    test_equivalence(script, |r| r.is_sat());
}

#[test]
fn test_shift_operations() {
    let mut script = Script::new();
    script.push(SmtCmd::SetLogic("QF_BV".to_string()));
    script.push(SmtCmd::DeclareConst("x".to_string(), Sort::BitVec(8)));

    // x << 2 = 12, x = 3
    script.push(SmtCmd::Assert(Term::Eq(
        Box::new(Term::BvShl(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::BitVecLit(2, 8)),
        )),
        Box::new(Term::BitVecLit(12, 8)),
    )));

    test_equivalence(script, |r| r.is_sat());
}

#[test]
fn test_extension_operations() {
    let mut script = Script::new();
    script.push(SmtCmd::SetLogic("QF_BV".to_string()));
    script.push(SmtCmd::DeclareConst("x".to_string(), Sort::BitVec(8)));

    // zero_extend(x, 8) with x = 0xFF should give 0x00FF (16-bit)
    script.push(SmtCmd::Assert(Term::Eq(
        Box::new(Term::Const("x".to_string())),
        Box::new(Term::BitVecLit(0xFF, 8)),
    )));
    script.push(SmtCmd::Assert(Term::Eq(
        Box::new(Term::ZeroExtend(8, Box::new(Term::Const("x".to_string())))),
        Box::new(Term::BitVecLit(0x00FF, 16)),
    )));

    test_equivalence(script, |r| r.is_sat());
}

#[test]
fn test_sign_extension() {
    let mut script = Script::new();
    script.push(SmtCmd::SetLogic("QF_BV".to_string()));
    script.push(SmtCmd::DeclareConst("x".to_string(), Sort::BitVec(8)));

    // sign_extend(x, 8) with x = 0xFF should give 0xFFFF (16-bit, -1)
    script.push(SmtCmd::Assert(Term::Eq(
        Box::new(Term::Const("x".to_string())),
        Box::new(Term::BitVecLit(0xFF, 8)),
    )));
    script.push(SmtCmd::Assert(Term::Eq(
        Box::new(Term::SignExtend(8, Box::new(Term::Const("x".to_string())))),
        Box::new(Term::BitVecLit(0xFFFF, 16)),
    )));

    test_equivalence(script, |r| r.is_sat());
}

#[test]
fn test_ite_expression() {
    let mut script = Script::new();
    script.push(SmtCmd::SetLogic("QF_BV".to_string()));
    script.push(SmtCmd::DeclareConst("x".to_string(), Sort::BitVec(8)));
    script.push(SmtCmd::DeclareConst("y".to_string(), Sort::BitVec(8)));

    // y = if x > 10 then 20 else 5, y = 20 => x > 10
    script.push(SmtCmd::Assert(Term::Eq(
        Box::new(Term::Const("y".to_string())),
        Box::new(Term::Ite(
            Box::new(Term::BvUGt(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::BitVecLit(10, 8)),
            )),
            Box::new(Term::BitVecLit(20, 8)),
            Box::new(Term::BitVecLit(5, 8)),
        )),
    )));
    script.push(SmtCmd::Assert(Term::Eq(
        Box::new(Term::Const("y".to_string())),
        Box::new(Term::BitVecLit(20, 8)),
    )));

    test_equivalence(script, |r| r.is_sat());
}

#[test]
fn test_complex_boolean_logic() {
    let mut script = Script::new();
    script.push(SmtCmd::SetLogic("QF_BV".to_string()));
    script.push(SmtCmd::DeclareConst("a".to_string(), Sort::Bool));
    script.push(SmtCmd::DeclareConst("b".to_string(), Sort::Bool));
    script.push(SmtCmd::DeclareConst("c".to_string(), Sort::Bool));

    // (a AND b) OR (NOT c) must be true, but a = false, b = false, c = true
    script.push(SmtCmd::Assert(Term::Or(vec![
        Term::And(vec![
            Term::Const("a".to_string()),
            Term::Const("b".to_string()),
        ]),
        Term::Not(Box::new(Term::Const("c".to_string()))),
    ])));
    script.push(SmtCmd::Assert(Term::Eq(
        Box::new(Term::Const("a".to_string())),
        Box::new(Term::BoolLit(false)),
    )));
    script.push(SmtCmd::Assert(Term::Eq(
        Box::new(Term::Const("b".to_string())),
        Box::new(Term::BoolLit(false)),
    )));
    script.push(SmtCmd::Assert(Term::Eq(
        Box::new(Term::Const("c".to_string())),
        Box::new(Term::BoolLit(true)),
    )));

    test_equivalence(script, |r| r.is_unsat());
}

#[test]
fn test_phase1_pattern_overflow_detection() {
    // Test pattern matching Phase 1: detecting overflow in addition
    let mut script = Script::new();
    script.push(SmtCmd::SetLogic("QF_BV".to_string()));
    script.push(SmtCmd::DeclareConst("x".to_string(), Sort::BitVec(32)));
    script.push(SmtCmd::DeclareConst("y".to_string(), Sort::BitVec(32)));
    script.push(SmtCmd::DeclareConst("result".to_string(), Sort::BitVec(32)));

    // result = x + y
    script.push(SmtCmd::Assert(Term::Eq(
        Box::new(Term::Const("result".to_string())),
        Box::new(Term::BvAdd(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::Const("y".to_string())),
        )),
    )));

    // Overflow check: (x > 0 AND y > 0 AND result < x) OR (x < 0 AND y < 0 AND result > x)
    script.push(SmtCmd::Assert(Term::Or(vec![
        Term::And(vec![
            Term::BvSGt(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::BitVecLit(0, 32)),
            ),
            Term::BvSGt(
                Box::new(Term::Const("y".to_string())),
                Box::new(Term::BitVecLit(0, 32)),
            ),
            Term::BvSLt(
                Box::new(Term::Const("result".to_string())),
                Box::new(Term::Const("x".to_string())),
            ),
        ]),
        Term::And(vec![
            Term::BvSLt(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::BitVecLit(0, 32)),
            ),
            Term::BvSLt(
                Box::new(Term::Const("y".to_string())),
                Box::new(Term::BitVecLit(0, 32)),
            ),
            Term::BvSGt(
                Box::new(Term::Const("result".to_string())),
                Box::new(Term::Const("x".to_string())),
            ),
        ]),
    ])));

    // This should be SAT (overflow is possible)
    test_equivalence(script, |r| r.is_sat());
}
