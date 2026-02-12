//! Comprehensive tests for formula simplification.
//!
//! Tests verify that simplification preserves semantic equivalence while
//! reducing term size.

use rust_fv_analysis::simplify::{simplify_script, simplify_term};
use rust_fv_smtlib::command::Command;
use rust_fv_smtlib::script::Script;
use rust_fv_smtlib::sort::Sort;
use rust_fv_smtlib::term::Term;

// ============================================================================
// Constant Folding Tests
// ============================================================================

#[test]
fn constant_folding_bvadd() {
    let term = Term::BvAdd(
        Box::new(Term::BitVecLit(42, 32)),
        Box::new(Term::BitVecLit(8, 32)),
    );
    let result = simplify_term(&term);
    assert_eq!(result, Term::BitVecLit(50, 32));
}

#[test]
fn constant_folding_bvadd_overflow() {
    // Test wrapping behavior: 2^32 - 1 + 1 = 0
    let max_u32 = (1i128 << 32) - 1;
    let term = Term::BvAdd(
        Box::new(Term::BitVecLit(max_u32, 32)),
        Box::new(Term::BitVecLit(1, 32)),
    );
    let result = simplify_term(&term);
    assert_eq!(result, Term::BitVecLit(0, 32));
}

#[test]
fn constant_folding_bvsub() {
    let term = Term::BvSub(
        Box::new(Term::BitVecLit(100, 32)),
        Box::new(Term::BitVecLit(42, 32)),
    );
    let result = simplify_term(&term);
    assert_eq!(result, Term::BitVecLit(58, 32));
}

#[test]
fn constant_folding_bvsub_underflow() {
    // Test wrapping behavior: 0 - 1 wraps to 2^32 - 1
    let expected = (1i128 << 32) - 1;
    let term = Term::BvSub(
        Box::new(Term::BitVecLit(0, 32)),
        Box::new(Term::BitVecLit(1, 32)),
    );
    let result = simplify_term(&term);
    assert_eq!(result, Term::BitVecLit(expected, 32));
}

#[test]
fn constant_folding_bvmul() {
    let term = Term::BvMul(
        Box::new(Term::BitVecLit(6, 32)),
        Box::new(Term::BitVecLit(7, 32)),
    );
    let result = simplify_term(&term);
    assert_eq!(result, Term::BitVecLit(42, 32));
}

#[test]
fn constant_folding_and() {
    let cases = vec![
        (
            Term::And(vec![Term::BoolLit(true), Term::BoolLit(true)]),
            Term::BoolLit(true),
        ),
        (
            Term::And(vec![Term::BoolLit(true), Term::BoolLit(false)]),
            Term::BoolLit(false),
        ),
        (
            Term::And(vec![Term::BoolLit(false), Term::BoolLit(false)]),
            Term::BoolLit(false),
        ),
    ];

    for (input, expected) in cases {
        assert_eq!(simplify_term(&input), expected);
    }
}

#[test]
fn constant_folding_or() {
    let cases = vec![
        (
            Term::Or(vec![Term::BoolLit(true), Term::BoolLit(true)]),
            Term::BoolLit(true),
        ),
        (
            Term::Or(vec![Term::BoolLit(true), Term::BoolLit(false)]),
            Term::BoolLit(true),
        ),
        (
            Term::Or(vec![Term::BoolLit(false), Term::BoolLit(false)]),
            Term::BoolLit(false),
        ),
    ];

    for (input, expected) in cases {
        assert_eq!(simplify_term(&input), expected);
    }
}

#[test]
fn constant_folding_not() {
    let cases = vec![
        (
            Term::Not(Box::new(Term::BoolLit(true))),
            Term::BoolLit(false),
        ),
        (
            Term::Not(Box::new(Term::BoolLit(false))),
            Term::BoolLit(true),
        ),
    ];

    for (input, expected) in cases {
        assert_eq!(simplify_term(&input), expected);
    }
}

#[test]
fn constant_folding_integer_ops() {
    let cases = vec![
        (
            Term::IntAdd(Box::new(Term::IntLit(10)), Box::new(Term::IntLit(20))),
            Term::IntLit(30),
        ),
        (
            Term::IntSub(Box::new(Term::IntLit(50)), Box::new(Term::IntLit(30))),
            Term::IntLit(20),
        ),
        (
            Term::IntMul(Box::new(Term::IntLit(6)), Box::new(Term::IntLit(7))),
            Term::IntLit(42),
        ),
        (Term::IntNeg(Box::new(Term::IntLit(42))), Term::IntLit(-42)),
    ];

    for (input, expected) in cases {
        assert_eq!(simplify_term(&input), expected);
    }
}

#[test]
fn constant_folding_integer_comparisons() {
    let cases = vec![
        (
            Term::IntLt(Box::new(Term::IntLit(5)), Box::new(Term::IntLit(10))),
            Term::BoolLit(true),
        ),
        (
            Term::IntLt(Box::new(Term::IntLit(10)), Box::new(Term::IntLit(5))),
            Term::BoolLit(false),
        ),
        (
            Term::IntLe(Box::new(Term::IntLit(10)), Box::new(Term::IntLit(10))),
            Term::BoolLit(true),
        ),
        (
            Term::IntGt(Box::new(Term::IntLit(10)), Box::new(Term::IntLit(5))),
            Term::BoolLit(true),
        ),
        (
            Term::IntGe(Box::new(Term::IntLit(5)), Box::new(Term::IntLit(5))),
            Term::BoolLit(true),
        ),
    ];

    for (input, expected) in cases {
        assert_eq!(simplify_term(&input), expected);
    }
}

#[test]
fn constant_folding_bvult() {
    let cases = vec![
        (
            Term::BvULt(
                Box::new(Term::BitVecLit(5, 32)),
                Box::new(Term::BitVecLit(10, 32)),
            ),
            Term::BoolLit(true),
        ),
        (
            Term::BvULt(
                Box::new(Term::BitVecLit(10, 32)),
                Box::new(Term::BitVecLit(5, 32)),
            ),
            Term::BoolLit(false),
        ),
        (
            Term::BvULt(
                Box::new(Term::BitVecLit(5, 32)),
                Box::new(Term::BitVecLit(5, 32)),
            ),
            Term::BoolLit(false),
        ),
    ];

    for (input, expected) in cases {
        assert_eq!(simplify_term(&input), expected);
    }
}

#[test]
fn constant_folding_bvslt() {
    // Positive < positive
    let term1 = Term::BvSLt(
        Box::new(Term::BitVecLit(5, 32)),
        Box::new(Term::BitVecLit(10, 32)),
    );
    assert_eq!(simplify_term(&term1), Term::BoolLit(true));

    // Negative < positive (using two's complement)
    let neg5 = (1i128 << 32) - 5;
    let term2 = Term::BvSLt(
        Box::new(Term::BitVecLit(neg5, 32)),
        Box::new(Term::BitVecLit(10, 32)),
    );
    assert_eq!(simplify_term(&term2), Term::BoolLit(true));

    // Positive > negative
    let term3 = Term::BvSLt(
        Box::new(Term::BitVecLit(10, 32)),
        Box::new(Term::BitVecLit(neg5, 32)),
    );
    assert_eq!(simplify_term(&term3), Term::BoolLit(false));
}

// ============================================================================
// Identity Elimination Tests
// ============================================================================

#[test]
fn identity_bvadd_zero() {
    let x = Term::Const("x".to_string());
    let cases = vec![
        Term::BvAdd(Box::new(x.clone()), Box::new(Term::BitVecLit(0, 32))),
        Term::BvAdd(Box::new(Term::BitVecLit(0, 32)), Box::new(x.clone())),
    ];

    for input in cases {
        assert_eq!(simplify_term(&input), x);
    }
}

#[test]
fn identity_bvsub_zero() {
    let x = Term::Const("x".to_string());
    let term = Term::BvSub(Box::new(x.clone()), Box::new(Term::BitVecLit(0, 32)));
    assert_eq!(simplify_term(&term), x);
}

#[test]
fn identity_bvmul_one() {
    let x = Term::Const("x".to_string());
    let cases = vec![
        Term::BvMul(Box::new(x.clone()), Box::new(Term::BitVecLit(1, 32))),
        Term::BvMul(Box::new(Term::BitVecLit(1, 32)), Box::new(x.clone())),
    ];

    for input in cases {
        assert_eq!(simplify_term(&input), x);
    }
}

#[test]
fn identity_bvmul_zero() {
    let x = Term::Const("x".to_string());
    let cases = vec![
        Term::BvMul(Box::new(x.clone()), Box::new(Term::BitVecLit(0, 32))),
        Term::BvMul(Box::new(Term::BitVecLit(0, 32)), Box::new(x)),
    ];

    for input in cases {
        assert_eq!(simplify_term(&input), Term::BitVecLit(0, 32));
    }
}

#[test]
fn identity_and_true() {
    let x = Term::Const("x".to_string());
    let term = Term::And(vec![Term::BoolLit(true), x.clone()]);
    assert_eq!(simplify_term(&term), x);
}

#[test]
fn identity_and_false() {
    let x = Term::Const("x".to_string());
    let term = Term::And(vec![x, Term::BoolLit(false)]);
    assert_eq!(simplify_term(&term), Term::BoolLit(false));
}

#[test]
fn identity_or_false() {
    let x = Term::Const("x".to_string());
    let term = Term::Or(vec![Term::BoolLit(false), x.clone()]);
    assert_eq!(simplify_term(&term), x);
}

#[test]
fn identity_or_true() {
    let x = Term::Const("x".to_string());
    let term = Term::Or(vec![x, Term::BoolLit(true)]);
    assert_eq!(simplify_term(&term), Term::BoolLit(true));
}

#[test]
fn identity_implies_patterns() {
    let x = Term::Const("x".to_string());

    // Implies(True, x) -> x
    let term1 = Term::Implies(Box::new(Term::BoolLit(true)), Box::new(x.clone()));
    assert_eq!(simplify_term(&term1), x);

    // Implies(False, _) -> True
    let term2 = Term::Implies(Box::new(Term::BoolLit(false)), Box::new(x.clone()));
    assert_eq!(simplify_term(&term2), Term::BoolLit(true));

    // Implies(_, True) -> True
    let term3 = Term::Implies(Box::new(x.clone()), Box::new(Term::BoolLit(true)));
    assert_eq!(simplify_term(&term3), Term::BoolLit(true));

    // Implies(x, False) -> Not(x)
    let term4 = Term::Implies(Box::new(x.clone()), Box::new(Term::BoolLit(false)));
    assert_eq!(simplify_term(&term4), Term::Not(Box::new(x)));
}

#[test]
fn identity_ite_conditions() {
    let t = Term::Const("then_val".to_string());
    let e = Term::Const("else_val".to_string());

    // Ite(True, t, _) -> t
    let term1 = Term::Ite(
        Box::new(Term::BoolLit(true)),
        Box::new(t.clone()),
        Box::new(e.clone()),
    );
    assert_eq!(simplify_term(&term1), t);

    // Ite(False, _, e) -> e
    let term2 = Term::Ite(
        Box::new(Term::BoolLit(false)),
        Box::new(t),
        Box::new(e.clone()),
    );
    assert_eq!(simplify_term(&term2), e);
}

#[test]
fn identity_integer_add_zero() {
    let x = Term::Const("x".to_string());
    let cases = vec![
        Term::IntAdd(Box::new(x.clone()), Box::new(Term::IntLit(0))),
        Term::IntAdd(Box::new(Term::IntLit(0)), Box::new(x.clone())),
    ];

    for input in cases {
        assert_eq!(simplify_term(&input), x);
    }
}

#[test]
fn identity_integer_mul_one() {
    let x = Term::Const("x".to_string());
    let cases = vec![
        Term::IntMul(Box::new(x.clone()), Box::new(Term::IntLit(1))),
        Term::IntMul(Box::new(Term::IntLit(1)), Box::new(x.clone())),
    ];

    for input in cases {
        assert_eq!(simplify_term(&input), x);
    }
}

#[test]
fn identity_integer_mul_zero() {
    let x = Term::Const("x".to_string());
    let cases = vec![
        Term::IntMul(Box::new(x.clone()), Box::new(Term::IntLit(0))),
        Term::IntMul(Box::new(Term::IntLit(0)), Box::new(x)),
    ];

    for input in cases {
        assert_eq!(simplify_term(&input), Term::IntLit(0));
    }
}

// ============================================================================
// Double Negation Tests
// ============================================================================

#[test]
fn double_negation_elimination() {
    let x = Term::Const("x".to_string());
    let term = Term::Not(Box::new(Term::Not(Box::new(x.clone()))));
    assert_eq!(simplify_term(&term), x);
}

#[test]
fn triple_negation() {
    let x = Term::Const("x".to_string());
    let term = Term::Not(Box::new(Term::Not(Box::new(Term::Not(Box::new(
        x.clone(),
    ))))));
    // Not(Not(Not(x))) -> Not(x)
    assert_eq!(simplify_term(&term), Term::Not(Box::new(x)));
}

// ============================================================================
// Nested Simplification Tests
// ============================================================================

#[test]
fn nested_boolean_and_arithmetic() {
    // And(BvAdd(x, 0), Or(False, y)) -> And(x, y)
    let x = Term::Const("x".to_string());
    let y = Term::Const("y".to_string());
    let term = Term::And(vec![
        Term::BvAdd(Box::new(x.clone()), Box::new(Term::BitVecLit(0, 32))),
        Term::Or(vec![Term::BoolLit(false), y.clone()]),
    ]);
    let result = simplify_term(&term);
    assert_eq!(result, Term::And(vec![x, y]));
}

#[test]
fn nested_ite_with_arithmetic() {
    // Ite(True, BvMul(x, 1), BvAdd(y, 0)) -> x
    let x = Term::Const("x".to_string());
    let y = Term::Const("y".to_string());
    let term = Term::Ite(
        Box::new(Term::BoolLit(true)),
        Box::new(Term::BvMul(
            Box::new(x.clone()),
            Box::new(Term::BitVecLit(1, 32)),
        )),
        Box::new(Term::BvAdd(Box::new(y), Box::new(Term::BitVecLit(0, 32)))),
    );
    let result = simplify_term(&term);
    assert_eq!(result, x);
}

#[test]
fn deeply_nested_constant_folding() {
    // BvAdd(BvMul(2, 3), BvSub(10, 4)) -> BvAdd(6, 6) -> 12
    let term = Term::BvAdd(
        Box::new(Term::BvMul(
            Box::new(Term::BitVecLit(2, 32)),
            Box::new(Term::BitVecLit(3, 32)),
        )),
        Box::new(Term::BvSub(
            Box::new(Term::BitVecLit(10, 32)),
            Box::new(Term::BitVecLit(4, 32)),
        )),
    );
    let result = simplify_term(&term);
    assert_eq!(result, Term::BitVecLit(12, 32));
}

#[test]
fn nested_inside_quantifier() {
    // Forall bindings are preserved, body is simplified
    let x = Term::Const("x".to_string());
    let body = Term::And(vec![Term::BoolLit(true), x.clone()]);
    let term = Term::Forall(vec![("x".to_string(), Sort::Int)], Box::new(body));
    let result = simplify_term(&term);

    if let Term::Forall(bindings, simplified_body) = result {
        assert_eq!(bindings, vec![("x".to_string(), Sort::Int)]);
        assert_eq!(*simplified_body, x);
    } else {
        panic!("Expected Forall term");
    }
}

// ============================================================================
// No-Change Tests (already simplified)
// ============================================================================

#[test]
fn no_change_variable() {
    let x = Term::Const("x".to_string());
    assert_eq!(simplify_term(&x), x);
}

#[test]
fn no_change_literal() {
    let lit = Term::BitVecLit(42, 32);
    assert_eq!(simplify_term(&lit), lit);
}

#[test]
fn no_change_irreducible_expression() {
    let x = Term::Const("x".to_string());
    let y = Term::Const("y".to_string());
    let term = Term::BvAdd(Box::new(x.clone()), Box::new(y.clone()));
    assert_eq!(simplify_term(&term), Term::BvAdd(Box::new(x), Box::new(y)));
}

// ============================================================================
// Script-level Simplification Tests
// ============================================================================

#[test]
fn script_simplification_preserves_non_assert() {
    let script = Script::with_commands(vec![
        Command::SetLogic("QF_BV".to_string()),
        Command::DeclareConst("x".to_string(), Sort::BitVec(32)),
        Command::SetOption("produce-models".to_string(), "true".to_string()),
        Command::CheckSat,
        Command::GetModel,
    ]);

    let result = simplify_script(&script);
    assert_eq!(result.commands().len(), 5);

    for (i, cmd) in result.commands().iter().enumerate() {
        assert_eq!(cmd, &script.commands()[i]);
    }
}

#[test]
fn script_simplification_transforms_asserts() {
    let x = Term::Const("x".to_string());
    let script = Script::with_commands(vec![
        Command::SetLogic("QF_BV".to_string()),
        Command::DeclareConst("x".to_string(), Sort::BitVec(32)),
        // Assert(And(True, x)) should simplify to Assert(x)
        Command::Assert(Term::And(vec![Term::BoolLit(true), x.clone()])),
        // Assert(BvAdd(x, 0)) should simplify to Assert(x)
        Command::Assert(Term::BvAdd(
            Box::new(x.clone()),
            Box::new(Term::BitVecLit(0, 32)),
        )),
        Command::CheckSat,
    ]);

    let result = simplify_script(&script);
    let cmds = result.commands();

    assert_eq!(cmds.len(), 5);
    assert!(matches!(cmds[0], Command::SetLogic(_)));
    assert!(matches!(cmds[1], Command::DeclareConst(_, _)));

    if let Command::Assert(term) = &cmds[2] {
        assert_eq!(*term, x);
    } else {
        panic!("Expected Assert command");
    }

    if let Command::Assert(term) = &cmds[3] {
        assert_eq!(*term, x);
    } else {
        panic!("Expected Assert command");
    }

    assert!(matches!(cmds[4], Command::CheckSat));
}

#[test]
fn script_simplification_constant_folding_in_asserts() {
    let script = Script::with_commands(vec![
        Command::SetLogic("QF_BV".to_string()),
        Command::Assert(Term::BvAdd(
            Box::new(Term::BitVecLit(10, 32)),
            Box::new(Term::BitVecLit(20, 32)),
        )),
        Command::Assert(Term::And(vec![Term::BoolLit(true), Term::BoolLit(false)])),
        Command::CheckSat,
    ]);

    let result = simplify_script(&script);
    let cmds = result.commands();

    if let Command::Assert(term) = &cmds[1] {
        assert_eq!(*term, Term::BitVecLit(30, 32));
    } else {
        panic!("Expected Assert command");
    }

    if let Command::Assert(term) = &cmds[2] {
        assert_eq!(*term, Term::BoolLit(false));
    } else {
        panic!("Expected Assert command");
    }
}

#[test]
fn script_empty() {
    let script = Script::new();
    let result = simplify_script(&script);
    assert_eq!(result.commands().len(), 0);
}

#[test]
fn script_no_asserts() {
    let script = Script::with_commands(vec![
        Command::SetLogic("QF_BV".to_string()),
        Command::CheckSat,
    ]);

    let result = simplify_script(&script);
    assert_eq!(result.commands().len(), 2);
    assert!(matches!(result.commands()[0], Command::SetLogic(_)));
    assert!(matches!(result.commands()[1], Command::CheckSat));
}
