//! Formula simplification for SMT-LIB terms and scripts.
//!
//! Performs AST-level simplification to reduce formula size before submission
//! to the SMT solver. This includes:
//!
//! - Constant folding (evaluate operations on literals)
//! - Identity elimination (remove no-op operations)
//! - Double negation elimination
//! - ITE simplification with constant conditions
//!
//! These transformations preserve semantic equivalence while potentially
//! reducing solver time by eliminating trivial subterms.

use rust_fv_smtlib::command::Command;
use rust_fv_smtlib::script::Script;
use rust_fv_smtlib::term::Term;

/// Simplify a single SMT term recursively.
///
/// Applies constant folding, identity elimination, and other algebraic
/// simplifications. The result is semantically equivalent to the input.
pub fn simplify_term(term: &Term) -> Term {
    match term {
        // === Literals and variables (already simplified) ===
        Term::BoolLit(_) | Term::IntLit(_) | Term::BitVecLit(_, _) | Term::Const(_) => term.clone(),

        // === Boolean operations ===
        Term::Not(inner) => {
            let simplified = simplify_term(inner);
            match simplified {
                // Not(True) -> False, Not(False) -> True
                Term::BoolLit(b) => Term::BoolLit(!b),
                // Not(Not(x)) -> x (double negation)
                Term::Not(inner2) => *inner2,
                _ => Term::Not(Box::new(simplified)),
            }
        }

        Term::And(terms) => {
            let simplified: Vec<Term> = terms.iter().map(simplify_term).collect();
            // Check for False (short-circuit)
            if simplified.iter().any(|t| matches!(t, Term::BoolLit(false))) {
                return Term::BoolLit(false);
            }
            // Filter out True literals
            let filtered: Vec<Term> = simplified
                .into_iter()
                .filter(|t| !matches!(t, Term::BoolLit(true)))
                .collect();
            match filtered.len() {
                0 => Term::BoolLit(true), // And() = True
                1 => filtered.into_iter().next().unwrap(),
                _ => Term::And(filtered),
            }
        }

        Term::Or(terms) => {
            let simplified: Vec<Term> = terms.iter().map(simplify_term).collect();
            // Check for True (short-circuit)
            if simplified.iter().any(|t| matches!(t, Term::BoolLit(true))) {
                return Term::BoolLit(true);
            }
            // Filter out False literals
            let filtered: Vec<Term> = simplified
                .into_iter()
                .filter(|t| !matches!(t, Term::BoolLit(false)))
                .collect();
            match filtered.len() {
                0 => Term::BoolLit(false), // Or() = False
                1 => filtered.into_iter().next().unwrap(),
                _ => Term::Or(filtered),
            }
        }

        Term::Implies(a, b) => {
            let a_simp = simplify_term(a);
            let b_simp = simplify_term(b);
            match (&a_simp, &b_simp) {
                // Implies(True, x) -> x
                (Term::BoolLit(true), _) => b_simp,
                // Implies(False, _) -> True
                (Term::BoolLit(false), _) => Term::BoolLit(true),
                // Implies(_, True) -> True
                (_, Term::BoolLit(true)) => Term::BoolLit(true),
                // Implies(_, False) -> Not(a)
                (_, Term::BoolLit(false)) => Term::Not(Box::new(a_simp)),
                _ => Term::Implies(Box::new(a_simp), Box::new(b_simp)),
            }
        }

        // === Equality and ITE ===
        Term::Eq(a, b) => {
            let a_simp = simplify_term(a);
            let b_simp = simplify_term(b);
            Term::Eq(Box::new(a_simp), Box::new(b_simp))
        }

        Term::Ite(cond, then_branch, else_branch) => {
            let cond_simp = simplify_term(cond);
            match cond_simp {
                // Ite(True, t, _) -> t
                Term::BoolLit(true) => simplify_term(then_branch),
                // Ite(False, _, e) -> e
                Term::BoolLit(false) => simplify_term(else_branch),
                _ => {
                    let then_simp = simplify_term(then_branch);
                    let else_simp = simplify_term(else_branch);
                    Term::Ite(
                        Box::new(cond_simp),
                        Box::new(then_simp),
                        Box::new(else_simp),
                    )
                }
            }
        }

        // === Bitvector arithmetic ===
        Term::BvAdd(a, b) => {
            let a_simp = simplify_term(a);
            let b_simp = simplify_term(b);
            match (&a_simp, &b_simp) {
                // BvAdd(lit1, lit2) -> lit(a+b mod 2^w)
                (Term::BitVecLit(val1, w1), Term::BitVecLit(val2, w2)) if w1 == w2 => {
                    let mask = if *w1 >= 128 {
                        i128::MAX
                    } else {
                        (1i128 << w1) - 1
                    };
                    let result = (val1.wrapping_add(*val2)) & mask;
                    Term::BitVecLit(result, *w1)
                }
                // BvAdd(x, 0) -> x
                (_, Term::BitVecLit(0, _)) => a_simp,
                // BvAdd(0, x) -> x
                (Term::BitVecLit(0, _), _) => b_simp,
                _ => Term::BvAdd(Box::new(a_simp), Box::new(b_simp)),
            }
        }

        Term::BvSub(a, b) => {
            let a_simp = simplify_term(a);
            let b_simp = simplify_term(b);
            match (&a_simp, &b_simp) {
                // BvSub(lit1, lit2) -> lit(a-b mod 2^w)
                (Term::BitVecLit(val1, w1), Term::BitVecLit(val2, w2)) if w1 == w2 => {
                    let mask = if *w1 >= 128 {
                        i128::MAX
                    } else {
                        (1i128 << w1) - 1
                    };
                    let result = (val1.wrapping_sub(*val2)) & mask;
                    Term::BitVecLit(result, *w1)
                }
                // BvSub(x, 0) -> x
                (_, Term::BitVecLit(0, _)) => a_simp,
                _ => Term::BvSub(Box::new(a_simp), Box::new(b_simp)),
            }
        }

        Term::BvMul(a, b) => {
            let a_simp = simplify_term(a);
            let b_simp = simplify_term(b);
            match (&a_simp, &b_simp) {
                // BvMul(lit1, lit2) -> lit(a*b mod 2^w)
                (Term::BitVecLit(val1, w1), Term::BitVecLit(val2, w2)) if w1 == w2 => {
                    let mask = if *w1 >= 128 {
                        i128::MAX
                    } else {
                        (1i128 << w1) - 1
                    };
                    let result = (val1.wrapping_mul(*val2)) & mask;
                    Term::BitVecLit(result, *w1)
                }
                // BvMul(_, 0) -> 0
                (_, Term::BitVecLit(0, w)) => Term::BitVecLit(0, *w),
                // BvMul(0, _) -> 0
                (Term::BitVecLit(0, w), _) => Term::BitVecLit(0, *w),
                // BvMul(x, 1) -> x
                (_, Term::BitVecLit(1, _)) => a_simp,
                // BvMul(1, x) -> x
                (Term::BitVecLit(1, _), _) => b_simp,
                _ => Term::BvMul(Box::new(a_simp), Box::new(b_simp)),
            }
        }

        // === Bitvector comparison ===
        Term::BvSLt(a, b) => {
            let a_simp = simplify_term(a);
            let b_simp = simplify_term(b);
            match (&a_simp, &b_simp) {
                (Term::BitVecLit(v1, w1), Term::BitVecLit(v2, w2)) if w1 == w2 => {
                    // Sign-extend to i128 for signed comparison
                    let sign_bit = 1i128 << (w1 - 1);
                    let mask = if *w1 >= 128 {
                        i128::MAX
                    } else {
                        (1i128 << w1) - 1
                    };
                    let s1 = if v1 & sign_bit != 0 {
                        v1 | !mask
                    } else {
                        v1 & mask
                    };
                    let s2 = if v2 & sign_bit != 0 {
                        v2 | !mask
                    } else {
                        v2 & mask
                    };
                    Term::BoolLit(s1 < s2)
                }
                _ => Term::BvSLt(Box::new(a_simp), Box::new(b_simp)),
            }
        }

        Term::BvULt(a, b) => {
            let a_simp = simplify_term(a);
            let b_simp = simplify_term(b);
            match (&a_simp, &b_simp) {
                (Term::BitVecLit(v1, w1), Term::BitVecLit(v2, w2)) if w1 == w2 => {
                    let mask = if *w1 >= 128 {
                        i128::MAX
                    } else {
                        (1i128 << w1) - 1
                    };
                    let u1 = v1 & mask;
                    let u2 = v2 & mask;
                    Term::BoolLit(u1 < u2)
                }
                _ => Term::BvULt(Box::new(a_simp), Box::new(b_simp)),
            }
        }

        // === Other bitvector operations (pass through with recursion) ===
        Term::BvSDiv(a, b) => Term::BvSDiv(Box::new(simplify_term(a)), Box::new(simplify_term(b))),
        Term::BvUDiv(a, b) => Term::BvUDiv(Box::new(simplify_term(a)), Box::new(simplify_term(b))),
        Term::BvSRem(a, b) => Term::BvSRem(Box::new(simplify_term(a)), Box::new(simplify_term(b))),
        Term::BvURem(a, b) => Term::BvURem(Box::new(simplify_term(a)), Box::new(simplify_term(b))),
        Term::BvNeg(a) => Term::BvNeg(Box::new(simplify_term(a))),
        Term::BvSLe(a, b) => Term::BvSLe(Box::new(simplify_term(a)), Box::new(simplify_term(b))),
        Term::BvSGt(a, b) => Term::BvSGt(Box::new(simplify_term(a)), Box::new(simplify_term(b))),
        Term::BvSGe(a, b) => Term::BvSGe(Box::new(simplify_term(a)), Box::new(simplify_term(b))),
        Term::BvULe(a, b) => Term::BvULe(Box::new(simplify_term(a)), Box::new(simplify_term(b))),
        Term::BvUGt(a, b) => Term::BvUGt(Box::new(simplify_term(a)), Box::new(simplify_term(b))),
        Term::BvUGe(a, b) => Term::BvUGe(Box::new(simplify_term(a)), Box::new(simplify_term(b))),
        Term::BvAnd(a, b) => Term::BvAnd(Box::new(simplify_term(a)), Box::new(simplify_term(b))),
        Term::BvOr(a, b) => Term::BvOr(Box::new(simplify_term(a)), Box::new(simplify_term(b))),
        Term::BvXor(a, b) => Term::BvXor(Box::new(simplify_term(a)), Box::new(simplify_term(b))),
        Term::BvNot(a) => Term::BvNot(Box::new(simplify_term(a))),
        Term::BvShl(a, b) => Term::BvShl(Box::new(simplify_term(a)), Box::new(simplify_term(b))),
        Term::BvLShr(a, b) => Term::BvLShr(Box::new(simplify_term(a)), Box::new(simplify_term(b))),
        Term::BvAShr(a, b) => Term::BvAShr(Box::new(simplify_term(a)), Box::new(simplify_term(b))),

        // === Bitvector conversion ===
        Term::ZeroExtend(n, a) => Term::ZeroExtend(*n, Box::new(simplify_term(a))),
        Term::SignExtend(n, a) => Term::SignExtend(*n, Box::new(simplify_term(a))),
        Term::Extract(hi, lo, a) => Term::Extract(*hi, *lo, Box::new(simplify_term(a))),
        Term::Concat(a, b) => Term::Concat(Box::new(simplify_term(a)), Box::new(simplify_term(b))),
        Term::Bv2Int(a) => Term::Bv2Int(Box::new(simplify_term(a))),
        Term::Int2Bv(n, a) => Term::Int2Bv(*n, Box::new(simplify_term(a))),

        // === Integer arithmetic ===
        Term::IntAdd(a, b) => {
            let a_simp = simplify_term(a);
            let b_simp = simplify_term(b);
            match (&a_simp, &b_simp) {
                (Term::IntLit(v1), Term::IntLit(v2)) => Term::IntLit(v1 + v2),
                (_, Term::IntLit(0)) => a_simp,
                (Term::IntLit(0), _) => b_simp,
                _ => Term::IntAdd(Box::new(a_simp), Box::new(b_simp)),
            }
        }
        Term::IntSub(a, b) => {
            let a_simp = simplify_term(a);
            let b_simp = simplify_term(b);
            match (&a_simp, &b_simp) {
                (Term::IntLit(v1), Term::IntLit(v2)) => Term::IntLit(v1 - v2),
                (_, Term::IntLit(0)) => a_simp,
                _ => Term::IntSub(Box::new(a_simp), Box::new(b_simp)),
            }
        }
        Term::IntMul(a, b) => {
            let a_simp = simplify_term(a);
            let b_simp = simplify_term(b);
            match (&a_simp, &b_simp) {
                (Term::IntLit(v1), Term::IntLit(v2)) => Term::IntLit(v1 * v2),
                (_, Term::IntLit(0)) | (Term::IntLit(0), _) => Term::IntLit(0),
                (_, Term::IntLit(1)) => a_simp,
                (Term::IntLit(1), _) => b_simp,
                _ => Term::IntMul(Box::new(a_simp), Box::new(b_simp)),
            }
        }
        Term::IntDiv(a, b) => Term::IntDiv(Box::new(simplify_term(a)), Box::new(simplify_term(b))),
        Term::IntMod(a, b) => Term::IntMod(Box::new(simplify_term(a)), Box::new(simplify_term(b))),
        Term::IntNeg(a) => {
            let a_simp = simplify_term(a);
            match a_simp {
                Term::IntLit(v) => Term::IntLit(-v),
                _ => Term::IntNeg(Box::new(a_simp)),
            }
        }
        Term::IntLt(a, b) => {
            let a_simp = simplify_term(a);
            let b_simp = simplify_term(b);
            match (&a_simp, &b_simp) {
                (Term::IntLit(v1), Term::IntLit(v2)) => Term::BoolLit(v1 < v2),
                _ => Term::IntLt(Box::new(a_simp), Box::new(b_simp)),
            }
        }
        Term::IntLe(a, b) => {
            let a_simp = simplify_term(a);
            let b_simp = simplify_term(b);
            match (&a_simp, &b_simp) {
                (Term::IntLit(v1), Term::IntLit(v2)) => Term::BoolLit(v1 <= v2),
                _ => Term::IntLe(Box::new(a_simp), Box::new(b_simp)),
            }
        }
        Term::IntGt(a, b) => {
            let a_simp = simplify_term(a);
            let b_simp = simplify_term(b);
            match (&a_simp, &b_simp) {
                (Term::IntLit(v1), Term::IntLit(v2)) => Term::BoolLit(v1 > v2),
                _ => Term::IntGt(Box::new(a_simp), Box::new(b_simp)),
            }
        }
        Term::IntGe(a, b) => {
            let a_simp = simplify_term(a);
            let b_simp = simplify_term(b);
            match (&a_simp, &b_simp) {
                (Term::IntLit(v1), Term::IntLit(v2)) => Term::BoolLit(v1 >= v2),
                _ => Term::IntGe(Box::new(a_simp), Box::new(b_simp)),
            }
        }

        // === Arrays, quantifiers, let, function application ===
        Term::Select(a, i) => Term::Select(Box::new(simplify_term(a)), Box::new(simplify_term(i))),
        Term::Store(a, i, v) => Term::Store(
            Box::new(simplify_term(a)),
            Box::new(simplify_term(i)),
            Box::new(simplify_term(v)),
        ),
        Term::Forall(bindings, body) => {
            Term::Forall(bindings.clone(), Box::new(simplify_term(body)))
        }
        Term::Exists(bindings, body) => {
            Term::Exists(bindings.clone(), Box::new(simplify_term(body)))
        }
        Term::Let(bindings, body) => {
            let simplified_bindings: Vec<(String, Term)> = bindings
                .iter()
                .map(|(name, val)| (name.clone(), simplify_term(val)))
                .collect();
            Term::Let(simplified_bindings, Box::new(simplify_term(body)))
        }
        Term::App(func, args) => {
            let simplified_args: Vec<Term> = args.iter().map(simplify_term).collect();
            Term::App(func.clone(), simplified_args)
        }
        Term::Annotated(body, annotations) => {
            let simplified_body = simplify_term(body);
            // Simplify annotation values too
            let simplified_annotations: Vec<(String, Vec<Term>)> = annotations
                .iter()
                .map(|(key, vals)| {
                    let simplified_vals = vals.iter().map(simplify_term).collect();
                    (key.clone(), simplified_vals)
                })
                .collect();
            Term::Annotated(Box::new(simplified_body), simplified_annotations)
        }

        // === Other term variants (if any) ===
        Term::Iff(a, b) => Term::Iff(Box::new(simplify_term(a)), Box::new(simplify_term(b))),
        Term::Distinct(terms) => {
            let simplified: Vec<Term> = terms.iter().map(simplify_term).collect();
            Term::Distinct(simplified)
        }
    }
}

/// Simplify an entire SMT-LIB script by simplifying all Assert commands.
///
/// Non-Assert commands (declarations, set-logic, check-sat, etc.) are
/// preserved unchanged. Only the terms inside Assert commands are simplified.
pub fn simplify_script(script: &Script) -> Script {
    let simplified_commands: Vec<Command> = script
        .commands()
        .iter()
        .map(|cmd| match cmd {
            Command::Assert(term) => Command::Assert(simplify_term(term)),
            _ => cmd.clone(),
        })
        .collect();

    Script::with_commands(simplified_commands)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_constant_folding_bvadd() {
        let term = Term::BvAdd(
            Box::new(Term::BitVecLit(5, 32)),
            Box::new(Term::BitVecLit(3, 32)),
        );
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BitVecLit(8, 32));
    }

    #[test]
    fn test_constant_folding_bvsub() {
        let term = Term::BvSub(
            Box::new(Term::BitVecLit(10, 32)),
            Box::new(Term::BitVecLit(3, 32)),
        );
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BitVecLit(7, 32));
    }

    #[test]
    fn test_constant_folding_bvmul() {
        let term = Term::BvMul(
            Box::new(Term::BitVecLit(4, 32)),
            Box::new(Term::BitVecLit(7, 32)),
        );
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BitVecLit(28, 32));
    }

    #[test]
    fn test_constant_folding_and_true_true() {
        let term = Term::And(vec![Term::BoolLit(true), Term::BoolLit(true)]);
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BoolLit(true));
    }

    #[test]
    fn test_constant_folding_and_true_false() {
        let term = Term::And(vec![Term::BoolLit(true), Term::BoolLit(false)]);
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BoolLit(false));
    }

    #[test]
    fn test_constant_folding_or_false_false() {
        let term = Term::Or(vec![Term::BoolLit(false), Term::BoolLit(false)]);
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BoolLit(false));
    }

    #[test]
    fn test_constant_folding_or_true_false() {
        let term = Term::Or(vec![Term::BoolLit(true), Term::BoolLit(false)]);
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BoolLit(true));
    }

    #[test]
    fn test_constant_folding_not_true() {
        let term = Term::Not(Box::new(Term::BoolLit(true)));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BoolLit(false));
    }

    #[test]
    fn test_constant_folding_not_false() {
        let term = Term::Not(Box::new(Term::BoolLit(false)));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BoolLit(true));
    }

    #[test]
    fn test_double_negation() {
        let x = Term::Const("x".to_string());
        let term = Term::Not(Box::new(Term::Not(Box::new(x.clone()))));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, x);
    }

    #[test]
    fn test_identity_bvadd_zero() {
        let x = Term::Const("x".to_string());
        let term = Term::BvAdd(Box::new(x.clone()), Box::new(Term::BitVecLit(0, 32)));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, x);
    }

    #[test]
    fn test_identity_bvmul_one() {
        let x = Term::Const("x".to_string());
        let term = Term::BvMul(Box::new(x.clone()), Box::new(Term::BitVecLit(1, 32)));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, x);
    }

    #[test]
    fn test_identity_bvmul_zero() {
        let x = Term::Const("x".to_string());
        let term = Term::BvMul(Box::new(x), Box::new(Term::BitVecLit(0, 32)));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BitVecLit(0, 32));
    }

    #[test]
    fn test_ite_true_condition() {
        let t = Term::Const("then_branch".to_string());
        let e = Term::Const("else_branch".to_string());
        let term = Term::Ite(
            Box::new(Term::BoolLit(true)),
            Box::new(t.clone()),
            Box::new(e),
        );
        let simplified = simplify_term(&term);
        assert_eq!(simplified, t);
    }

    #[test]
    fn test_ite_false_condition() {
        let t = Term::Const("then_branch".to_string());
        let e = Term::Const("else_branch".to_string());
        let term = Term::Ite(
            Box::new(Term::BoolLit(false)),
            Box::new(t),
            Box::new(e.clone()),
        );
        let simplified = simplify_term(&term);
        assert_eq!(simplified, e);
    }

    #[test]
    fn test_implies_true_antecedent() {
        let x = Term::Const("x".to_string());
        let term = Term::Implies(Box::new(Term::BoolLit(true)), Box::new(x.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, x);
    }

    #[test]
    fn test_implies_false_antecedent() {
        let x = Term::Const("x".to_string());
        let term = Term::Implies(Box::new(Term::BoolLit(false)), Box::new(x));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BoolLit(true));
    }

    #[test]
    fn test_implies_true_consequent() {
        let x = Term::Const("x".to_string());
        let term = Term::Implies(Box::new(x), Box::new(Term::BoolLit(true)));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BoolLit(true));
    }

    #[test]
    fn test_and_with_variable() {
        let x = Term::Const("x".to_string());
        let term = Term::And(vec![Term::BoolLit(true), x.clone()]);
        let simplified = simplify_term(&term);
        assert_eq!(simplified, x);
    }

    #[test]
    fn test_or_with_variable() {
        let x = Term::Const("x".to_string());
        let term = Term::Or(vec![Term::BoolLit(false), x.clone()]);
        let simplified = simplify_term(&term);
        assert_eq!(simplified, x);
    }

    #[test]
    fn test_nested_simplification() {
        // And(BvAdd(x, 0), Not(Not(y))) -> And(x, y)
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::And(vec![
            Term::BvAdd(Box::new(x.clone()), Box::new(Term::BitVecLit(0, 32))),
            Term::Not(Box::new(Term::Not(Box::new(y.clone())))),
        ]);
        let simplified = simplify_term(&term);
        // Inner terms should simplify to x and y, leaving And(x, y)
        assert_eq!(simplified, Term::And(vec![x, y]));
    }

    #[test]
    fn test_no_change_already_simplified() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::BvAdd(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BvAdd(Box::new(x), Box::new(y)));
    }

    #[test]
    fn test_script_simplification() {
        let x = Term::Const("x".to_string());
        let original_script = Script::with_commands(vec![
            Command::SetLogic("QF_BV".to_string()),
            Command::DeclareConst("x".to_string(), rust_fv_smtlib::sort::Sort::BitVec(32)),
            Command::Assert(Term::And(vec![Term::BoolLit(true), x.clone()])),
            Command::Assert(Term::BvAdd(
                Box::new(x.clone()),
                Box::new(Term::BitVecLit(0, 32)),
            )),
            Command::CheckSat,
        ]);

        let simplified_script = simplify_script(&original_script);
        let cmds = simplified_script.commands();

        // SetLogic and DeclareConst should be unchanged
        assert!(matches!(cmds[0], Command::SetLogic(_)));
        assert!(matches!(cmds[1], Command::DeclareConst(_, _)));

        // Assert commands should be simplified
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

        // CheckSat should be unchanged
        assert!(matches!(cmds[4], Command::CheckSat));
    }

    #[test]
    fn test_integer_constant_folding() {
        let term = Term::IntAdd(Box::new(Term::IntLit(3)), Box::new(Term::IntLit(5)));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::IntLit(8));
    }

    #[test]
    fn test_integer_identity() {
        let x = Term::Const("x".to_string());
        let term = Term::IntMul(Box::new(x.clone()), Box::new(Term::IntLit(1)));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, x);
    }

    #[test]
    fn test_bvult_constant_folding() {
        let term = Term::BvULt(
            Box::new(Term::BitVecLit(5, 32)),
            Box::new(Term::BitVecLit(10, 32)),
        );
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BoolLit(true));
    }

    #[test]
    fn test_bvslt_constant_folding() {
        // -5 < 10 in 32-bit signed
        let neg5 = (1i128 << 32) - 5; // Two's complement representation
        let term = Term::BvSLt(
            Box::new(Term::BitVecLit(neg5, 32)),
            Box::new(Term::BitVecLit(10, 32)),
        );
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BoolLit(true));
    }
}
