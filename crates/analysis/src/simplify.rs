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
        Term::BoolLit(_)
        | Term::IntLit(_)
        | Term::BitVecLit(_, _)
        | Term::Const(_)
        | Term::FpNaN(_, _)
        | Term::FpPosInf(_, _)
        | Term::FpNegInf(_, _)
        | Term::FpPosZero(_, _)
        | Term::FpNegZero(_, _)
        | Term::FpFromBits(_, _, _, _, _)
        | Term::RoundingMode(_) => term.clone(),

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

        // === Floating-point operations (passthrough with recursion) ===
        Term::FpAdd(rm, a, b) => Term::FpAdd(
            Box::new(simplify_term(rm)),
            Box::new(simplify_term(a)),
            Box::new(simplify_term(b)),
        ),
        Term::FpSub(rm, a, b) => Term::FpSub(
            Box::new(simplify_term(rm)),
            Box::new(simplify_term(a)),
            Box::new(simplify_term(b)),
        ),
        Term::FpMul(rm, a, b) => Term::FpMul(
            Box::new(simplify_term(rm)),
            Box::new(simplify_term(a)),
            Box::new(simplify_term(b)),
        ),
        Term::FpDiv(rm, a, b) => Term::FpDiv(
            Box::new(simplify_term(rm)),
            Box::new(simplify_term(a)),
            Box::new(simplify_term(b)),
        ),
        Term::FpSqrt(rm, a) => {
            Term::FpSqrt(Box::new(simplify_term(rm)), Box::new(simplify_term(a)))
        }
        Term::FpAbs(a) => Term::FpAbs(Box::new(simplify_term(a))),
        Term::FpNeg(a) => Term::FpNeg(Box::new(simplify_term(a))),
        Term::FpEq(a, b) => Term::FpEq(Box::new(simplify_term(a)), Box::new(simplify_term(b))),
        Term::FpLt(a, b) => Term::FpLt(Box::new(simplify_term(a)), Box::new(simplify_term(b))),
        Term::FpLeq(a, b) => Term::FpLeq(Box::new(simplify_term(a)), Box::new(simplify_term(b))),
        Term::FpGt(a, b) => Term::FpGt(Box::new(simplify_term(a)), Box::new(simplify_term(b))),
        Term::FpGeq(a, b) => Term::FpGeq(Box::new(simplify_term(a)), Box::new(simplify_term(b))),
        Term::FpIsNaN(a) => Term::FpIsNaN(Box::new(simplify_term(a))),
        Term::FpIsInfinite(a) => Term::FpIsInfinite(Box::new(simplify_term(a))),
        Term::FpIsZero(a) => Term::FpIsZero(Box::new(simplify_term(a))),
        Term::FpIsNegative(a) => Term::FpIsNegative(Box::new(simplify_term(a))),
        Term::FpIsPositive(a) => Term::FpIsPositive(Box::new(simplify_term(a))),

        // === Sequence operations (passthrough with recursion) ===
        Term::SeqEmpty(sort) => Term::SeqEmpty(sort.clone()),
        Term::SeqUnit(a) => Term::SeqUnit(Box::new(simplify_term(a))),
        Term::SeqConcat(a, b) => {
            Term::SeqConcat(Box::new(simplify_term(a)), Box::new(simplify_term(b)))
        }
        Term::SeqLen(a) => Term::SeqLen(Box::new(simplify_term(a))),
        Term::SeqNth(a, b) => Term::SeqNth(Box::new(simplify_term(a)), Box::new(simplify_term(b))),
        Term::SeqExtract(a, b, c) => Term::SeqExtract(
            Box::new(simplify_term(a)),
            Box::new(simplify_term(b)),
            Box::new(simplify_term(c)),
        ),
        Term::SeqContains(a, b) => {
            Term::SeqContains(Box::new(simplify_term(a)), Box::new(simplify_term(b)))
        }
        Term::SeqUpdate(a, b, c) => Term::SeqUpdate(
            Box::new(simplify_term(a)),
            Box::new(simplify_term(b)),
            Box::new(simplify_term(c)),
        ),
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

    // ====== Or: multiple non-literal terms remain (line 71) ======

    #[test]
    fn test_or_multiple_non_literal_terms() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::Or(vec![x.clone(), y.clone()]);
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::Or(vec![x, y]));
    }

    #[test]
    fn test_or_mixed_false_and_multiple_vars() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        // Or(false, x, y) -> Or(x, y) since false is filtered and 2 remain
        let term = Term::Or(vec![Term::BoolLit(false), x.clone(), y.clone()]);
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::Or(vec![x, y]));
    }

    // ====== Implies: non-literal fallthrough (line 87) ======

    #[test]
    fn test_implies_non_literal_passthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::Implies(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::Implies(Box::new(x), Box::new(y)));
    }

    #[test]
    fn test_implies_false_consequent() {
        // Implies(x, false) -> Not(x)
        let x = Term::Const("x".to_string());
        let term = Term::Implies(Box::new(x.clone()), Box::new(Term::BoolLit(false)));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::Not(Box::new(x)));
    }

    // ====== Eq simplification (lines 92-95) ======

    #[test]
    fn test_eq_simplification_with_literals() {
        let term = Term::Eq(Box::new(Term::IntLit(5)), Box::new(Term::IntLit(5)));
        let simplified = simplify_term(&term);
        assert_eq!(
            simplified,
            Term::Eq(Box::new(Term::IntLit(5)), Box::new(Term::IntLit(5)))
        );
    }

    #[test]
    fn test_eq_simplification_with_vars() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::Eq(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::Eq(Box::new(x), Box::new(y)));
    }

    #[test]
    fn test_eq_simplifies_subterms() {
        // Eq(BvAdd(x, 0), y) -> Eq(x, y)
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::Eq(
            Box::new(Term::BvAdd(
                Box::new(x.clone()),
                Box::new(Term::BitVecLit(0, 32)),
            )),
            Box::new(y.clone()),
        );
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::Eq(Box::new(x), Box::new(y)));
    }

    // ====== Ite with non-constant condition (lines 106-111) ======

    #[test]
    fn test_ite_non_constant_condition() {
        let cond = Term::Const("c".to_string());
        let t = Term::IntLit(1);
        let e = Term::IntLit(2);
        let term = Term::Ite(
            Box::new(cond.clone()),
            Box::new(t.clone()),
            Box::new(e.clone()),
        );
        let simplified = simplify_term(&term);
        assert_eq!(
            simplified,
            Term::Ite(Box::new(cond), Box::new(t), Box::new(e))
        );
    }

    #[test]
    fn test_ite_non_constant_simplifies_branches() {
        let cond = Term::Const("c".to_string());
        let t = Term::BvAdd(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::BitVecLit(0, 32)),
        );
        let e = Term::Not(Box::new(Term::Not(Box::new(Term::Const("y".to_string())))));
        let term = Term::Ite(Box::new(cond.clone()), Box::new(t), Box::new(e));
        let simplified = simplify_term(&term);
        assert_eq!(
            simplified,
            Term::Ite(
                Box::new(cond),
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::Const("y".to_string())),
            )
        );
    }

    // ====== BvAdd with width >= 128 (line 125) ======

    #[test]
    fn test_bvadd_large_width_128() {
        let term = Term::BvAdd(
            Box::new(Term::BitVecLit(10, 128)),
            Box::new(Term::BitVecLit(20, 128)),
        );
        let simplified = simplify_term(&term);
        // For width 128, mask = i128::MAX
        let expected = (10i128.wrapping_add(20)) & i128::MAX;
        assert_eq!(simplified, Term::BitVecLit(expected, 128));
    }

    #[test]
    fn test_bvadd_zero_left() {
        let x = Term::Const("x".to_string());
        let term = Term::BvAdd(Box::new(Term::BitVecLit(0, 32)), Box::new(x.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, x);
    }

    // ====== BvSub large width and non-literal fallthrough (lines 147, 156) ======

    #[test]
    fn test_bvsub_large_width_128() {
        let term = Term::BvSub(
            Box::new(Term::BitVecLit(50, 128)),
            Box::new(Term::BitVecLit(20, 128)),
        );
        let simplified = simplify_term(&term);
        let expected = (50i128.wrapping_sub(20)) & i128::MAX;
        assert_eq!(simplified, Term::BitVecLit(expected, 128));
    }

    #[test]
    fn test_bvsub_non_literal_fallthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::BvSub(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BvSub(Box::new(x), Box::new(y)));
    }

    #[test]
    fn test_bvsub_identity_zero() {
        let x = Term::Const("x".to_string());
        let term = Term::BvSub(Box::new(x.clone()), Box::new(Term::BitVecLit(0, 32)));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, x);
    }

    // ====== BvMul large width and non-literal fallthrough (lines 167, 182) ======

    #[test]
    fn test_bvmul_large_width_128() {
        let term = Term::BvMul(
            Box::new(Term::BitVecLit(3, 128)),
            Box::new(Term::BitVecLit(7, 128)),
        );
        let simplified = simplify_term(&term);
        let expected = (3i128.wrapping_mul(7)) & i128::MAX;
        assert_eq!(simplified, Term::BitVecLit(expected, 128));
    }

    #[test]
    fn test_bvmul_non_literal_fallthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::BvMul(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BvMul(Box::new(x), Box::new(y)));
    }

    #[test]
    fn test_bvmul_zero_left() {
        let x = Term::Const("x".to_string());
        let term = Term::BvMul(Box::new(Term::BitVecLit(0, 32)), Box::new(x));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BitVecLit(0, 32));
    }

    #[test]
    fn test_bvmul_one_left() {
        let x = Term::Const("x".to_string());
        let term = Term::BvMul(Box::new(Term::BitVecLit(1, 32)), Box::new(x.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, x);
    }

    // ====== BvSLt large width and non-literal fallthrough (lines 195, 211) ======

    #[test]
    fn test_bvslt_large_width_128() {
        let term = Term::BvSLt(
            Box::new(Term::BitVecLit(5, 128)),
            Box::new(Term::BitVecLit(10, 128)),
        );
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BoolLit(true));
    }

    #[test]
    fn test_bvslt_non_literal_fallthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::BvSLt(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BvSLt(Box::new(x), Box::new(y)));
    }

    #[test]
    fn test_bvslt_false_case() {
        // 10 is not < 5
        let term = Term::BvSLt(
            Box::new(Term::BitVecLit(10, 32)),
            Box::new(Term::BitVecLit(5, 32)),
        );
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BoolLit(false));
    }

    // ====== BvULt large width and non-literal fallthrough (lines 221, 229) ======

    #[test]
    fn test_bvult_large_width_128() {
        let term = Term::BvULt(
            Box::new(Term::BitVecLit(3, 128)),
            Box::new(Term::BitVecLit(100, 128)),
        );
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BoolLit(true));
    }

    #[test]
    fn test_bvult_non_literal_fallthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::BvULt(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BvULt(Box::new(x), Box::new(y)));
    }

    #[test]
    fn test_bvult_false_case() {
        let term = Term::BvULt(
            Box::new(Term::BitVecLit(10, 32)),
            Box::new(Term::BitVecLit(5, 32)),
        );
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BoolLit(false));
    }

    // ====== Passthrough bitvector operations (lines 234-251) ======

    #[test]
    fn test_bvsdiv_passthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::BvSDiv(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BvSDiv(Box::new(x), Box::new(y)));
    }

    #[test]
    fn test_bvudiv_passthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::BvUDiv(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BvUDiv(Box::new(x), Box::new(y)));
    }

    #[test]
    fn test_bvsrem_passthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::BvSRem(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BvSRem(Box::new(x), Box::new(y)));
    }

    #[test]
    fn test_bvurem_passthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::BvURem(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BvURem(Box::new(x), Box::new(y)));
    }

    #[test]
    fn test_bvneg_passthrough() {
        let x = Term::Const("x".to_string());
        let term = Term::BvNeg(Box::new(x.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BvNeg(Box::new(x)));
    }

    #[test]
    fn test_bvsle_passthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::BvSLe(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BvSLe(Box::new(x), Box::new(y)));
    }

    #[test]
    fn test_bvsgt_passthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::BvSGt(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BvSGt(Box::new(x), Box::new(y)));
    }

    #[test]
    fn test_bvsge_passthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::BvSGe(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BvSGe(Box::new(x), Box::new(y)));
    }

    #[test]
    fn test_bvule_passthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::BvULe(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BvULe(Box::new(x), Box::new(y)));
    }

    #[test]
    fn test_bvugt_passthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::BvUGt(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BvUGt(Box::new(x), Box::new(y)));
    }

    #[test]
    fn test_bvuge_passthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::BvUGe(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BvUGe(Box::new(x), Box::new(y)));
    }

    #[test]
    fn test_bvand_passthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::BvAnd(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BvAnd(Box::new(x), Box::new(y)));
    }

    #[test]
    fn test_bvor_passthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::BvOr(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BvOr(Box::new(x), Box::new(y)));
    }

    #[test]
    fn test_bvxor_passthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::BvXor(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BvXor(Box::new(x), Box::new(y)));
    }

    #[test]
    fn test_bvnot_passthrough() {
        let x = Term::Const("x".to_string());
        let term = Term::BvNot(Box::new(x.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BvNot(Box::new(x)));
    }

    #[test]
    fn test_bvshl_passthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::BvShl(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BvShl(Box::new(x), Box::new(y)));
    }

    #[test]
    fn test_bvlshr_passthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::BvLShr(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BvLShr(Box::new(x), Box::new(y)));
    }

    #[test]
    fn test_bvashr_passthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::BvAShr(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BvAShr(Box::new(x), Box::new(y)));
    }

    // ====== Bitvector conversion passthroughs (lines 254-259) ======

    #[test]
    fn test_zero_extend_passthrough() {
        let x = Term::Const("x".to_string());
        let term = Term::ZeroExtend(16, Box::new(x.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::ZeroExtend(16, Box::new(x)));
    }

    #[test]
    fn test_sign_extend_passthrough() {
        let x = Term::Const("x".to_string());
        let term = Term::SignExtend(16, Box::new(x.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::SignExtend(16, Box::new(x)));
    }

    #[test]
    fn test_extract_passthrough() {
        let x = Term::Const("x".to_string());
        let term = Term::Extract(31, 0, Box::new(x.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::Extract(31, 0, Box::new(x)));
    }

    #[test]
    fn test_concat_passthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::Concat(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::Concat(Box::new(x), Box::new(y)));
    }

    #[test]
    fn test_bv2int_passthrough() {
        let x = Term::Const("x".to_string());
        let term = Term::Bv2Int(Box::new(x.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::Bv2Int(Box::new(x)));
    }

    #[test]
    fn test_int2bv_passthrough() {
        let x = Term::Const("x".to_string());
        let term = Term::Int2Bv(32, Box::new(x.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::Int2Bv(32, Box::new(x)));
    }

    // ====== IntAdd non-literal fallthrough (line 269) ======

    #[test]
    fn test_intadd_non_literal_fallthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::IntAdd(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::IntAdd(Box::new(x), Box::new(y)));
    }

    #[test]
    fn test_intadd_zero_left() {
        let x = Term::Const("x".to_string());
        let term = Term::IntAdd(Box::new(Term::IntLit(0)), Box::new(x.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, x);
    }

    // ====== IntSub identity and fallthrough (lines 277-278) ======

    #[test]
    fn test_intsub_identity_zero() {
        let x = Term::Const("x".to_string());
        let term = Term::IntSub(Box::new(x.clone()), Box::new(Term::IntLit(0)));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, x);
    }

    #[test]
    fn test_intsub_non_literal_fallthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::IntSub(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::IntSub(Box::new(x), Box::new(y)));
    }

    #[test]
    fn test_intsub_constant_folding() {
        let term = Term::IntSub(Box::new(Term::IntLit(10)), Box::new(Term::IntLit(3)));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::IntLit(7));
    }

    // ====== IntMul non-literal fallthrough (line 289) ======

    #[test]
    fn test_intmul_non_literal_fallthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::IntMul(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::IntMul(Box::new(x), Box::new(y)));
    }

    #[test]
    fn test_intmul_zero_left() {
        let x = Term::Const("x".to_string());
        let term = Term::IntMul(Box::new(Term::IntLit(0)), Box::new(x));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::IntLit(0));
    }

    #[test]
    fn test_intmul_one_left() {
        let x = Term::Const("x".to_string());
        let term = Term::IntMul(Box::new(Term::IntLit(1)), Box::new(x.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, x);
    }

    // ====== IntDiv and IntMod passthrough (lines 292-293) ======

    #[test]
    fn test_intdiv_passthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::IntDiv(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::IntDiv(Box::new(x), Box::new(y)));
    }

    #[test]
    fn test_intmod_passthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::IntMod(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::IntMod(Box::new(x), Box::new(y)));
    }

    // ====== IntNeg non-literal fallthrough (line 298) ======

    #[test]
    fn test_intneg_constant_folding() {
        let term = Term::IntNeg(Box::new(Term::IntLit(42)));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::IntLit(-42));
    }

    #[test]
    fn test_intneg_non_literal_fallthrough() {
        let x = Term::Const("x".to_string());
        let term = Term::IntNeg(Box::new(x.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::IntNeg(Box::new(x)));
    }

    // ====== IntLt non-literal fallthrough (line 306) ======

    #[test]
    fn test_intlt_constant_folding_true() {
        let term = Term::IntLt(Box::new(Term::IntLit(3)), Box::new(Term::IntLit(5)));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BoolLit(true));
    }

    #[test]
    fn test_intlt_constant_folding_false() {
        let term = Term::IntLt(Box::new(Term::IntLit(5)), Box::new(Term::IntLit(3)));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BoolLit(false));
    }

    #[test]
    fn test_intlt_non_literal_fallthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::IntLt(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::IntLt(Box::new(x), Box::new(y)));
    }

    // ====== IntLe non-literal fallthrough (line 314) ======

    #[test]
    fn test_intle_constant_folding_true() {
        let term = Term::IntLe(Box::new(Term::IntLit(5)), Box::new(Term::IntLit(5)));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BoolLit(true));
    }

    #[test]
    fn test_intle_non_literal_fallthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::IntLe(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::IntLe(Box::new(x), Box::new(y)));
    }

    // ====== IntGt non-literal fallthrough (line 322) ======

    #[test]
    fn test_intgt_constant_folding_true() {
        let term = Term::IntGt(Box::new(Term::IntLit(10)), Box::new(Term::IntLit(5)));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BoolLit(true));
    }

    #[test]
    fn test_intgt_non_literal_fallthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::IntGt(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::IntGt(Box::new(x), Box::new(y)));
    }

    // ====== IntGe non-literal fallthrough (line 330) ======

    #[test]
    fn test_intge_constant_folding_true() {
        let term = Term::IntGe(Box::new(Term::IntLit(5)), Box::new(Term::IntLit(5)));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BoolLit(true));
    }

    #[test]
    fn test_intge_constant_folding_false() {
        let term = Term::IntGe(Box::new(Term::IntLit(3)), Box::new(Term::IntLit(5)));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BoolLit(false));
    }

    #[test]
    fn test_intge_non_literal_fallthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::IntGe(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::IntGe(Box::new(x), Box::new(y)));
    }

    // ====== Select (line 335) ======

    #[test]
    fn test_select_passthrough() {
        let arr = Term::Const("arr".to_string());
        let idx = Term::IntLit(0);
        let term = Term::Select(Box::new(arr.clone()), Box::new(idx.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::Select(Box::new(arr), Box::new(idx)));
    }

    #[test]
    fn test_select_simplifies_subterms() {
        let arr = Term::Const("arr".to_string());
        let idx = Term::IntAdd(Box::new(Term::IntLit(0)), Box::new(Term::IntLit(5)));
        let term = Term::Select(Box::new(arr.clone()), Box::new(idx));
        let simplified = simplify_term(&term);
        assert_eq!(
            simplified,
            Term::Select(Box::new(arr), Box::new(Term::IntLit(5)))
        );
    }

    // ====== Store (lines 337-339) ======

    #[test]
    fn test_store_passthrough() {
        let arr = Term::Const("arr".to_string());
        let idx = Term::IntLit(0);
        let val = Term::IntLit(42);
        let term = Term::Store(
            Box::new(arr.clone()),
            Box::new(idx.clone()),
            Box::new(val.clone()),
        );
        let simplified = simplify_term(&term);
        assert_eq!(
            simplified,
            Term::Store(Box::new(arr), Box::new(idx), Box::new(val))
        );
    }

    #[test]
    fn test_store_simplifies_subterms() {
        let arr = Term::Const("arr".to_string());
        let idx = Term::IntAdd(Box::new(Term::IntLit(1)), Box::new(Term::IntLit(2)));
        let val = Term::IntMul(Box::new(Term::IntLit(3)), Box::new(Term::IntLit(4)));
        let term = Term::Store(Box::new(arr.clone()), Box::new(idx), Box::new(val));
        let simplified = simplify_term(&term);
        assert_eq!(
            simplified,
            Term::Store(
                Box::new(arr),
                Box::new(Term::IntLit(3)),
                Box::new(Term::IntLit(12)),
            )
        );
    }

    // ====== Forall and Exists (lines 344-345) ======

    #[test]
    fn test_forall_simplifies_body() {
        use rust_fv_smtlib::sort::Sort;
        let body = Term::Not(Box::new(Term::Not(Box::new(Term::Const("x".to_string())))));
        let bindings = vec![("x".to_string(), Sort::Bool)];
        let term = Term::Forall(bindings.clone(), Box::new(body));
        let simplified = simplify_term(&term);
        assert_eq!(
            simplified,
            Term::Forall(bindings, Box::new(Term::Const("x".to_string())))
        );
    }

    #[test]
    fn test_exists_simplifies_body() {
        use rust_fv_smtlib::sort::Sort;
        let body = Term::IntAdd(
            Box::new(Term::IntLit(0)),
            Box::new(Term::Const("x".to_string())),
        );
        let bindings = vec![("x".to_string(), Sort::Int)];
        let term = Term::Exists(bindings.clone(), Box::new(body));
        let simplified = simplify_term(&term);
        assert_eq!(
            simplified,
            Term::Exists(bindings, Box::new(Term::Const("x".to_string())))
        );
    }

    // ====== Let (lines 347-352) ======

    #[test]
    fn test_let_simplifies_bindings_and_body() {
        let binding_val = Term::IntAdd(Box::new(Term::IntLit(1)), Box::new(Term::IntLit(2)));
        let body = Term::Not(Box::new(Term::Not(Box::new(Term::Const("y".to_string())))));
        let bindings = vec![("x".to_string(), binding_val)];
        let term = Term::Let(bindings, Box::new(body));
        let simplified = simplify_term(&term);
        assert_eq!(
            simplified,
            Term::Let(
                vec![("x".to_string(), Term::IntLit(3))],
                Box::new(Term::Const("y".to_string())),
            )
        );
    }

    #[test]
    fn test_let_multiple_bindings() {
        let bindings = vec![
            ("a".to_string(), Term::IntLit(5)),
            (
                "b".to_string(),
                Term::BvAdd(
                    Box::new(Term::Const("c".to_string())),
                    Box::new(Term::BitVecLit(0, 32)),
                ),
            ),
        ];
        let body = Term::Const("a".to_string());
        let term = Term::Let(bindings, Box::new(body.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(
            simplified,
            Term::Let(
                vec![
                    ("a".to_string(), Term::IntLit(5)),
                    ("b".to_string(), Term::Const("c".to_string())),
                ],
                Box::new(body),
            )
        );
    }

    // ====== App (lines 354-356) ======

    #[test]
    fn test_app_simplifies_args() {
        let args = vec![
            Term::IntAdd(Box::new(Term::IntLit(1)), Box::new(Term::IntLit(2))),
            Term::Const("y".to_string()),
        ];
        let term = Term::App("f".to_string(), args);
        let simplified = simplify_term(&term);
        assert_eq!(
            simplified,
            Term::App(
                "f".to_string(),
                vec![Term::IntLit(3), Term::Const("y".to_string())],
            )
        );
    }

    #[test]
    fn test_app_no_args() {
        let term = Term::App("g".to_string(), vec![]);
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::App("g".to_string(), vec![]));
    }

    // ====== Annotated (lines 358-368) ======

    #[test]
    fn test_annotated_simplifies_body_and_values() {
        let body = Term::Not(Box::new(Term::Not(Box::new(Term::Const("x".to_string())))));
        let annotation_val = Term::IntAdd(Box::new(Term::IntLit(1)), Box::new(Term::IntLit(2)));
        let annotations = vec![("pattern".to_string(), vec![annotation_val])];
        let term = Term::Annotated(Box::new(body), annotations);
        let simplified = simplify_term(&term);
        assert_eq!(
            simplified,
            Term::Annotated(
                Box::new(Term::Const("x".to_string())),
                vec![("pattern".to_string(), vec![Term::IntLit(3)])],
            )
        );
    }

    #[test]
    fn test_annotated_multiple_annotations() {
        let body = Term::Const("x".to_string());
        let annotations = vec![
            ("key1".to_string(), vec![Term::BoolLit(true)]),
            (
                "key2".to_string(),
                vec![
                    Term::IntAdd(Box::new(Term::IntLit(0)), Box::new(Term::IntLit(7))),
                    Term::Const("y".to_string()),
                ],
            ),
        ];
        let term = Term::Annotated(Box::new(body.clone()), annotations);
        let simplified = simplify_term(&term);
        assert_eq!(
            simplified,
            Term::Annotated(
                Box::new(body),
                vec![
                    ("key1".to_string(), vec![Term::BoolLit(true)]),
                    (
                        "key2".to_string(),
                        vec![Term::IntLit(7), Term::Const("y".to_string())],
                    ),
                ],
            )
        );
    }

    #[test]
    fn test_annotated_empty_annotation_values() {
        let body = Term::Const("x".to_string());
        let annotations = vec![("named".to_string(), vec![])];
        let term = Term::Annotated(Box::new(body.clone()), annotations);
        let simplified = simplify_term(&term);
        assert_eq!(
            simplified,
            Term::Annotated(Box::new(body), vec![("named".to_string(), vec![])],)
        );
    }

    // ====== Iff (line 372) ======

    #[test]
    fn test_iff_passthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::Iff(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::Iff(Box::new(x), Box::new(y)));
    }

    #[test]
    fn test_iff_simplifies_subterms() {
        let a = Term::Not(Box::new(Term::Not(Box::new(Term::Const("x".to_string())))));
        let b = Term::IntAdd(
            Box::new(Term::IntLit(0)),
            Box::new(Term::Const("y".to_string())),
        );
        let term = Term::Iff(Box::new(a), Box::new(b));
        let simplified = simplify_term(&term);
        assert_eq!(
            simplified,
            Term::Iff(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::Const("y".to_string())),
            )
        );
    }

    // ====== Distinct (lines 373-375) ======

    #[test]
    fn test_distinct_passthrough() {
        let x = Term::Const("x".to_string());
        let y = Term::Const("y".to_string());
        let term = Term::Distinct(vec![x.clone(), y.clone()]);
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::Distinct(vec![x, y]));
    }

    #[test]
    fn test_distinct_simplifies_subterms() {
        let a = Term::IntAdd(Box::new(Term::IntLit(1)), Box::new(Term::IntLit(2)));
        let b = Term::Const("y".to_string());
        let term = Term::Distinct(vec![a, b.clone()]);
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::Distinct(vec![Term::IntLit(3), b]));
    }

    // ====== Additional edge cases for improved coverage ======

    #[test]
    fn test_not_variable_passthrough() {
        let x = Term::Const("x".to_string());
        let term = Term::Not(Box::new(x.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::Not(Box::new(x)));
    }

    #[test]
    fn test_and_empty() {
        let term = Term::And(vec![]);
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BoolLit(true));
    }

    #[test]
    fn test_or_empty() {
        let term = Term::Or(vec![]);
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BoolLit(false));
    }

    #[test]
    fn test_and_single_after_filter() {
        // And(true, x) -> x (single element after filtering true)
        let x = Term::Const("x".to_string());
        let term = Term::And(vec![Term::BoolLit(true), x.clone(), Term::BoolLit(true)]);
        let simplified = simplify_term(&term);
        assert_eq!(simplified, x);
    }

    #[test]
    fn test_or_single_after_filter() {
        // Or(false, x) -> x (single element after filtering false)
        let x = Term::Const("x".to_string());
        let term = Term::Or(vec![Term::BoolLit(false), x.clone(), Term::BoolLit(false)]);
        let simplified = simplify_term(&term);
        assert_eq!(simplified, x);
    }

    #[test]
    fn test_literal_passthrough() {
        assert_eq!(simplify_term(&Term::BoolLit(true)), Term::BoolLit(true));
        assert_eq!(simplify_term(&Term::BoolLit(false)), Term::BoolLit(false));
        assert_eq!(simplify_term(&Term::IntLit(42)), Term::IntLit(42));
        assert_eq!(
            simplify_term(&Term::BitVecLit(255, 8)),
            Term::BitVecLit(255, 8)
        );
        assert_eq!(
            simplify_term(&Term::Const("x".to_string())),
            Term::Const("x".to_string())
        );
    }

    #[test]
    fn test_bvsub_zero_right() {
        let x = Term::Const("x".to_string());
        let term = Term::BvSub(Box::new(x.clone()), Box::new(Term::BitVecLit(0, 64)));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, x);
    }

    #[test]
    fn test_bvslt_equal_values() {
        // 5 is not < 5
        let term = Term::BvSLt(
            Box::new(Term::BitVecLit(5, 32)),
            Box::new(Term::BitVecLit(5, 32)),
        );
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BoolLit(false));
    }

    #[test]
    fn test_bvult_equal_values() {
        let term = Term::BvULt(
            Box::new(Term::BitVecLit(5, 32)),
            Box::new(Term::BitVecLit(5, 32)),
        );
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BoolLit(false));
    }

    #[test]
    fn test_intadd_zero_right() {
        let x = Term::Const("x".to_string());
        let term = Term::IntAdd(Box::new(x.clone()), Box::new(Term::IntLit(0)));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, x);
    }

    #[test]
    fn test_intmul_constant_folding() {
        let term = Term::IntMul(Box::new(Term::IntLit(6)), Box::new(Term::IntLit(7)));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::IntLit(42));
    }

    #[test]
    fn test_intmul_zero_right() {
        let x = Term::Const("x".to_string());
        let term = Term::IntMul(Box::new(x), Box::new(Term::IntLit(0)));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::IntLit(0));
    }

    #[test]
    fn test_intmul_one_right() {
        let x = Term::Const("x".to_string());
        let term = Term::IntMul(Box::new(x.clone()), Box::new(Term::IntLit(1)));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, x);
    }

    #[test]
    fn test_bvneg_simplifies_subterm() {
        // BvNeg(BvAdd(x, 0)) -> BvNeg(x)
        let x = Term::Const("x".to_string());
        let inner = Term::BvAdd(Box::new(x.clone()), Box::new(Term::BitVecLit(0, 32)));
        let term = Term::BvNeg(Box::new(inner));
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::BvNeg(Box::new(x)));
    }

    #[test]
    fn test_zero_extend_simplifies_subterm() {
        let inner = Term::BvAdd(
            Box::new(Term::BitVecLit(1, 16)),
            Box::new(Term::BitVecLit(2, 16)),
        );
        let term = Term::ZeroExtend(16, Box::new(inner));
        let simplified = simplify_term(&term);
        assert_eq!(
            simplified,
            Term::ZeroExtend(16, Box::new(Term::BitVecLit(3, 16)))
        );
    }

    #[test]
    fn test_deeply_nested_simplification() {
        // IntAdd(IntAdd(IntLit(1), IntLit(2)), IntMul(IntLit(3), IntLit(1)))
        // -> IntAdd(IntLit(3), IntLit(3)) -> IntLit(6)
        let term = Term::IntAdd(
            Box::new(Term::IntAdd(
                Box::new(Term::IntLit(1)),
                Box::new(Term::IntLit(2)),
            )),
            Box::new(Term::IntMul(
                Box::new(Term::IntLit(3)),
                Box::new(Term::IntLit(1)),
            )),
        );
        let simplified = simplify_term(&term);
        assert_eq!(simplified, Term::IntLit(6));
    }

    #[test]
    fn test_intdiv_simplifies_subterms() {
        let a = Term::IntAdd(Box::new(Term::IntLit(1)), Box::new(Term::IntLit(2)));
        let b = Term::Const("x".to_string());
        let term = Term::IntDiv(Box::new(a), Box::new(b.clone()));
        let simplified = simplify_term(&term);
        assert_eq!(
            simplified,
            Term::IntDiv(Box::new(Term::IntLit(3)), Box::new(b))
        );
    }

    #[test]
    fn test_intmod_simplifies_subterms() {
        let a = Term::Const("x".to_string());
        let b = Term::IntAdd(Box::new(Term::IntLit(2)), Box::new(Term::IntLit(3)));
        let term = Term::IntMod(Box::new(a.clone()), Box::new(b));
        let simplified = simplify_term(&term);
        assert_eq!(
            simplified,
            Term::IntMod(Box::new(a), Box::new(Term::IntLit(5)))
        );
    }
}
