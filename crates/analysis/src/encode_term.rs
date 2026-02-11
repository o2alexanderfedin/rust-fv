/// Encode MIR operations as SMT-LIB terms.
///
/// Each MIR operation is translated to an SMT-LIB term that captures
/// its exact semantics, including overflow and division-by-zero checks.
use rust_fv_smtlib::term::Term;

use crate::ir::{BinOp, Constant, Operand, Place, Ty, UnOp};

/// Encode an operand as an SMT-LIB term.
pub fn encode_operand(op: &Operand) -> Term {
    match op {
        Operand::Copy(place) | Operand::Move(place) => encode_place(place),
        Operand::Constant(c) => encode_constant(c),
    }
}

/// Encode a place (variable reference) as an SMT-LIB constant.
///
/// For now, flattens place projections into a dotted name.
pub fn encode_place(place: &Place) -> Term {
    use crate::ir::Projection;

    if place.projections.is_empty() {
        Term::Const(place.local.clone())
    } else {
        // Flatten projections into a name: `_1.0.deref`
        let mut name = place.local.clone();
        for proj in &place.projections {
            match proj {
                Projection::Deref => name.push_str(".deref"),
                Projection::Field(idx) => {
                    name.push('.');
                    name.push_str(&idx.to_string());
                }
                Projection::Index(idx_local) => {
                    name.push('[');
                    name.push_str(idx_local);
                    name.push(']');
                }
                Projection::Downcast(variant) => {
                    name.push_str(".variant");
                    name.push_str(&variant.to_string());
                }
            }
        }
        Term::Const(name)
    }
}

/// Encode a constant value as an SMT-LIB term.
pub fn encode_constant(c: &Constant) -> Term {
    match c {
        Constant::Bool(b) => Term::BoolLit(*b),
        Constant::Int(val, ity) => Term::BitVecLit(*val, ity.bit_width()),
        Constant::Uint(val, uty) => Term::BitVecLit(*val as i128, uty.bit_width()),
        Constant::Float(_, _) => {
            // Phase 1: floats represented as uninterpreted constants
            Term::Const("FLOAT_UNSUPPORTED".to_string())
        }
        Constant::Unit => Term::BoolLit(true),
        Constant::Str(s) => Term::Const(format!("STR_{s}")),
    }
}

/// Encode a binary operation as an SMT-LIB term.
///
/// Selects signed vs unsigned operations based on the type.
pub fn encode_binop(op: BinOp, lhs: &Term, rhs: &Term, ty: &Ty) -> Term {
    let l = Box::new(lhs.clone());
    let r = Box::new(rhs.clone());
    let signed = ty.is_signed();

    match op {
        BinOp::Add => Term::BvAdd(l, r),
        BinOp::Sub => Term::BvSub(l, r),
        BinOp::Mul => Term::BvMul(l, r),
        BinOp::Div => {
            if signed {
                Term::BvSDiv(l, r)
            } else {
                Term::BvUDiv(l, r)
            }
        }
        BinOp::Rem => {
            if signed {
                Term::BvSRem(l, r)
            } else {
                Term::BvURem(l, r)
            }
        }
        BinOp::BitAnd => Term::BvAnd(l, r),
        BinOp::BitOr => Term::BvOr(l, r),
        BinOp::BitXor => Term::BvXor(l, r),
        BinOp::Shl => Term::BvShl(l, r),
        BinOp::Shr => {
            if signed {
                Term::BvAShr(l, r)
            } else {
                Term::BvLShr(l, r)
            }
        }
        BinOp::Eq => Term::Eq(l, r),
        BinOp::Ne => Term::Not(Box::new(Term::Eq(l, r))),
        BinOp::Lt => {
            if signed {
                Term::BvSLt(l, r)
            } else {
                Term::BvULt(l, r)
            }
        }
        BinOp::Le => {
            if signed {
                Term::BvSLe(l, r)
            } else {
                Term::BvULe(l, r)
            }
        }
        BinOp::Gt => {
            if signed {
                Term::BvSGt(l, r)
            } else {
                Term::BvUGt(l, r)
            }
        }
        BinOp::Ge => {
            if signed {
                Term::BvSGe(l, r)
            } else {
                Term::BvUGe(l, r)
            }
        }
    }
}

/// Encode a unary operation as an SMT-LIB term.
pub fn encode_unop(op: UnOp, operand: &Term, ty: &Ty) -> Term {
    match op {
        UnOp::Not => {
            if ty.is_bool() {
                Term::Not(Box::new(operand.clone()))
            } else {
                // Bitwise NOT for integers
                Term::BvNot(Box::new(operand.clone()))
            }
        }
        UnOp::Neg => Term::BvNeg(Box::new(operand.clone())),
    }
}

// === Overflow checking ===

/// Generate an overflow check for a signed addition.
///
/// Signed addition `a + b` overflows when:
/// - Both positive and result negative (positive overflow)
/// - Both negative and result positive (negative overflow)
///
/// Returns a term that is `true` when overflow DOES NOT occur.
pub fn signed_add_no_overflow(lhs: &Term, rhs: &Term, width: u32) -> Term {
    let result = Term::BvAdd(Box::new(lhs.clone()), Box::new(rhs.clone()));
    let zero = Term::BitVecLit(0, width);

    // lhs >= 0
    let lhs_non_neg = Term::BvSGe(Box::new(lhs.clone()), Box::new(zero.clone()));
    // rhs >= 0
    let rhs_non_neg = Term::BvSGe(Box::new(rhs.clone()), Box::new(zero.clone()));
    // result >= 0
    let result_non_neg = Term::BvSGe(Box::new(result.clone()), Box::new(zero.clone()));

    // lhs < 0
    let lhs_neg = Term::BvSLt(Box::new(lhs.clone()), Box::new(zero.clone()));
    // rhs < 0
    let rhs_neg = Term::BvSLt(Box::new(rhs.clone()), Box::new(zero.clone()));
    // result < 0
    let result_neg = Term::BvSLt(Box::new(result), Box::new(zero));

    // No positive overflow: !(lhs >= 0 && rhs >= 0 && result < 0)
    let no_pos_overflow = Term::Not(Box::new(Term::And(vec![
        lhs_non_neg.clone(),
        rhs_non_neg,
        result_neg,
    ])));

    // No negative overflow: !(lhs < 0 && rhs < 0 && result >= 0)
    let no_neg_overflow = Term::Not(Box::new(Term::And(vec![lhs_neg, rhs_neg, result_non_neg])));

    Term::And(vec![no_pos_overflow, no_neg_overflow])
}

/// Generate an overflow check for unsigned addition.
///
/// Unsigned addition `a + b` overflows when `result < a`.
///
/// Returns a term that is `true` when overflow DOES NOT occur.
pub fn unsigned_add_no_overflow(lhs: &Term, rhs: &Term, _width: u32) -> Term {
    let result = Term::BvAdd(Box::new(lhs.clone()), Box::new(rhs.clone()));
    // result >= lhs means no overflow
    Term::BvUGe(Box::new(result), Box::new(lhs.clone()))
}

/// Generate an overflow check for signed subtraction.
///
/// Returns a term that is `true` when overflow DOES NOT occur.
pub fn signed_sub_no_overflow(lhs: &Term, rhs: &Term, width: u32) -> Term {
    let result = Term::BvSub(Box::new(lhs.clone()), Box::new(rhs.clone()));
    let zero = Term::BitVecLit(0, width);

    let lhs_non_neg = Term::BvSGe(Box::new(lhs.clone()), Box::new(zero.clone()));
    let rhs_neg = Term::BvSLt(Box::new(rhs.clone()), Box::new(zero.clone()));
    let result_neg = Term::BvSLt(Box::new(result.clone()), Box::new(zero.clone()));

    let lhs_neg = Term::BvSLt(Box::new(lhs.clone()), Box::new(zero.clone()));
    let rhs_non_neg = Term::BvSGe(Box::new(rhs.clone()), Box::new(zero.clone()));
    let result_non_neg = Term::BvSGe(Box::new(result), Box::new(zero));

    // No positive overflow: !(lhs >= 0 && rhs < 0 && result < 0)
    let no_pos_overflow = Term::Not(Box::new(Term::And(vec![lhs_non_neg, rhs_neg, result_neg])));

    // No negative overflow: !(lhs < 0 && rhs >= 0 && result >= 0)
    let no_neg_overflow = Term::Not(Box::new(Term::And(vec![
        lhs_neg,
        rhs_non_neg,
        result_non_neg,
    ])));

    Term::And(vec![no_pos_overflow, no_neg_overflow])
}

/// Generate a signed multiplication overflow check.
///
/// Uses sign-extension to double width, multiplies in wider type,
/// then checks that the result fits in the original width.
///
/// Returns a term that is `true` when overflow DOES NOT occur.
pub fn signed_mul_no_overflow(lhs: &Term, rhs: &Term, width: u32) -> Term {
    let ext_lhs = Term::SignExtend(width, Box::new(lhs.clone()));
    let ext_rhs = Term::SignExtend(width, Box::new(rhs.clone()));
    let wide_result = Term::BvMul(Box::new(ext_lhs), Box::new(ext_rhs));

    // Extract the original-width result
    let narrow = Term::Extract(width - 1, 0, Box::new(wide_result.clone()));
    // Sign-extend the narrow result back to double width
    let re_extended = Term::SignExtend(width, Box::new(narrow));

    // No overflow if re-extending gives the same wide result
    Term::Eq(Box::new(wide_result), Box::new(re_extended))
}

/// Generate a division-by-zero check.
///
/// Returns a term that is `true` when the divisor is NOT zero.
pub fn division_not_by_zero(divisor: &Term, width: u32) -> Term {
    let zero = Term::BitVecLit(0, width);
    Term::Not(Box::new(Term::Eq(
        Box::new(divisor.clone()),
        Box::new(zero),
    )))
}

/// Generate a signed division overflow check.
///
/// Signed division overflows only for `INT_MIN / -1`.
///
/// Returns a term that is `true` when overflow DOES NOT occur.
pub fn signed_div_no_overflow(lhs: &Term, rhs: &Term, width: u32) -> Term {
    let min_val = Term::BitVecLit(min_signed_value(width), width);
    let neg_one = Term::BitVecLit(-1, width);

    let is_min = Term::Eq(Box::new(lhs.clone()), Box::new(min_val));
    let is_neg_one = Term::Eq(Box::new(rhs.clone()), Box::new(neg_one));

    // Not (lhs == MIN && rhs == -1)
    Term::Not(Box::new(Term::And(vec![is_min, is_neg_one])))
}

/// Compute the minimum signed value for a given bit width.
fn min_signed_value(width: u32) -> i128 {
    if width >= 128 {
        i128::MIN
    } else {
        -(1i128 << (width - 1))
    }
}

/// Generate an overflow check for a binary operation.
///
/// Returns `Some(term)` where the term is `true` when the operation
/// does NOT overflow, or `None` if the operation cannot overflow.
pub fn overflow_check(op: BinOp, lhs: &Term, rhs: &Term, ty: &Ty) -> Option<Term> {
    let width = ty.bit_width()?;

    match op {
        BinOp::Add => {
            if ty.is_signed() {
                Some(signed_add_no_overflow(lhs, rhs, width))
            } else if ty.is_unsigned() {
                Some(unsigned_add_no_overflow(lhs, rhs, width))
            } else {
                None
            }
        }
        BinOp::Sub => {
            if ty.is_signed() {
                Some(signed_sub_no_overflow(lhs, rhs, width))
            } else {
                // Unsigned sub: no overflow if lhs >= rhs
                Some(Term::BvUGe(Box::new(lhs.clone()), Box::new(rhs.clone())))
            }
        }
        BinOp::Mul => {
            if ty.is_signed() {
                Some(signed_mul_no_overflow(lhs, rhs, width))
            } else {
                // Unsigned mul: use zero-extension approach
                let ext_lhs = Term::ZeroExtend(width, Box::new(lhs.clone()));
                let ext_rhs = Term::ZeroExtend(width, Box::new(rhs.clone()));
                let wide_result = Term::BvMul(Box::new(ext_lhs), Box::new(ext_rhs));
                let narrow = Term::Extract(width - 1, 0, Box::new(wide_result.clone()));
                let re_extended = Term::ZeroExtend(width, Box::new(narrow));
                Some(Term::Eq(Box::new(wide_result), Box::new(re_extended)))
            }
        }
        BinOp::Div | BinOp::Rem => {
            let mut checks = vec![division_not_by_zero(rhs, width)];
            if ty.is_signed() && op == BinOp::Div {
                checks.push(signed_div_no_overflow(lhs, rhs, width));
            }
            Some(Term::And(checks))
        }
        BinOp::Shl | BinOp::Shr => {
            // Shift amount must be less than bit width
            let max_shift = Term::BitVecLit(i128::from(width), width);
            Some(Term::BvULt(Box::new(rhs.clone()), Box::new(max_shift)))
        }
        // Comparison and bitwise ops cannot overflow
        BinOp::Eq
        | BinOp::Ne
        | BinOp::Lt
        | BinOp::Le
        | BinOp::Gt
        | BinOp::Ge
        | BinOp::BitAnd
        | BinOp::BitOr
        | BinOp::BitXor => None,
    }
}

// === Unit tests ===

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Constant, IntTy, Place, UintTy};

    fn var(name: &str) -> Term {
        Term::Const(name.to_string())
    }

    #[test]
    fn encode_bool_constant() {
        let c = Constant::Bool(true);
        assert_eq!(encode_constant(&c), Term::BoolLit(true));
    }

    #[test]
    fn encode_i32_constant() {
        let c = Constant::Int(42, IntTy::I32);
        assert_eq!(encode_constant(&c), Term::BitVecLit(42, 32));
    }

    #[test]
    fn encode_u64_constant() {
        let c = Constant::Uint(100, UintTy::U64);
        assert_eq!(encode_constant(&c), Term::BitVecLit(100, 64));
    }

    #[test]
    fn encode_simple_place() {
        let place = Place {
            local: "_1".to_string(),
            projections: vec![],
        };
        assert_eq!(encode_place(&place), Term::Const("_1".to_string()));
    }

    #[test]
    fn encode_place_with_field() {
        let place = Place::local("_1").field(0);
        assert_eq!(encode_place(&place), Term::Const("_1.0".to_string()));
    }

    #[test]
    fn signed_add_produces_bvadd() {
        let ty = Ty::Int(IntTy::I32);
        let result = encode_binop(BinOp::Add, &var("a"), &var("b"), &ty);
        assert!(matches!(result, Term::BvAdd(_, _)));
    }

    #[test]
    fn unsigned_div_produces_bvudiv() {
        let ty = Ty::Uint(UintTy::U32);
        let result = encode_binop(BinOp::Div, &var("a"), &var("b"), &ty);
        assert!(matches!(result, Term::BvUDiv(_, _)));
    }

    #[test]
    fn signed_div_produces_bvsdiv() {
        let ty = Ty::Int(IntTy::I32);
        let result = encode_binop(BinOp::Div, &var("a"), &var("b"), &ty);
        assert!(matches!(result, Term::BvSDiv(_, _)));
    }

    #[test]
    fn signed_shr_produces_bvashr() {
        let ty = Ty::Int(IntTy::I32);
        let result = encode_binop(BinOp::Shr, &var("a"), &var("b"), &ty);
        assert!(matches!(result, Term::BvAShr(_, _)));
    }

    #[test]
    fn unsigned_shr_produces_bvlshr() {
        let ty = Ty::Uint(UintTy::U32);
        let result = encode_binop(BinOp::Shr, &var("a"), &var("b"), &ty);
        assert!(matches!(result, Term::BvLShr(_, _)));
    }

    #[test]
    fn ne_produces_not_eq() {
        let ty = Ty::Int(IntTy::I32);
        let result = encode_binop(BinOp::Ne, &var("a"), &var("b"), &ty);
        assert!(matches!(result, Term::Not(_)));
    }

    #[test]
    fn not_on_bool_produces_smt_not() {
        let result = encode_unop(UnOp::Not, &var("x"), &Ty::Bool);
        assert!(matches!(result, Term::Not(_)));
    }

    #[test]
    fn not_on_int_produces_bvnot() {
        let result = encode_unop(UnOp::Not, &var("x"), &Ty::Int(IntTy::I32));
        assert!(matches!(result, Term::BvNot(_)));
    }

    #[test]
    fn neg_produces_bvneg() {
        let result = encode_unop(UnOp::Neg, &var("x"), &Ty::Int(IntTy::I32));
        assert!(matches!(result, Term::BvNeg(_)));
    }

    #[test]
    fn overflow_check_add_signed() {
        let ty = Ty::Int(IntTy::I32);
        let check = overflow_check(BinOp::Add, &var("a"), &var("b"), &ty);
        assert!(check.is_some());
    }

    #[test]
    fn overflow_check_add_unsigned() {
        let ty = Ty::Uint(UintTy::U32);
        let check = overflow_check(BinOp::Add, &var("a"), &var("b"), &ty);
        assert!(check.is_some());
    }

    #[test]
    fn overflow_check_div_includes_zero_check() {
        let ty = Ty::Int(IntTy::I32);
        let check = overflow_check(BinOp::Div, &var("a"), &var("b"), &ty);
        assert!(check.is_some());
    }

    #[test]
    fn overflow_check_eq_returns_none() {
        let ty = Ty::Int(IntTy::I32);
        let check = overflow_check(BinOp::Eq, &var("a"), &var("b"), &ty);
        assert!(check.is_none());
    }

    #[test]
    fn overflow_check_bitwise_returns_none() {
        let ty = Ty::Uint(UintTy::U32);
        assert!(overflow_check(BinOp::BitAnd, &var("a"), &var("b"), &ty).is_none());
        assert!(overflow_check(BinOp::BitOr, &var("a"), &var("b"), &ty).is_none());
        assert!(overflow_check(BinOp::BitXor, &var("a"), &var("b"), &ty).is_none());
    }

    #[test]
    fn shift_overflow_check_bounds_shift_amount() {
        let ty = Ty::Uint(UintTy::U32);
        let check = overflow_check(BinOp::Shl, &var("a"), &var("b"), &ty);
        assert!(check.is_some());
        // Should be BvULt(b, 32)
        if let Some(Term::BvULt(_, rhs)) = &check {
            assert_eq!(**rhs, Term::BitVecLit(32, 32));
        } else {
            panic!("Expected BvULt for shift overflow check");
        }
    }

    #[test]
    fn division_not_by_zero_check() {
        let term = division_not_by_zero(&var("d"), 32);
        // Should be Not(Eq(d, 0))
        assert!(matches!(term, Term::Not(_)));
    }

    #[test]
    fn signed_div_overflow_min_neg_one() {
        let term = signed_div_no_overflow(&var("a"), &var("b"), 32);
        // Should be Not(And(a == MIN, b == -1))
        assert!(matches!(term, Term::Not(_)));
    }
}
