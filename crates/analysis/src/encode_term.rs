/// Encode MIR operations as SMT-LIB terms.
///
/// Each MIR operation is translated to an SMT-LIB term that captures
/// its exact semantics, including overflow and division-by-zero checks.
use rust_fv_smtlib::term::Term;

use crate::ir::{
    AggregateKind, BinOp, CastKind, Constant, FloatTy, Function, IntTy, Operand, Place, Projection,
    Ty, UintTy, UnOp,
};

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

/// Encode a place with projections resolved using type information.
///
/// For struct field access: applies selector function `Term::App("{Type}-{field}", [base])`
/// For tuple field access: applies selector function `Term::App("Tuple{N}-_{idx}", [base])`
/// For array index access: applies `Term::Select(base, index)`
/// For deref: transparent (same as inner)
pub fn encode_place_with_type(place: &Place, func: &Function) -> Option<Term> {
    if place.projections.is_empty() {
        return Some(Term::Const(place.local.clone()));
    }

    let mut current = Term::Const(place.local.clone());
    let mut current_ty = find_local_type(func, &place.local)?;

    for proj in &place.projections {
        match proj {
            Projection::Field(idx) => {
                current = encode_field_access(current, current_ty, *idx)?;
                // Update current_ty to the field's type
                current_ty = get_field_type(current_ty, *idx)?;
            }
            Projection::Index(idx_local) => {
                let index_term = Term::Const(idx_local.clone());
                current = Term::Select(Box::new(current), Box::new(index_term));
                // Update current_ty to the element type
                current_ty = get_element_type(current_ty)?;
            }
            Projection::Deref => {
                // References are transparent
                if let Ty::Ref(inner, _) = current_ty {
                    current_ty = inner;
                }
            }
            Projection::Downcast(_variant_idx) => {
                // Enum downcast is handled during pattern matching
                // The type doesn't change here
            }
        }
    }

    Some(current)
}

/// Encode struct/tuple field access as a selector application.
pub fn encode_field_access(base: Term, ty: &Ty, field_idx: usize) -> Option<Term> {
    match ty {
        Ty::Struct(name, fields) => {
            let field_name = &fields.get(field_idx)?.0;
            let selector = format!("{name}-{field_name}");
            Some(Term::App(selector, vec![base]))
        }
        Ty::Tuple(fields) => {
            if field_idx < fields.len() {
                let selector = format!("Tuple{}-_{field_idx}", fields.len());
                Some(Term::App(selector, vec![base]))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Encode aggregate construction as a constructor application.
pub fn encode_aggregate(kind: &AggregateKind, operands: &[Operand]) -> Option<Term> {
    let encoded_ops: Vec<Term> = operands.iter().map(encode_operand).collect();

    match kind {
        AggregateKind::Struct(name) => {
            let constructor = format!("mk-{name}");
            Some(Term::App(constructor, encoded_ops))
        }
        AggregateKind::Tuple => {
            let n = operands.len();
            if n == 0 {
                // Unit tuple -> Bool true
                return Some(Term::BoolLit(true));
            }
            let constructor = format!("mk-Tuple{n}");
            Some(Term::App(constructor, encoded_ops))
        }
        AggregateKind::Enum(_name, variant_idx) => {
            // For enums, we need the variant name from the type.
            // For now, use a generic constructor with variant index.
            // In practice, the caller should provide the variant name from
            // the type definition. We use a placeholder pattern.
            let constructor = format!("mk-variant-{variant_idx}");
            Some(Term::App(constructor, encoded_ops))
        }
        AggregateKind::Closure(name) => {
            // Closure environment construction
            let constructor = format!("mk-{name}");
            Some(Term::App(constructor, encoded_ops))
        }
    }
}

/// Encode aggregate construction with full type information.
///
/// For enum variants, uses the type to resolve the variant name.
pub fn encode_aggregate_with_type(
    kind: &AggregateKind,
    operands: &[Operand],
    result_ty: &Ty,
) -> Option<Term> {
    let encoded_ops: Vec<Term> = operands.iter().map(encode_operand).collect();

    match kind {
        AggregateKind::Struct(name) => {
            let constructor = format!("mk-{name}");
            Some(Term::App(constructor, encoded_ops))
        }
        AggregateKind::Tuple => {
            let n = operands.len();
            if n == 0 {
                return Some(Term::BoolLit(true));
            }
            let constructor = format!("mk-Tuple{n}");
            Some(Term::App(constructor, encoded_ops))
        }
        AggregateKind::Enum(_name, variant_idx) => {
            if let Ty::Enum(_enum_name, variants) = result_ty
                && let Some((variant_name, _)) = variants.get(*variant_idx)
            {
                let constructor = format!("mk-{variant_name}");
                return Some(Term::App(constructor, encoded_ops));
            }
            // Fallback: use variant index
            let constructor = format!("mk-variant-{variant_idx}");
            Some(Term::App(constructor, encoded_ops))
        }
        AggregateKind::Closure(name) => {
            // Closure environment construction (same as Struct)
            let constructor = format!("mk-{name}");
            Some(Term::App(constructor, encoded_ops))
        }
    }
}

/// Get the type of a field at the given index.
fn get_field_type(ty: &Ty, idx: usize) -> Option<&Ty> {
    match ty {
        Ty::Struct(_, fields) => fields.get(idx).map(|(_, ty)| ty),
        Ty::Tuple(fields) => fields.get(idx),
        _ => None,
    }
}

/// Get the element type of an array or slice.
fn get_element_type(ty: &Ty) -> Option<&Ty> {
    match ty {
        Ty::Array(elem, _) | Ty::Slice(elem) => Some(elem),
        _ => None,
    }
}

/// Find the type of a local variable by name.
fn find_local_type<'a>(func: &'a Function, name: &str) -> Option<&'a Ty> {
    if func.return_local.name == name {
        return Some(&func.return_local.ty);
    }
    for p in &func.params {
        if p.name == name {
            return Some(&p.ty);
        }
    }
    for l in &func.locals {
        if l.name == name {
            return Some(&l.ty);
        }
    }
    None
}

/// Encode a float constant as an SMT-LIB floating-point term.
///
/// IEEE 754 encoding:
/// - f32: 8-bit exponent, 24-bit significand (eb=8, sb=24)
/// - f64: 11-bit exponent, 53-bit significand (eb=11, sb=53)
pub fn encode_float_constant(value: f64, fty: FloatTy) -> Term {
    let (eb, sb) = match fty {
        FloatTy::F32 => (8, 24),
        FloatTy::F64 => (11, 53),
    };

    // Special values
    if value.is_nan() {
        return Term::FpNaN(eb, sb);
    }
    if value.is_infinite() {
        return if value.is_sign_positive() {
            Term::FpPosInf(eb, sb)
        } else {
            Term::FpNegInf(eb, sb)
        };
    }
    if value == 0.0 {
        return if value.is_sign_positive() {
            Term::FpPosZero(eb, sb)
        } else {
            Term::FpNegZero(eb, sb)
        };
    }

    // Normal values: convert to bit representation
    let bits = match fty {
        FloatTy::F32 => {
            let f32_val = value as f32;
            f32_val.to_bits() as u64
        }
        FloatTy::F64 => value.to_bits(),
    };

    // Extract sign, exponent, significand
    let (sign_bit, exp_bits, sig_bits) = match fty {
        FloatTy::F32 => {
            // f32: 1 sign + 8 exp + 23 mantissa
            let sign = ((bits >> 31) & 1) as u8;
            let exp = (bits >> 23) & 0xFF;
            let sig = bits & 0x7FFFFF;
            (sign, exp, sig)
        }
        FloatTy::F64 => {
            // f64: 1 sign + 11 exp + 52 mantissa
            let sign = ((bits >> 63) & 1) as u8;
            let exp = (bits >> 52) & 0x7FF;
            let sig = bits & 0xFFFFFFFFFFFFF;
            (sign, exp, sig)
        }
    };

    Term::FpFromBits(sign_bit, exp_bits, sig_bits, eb, sb)
}

/// Encode a constant value as an SMT-LIB term.
pub fn encode_constant(c: &Constant) -> Term {
    match c {
        Constant::Bool(b) => Term::BoolLit(*b),
        Constant::Int(val, ity) => Term::BitVecLit(*val, ity.bit_width()),
        Constant::Uint(val, uty) => Term::BitVecLit(*val as i128, uty.bit_width()),
        Constant::Float(value, fty) => encode_float_constant(*value, *fty),
        Constant::Unit => Term::BoolLit(true),
        Constant::Str(s) => Term::Const(format!("STR_{s}")),
    }
}

/// Encode floating-point binary operations.
///
/// For arithmetic operations (Add, Sub, Mul, Div), uses RNE (Round to Nearest, ties to Even) rounding mode.
/// For comparisons, uses IEEE 754 semantics (FpEq, FpLt, etc.).
pub fn encode_fp_binop(op: BinOp, lhs: &Term, rhs: &Term) -> Term {
    let l = Box::new(lhs.clone());
    let r = Box::new(rhs.clone());

    match op {
        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => {
            let rm = Box::new(Term::RoundingMode("RNE".to_string()));
            match op {
                BinOp::Add => Term::FpAdd(rm, l, r),
                BinOp::Sub => Term::FpSub(rm, l, r),
                BinOp::Mul => Term::FpMul(rm, l, r),
                BinOp::Div => Term::FpDiv(rm, l, r),
                _ => unreachable!(),
            }
        }
        BinOp::Eq => Term::FpEq(l, r),
        BinOp::Ne => Term::Not(Box::new(Term::FpEq(l, r))),
        BinOp::Lt => Term::FpLt(l, r),
        BinOp::Le => Term::FpLeq(l, r),
        BinOp::Gt => Term::FpGt(l, r),
        BinOp::Ge => Term::FpGeq(l, r),
        BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr | BinOp::Rem => {
            panic!("unsupported float binop: {op:?}")
        }
    }
}

/// Encode floating-point unary operations.
pub fn encode_fp_unop(op: UnOp, operand: &Term) -> Term {
    match op {
        UnOp::Neg => Term::FpNeg(Box::new(operand.clone())),
        UnOp::Not => panic!("Not operation is not valid for float types"),
    }
}

/// Encode a binary operation as an SMT-LIB term.
///
/// Selects signed vs unsigned operations based on the type.
pub fn encode_binop(op: BinOp, lhs: &Term, rhs: &Term, ty: &Ty) -> Term {
    // Dispatch to float encoding for float types
    if matches!(ty, Ty::Float(_)) {
        return encode_fp_binop(op, lhs, rhs);
    }

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
    // Dispatch to float encoding for float types
    if matches!(ty, Ty::Float(_)) {
        return encode_fp_unop(op, operand);
    }

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
            if ty.is_signed() {
                // Both signed division AND signed remainder overflow for INT_MIN / -1.
                // In Rust, `i32::MIN % -1` panics because the underlying division overflows.
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

// === Cast encoding ===

/// Returns the bit width of a Rust numeric type, or 64 as default for pointers/unknown.
pub fn ty_bit_width(ty: &Ty) -> u32 {
    match ty {
        Ty::Int(int_ty) => match int_ty {
            IntTy::I8 => 8,
            IntTy::I16 => 16,
            IntTy::I32 => 32,
            IntTy::I64 => 64,
            IntTy::I128 => 128,
            IntTy::Isize => 64,
        },
        Ty::Uint(uint_ty) => match uint_ty {
            UintTy::U8 => 8,
            UintTy::U16 => 16,
            UintTy::U32 => 32,
            UintTy::U64 => 64,
            UintTy::U128 => 128,
            UintTy::Usize => 64,
        },
        Ty::Float(float_ty) => match float_ty {
            FloatTy::F32 => 32,
            FloatTy::F64 => 64,
        },
        _ => 64, // pointer default (conservative)
    }
}

/// Returns true if the type is a signed integer type.
pub fn ty_is_signed(ty: &Ty) -> bool {
    matches!(ty, Ty::Int(_))
}

/// Encode a Rust `as` cast or `transmute` as an SMT-LIB term.
///
/// `kind`: the cast kind from IR
/// `src`: the already-encoded source operand term
/// `from_bits`: bit width of source type (from `ty_bit_width(source_ty)`)
/// `to_bits`: bit width of target type
/// `from_signed`: whether source integer type is signed
pub fn encode_cast(
    kind: &CastKind,
    src: Term,
    from_bits: u32,
    to_bits: u32,
    from_signed: bool,
) -> Term {
    match kind {
        CastKind::IntToInt => encode_int_to_int_cast(src, from_bits, to_bits, from_signed),
        CastKind::IntToFloat => encode_int_to_float_cast(src, from_bits, to_bits, from_signed),
        CastKind::FloatToInt => encode_float_to_int_cast(src, from_bits, to_bits),
        CastKind::FloatToFloat => encode_float_to_float_cast(src, from_bits, to_bits),
        // Pointer casts: identity on bitvector (pointer is BitVec 64)
        CastKind::Pointer => src,
    }
}

/// Integer-to-integer cast: widening (zero/sign extend) or narrowing (extract low bits).
pub fn encode_int_to_int_cast(src: Term, from_bits: u32, to_bits: u32, from_signed: bool) -> Term {
    use std::cmp::Ordering;
    match from_bits.cmp(&to_bits) {
        Ordering::Equal => src, // no-op cast (reinterpret, same width)
        Ordering::Less => {
            if from_signed {
                Term::SignExtend(to_bits - from_bits, Box::new(src))
            } else {
                Term::ZeroExtend(to_bits - from_bits, Box::new(src))
            }
        }
        Ordering::Greater => Term::Extract(to_bits - 1, 0, Box::new(src)),
    }
}

/// Integer-to-float cast: reinterpret bitvector as float using SMT-LIB to_fp.
///
/// Models transmute semantics: reinterpret the source BV bits as float.
/// Uses Term::App to represent `((_ to_fp eb sb) RNE src_bv)`.
fn encode_int_to_float_cast(src: Term, from_bits: u32, to_bits: u32, from_signed: bool) -> Term {
    // Ensure source is the right bit width for the target float
    let adjusted = if from_bits == to_bits {
        src
    } else {
        encode_int_to_int_cast(src, from_bits, to_bits, from_signed)
    };
    // SMT-LIB: ((_ to_fp eb sb) RNE adjusted)
    // For f32: eb=8, sb=24; for f64: eb=11, sb=53
    let (eb, sb) = float_params(to_bits);
    Term::App(
        format!("(_ to_fp {eb} {sb})"),
        vec![Term::RoundingMode("RNE".to_string()), adjusted],
    )
}

/// Float-to-integer cast: extract lower bits from the float bitvector.
///
/// Conservative approximation: model as extraction of the lower to_bits.
/// TODO Phase 29: proper round-to-zero conversion.
fn encode_float_to_int_cast(src: Term, _from_bits: u32, to_bits: u32) -> Term {
    Term::Extract(to_bits - 1, 0, Box::new(src))
}

/// Float-to-float cast (f32 <-> f64): identity for same size, FpFromBits after adjustment otherwise.
fn encode_float_to_float_cast(src: Term, from_bits: u32, to_bits: u32) -> Term {
    if from_bits == to_bits {
        src
    } else {
        // Use to_fp for float width conversion
        let (eb, sb) = float_params(to_bits);
        Term::App(
            format!("(_ to_fp {eb} {sb})"),
            vec![Term::RoundingMode("RNE".to_string()), src],
        )
    }
}

/// Returns (exponent_bits, significand_bits) for a float of the given bit width.
fn float_params(bits: u32) -> (u32, u32) {
    match bits {
        32 => (8, 24),
        64 => (11, 53),
        _ => (11, 53), // default to f64 params
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

    // === Audit item tests (Plan 01-02) ===

    #[test]
    fn overflow_check_signed_rem_includes_overflow_check() {
        // Audit item 10: signed Rem must include INT_MIN % -1 overflow check
        let ty = Ty::Int(IntTy::I32);
        let check = overflow_check(BinOp::Rem, &var("a"), &var("b"), &ty);
        assert!(check.is_some(), "Signed Rem should produce overflow check");
        // Should be And([div-by-zero-check, signed-div-overflow-check])
        if let Some(Term::And(parts)) = &check {
            assert_eq!(
                parts.len(),
                2,
                "Signed Rem should have 2 checks: div-by-zero + INT_MIN%-1 overflow"
            );
        } else {
            panic!("Expected And term for signed Rem overflow check, got: {check:?}");
        }
    }

    #[test]
    fn overflow_check_unsigned_rem_no_overflow_check() {
        // Unsigned Rem only has div-by-zero, no INT_MIN overflow
        let ty = Ty::Uint(UintTy::U32);
        let check = overflow_check(BinOp::Rem, &var("a"), &var("b"), &ty);
        assert!(
            check.is_some(),
            "Unsigned Rem should produce overflow check"
        );
        // Should be And([div-by-zero-check]) -- just one element
        if let Some(Term::And(parts)) = &check {
            assert_eq!(
                parts.len(),
                1,
                "Unsigned Rem should have only div-by-zero check"
            );
        } else {
            panic!("Expected And term for unsigned Rem overflow check, got: {check:?}");
        }
    }

    #[test]
    fn overflow_check_signed_div_includes_both_checks() {
        // Audit item 8: signed Div must include both div-by-zero and INT_MIN/-1
        let ty = Ty::Int(IntTy::I32);
        let check = overflow_check(BinOp::Div, &var("a"), &var("b"), &ty);
        assert!(check.is_some());
        if let Some(Term::And(parts)) = &check {
            assert_eq!(
                parts.len(),
                2,
                "Signed Div should have 2 checks: div-by-zero + INT_MIN/-1 overflow"
            );
        } else {
            panic!("Expected And term for signed Div overflow check, got: {check:?}");
        }
    }

    #[test]
    fn overflow_check_unsigned_div_only_zero_check() {
        // Unsigned Div only has div-by-zero
        let ty = Ty::Uint(UintTy::U32);
        let check = overflow_check(BinOp::Div, &var("a"), &var("b"), &ty);
        assert!(check.is_some());
        if let Some(Term::And(parts)) = &check {
            assert_eq!(
                parts.len(),
                1,
                "Unsigned Div should have only div-by-zero check"
            );
        } else {
            panic!("Expected And term for unsigned Div overflow check, got: {check:?}");
        }
    }

    #[test]
    fn min_signed_value_all_widths() {
        // Audit item: verify min_signed_value is correct for all widths
        assert_eq!(min_signed_value(8), -128);
        assert_eq!(min_signed_value(16), -32768);
        assert_eq!(min_signed_value(32), -2_147_483_648);
        assert_eq!(min_signed_value(64), -9_223_372_036_854_775_808);
        assert_eq!(min_signed_value(128), i128::MIN);
    }

    #[test]
    fn overflow_check_sub_signed() {
        // Audit item 3: signed subtraction overflow check exists
        let ty = Ty::Int(IntTy::I32);
        let check = overflow_check(BinOp::Sub, &var("a"), &var("b"), &ty);
        assert!(check.is_some(), "Signed Sub should produce overflow check");
    }

    #[test]
    fn overflow_check_sub_unsigned() {
        // Audit item 4: unsigned subtraction underflow check (lhs >= rhs)
        let ty = Ty::Uint(UintTy::U32);
        let check = overflow_check(BinOp::Sub, &var("a"), &var("b"), &ty);
        assert!(
            check.is_some(),
            "Unsigned Sub should produce overflow check"
        );
        // Should be BvUGe(lhs, rhs)
        assert!(
            matches!(check, Some(Term::BvUGe(_, _))),
            "Unsigned sub overflow check should be BvUGe(lhs, rhs)"
        );
    }

    #[test]
    fn overflow_check_mul_signed() {
        // Audit item 5: signed multiplication overflow uses sign-extension
        let ty = Ty::Int(IntTy::I32);
        let check = overflow_check(BinOp::Mul, &var("a"), &var("b"), &ty);
        assert!(check.is_some(), "Signed Mul should produce overflow check");
        // Should be Eq(wide_result, re_extended)
        assert!(
            matches!(check, Some(Term::Eq(_, _))),
            "Signed mul overflow check should be Eq(wide, re_extended)"
        );
    }

    #[test]
    fn overflow_check_mul_unsigned() {
        // Audit item 6: unsigned multiplication overflow uses zero-extension
        let ty = Ty::Uint(UintTy::U32);
        let check = overflow_check(BinOp::Mul, &var("a"), &var("b"), &ty);
        assert!(
            check.is_some(),
            "Unsigned Mul should produce overflow check"
        );
        assert!(
            matches!(check, Some(Term::Eq(_, _))),
            "Unsigned mul overflow check should be Eq(wide, re_extended)"
        );
    }

    #[test]
    fn overflow_check_shr_bounds_shift_amount() {
        // Audit item 9: shift bounds check for Shr as well
        let ty = Ty::Uint(UintTy::U32);
        let check = overflow_check(BinOp::Shr, &var("a"), &var("b"), &ty);
        assert!(check.is_some(), "Shr should produce overflow check");
        if let Some(Term::BvULt(_, rhs)) = &check {
            assert_eq!(**rhs, Term::BitVecLit(32, 32));
        } else {
            panic!("Expected BvULt for shift overflow check");
        }
    }

    // ====== Coverage: encode_place with projections (lines 30, 35-38, 40-42) ======

    #[test]
    fn encode_place_with_deref_projection() {
        let place = Place::local("_1").deref();
        assert_eq!(encode_place(&place), Term::Const("_1.deref".to_string()));
    }

    #[test]
    fn encode_place_with_index_projection() {
        let place = Place::local("_1").index("_2".to_string());
        assert_eq!(encode_place(&place), Term::Const("_1[_2]".to_string()));
    }

    #[test]
    fn encode_place_with_downcast_projection() {
        let place = Place {
            local: "_1".to_string(),
            projections: vec![Projection::Downcast(3)],
        };
        assert_eq!(encode_place(&place), Term::Const("_1.variant3".to_string()));
    }

    #[test]
    fn encode_place_with_multiple_projections() {
        // deref then field then index
        let place = Place {
            local: "_1".to_string(),
            projections: vec![
                Projection::Deref,
                Projection::Field(2),
                Projection::Index("idx".to_string()),
            ],
        };
        assert_eq!(
            encode_place(&place),
            Term::Const("_1.deref.2[idx]".to_string())
        );
    }

    #[test]
    fn encode_place_with_downcast_then_field() {
        let place = Place {
            local: "_1".to_string(),
            projections: vec![Projection::Downcast(0), Projection::Field(1)],
        };
        assert_eq!(
            encode_place(&place),
            Term::Const("_1.variant0.1".to_string())
        );
    }

    // ====== Coverage: encode_operand (lines 12-13) ======

    #[test]
    fn encode_operand_copy() {
        let op = Operand::Copy(Place::local("_1"));
        assert_eq!(encode_operand(&op), Term::Const("_1".to_string()));
    }

    #[test]
    fn encode_operand_move() {
        let op = Operand::Move(Place::local("_2"));
        assert_eq!(encode_operand(&op), Term::Const("_2".to_string()));
    }

    #[test]
    fn encode_operand_constant() {
        let op = Operand::Constant(Constant::Bool(false));
        assert_eq!(encode_operand(&op), Term::BoolLit(false));
    }

    // ====== Coverage: encode_constant (lines 222, 224-225) ======

    #[test]
    fn encode_float_constant_2_71() {
        let c = Constant::Float(2.71, crate::ir::FloatTy::F64);
        // Should produce FpFromBits, not FLOAT_UNSUPPORTED
        assert!(matches!(
            encode_constant(&c),
            Term::FpFromBits(_, _, _, 11, 53)
        ));
    }

    #[test]
    fn encode_unit_constant() {
        let c = Constant::Unit;
        assert_eq!(encode_constant(&c), Term::BoolLit(true));
    }

    #[test]
    fn encode_str_constant() {
        let c = Constant::Str("hello".to_string());
        assert_eq!(encode_constant(&c), Term::Const("STR_hello".to_string()));
    }

    // ====== Coverage: encode_binop remaining variants (lines 240, 252, 255-258, 272, 276-277, 279, 293) ======

    #[test]
    fn binop_mul_produces_bvmul() {
        let ty = Ty::Int(IntTy::I32);
        let result = encode_binop(BinOp::Mul, &var("a"), &var("b"), &ty);
        assert!(matches!(result, Term::BvMul(_, _)));
    }

    #[test]
    fn binop_signed_rem_produces_bvsrem() {
        let ty = Ty::Int(IntTy::I32);
        let result = encode_binop(BinOp::Rem, &var("a"), &var("b"), &ty);
        assert!(matches!(result, Term::BvSRem(_, _)));
    }

    #[test]
    fn binop_unsigned_rem_produces_bvurem() {
        let ty = Ty::Uint(UintTy::U32);
        let result = encode_binop(BinOp::Rem, &var("a"), &var("b"), &ty);
        assert!(matches!(result, Term::BvURem(_, _)));
    }

    #[test]
    fn binop_bitand_produces_bvand() {
        let ty = Ty::Uint(UintTy::U32);
        let result = encode_binop(BinOp::BitAnd, &var("a"), &var("b"), &ty);
        assert!(matches!(result, Term::BvAnd(_, _)));
    }

    #[test]
    fn binop_bitor_produces_bvor() {
        let ty = Ty::Int(IntTy::I32);
        let result = encode_binop(BinOp::BitOr, &var("a"), &var("b"), &ty);
        assert!(matches!(result, Term::BvOr(_, _)));
    }

    #[test]
    fn binop_bitxor_produces_bvxor() {
        let ty = Ty::Uint(UintTy::U64);
        let result = encode_binop(BinOp::BitXor, &var("a"), &var("b"), &ty);
        assert!(matches!(result, Term::BvXor(_, _)));
    }

    #[test]
    fn binop_shl_produces_bvshl() {
        let ty = Ty::Uint(UintTy::U32);
        let result = encode_binop(BinOp::Shl, &var("a"), &var("b"), &ty);
        assert!(matches!(result, Term::BvShl(_, _)));
    }

    #[test]
    fn binop_unsigned_lt_produces_bvult() {
        let ty = Ty::Uint(UintTy::U32);
        let result = encode_binop(BinOp::Lt, &var("a"), &var("b"), &ty);
        assert!(matches!(result, Term::BvULt(_, _)));
    }

    #[test]
    fn binop_signed_lt_produces_bvslt() {
        let ty = Ty::Int(IntTy::I32);
        let result = encode_binop(BinOp::Lt, &var("a"), &var("b"), &ty);
        assert!(matches!(result, Term::BvSLt(_, _)));
    }

    #[test]
    fn binop_signed_le_produces_bvsle() {
        let ty = Ty::Int(IntTy::I32);
        let result = encode_binop(BinOp::Le, &var("a"), &var("b"), &ty);
        assert!(matches!(result, Term::BvSLe(_, _)));
    }

    #[test]
    fn binop_unsigned_le_produces_bvule() {
        let ty = Ty::Uint(UintTy::U32);
        let result = encode_binop(BinOp::Le, &var("a"), &var("b"), &ty);
        assert!(matches!(result, Term::BvULe(_, _)));
    }

    #[test]
    fn binop_signed_gt_produces_bvsgt() {
        let ty = Ty::Int(IntTy::I32);
        let result = encode_binop(BinOp::Gt, &var("a"), &var("b"), &ty);
        assert!(matches!(result, Term::BvSGt(_, _)));
    }

    #[test]
    fn binop_unsigned_gt_produces_bvugt() {
        let ty = Ty::Uint(UintTy::U32);
        let result = encode_binop(BinOp::Gt, &var("a"), &var("b"), &ty);
        assert!(matches!(result, Term::BvUGt(_, _)));
    }

    #[test]
    fn binop_signed_ge_produces_bvsge() {
        let ty = Ty::Int(IntTy::I32);
        let result = encode_binop(BinOp::Ge, &var("a"), &var("b"), &ty);
        assert!(matches!(result, Term::BvSGe(_, _)));
    }

    #[test]
    fn binop_unsigned_ge_produces_bvuge() {
        let ty = Ty::Uint(UintTy::U32);
        let result = encode_binop(BinOp::Ge, &var("a"), &var("b"), &ty);
        assert!(matches!(result, Term::BvUGe(_, _)));
    }

    #[test]
    fn binop_eq_produces_eq() {
        let ty = Ty::Int(IntTy::I32);
        let result = encode_binop(BinOp::Eq, &var("a"), &var("b"), &ty);
        assert!(matches!(result, Term::Eq(_, _)));
    }

    #[test]
    fn binop_sub_produces_bvsub() {
        let ty = Ty::Int(IntTy::I32);
        let result = encode_binop(BinOp::Sub, &var("a"), &var("b"), &ty);
        assert!(matches!(result, Term::BvSub(_, _)));
    }

    // ====== Coverage: overflow_check Add on non-integer type returns None (line 463) ======

    #[test]
    fn overflow_check_add_on_bool_returns_none() {
        let ty = Ty::Bool;
        let check = overflow_check(BinOp::Add, &var("a"), &var("b"), &ty);
        // Bool has bit_width = Some(1), but is neither signed nor unsigned
        assert!(check.is_none());
    }

    // ====== Coverage: overflow_check remaining no-overflow ops (Ne, Lt, Le, Gt, Ge) ======

    #[test]
    fn overflow_check_ne_returns_none() {
        let ty = Ty::Int(IntTy::I32);
        assert!(overflow_check(BinOp::Ne, &var("a"), &var("b"), &ty).is_none());
    }

    #[test]
    fn overflow_check_lt_returns_none() {
        let ty = Ty::Int(IntTy::I32);
        assert!(overflow_check(BinOp::Lt, &var("a"), &var("b"), &ty).is_none());
    }

    #[test]
    fn overflow_check_le_returns_none() {
        let ty = Ty::Int(IntTy::I32);
        assert!(overflow_check(BinOp::Le, &var("a"), &var("b"), &ty).is_none());
    }

    #[test]
    fn overflow_check_gt_returns_none() {
        let ty = Ty::Int(IntTy::I32);
        assert!(overflow_check(BinOp::Gt, &var("a"), &var("b"), &ty).is_none());
    }

    #[test]
    fn overflow_check_ge_returns_none() {
        let ty = Ty::Int(IntTy::I32);
        assert!(overflow_check(BinOp::Ge, &var("a"), &var("b"), &ty).is_none());
    }

    // ====== Coverage: encode_field_access (lines 94-99, 101-104, 106, 109) ======

    #[test]
    fn encode_field_access_struct() {
        let ty = Ty::Struct(
            "Point".to_string(),
            vec![
                ("x".to_string(), Ty::Int(IntTy::I32)),
                ("y".to_string(), Ty::Int(IntTy::I32)),
            ],
        );
        let result = encode_field_access(var("p"), &ty, 0);
        assert_eq!(
            result,
            Some(Term::App("Point-x".to_string(), vec![var("p")]))
        );
    }

    #[test]
    fn encode_field_access_struct_second_field() {
        let ty = Ty::Struct(
            "Point".to_string(),
            vec![
                ("x".to_string(), Ty::Int(IntTy::I32)),
                ("y".to_string(), Ty::Int(IntTy::I32)),
            ],
        );
        let result = encode_field_access(var("p"), &ty, 1);
        assert_eq!(
            result,
            Some(Term::App("Point-y".to_string(), vec![var("p")]))
        );
    }

    #[test]
    fn encode_field_access_struct_out_of_bounds() {
        let ty = Ty::Struct(
            "Point".to_string(),
            vec![("x".to_string(), Ty::Int(IntTy::I32))],
        );
        let result = encode_field_access(var("p"), &ty, 5);
        assert_eq!(result, None);
    }

    #[test]
    fn encode_field_access_tuple() {
        let ty = Ty::Tuple(vec![Ty::Int(IntTy::I32), Ty::Bool]);
        let result = encode_field_access(var("t"), &ty, 0);
        assert_eq!(
            result,
            Some(Term::App("Tuple2-_0".to_string(), vec![var("t")]))
        );
    }

    #[test]
    fn encode_field_access_tuple_second_field() {
        let ty = Ty::Tuple(vec![Ty::Int(IntTy::I32), Ty::Bool]);
        let result = encode_field_access(var("t"), &ty, 1);
        assert_eq!(
            result,
            Some(Term::App("Tuple2-_1".to_string(), vec![var("t")]))
        );
    }

    #[test]
    fn encode_field_access_tuple_out_of_bounds() {
        let ty = Ty::Tuple(vec![Ty::Int(IntTy::I32)]);
        let result = encode_field_access(var("t"), &ty, 3);
        assert_eq!(result, None);
    }

    #[test]
    fn encode_field_access_non_struct_returns_none() {
        let ty = Ty::Int(IntTy::I32);
        let result = encode_field_access(var("x"), &ty, 0);
        assert_eq!(result, None);
    }

    #[test]
    fn encode_field_access_bool_returns_none() {
        let ty = Ty::Bool;
        let result = encode_field_access(var("b"), &ty, 0);
        assert_eq!(result, None);
    }

    // ====== Coverage: encode_aggregate (lines 114-115, 117-120, 123-124, 126, 128-129, 131, 136-137) ======

    #[test]
    fn encode_aggregate_struct() {
        let kind = AggregateKind::Struct("Point".to_string());
        let ops = vec![
            Operand::Constant(Constant::Int(1, IntTy::I32)),
            Operand::Constant(Constant::Int(2, IntTy::I32)),
        ];
        let result = encode_aggregate(&kind, &ops);
        assert_eq!(
            result,
            Some(Term::App(
                "mk-Point".to_string(),
                vec![Term::BitVecLit(1, 32), Term::BitVecLit(2, 32)]
            ))
        );
    }

    #[test]
    fn encode_aggregate_tuple_two_elements() {
        let kind = AggregateKind::Tuple;
        let ops = vec![
            Operand::Constant(Constant::Int(10, IntTy::I32)),
            Operand::Constant(Constant::Bool(true)),
        ];
        let result = encode_aggregate(&kind, &ops);
        assert_eq!(
            result,
            Some(Term::App(
                "mk-Tuple2".to_string(),
                vec![Term::BitVecLit(10, 32), Term::BoolLit(true)]
            ))
        );
    }

    #[test]
    fn encode_aggregate_unit_tuple() {
        let kind = AggregateKind::Tuple;
        let ops: Vec<Operand> = vec![];
        let result = encode_aggregate(&kind, &ops);
        assert_eq!(result, Some(Term::BoolLit(true)));
    }

    #[test]
    fn encode_aggregate_single_tuple() {
        let kind = AggregateKind::Tuple;
        let ops = vec![Operand::Constant(Constant::Bool(false))];
        let result = encode_aggregate(&kind, &ops);
        assert_eq!(
            result,
            Some(Term::App(
                "mk-Tuple1".to_string(),
                vec![Term::BoolLit(false)]
            ))
        );
    }

    #[test]
    fn encode_aggregate_enum_variant() {
        let kind = AggregateKind::Enum("Option".to_string(), 1);
        let ops = vec![Operand::Constant(Constant::Int(42, IntTy::I32))];
        let result = encode_aggregate(&kind, &ops);
        assert_eq!(
            result,
            Some(Term::App(
                "mk-variant-1".to_string(),
                vec![Term::BitVecLit(42, 32)]
            ))
        );
    }

    #[test]
    fn encode_aggregate_enum_variant_no_fields() {
        let kind = AggregateKind::Enum("Option".to_string(), 0);
        let ops: Vec<Operand> = vec![];
        let result = encode_aggregate(&kind, &ops);
        assert_eq!(result, Some(Term::App("mk-variant-0".to_string(), vec![])));
    }

    // ====== Coverage: encode_aggregate_with_type (lines 160, 165-167, 169-170, 173-174) ======

    #[test]
    fn encode_aggregate_with_type_struct() {
        let kind = AggregateKind::Struct("Point".to_string());
        let ops = vec![
            Operand::Constant(Constant::Int(1, IntTy::I32)),
            Operand::Constant(Constant::Int(2, IntTy::I32)),
        ];
        let result_ty = Ty::Struct(
            "Point".to_string(),
            vec![
                ("x".to_string(), Ty::Int(IntTy::I32)),
                ("y".to_string(), Ty::Int(IntTy::I32)),
            ],
        );
        let result = encode_aggregate_with_type(&kind, &ops, &result_ty);
        assert_eq!(
            result,
            Some(Term::App(
                "mk-Point".to_string(),
                vec![Term::BitVecLit(1, 32), Term::BitVecLit(2, 32)]
            ))
        );
    }

    #[test]
    fn encode_aggregate_with_type_unit_tuple() {
        let kind = AggregateKind::Tuple;
        let ops: Vec<Operand> = vec![];
        let result_ty = Ty::Unit;
        let result = encode_aggregate_with_type(&kind, &ops, &result_ty);
        assert_eq!(result, Some(Term::BoolLit(true)));
    }

    #[test]
    fn encode_aggregate_with_type_tuple() {
        let kind = AggregateKind::Tuple;
        let ops = vec![
            Operand::Constant(Constant::Int(1, IntTy::I32)),
            Operand::Constant(Constant::Bool(true)),
        ];
        let result_ty = Ty::Tuple(vec![Ty::Int(IntTy::I32), Ty::Bool]);
        let result = encode_aggregate_with_type(&kind, &ops, &result_ty);
        assert_eq!(
            result,
            Some(Term::App(
                "mk-Tuple2".to_string(),
                vec![Term::BitVecLit(1, 32), Term::BoolLit(true)]
            ))
        );
    }

    #[test]
    fn encode_aggregate_with_type_enum_variant_resolved() {
        // Enum with type info resolves variant name
        let kind = AggregateKind::Enum("Option".to_string(), 1);
        let ops = vec![Operand::Constant(Constant::Int(42, IntTy::I32))];
        let result_ty = Ty::Enum(
            "Option".to_string(),
            vec![
                ("None".to_string(), vec![]),
                ("Some".to_string(), vec![Ty::Int(IntTy::I32)]),
            ],
        );
        let result = encode_aggregate_with_type(&kind, &ops, &result_ty);
        assert_eq!(
            result,
            Some(Term::App(
                "mk-Some".to_string(),
                vec![Term::BitVecLit(42, 32)]
            ))
        );
    }

    #[test]
    fn encode_aggregate_with_type_enum_variant_fallback() {
        // Enum variant out of bounds falls back to generic constructor
        let kind = AggregateKind::Enum("Option".to_string(), 5);
        let ops: Vec<Operand> = vec![];
        let result_ty = Ty::Enum(
            "Option".to_string(),
            vec![
                ("None".to_string(), vec![]),
                ("Some".to_string(), vec![Ty::Int(IntTy::I32)]),
            ],
        );
        let result = encode_aggregate_with_type(&kind, &ops, &result_ty);
        assert_eq!(result, Some(Term::App("mk-variant-5".to_string(), vec![])));
    }

    #[test]
    fn encode_aggregate_with_type_enum_non_enum_type_fallback() {
        // If result_ty is not Enum, falls back to generic constructor
        let kind = AggregateKind::Enum("Foo".to_string(), 0);
        let ops = vec![Operand::Constant(Constant::Bool(true))];
        let result_ty = Ty::Int(IntTy::I32); // Not an Enum type
        let result = encode_aggregate_with_type(&kind, &ops, &result_ty);
        assert_eq!(
            result,
            Some(Term::App(
                "mk-variant-0".to_string(),
                vec![Term::BoolLit(true)]
            ))
        );
    }

    // ====== Coverage: encode_place_with_type + find_local_type + get_field_type + get_element_type
    //        (lines 56-58, 61-62, 64-67, 69, 71-73, 75, 79-80, 83, 90,
    //         180-184, 189-192, 197-199, 201-203, 206-208, 211) ======

    use crate::ir::{BasicBlock, Contracts, Function, Local, Mutability, Terminator};

    /// Helper to build a minimal Function for encode_place_with_type tests.
    fn make_func(params: Vec<Local>, locals: Vec<Local>, return_ty: Ty) -> Function {
        Function {
            name: "test_fn".to_string(),
            params,
            return_local: Local::new("_0", return_ty),
            locals,
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

    #[test]
    fn encode_place_with_type_no_projections() {
        let func = make_func(
            vec![Local::new("_1", Ty::Int(IntTy::I32))],
            vec![],
            Ty::Int(IntTy::I32),
        );
        let place = Place::local("_1");
        let result = encode_place_with_type(&place, &func);
        assert_eq!(result, Some(Term::Const("_1".to_string())));
    }

    #[test]
    fn encode_place_with_type_struct_field() {
        let struct_ty = Ty::Struct(
            "Point".to_string(),
            vec![
                ("x".to_string(), Ty::Int(IntTy::I32)),
                ("y".to_string(), Ty::Int(IntTy::I32)),
            ],
        );
        let func = make_func(
            vec![Local::new("_1", struct_ty)],
            vec![],
            Ty::Int(IntTy::I32),
        );
        let place = Place::local("_1").field(0);
        let result = encode_place_with_type(&place, &func);
        assert_eq!(
            result,
            Some(Term::App(
                "Point-x".to_string(),
                vec![Term::Const("_1".to_string())]
            ))
        );
    }

    #[test]
    fn encode_place_with_type_tuple_field() {
        let tuple_ty = Ty::Tuple(vec![Ty::Int(IntTy::I32), Ty::Bool]);
        let func = make_func(
            vec![Local::new("_1", tuple_ty)],
            vec![],
            Ty::Int(IntTy::I32),
        );
        let place = Place::local("_1").field(1);
        let result = encode_place_with_type(&place, &func);
        assert_eq!(
            result,
            Some(Term::App(
                "Tuple2-_1".to_string(),
                vec![Term::Const("_1".to_string())]
            ))
        );
    }

    #[test]
    fn encode_place_with_type_index_projection() {
        let array_ty = Ty::Array(Box::new(Ty::Int(IntTy::I32)), 10);
        let func = make_func(
            vec![Local::new("_1", array_ty)],
            vec![],
            Ty::Int(IntTy::I32),
        );
        let place = Place::local("_1").index("idx".to_string());
        let result = encode_place_with_type(&place, &func);
        assert_eq!(
            result,
            Some(Term::Select(
                Box::new(Term::Const("_1".to_string())),
                Box::new(Term::Const("idx".to_string()))
            ))
        );
    }

    #[test]
    fn encode_place_with_type_deref_ref() {
        let ref_ty = Ty::Ref(Box::new(Ty::Int(IntTy::I32)), Mutability::Shared);
        let func = make_func(vec![Local::new("_1", ref_ty)], vec![], Ty::Int(IntTy::I32));
        let place = Place::local("_1").deref();
        let result = encode_place_with_type(&place, &func);
        // Deref is transparent for references
        assert_eq!(result, Some(Term::Const("_1".to_string())));
    }

    #[test]
    fn encode_place_with_type_deref_non_ref() {
        // Deref on non-ref type (e.g., raw pointer behavior)
        let func = make_func(
            vec![Local::new("_1", Ty::Int(IntTy::I32))],
            vec![],
            Ty::Int(IntTy::I32),
        );
        let place = Place::local("_1").deref();
        let result = encode_place_with_type(&place, &func);
        // Deref on non-ref is a no-op (doesn't change current)
        assert_eq!(result, Some(Term::Const("_1".to_string())));
    }

    #[test]
    fn encode_place_with_type_downcast_projection() {
        let enum_ty = Ty::Enum(
            "Option".to_string(),
            vec![
                ("None".to_string(), vec![]),
                ("Some".to_string(), vec![Ty::Int(IntTy::I32)]),
            ],
        );
        let func = make_func(vec![Local::new("_1", enum_ty)], vec![], Ty::Int(IntTy::I32));
        let place = Place {
            local: "_1".to_string(),
            projections: vec![Projection::Downcast(1)],
        };
        let result = encode_place_with_type(&place, &func);
        // Downcast doesn't change the term, just keeps current
        assert_eq!(result, Some(Term::Const("_1".to_string())));
    }

    #[test]
    fn encode_place_with_type_unknown_local_returns_none() {
        let func = make_func(
            vec![Local::new("_1", Ty::Int(IntTy::I32))],
            vec![],
            Ty::Int(IntTy::I32),
        );
        let place = Place::local("_unknown").field(0);
        let result = encode_place_with_type(&place, &func);
        assert_eq!(result, None);
    }

    #[test]
    fn encode_place_with_type_return_local() {
        // Tests find_local_type finding the return local
        let func = make_func(vec![], vec![], Ty::Int(IntTy::I32));
        let place = Place::local("_0");
        let result = encode_place_with_type(&place, &func);
        assert_eq!(result, Some(Term::Const("_0".to_string())));
    }

    #[test]
    fn encode_place_with_type_in_locals() {
        // Tests find_local_type finding a local variable
        let func = make_func(
            vec![],
            vec![Local::new("_3", Ty::Int(IntTy::I32))],
            Ty::Unit,
        );
        let place = Place::local("_3");
        let result = encode_place_with_type(&place, &func);
        assert_eq!(result, Some(Term::Const("_3".to_string())));
    }

    #[test]
    fn encode_place_with_type_locals_with_field() {
        // Tests find_local_type via locals vec + field projection
        let struct_ty = Ty::Struct(
            "Pair".to_string(),
            vec![
                ("a".to_string(), Ty::Bool),
                ("b".to_string(), Ty::Int(IntTy::I32)),
            ],
        );
        let func = make_func(vec![], vec![Local::new("_5", struct_ty)], Ty::Unit);
        let place = Place::local("_5").field(1);
        let result = encode_place_with_type(&place, &func);
        assert_eq!(
            result,
            Some(Term::App(
                "Pair-b".to_string(),
                vec![Term::Const("_5".to_string())]
            ))
        );
    }

    #[test]
    fn find_local_type_returns_none_for_absent_name() {
        let func = make_func(
            vec![Local::new("_1", Ty::Bool)],
            vec![Local::new("_2", Ty::Int(IntTy::I32))],
            Ty::Unit,
        );
        // Access a place with projections for an unknown local
        let place = Place::local("_99").field(0);
        let result = encode_place_with_type(&place, &func);
        assert_eq!(result, None);
    }

    // ====== Coverage: get_field_type edge cases ======

    #[test]
    fn encode_place_with_type_field_out_of_bounds_returns_none() {
        let struct_ty = Ty::Struct("S".to_string(), vec![("x".to_string(), Ty::Bool)]);
        let func = make_func(vec![Local::new("_1", struct_ty)], vec![], Ty::Unit);
        let place = Place::local("_1").field(5); // out of bounds
        let result = encode_place_with_type(&place, &func);
        assert_eq!(result, None);
    }

    #[test]
    fn encode_place_with_type_field_on_non_struct_returns_none() {
        let func = make_func(
            vec![Local::new("_1", Ty::Int(IntTy::I32))],
            vec![],
            Ty::Unit,
        );
        let place = Place::local("_1").field(0); // field on Int - invalid
        let result = encode_place_with_type(&place, &func);
        assert_eq!(result, None);
    }

    // ====== Coverage: get_element_type edge cases ======

    #[test]
    fn encode_place_with_type_index_on_slice() {
        let slice_ty = Ty::Slice(Box::new(Ty::Bool));
        let func = make_func(vec![Local::new("_1", slice_ty)], vec![], Ty::Unit);
        let place = Place::local("_1").index("i".to_string());
        let result = encode_place_with_type(&place, &func);
        assert_eq!(
            result,
            Some(Term::Select(
                Box::new(Term::Const("_1".to_string())),
                Box::new(Term::Const("i".to_string()))
            ))
        );
    }

    #[test]
    fn encode_place_with_type_index_on_non_array_returns_none() {
        // Index projection on a non-indexable type
        let func = make_func(
            vec![Local::new("_1", Ty::Int(IntTy::I32))],
            vec![],
            Ty::Unit,
        );
        let place = Place::local("_1").index("i".to_string());
        let result = encode_place_with_type(&place, &func);
        // get_element_type returns None for Int
        assert_eq!(result, None);
    }

    // ====== Coverage: multi-projection chains with type info ======

    #[test]
    fn encode_place_with_type_struct_field_chain() {
        // Nested struct access: _1.field0.field0
        let inner_struct = Ty::Struct(
            "Inner".to_string(),
            vec![("val".to_string(), Ty::Int(IntTy::I32))],
        );
        let outer_struct = Ty::Struct(
            "Outer".to_string(),
            vec![("inner".to_string(), inner_struct)],
        );
        let func = make_func(vec![Local::new("_1", outer_struct)], vec![], Ty::Unit);
        let place = Place::local("_1").field(0).field(0);
        let result = encode_place_with_type(&place, &func);
        assert_eq!(
            result,
            Some(Term::App(
                "Inner-val".to_string(),
                vec![Term::App(
                    "Outer-inner".to_string(),
                    vec![Term::Const("_1".to_string())]
                )]
            ))
        );
    }

    #[test]
    fn encode_place_with_type_deref_then_field() {
        // _1.deref.field(0) where _1 is &Struct
        let struct_ty = Ty::Struct("S".to_string(), vec![("x".to_string(), Ty::Bool)]);
        let ref_ty = Ty::Ref(Box::new(struct_ty), Mutability::Shared);
        let func = make_func(vec![Local::new("_1", ref_ty)], vec![], Ty::Unit);
        let place = Place::local("_1").deref().field(0);
        let result = encode_place_with_type(&place, &func);
        assert_eq!(
            result,
            Some(Term::App(
                "S-x".to_string(),
                vec![Term::Const("_1".to_string())]
            ))
        );
    }

    // ====== Coverage: various integer widths for binop encoding ======

    #[test]
    fn binop_add_i8() {
        let ty = Ty::Int(IntTy::I8);
        let result = encode_binop(BinOp::Add, &var("a"), &var("b"), &ty);
        assert!(matches!(result, Term::BvAdd(_, _)));
    }

    #[test]
    fn binop_mul_u64() {
        let ty = Ty::Uint(UintTy::U64);
        let result = encode_binop(BinOp::Mul, &var("a"), &var("b"), &ty);
        assert!(matches!(result, Term::BvMul(_, _)));
    }

    #[test]
    fn binop_div_i128() {
        let ty = Ty::Int(IntTy::I128);
        let result = encode_binop(BinOp::Div, &var("a"), &var("b"), &ty);
        assert!(matches!(result, Term::BvSDiv(_, _)));
    }

    // ====== Coverage: encode_constant for different int/uint widths ======

    #[test]
    fn encode_constant_i8() {
        let c = Constant::Int(-128, IntTy::I8);
        assert_eq!(encode_constant(&c), Term::BitVecLit(-128, 8));
    }

    #[test]
    fn encode_constant_u8() {
        let c = Constant::Uint(255, UintTy::U8);
        assert_eq!(encode_constant(&c), Term::BitVecLit(255, 8));
    }

    #[test]
    fn encode_constant_i16() {
        let c = Constant::Int(-1, IntTy::I16);
        assert_eq!(encode_constant(&c), Term::BitVecLit(-1, 16));
    }

    #[test]
    fn encode_constant_u16() {
        let c = Constant::Uint(0, UintTy::U16);
        assert_eq!(encode_constant(&c), Term::BitVecLit(0, 16));
    }

    #[test]
    fn encode_constant_i128() {
        let c = Constant::Int(0, IntTy::I128);
        assert_eq!(encode_constant(&c), Term::BitVecLit(0, 128));
    }

    #[test]
    fn encode_constant_u128() {
        let c = Constant::Uint(1, UintTy::U128);
        assert_eq!(encode_constant(&c), Term::BitVecLit(1, 128));
    }

    #[test]
    fn encode_constant_bool_false() {
        let c = Constant::Bool(false);
        assert_eq!(encode_constant(&c), Term::BoolLit(false));
    }

    #[test]
    fn encode_constant_f32_1_0() {
        let c = Constant::Float(1.0, crate::ir::FloatTy::F32);
        // Should produce FpFromBits with f32 parameters (8, 24)
        assert!(matches!(
            encode_constant(&c),
            Term::FpFromBits(_, _, _, 8, 24)
        ));
    }

    // ====== Coverage: overflow_check on non-bit-width type returns None ======

    #[test]
    fn overflow_check_on_unit_type_returns_none() {
        // Unit has no bit_width, so overflow_check returns None early
        let ty = Ty::Unit;
        let check = overflow_check(BinOp::Add, &var("a"), &var("b"), &ty);
        assert!(check.is_none());
    }

    #[test]
    fn overflow_check_on_named_type_returns_none() {
        let ty = Ty::Named("SomeType".to_string());
        let check = overflow_check(BinOp::Sub, &var("a"), &var("b"), &ty);
        assert!(check.is_none());
    }

    // ====== Coverage: encode_aggregate_with_type enum variant 0 (None) ======

    #[test]
    fn encode_aggregate_with_type_enum_none_variant() {
        let kind = AggregateKind::Enum("Option".to_string(), 0);
        let ops: Vec<Operand> = vec![];
        let result_ty = Ty::Enum(
            "Option".to_string(),
            vec![
                ("None".to_string(), vec![]),
                ("Some".to_string(), vec![Ty::Int(IntTy::I32)]),
            ],
        );
        let result = encode_aggregate_with_type(&kind, &ops, &result_ty);
        assert_eq!(result, Some(Term::App("mk-None".to_string(), vec![])));
    }

    // ====== Float encoding tests (Phase 11 Plan 02 - TDD RED) ======

    #[test]
    fn test_encode_float_constant_f64_1_0() {
        use crate::ir::FloatTy;
        // 1.0_f64 = 0x3FF0000000000000
        let result = encode_float_constant(1.0, FloatTy::F64);
        assert!(matches!(result, Term::FpFromBits(_, _, _, 11, 53)));
    }

    #[test]
    fn test_encode_float_constant_f32_1_0() {
        use crate::ir::FloatTy;
        let result = encode_float_constant(1.0, FloatTy::F32);
        assert!(matches!(result, Term::FpFromBits(_, _, _, 8, 24)));
    }

    #[test]
    fn test_encode_float_constant_nan() {
        use crate::ir::FloatTy;
        let result = encode_float_constant(f64::NAN, FloatTy::F64);
        assert_eq!(result, Term::FpNaN(11, 53));
    }

    #[test]
    fn test_encode_float_constant_pos_inf() {
        use crate::ir::FloatTy;
        let result = encode_float_constant(f64::INFINITY, FloatTy::F64);
        assert_eq!(result, Term::FpPosInf(11, 53));
    }

    #[test]
    fn test_encode_float_constant_neg_inf() {
        use crate::ir::FloatTy;
        let result = encode_float_constant(f64::NEG_INFINITY, FloatTy::F64);
        assert_eq!(result, Term::FpNegInf(11, 53));
    }

    #[test]
    fn test_encode_float_constant_pos_zero() {
        use crate::ir::FloatTy;
        let result = encode_float_constant(0.0, FloatTy::F64);
        assert_eq!(result, Term::FpPosZero(11, 53));
    }

    #[test]
    fn test_encode_float_constant_neg_zero() {
        use crate::ir::FloatTy;
        let result = encode_float_constant(-0.0_f64, FloatTy::F64);
        assert_eq!(result, Term::FpNegZero(11, 53));
    }

    #[test]
    fn test_encode_fp_binop_add() {
        let result = encode_fp_binop(BinOp::Add, &var("x"), &var("y"));
        assert!(matches!(result, Term::FpAdd(_, _, _)));
    }

    #[test]
    fn test_encode_fp_binop_sub() {
        let result = encode_fp_binop(BinOp::Sub, &var("x"), &var("y"));
        assert!(matches!(result, Term::FpSub(_, _, _)));
    }

    #[test]
    fn test_encode_fp_binop_mul() {
        let result = encode_fp_binop(BinOp::Mul, &var("x"), &var("y"));
        assert!(matches!(result, Term::FpMul(_, _, _)));
    }

    #[test]
    fn test_encode_fp_binop_div() {
        let result = encode_fp_binop(BinOp::Div, &var("x"), &var("y"));
        assert!(matches!(result, Term::FpDiv(_, _, _)));
    }

    #[test]
    fn test_encode_fp_comparison_eq() {
        let result = encode_fp_binop(BinOp::Eq, &var("x"), &var("y"));
        assert!(matches!(result, Term::FpEq(_, _)));
    }

    #[test]
    fn test_encode_fp_comparison_lt() {
        let result = encode_fp_binop(BinOp::Lt, &var("x"), &var("y"));
        assert!(matches!(result, Term::FpLt(_, _)));
    }

    #[test]
    fn test_encode_fp_comparison_le() {
        let result = encode_fp_binop(BinOp::Le, &var("x"), &var("y"));
        assert!(matches!(result, Term::FpLeq(_, _)));
    }

    #[test]
    fn test_encode_fp_comparison_gt() {
        let result = encode_fp_binop(BinOp::Gt, &var("x"), &var("y"));
        assert!(matches!(result, Term::FpGt(_, _)));
    }

    #[test]
    fn test_encode_fp_comparison_ge() {
        let result = encode_fp_binop(BinOp::Ge, &var("x"), &var("y"));
        assert!(matches!(result, Term::FpGeq(_, _)));
    }

    #[test]
    fn test_encode_fp_unop_neg() {
        let result = encode_fp_unop(UnOp::Neg, &var("x"));
        assert!(matches!(result, Term::FpNeg(_)));
    }

    #[test]
    fn test_encode_binop_dispatches_float() {
        use crate::ir::FloatTy;
        let ty = Ty::Float(FloatTy::F64);
        let result = encode_binop(BinOp::Add, &var("x"), &var("y"), &ty);
        // Should produce FpAdd, not BvAdd
        assert!(matches!(result, Term::FpAdd(_, _, _)));
    }
}
