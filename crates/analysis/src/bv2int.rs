//! bv2int optimization infrastructure for arithmetic-heavy verification.
//!
//! This module provides:
//! - `EncodingMode` enum: chooses between bitvector and integer arithmetic encoding
//! - `IneligibilityReason`: explains why a function cannot use bv2int
//! - `is_bv2int_eligible`: conservative applicability analysis
//! - `encode_type_with_mode`: mode-aware type-to-sort mapping
//! - `encode_binop_with_mode`: mode-aware binary operation encoding
//! - `wrap_overflow`: wrapping arithmetic modulo constraint per Rust RFC 0560

// ============================================================
// Public types
// ============================================================

/// SMT encoding strategy for integer types.
///
/// `Bitvector` (default): all integers are encoded as `(_ BitVec N)` sorts.
/// `Integer`: integers are encoded as `Int` sort with integer arithmetic, enabling
/// significant solver speedup on arithmetic-heavy verification tasks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum EncodingMode {
    /// Default bitvector encoding — all integers as `(_ BitVec N)`.
    #[default]
    Bitvector,
    /// Integer arithmetic encoding — eligible integers as `Int` sort.
    Integer,
}

/// Reason a function is ineligible for bv2int optimization.
///
/// Displayed to the user when `--bv2int` is requested but a function is skipped.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IneligibilityReason {
    /// Function contains a bitwise operation (`&`, `|`, `^`).
    BitwiseOp {
        /// Symbol of the offending operation (e.g. `"&"`)
        op_symbol: &'static str,
        /// Human-readable location (e.g. `"basic block 0, statement 2"`)
        location: String,
    },
    /// Function contains a shift operation (`<<`, `>>`).
    ShiftOp {
        /// Symbol of the offending operation (e.g. `"<<"`)
        op_symbol: &'static str,
        /// Human-readable location
        location: String,
    },
    /// Function has the `#[fv::no_bv2int]` attribute.
    OptOut,
}

impl std::fmt::Display for IneligibilityReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BitwiseOp {
                op_symbol,
                location,
            } => write!(
                f,
                "Function uses bitwise operation `{op_symbol}` at {location} -- bv2int not applicable"
            ),
            Self::ShiftOp {
                op_symbol,
                location,
            } => write!(
                f,
                "Function uses shift operation `{op_symbol}` at {location} -- bv2int not applicable"
            ),
            Self::OptOut => write!(f, "Function has #[fv::no_bv2int] attribute"),
        }
    }
}

// ============================================================
// Eligibility analysis
// ============================================================

use crate::ir::{BinOp, Function, Rvalue, Statement, Ty};
use rust_fv_smtlib::sort::Sort;
use rust_fv_smtlib::term::Term;

use crate::encode_sort::encode_type;
use crate::encode_term::encode_binop;

/// Analyse `func` to determine whether bv2int encoding is applicable.
///
/// Returns `Ok(())` if the function is eligible (only arithmetic and comparison
/// operations), or `Err(IneligibilityReason)` if any disqualifying operation is
/// present or the function has the `#[fv::no_bv2int]` attribute.
///
/// Conservative strategy: the **entire** function is rejected if ANY bitwise or
/// shift operation is found. Per-expression mixed encoding is not supported — it
/// would require tracking which variables are bitvector vs integer throughout the
/// encoding pipeline.
pub fn is_bv2int_eligible(func: &Function) -> Result<(), IneligibilityReason> {
    // Check #[fv::no_bv2int] attribute (represented in Contracts for now)
    if has_no_bv2int_attribute(func) {
        return Err(IneligibilityReason::OptOut);
    }

    for (bb_idx, bb) in func.basic_blocks.iter().enumerate() {
        for (stmt_idx, stmt) in bb.statements.iter().enumerate() {
            if let Statement::Assign(
                _,
                Rvalue::BinaryOp(op, _, _) | Rvalue::CheckedBinaryOp(op, _, _),
            ) = stmt
            {
                let location = format!("basic block {bb_idx}, statement {stmt_idx}");
                match op {
                    BinOp::BitAnd => {
                        return Err(IneligibilityReason::BitwiseOp {
                            op_symbol: "&",
                            location,
                        });
                    }
                    BinOp::BitOr => {
                        return Err(IneligibilityReason::BitwiseOp {
                            op_symbol: "|",
                            location,
                        });
                    }
                    BinOp::BitXor => {
                        return Err(IneligibilityReason::BitwiseOp {
                            op_symbol: "^",
                            location,
                        });
                    }
                    BinOp::Shl => {
                        return Err(IneligibilityReason::ShiftOp {
                            op_symbol: "<<",
                            location,
                        });
                    }
                    BinOp::Shr => {
                        return Err(IneligibilityReason::ShiftOp {
                            op_symbol: ">>",
                            location,
                        });
                    }
                    _ => {} // Add, Sub, Mul, Div, Rem, comparisons: OK
                }
            }
        }
    }

    Ok(())
}

/// Detect `#[fv::no_bv2int]` attribute on a function.
///
/// The attribute is stored as a `requires` spec expression with the raw string
/// `"__fv_no_bv2int__"` by the driver during attribute parsing. This is a
/// lightweight encoding that avoids adding a new field to `Contracts`.
fn has_no_bv2int_attribute(func: &Function) -> bool {
    func.contracts
        .requires
        .iter()
        .any(|expr| expr.raw == "__fv_no_bv2int__")
}

// ============================================================
// Mode-aware type encoding
// ============================================================

/// Encode a Rust type to an SMT-LIB sort, respecting the encoding mode.
///
/// In `EncodingMode::Bitvector` this delegates to `encode_type` unchanged.
/// In `EncodingMode::Integer` integer types (`Int(_)` and `Uint(_)`) are mapped
/// to `Sort::Int` (unbounded mathematical integers).  All other types are
/// unaffected by the mode.
pub fn encode_type_with_mode(ty: &Ty, mode: EncodingMode) -> Sort {
    match mode {
        EncodingMode::Bitvector => encode_type(ty),
        EncodingMode::Integer => match ty {
            Ty::Int(_) | Ty::Uint(_) => Sort::Int,
            _ => encode_type(ty),
        },
    }
}

// ============================================================
// Mode-aware binary operation encoding
// ============================================================

/// Encode a binary operation as an SMT-LIB term, respecting the encoding mode.
///
/// In `EncodingMode::Bitvector` this delegates to `encode_binop` unchanged.
/// In `EncodingMode::Integer` arithmetic operations are encoded using `Int`
/// arithmetic with wrapping overflow guards per Rust RFC 0560.
///
/// # Panics
/// Panics if `mode == Integer` and `op` is a bitwise or shift operation.
/// Callers must ensure eligibility is checked before calling this function.
pub fn encode_binop_with_mode(
    op: BinOp,
    lhs: &Term,
    rhs: &Term,
    ty: &Ty,
    mode: EncodingMode,
) -> Term {
    match mode {
        EncodingMode::Bitvector => encode_binop(op, lhs, rhs, ty),
        EncodingMode::Integer => encode_binop_as_int(op, lhs.clone(), rhs.clone(), ty),
    }
}

/// Encode a binary operation using unbounded integer arithmetic.
///
/// For wrapping operations (Add, Sub, Mul) applies `wrap_overflow` to match
/// Rust's default wrapping semantics in release mode (Rust RFC 0560).
/// Div and Rem map directly to SMT integer division and modulo.
/// Comparisons map to integer comparisons (no bitvector signedness needed).
///
/// # Panics
/// Panics if `op` is a bitwise or shift operation — these must be caught by
/// `is_bv2int_eligible` before this function is called.
fn encode_binop_as_int(op: BinOp, lhs: Term, rhs: Term, ty: &Ty) -> Term {
    match op {
        // Wrapping arithmetic: apply overflow guard
        BinOp::Add => {
            let raw = Term::IntAdd(Box::new(lhs), Box::new(rhs));
            wrap_overflow(raw, ty)
        }
        BinOp::Sub => {
            let raw = Term::IntSub(Box::new(lhs), Box::new(rhs));
            wrap_overflow(raw, ty)
        }
        BinOp::Mul => {
            let raw = Term::IntMul(Box::new(lhs), Box::new(rhs));
            wrap_overflow(raw, ty)
        }
        // Division and remainder: no overflow guard needed (modular semantics don't apply)
        BinOp::Div => Term::IntDiv(Box::new(lhs), Box::new(rhs)),
        BinOp::Rem => Term::IntMod(Box::new(lhs), Box::new(rhs)),
        // Comparisons: use integer comparisons
        BinOp::Eq => Term::Eq(Box::new(lhs), Box::new(rhs)),
        BinOp::Ne => Term::Not(Box::new(Term::Eq(Box::new(lhs), Box::new(rhs)))),
        BinOp::Lt => Term::IntLt(Box::new(lhs), Box::new(rhs)),
        BinOp::Le => Term::IntLe(Box::new(lhs), Box::new(rhs)),
        BinOp::Gt => Term::IntGt(Box::new(lhs), Box::new(rhs)),
        BinOp::Ge => Term::IntGe(Box::new(lhs), Box::new(rhs)),
        // Bitwise and shift operations cannot appear in integer encoding
        BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr => {
            panic!(
                "encode_binop_as_int called with bitwise/shift op {:?} — check is_bv2int_eligible first",
                op
            )
        }
    }
}

// ============================================================
// Overflow wrapping
// ============================================================

/// Apply wrapping overflow constraints to an integer arithmetic result.
///
/// Implements Rust RFC 0560 wrapping semantics for integer types.
///
/// **Unsigned types** (`Uint(_)`): modulo 2^N so the result stays in [0, 2^N).
///   `(mod result 2^N)`
///
/// **Signed types** (`Int(_)`): two's complement range [-2^(N-1), 2^(N-1)).
///   `(ite (>= result 2^(N-1)) (- result 2^N) (ite (< result (- 2^(N-1))) (+ result 2^N) result))`
///
/// For non-integer types the result is returned unchanged (no overflow semantics).
pub fn wrap_overflow(result: Term, ty: &Ty) -> Term {
    match ty {
        Ty::Uint(uty) => {
            let n = uty.bit_width();
            let modulus = pow2_lit(n);
            Term::IntMod(Box::new(result), Box::new(modulus))
        }
        Ty::Int(ity) => {
            let n = ity.bit_width();
            let half = pow2_lit(n - 1); // 2^(N-1)
            let full = pow2_lit(n); // 2^N

            // Two's complement wrapping:
            // if result >= 2^(N-1): result - 2^N   (overflow into negative range)
            // elif result < -(2^(N-1)): result + 2^N  (underflow into positive range)
            // else: result
            let result_minus_full = Term::IntSub(Box::new(result.clone()), Box::new(full.clone()));
            let result_plus_full = Term::IntAdd(Box::new(result.clone()), Box::new(full));
            let neg_half = Term::IntNeg(Box::new(half.clone()));

            // Inner ite: result < -2^(N-1) ? result + 2^N : result
            let inner = Term::Ite(
                Box::new(Term::IntLt(Box::new(result.clone()), Box::new(neg_half))),
                Box::new(result_plus_full),
                Box::new(result.clone()),
            );
            // Outer ite: result >= 2^(N-1) ? result - 2^N : inner
            Term::Ite(
                Box::new(Term::IntGe(Box::new(result), Box::new(half))),
                Box::new(result_minus_full),
                Box::new(inner),
            )
        }
        _ => result, // Non-integer types: no overflow semantics
    }
}

/// Create an SMT-LIB integer literal for 2^n.
fn pow2_lit(n: u32) -> Term {
    Term::IntLit(1i128 << n)
}

// ============================================================
// Unit tests
// ============================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{
        BasicBlock, BinOp, Contracts, Function, IntTy, Local, Operand, Place, Rvalue, SpecExpr,
        Statement, Terminator, Ty, UintTy,
    };
    use rust_fv_smtlib::sort::Sort;
    use rust_fv_smtlib::term::Term;

    // ---- helpers ----

    fn make_function_with_binop(op: BinOp) -> Function {
        Function {
            name: "test_fn".to_string(),
            params: vec![Local::new("_1", Ty::Int(IntTy::I32))],
            return_local: Local::new("_0", Ty::Int(IntTy::I32)),
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::BinaryOp(
                        op,
                        Operand::Copy(Place::local("_1")),
                        Operand::Copy(Place::local("_1")),
                    ),
                )],
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
        }
    }

    fn make_arithmetic_function() -> Function {
        // Function with Add and Sub only — should be eligible
        let mut func = make_function_with_binop(BinOp::Add);
        func.basic_blocks.push(BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::BinaryOp(
                    BinOp::Sub,
                    Operand::Copy(Place::local("_1")),
                    Operand::Copy(Place::local("_1")),
                ),
            )],
            terminator: Terminator::Return,
        });
        func
    }

    fn make_no_bv2int_function() -> Function {
        let mut func = make_arithmetic_function();
        func.contracts.requires.push(SpecExpr {
            raw: "__fv_no_bv2int__".to_string(),
        });
        func
    }

    fn make_empty_function() -> Function {
        Function {
            name: "empty".to_string(),
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
        }
    }

    // ---- EncodingMode tests ----

    #[test]
    fn encoding_mode_default_is_bitvector() {
        let mode = EncodingMode::default();
        assert_eq!(mode, EncodingMode::Bitvector);
    }

    #[test]
    fn encoding_mode_copy() {
        let mode = EncodingMode::Integer;
        let copied = mode;
        assert_eq!(copied, EncodingMode::Integer);
    }

    // ---- IneligibilityReason display tests ----

    #[test]
    fn ineligibility_bitwise_display() {
        let reason = IneligibilityReason::BitwiseOp {
            op_symbol: "&",
            location: "basic block 0, statement 1".to_string(),
        };
        let msg = reason.to_string();
        assert!(msg.contains('`'));
        assert!(msg.contains('&'));
        assert!(msg.contains("bv2int not applicable"));
        assert!(msg.contains("basic block 0, statement 1"));
    }

    #[test]
    fn ineligibility_shift_display() {
        let reason = IneligibilityReason::ShiftOp {
            op_symbol: "<<",
            location: "basic block 2, statement 0".to_string(),
        };
        let msg = reason.to_string();
        assert!(msg.contains("<<"));
        assert!(msg.contains("bv2int not applicable"));
    }

    #[test]
    fn ineligibility_opt_out_display() {
        let reason = IneligibilityReason::OptOut;
        let msg = reason.to_string();
        assert!(msg.contains("no_bv2int"));
    }

    // ---- is_bv2int_eligible tests ----

    #[test]
    fn eligible_empty_function() {
        let func = make_empty_function();
        assert!(is_bv2int_eligible(&func).is_ok());
    }

    #[test]
    fn eligible_arithmetic_function() {
        let func = make_arithmetic_function();
        assert!(is_bv2int_eligible(&func).is_ok());
    }

    #[test]
    fn eligible_comparison_ops() {
        // All comparison ops should be eligible
        for op in [
            BinOp::Eq,
            BinOp::Ne,
            BinOp::Lt,
            BinOp::Le,
            BinOp::Gt,
            BinOp::Ge,
        ] {
            let func = make_function_with_binop(op);
            assert!(
                is_bv2int_eligible(&func).is_ok(),
                "Expected eligible for {op:?}"
            );
        }
    }

    #[test]
    fn ineligible_bit_and() {
        let func = make_function_with_binop(BinOp::BitAnd);
        let result = is_bv2int_eligible(&func);
        assert!(result.is_err());
        let reason = result.unwrap_err();
        assert!(matches!(
            reason,
            IneligibilityReason::BitwiseOp { op_symbol: "&", .. }
        ));
    }

    #[test]
    fn ineligible_bit_or() {
        let func = make_function_with_binop(BinOp::BitOr);
        let result = is_bv2int_eligible(&func);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            IneligibilityReason::BitwiseOp { op_symbol: "|", .. }
        ));
    }

    #[test]
    fn ineligible_bit_xor() {
        let func = make_function_with_binop(BinOp::BitXor);
        let result = is_bv2int_eligible(&func);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            IneligibilityReason::BitwiseOp { op_symbol: "^", .. }
        ));
    }

    #[test]
    fn ineligible_shl() {
        let func = make_function_with_binop(BinOp::Shl);
        let result = is_bv2int_eligible(&func);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            IneligibilityReason::ShiftOp {
                op_symbol: "<<",
                ..
            }
        ));
    }

    #[test]
    fn ineligible_shr() {
        let func = make_function_with_binop(BinOp::Shr);
        let result = is_bv2int_eligible(&func);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            IneligibilityReason::ShiftOp {
                op_symbol: ">>",
                ..
            }
        ));
    }

    #[test]
    fn ineligible_opt_out_attribute() {
        let func = make_no_bv2int_function();
        let result = is_bv2int_eligible(&func);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), IneligibilityReason::OptOut);
    }

    #[test]
    fn ineligibility_reason_carries_location() {
        let func = make_function_with_binop(BinOp::BitAnd);
        let reason = is_bv2int_eligible(&func).unwrap_err();
        if let IneligibilityReason::BitwiseOp { location, .. } = reason {
            assert!(location.contains("basic block 0"));
            assert!(location.contains("statement 0"));
        } else {
            panic!("Expected BitwiseOp reason");
        }
    }

    // ---- encode_type_with_mode tests ----

    #[test]
    fn bitvector_mode_i32_gives_bv32() {
        let sort = encode_type_with_mode(&Ty::Int(IntTy::I32), EncodingMode::Bitvector);
        assert_eq!(sort, Sort::BitVec(32));
    }

    #[test]
    fn integer_mode_i32_gives_int() {
        let sort = encode_type_with_mode(&Ty::Int(IntTy::I32), EncodingMode::Integer);
        assert_eq!(sort, Sort::Int);
    }

    #[test]
    fn integer_mode_u64_gives_int() {
        let sort = encode_type_with_mode(&Ty::Uint(UintTy::U64), EncodingMode::Integer);
        assert_eq!(sort, Sort::Int);
    }

    #[test]
    fn integer_mode_bool_unchanged() {
        let sort = encode_type_with_mode(&Ty::Bool, EncodingMode::Integer);
        assert_eq!(sort, Sort::Bool);
    }

    #[test]
    fn integer_mode_all_signed_types_give_int() {
        use crate::ir::IntTy;
        for ity in [
            IntTy::I8,
            IntTy::I16,
            IntTy::I32,
            IntTy::I64,
            IntTy::I128,
            IntTy::Isize,
        ] {
            assert_eq!(
                encode_type_with_mode(&Ty::Int(ity), EncodingMode::Integer),
                Sort::Int,
                "Expected Sort::Int for {ity:?}"
            );
        }
    }

    #[test]
    fn integer_mode_all_unsigned_types_give_int() {
        use crate::ir::UintTy;
        for uty in [
            UintTy::U8,
            UintTy::U16,
            UintTy::U32,
            UintTy::U64,
            UintTy::U128,
            UintTy::Usize,
        ] {
            assert_eq!(
                encode_type_with_mode(&Ty::Uint(uty), EncodingMode::Integer),
                Sort::Int,
                "Expected Sort::Int for {uty:?}"
            );
        }
    }

    // ---- encode_binop_with_mode tests ----

    #[test]
    fn bitvector_mode_add_delegates_to_encode_binop() {
        // In bitvector mode, encode_binop_with_mode should produce BvAdd
        let lhs = Term::Const("a".to_string());
        let rhs = Term::Const("b".to_string());
        let term = encode_binop_with_mode(
            BinOp::Add,
            &lhs,
            &rhs,
            &Ty::Int(IntTy::I32),
            EncodingMode::Bitvector,
        );
        // Should produce BvAdd (delegated to encode_binop)
        assert!(
            matches!(term, Term::BvAdd(_, _)),
            "Expected BvAdd for bitvector mode, got {term:?}"
        );
    }

    #[test]
    fn integer_mode_add_produces_int_add_with_overflow() {
        let lhs = Term::IntLit(10);
        let rhs = Term::IntLit(20);
        let term = encode_binop_with_mode(
            BinOp::Add,
            &lhs,
            &rhs,
            &Ty::Uint(UintTy::U8),
            EncodingMode::Integer,
        );
        // Should be IntMod(IntAdd(10, 20), 256) for u8 wrapping
        assert!(
            matches!(term, Term::IntMod(_, _)),
            "Expected IntMod wrapper for unsigned Add"
        );
    }

    #[test]
    fn integer_mode_sub_produces_int_sub_with_overflow() {
        let lhs = Term::IntLit(5);
        let rhs = Term::IntLit(10);
        let term = encode_binop_with_mode(
            BinOp::Sub,
            &lhs,
            &rhs,
            &Ty::Uint(UintTy::U8),
            EncodingMode::Integer,
        );
        assert!(
            matches!(term, Term::IntMod(_, _)),
            "Expected IntMod wrapper for unsigned Sub"
        );
    }

    #[test]
    fn integer_mode_mul_produces_int_mul_with_overflow() {
        let lhs = Term::IntLit(100);
        let rhs = Term::IntLit(200);
        let term = encode_binop_with_mode(
            BinOp::Mul,
            &lhs,
            &rhs,
            &Ty::Uint(UintTy::U16),
            EncodingMode::Integer,
        );
        assert!(
            matches!(term, Term::IntMod(_, _)),
            "Expected IntMod wrapper for unsigned Mul"
        );
    }

    #[test]
    fn integer_mode_div_no_overflow_guard() {
        let lhs = Term::IntLit(100);
        let rhs = Term::IntLit(3);
        let term = encode_binop_with_mode(
            BinOp::Div,
            &lhs,
            &rhs,
            &Ty::Uint(UintTy::U32),
            EncodingMode::Integer,
        );
        assert!(
            matches!(term, Term::IntDiv(_, _)),
            "Expected IntDiv for Div"
        );
    }

    #[test]
    fn integer_mode_rem_is_int_mod() {
        let lhs = Term::IntLit(10);
        let rhs = Term::IntLit(3);
        let term = encode_binop_with_mode(
            BinOp::Rem,
            &lhs,
            &rhs,
            &Ty::Uint(UintTy::U32),
            EncodingMode::Integer,
        );
        assert!(
            matches!(term, Term::IntMod(_, _)),
            "Expected IntMod for Rem"
        );
    }

    #[test]
    fn integer_mode_comparisons() {
        let lhs = Term::IntLit(5);
        let rhs = Term::IntLit(10);
        let ty = Ty::Int(IntTy::I32);
        assert!(matches!(
            encode_binop_with_mode(BinOp::Lt, &lhs, &rhs, &ty, EncodingMode::Integer),
            Term::IntLt(_, _)
        ));
        assert!(matches!(
            encode_binop_with_mode(BinOp::Le, &lhs, &rhs, &ty, EncodingMode::Integer),
            Term::IntLe(_, _)
        ));
        assert!(matches!(
            encode_binop_with_mode(BinOp::Gt, &lhs, &rhs, &ty, EncodingMode::Integer),
            Term::IntGt(_, _)
        ));
        assert!(matches!(
            encode_binop_with_mode(BinOp::Ge, &lhs, &rhs, &ty, EncodingMode::Integer),
            Term::IntGe(_, _)
        ));
    }

    #[test]
    fn integer_mode_eq_is_eq_term() {
        let lhs = Term::IntLit(5);
        let rhs = Term::IntLit(5);
        let term = encode_binop_with_mode(
            BinOp::Eq,
            &lhs,
            &rhs,
            &Ty::Int(IntTy::I32),
            EncodingMode::Integer,
        );
        assert!(matches!(term, Term::Eq(_, _)));
    }

    #[test]
    fn integer_mode_ne_is_not_eq() {
        let lhs = Term::IntLit(5);
        let rhs = Term::IntLit(6);
        let term = encode_binop_with_mode(
            BinOp::Ne,
            &lhs,
            &rhs,
            &Ty::Int(IntTy::I32),
            EncodingMode::Integer,
        );
        assert!(matches!(term, Term::Not(_)));
    }

    // ---- wrap_overflow tests ----

    #[test]
    fn wrap_overflow_unsigned_u8_produces_mod_256() {
        let result = Term::IntLit(300);
        let wrapped = wrap_overflow(result, &Ty::Uint(UintTy::U8));
        // Should be IntMod(300, 256)
        if let Term::IntMod(inner, modulus) = wrapped {
            assert_eq!(*inner, Term::IntLit(300));
            assert_eq!(*modulus, Term::IntLit(256));
        } else {
            panic!("Expected IntMod for unsigned wrapping");
        }
    }

    #[test]
    fn wrap_overflow_unsigned_u32_produces_mod_2_32() {
        let result = Term::Const("x".to_string());
        let wrapped = wrap_overflow(result, &Ty::Uint(UintTy::U32));
        if let Term::IntMod(_, modulus) = wrapped {
            assert_eq!(*modulus, Term::IntLit(1i128 << 32));
        } else {
            panic!("Expected IntMod for u32 wrapping");
        }
    }

    #[test]
    fn wrap_overflow_signed_i8_produces_ite_chain() {
        let result = Term::Const("x".to_string());
        let wrapped = wrap_overflow(result, &Ty::Int(IntTy::I8));
        // Should be Ite(Ge(x, 128), Sub(x, 256), Ite(Lt(x, -128), Add(x, 256), x))
        assert!(
            matches!(wrapped, Term::Ite(_, _, _)),
            "Expected Ite chain for signed wrapping"
        );
    }

    #[test]
    fn wrap_overflow_non_integer_unchanged() {
        let result = Term::BoolLit(true);
        let wrapped = wrap_overflow(result.clone(), &Ty::Bool);
        assert_eq!(
            wrapped, result,
            "Non-integer type should be unchanged by wrap_overflow"
        );
    }

    #[test]
    fn wrap_overflow_signed_i32_correct_modulus() {
        let result = Term::Const("y".to_string());
        let wrapped = wrap_overflow(result, &Ty::Int(IntTy::I32));
        // The outer Ite condition should use 2^31 (half = 2^(32-1) = 2^31)
        if let Term::Ite(cond, then_branch, _) = wrapped {
            // cond should be Ge(y, 2^31)
            if let Term::IntGe(_, rhs) = *cond {
                assert_eq!(
                    *rhs,
                    Term::IntLit(1i128 << 31),
                    "Expected 2^31 threshold for i32"
                );
            } else {
                panic!("Expected IntGe condition");
            }
            // then_branch should be Sub(y, 2^32)
            if let Term::IntSub(_, sub_rhs) = *then_branch {
                assert_eq!(
                    *sub_rhs,
                    Term::IntLit(1i128 << 32),
                    "Expected subtract 2^32 for i32"
                );
            } else {
                panic!("Expected IntSub in then branch");
            }
        } else {
            panic!("Expected Ite for signed wrapping");
        }
    }
}
