/// Floating-point verification condition generation.
///
/// Generates VCs for NaN propagation and infinity overflow checks
/// for all floating-point arithmetic operations.
use rust_fv_smtlib::command::Command;
use rust_fv_smtlib::script::Script;
use rust_fv_smtlib::term::Term;

use crate::ir::{BinOp, Function, Rvalue, Statement, Ty};
use crate::vcgen::{VcKind, VcLocation, VerificationCondition};

/// Generate a NaN propagation verification condition.
///
/// Checks: if all operands are not NaN, then result is not NaN.
pub fn nan_propagation_vc(
    result: Term,
    operands: &[Term],
    operation: &str,
    location: VcLocation,
) -> VerificationCondition {
    // Build VC term: if all operands are not NaN, then result is not NaN
    let vc_term = if operands.is_empty() {
        // No operands: result should not be NaN
        Term::Not(Box::new(Term::FpIsNaN(Box::new(result.clone()))))
    } else {
        // operands_not_nan = And(Not(FpIsNaN(op1)), Not(FpIsNaN(op2)), ...)
        let operands_not_nan: Vec<Term> = operands
            .iter()
            .map(|op| Term::Not(Box::new(Term::FpIsNaN(Box::new(op.clone())))))
            .collect();

        let result_not_nan = Term::Not(Box::new(Term::FpIsNaN(Box::new(result.clone()))));

        // VC: operands_not_nan => result_not_nan
        Term::Implies(
            Box::new(Term::And(operands_not_nan)),
            Box::new(result_not_nan),
        )
    };

    let description =
        format!("NaN propagation: {operation} should not produce NaN when operands are finite");

    // For simplicity, create a minimal script (VCGen will handle full encoding)
    let script = Script::with_commands(vec![Command::Assert(vc_term)]);

    VerificationCondition {
        description,
        script,
        location,
    }
}

/// Generate an infinity overflow verification condition.
///
/// Checks: if operands are finite (not infinite), result should be finite.
pub fn infinity_overflow_vc(
    result: Term,
    operands: &[Term],
    operation: &str,
    location: VcLocation,
) -> VerificationCondition {
    // operands_finite = And(Not(FpIsInfinite(op1)), Not(FpIsInfinite(op2)), ...)
    let operands_finite: Vec<Term> = operands
        .iter()
        .map(|op| Term::Not(Box::new(Term::FpIsInfinite(Box::new(op.clone())))))
        .collect();

    let result_finite = Term::Not(Box::new(Term::FpIsInfinite(Box::new(result.clone()))));

    // VC: operands_finite => result_finite
    let vc_term = Term::Implies(
        Box::new(Term::And(operands_finite)),
        Box::new(result_finite),
    );

    let description = format!(
        "Infinity check: {operation} must not overflow to infinity when operands are finite"
    );

    let script = Script::with_commands(vec![Command::Assert(vc_term)]);

    VerificationCondition {
        description,
        script,
        location,
    }
}

/// Generate all floating-point verification conditions for a function.
pub fn generate_float_vcs(func: &Function) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    for (block_idx, block) in func.basic_blocks.iter().enumerate() {
        for (stmt_idx, stmt) in block.statements.iter().enumerate() {
            if let Statement::Assign(place, rvalue) = stmt {
                // Check if result type is float
                if let Some(result_ty) = get_place_type(func, place) {
                    if !matches!(result_ty, Ty::Float(_)) {
                        continue;
                    }

                    // Handle BinaryOp
                    if let Rvalue::BinaryOp(op, _lhs, _rhs) = rvalue {
                        if !is_float_arithmetic(op) {
                            continue; // Skip comparisons
                        }

                        let location = VcLocation {
                            function: func.name.clone(),
                            block: block_idx,
                            statement: stmt_idx,
                            source_file: None,
                            source_line: None,
                            source_column: None,
                            contract_text: None,
                            vc_kind: VcKind::FloatingPointNaN,
                        };

                        // Encode operands and result as terms (placeholder - real encoding in VCGen)
                        let result_term = Term::Const(place.local.clone());
                        let lhs_term = Term::Const("lhs".to_string());
                        let rhs_term = Term::Const("rhs".to_string());
                        let operands = vec![lhs_term, rhs_term];

                        let op_name = format!("{:?}", op);

                        // Generate NaN propagation VC
                        vcs.push(nan_propagation_vc(
                            result_term.clone(),
                            &operands,
                            &op_name,
                            location.clone(),
                        ));

                        // Generate Infinity overflow VC
                        vcs.push(infinity_overflow_vc(
                            result_term,
                            &operands,
                            &op_name,
                            location,
                        ));
                    }

                    // UnaryOp(Neg) for floats: Neg preserves NaN/Inf, so no VCs needed
                }
            }
        }
    }

    vcs
}

/// Helper: get the type of a place.
fn get_place_type<'a>(func: &'a Function, place: &crate::ir::Place) -> Option<&'a Ty> {
    if func.return_local.name == place.local {
        return Some(&func.return_local.ty);
    }
    for p in &func.params {
        if p.name == place.local {
            return Some(&p.ty);
        }
    }
    for l in &func.locals {
        if l.name == place.local {
            return Some(&l.ty);
        }
    }
    None
}

/// Helper: check if operation is float arithmetic (may produce NaN/Inf).
pub fn is_float_arithmetic(op: &BinOp) -> bool {
    matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div)
}

// === Unit tests (RED phase) ===

#[cfg(test)]
mod tests {
    use super::*;

    fn var(name: &str) -> Term {
        Term::Const(name.to_string())
    }

    fn test_location() -> VcLocation {
        VcLocation {
            function: "test_fn".to_string(),
            block: 0,
            statement: 0,
            source_file: None,
            source_line: None,
            source_column: None,
            contract_text: None,
            vc_kind: VcKind::FloatingPointNaN,
        }
    }

    #[test]
    fn test_nan_propagation_vc_binary() {
        let result = var("result");
        let operands = vec![var("x"), var("y")];
        let vc = nan_propagation_vc(result, &operands, "fp.add", test_location());

        // VC should have description mentioning NaN and operation
        assert!(vc.description.contains("NaN"));
        assert!(vc.description.contains("fp.add"));
    }

    #[test]
    fn test_nan_propagation_vc_description() {
        let vc = nan_propagation_vc(var("r"), &[var("a"), var("b")], "fp.mul", test_location());
        assert!(vc.description.contains("fp.mul"));
    }

    #[test]
    fn test_nan_propagation_vc_kind() {
        let vc = nan_propagation_vc(var("r"), &[var("a")], "fp.sqrt", test_location());
        assert_eq!(vc.location.vc_kind, VcKind::FloatingPointNaN);
    }

    #[test]
    fn test_infinity_overflow_vc_binary() {
        let result = var("result");
        let operands = vec![var("x"), var("y")];
        let vc = infinity_overflow_vc(result, &operands, "fp.add", test_location());

        // VC should have description mentioning overflow or infinity
        assert!(vc.description.contains("overflow") || vc.description.contains("infinity"));
    }

    #[test]
    fn test_infinity_overflow_vc_description() {
        let vc = infinity_overflow_vc(var("r"), &[var("a"), var("b")], "fp.div", test_location());
        assert!(vc.description.contains("fp.div"));
    }

    #[test]
    fn test_is_float_arithmetic() {
        // Arithmetic ops return true
        assert!(is_float_arithmetic(&BinOp::Add));
        assert!(is_float_arithmetic(&BinOp::Sub));
        assert!(is_float_arithmetic(&BinOp::Mul));
        assert!(is_float_arithmetic(&BinOp::Div));

        // Comparisons return false
        assert!(!is_float_arithmetic(&BinOp::Eq));
        assert!(!is_float_arithmetic(&BinOp::Lt));

        // Bitwise returns false (would panic on floats anyway)
        assert!(!is_float_arithmetic(&BinOp::Shl));
    }

    #[test]
    fn test_generate_float_vcs_no_floats() {
        use crate::ir::{BasicBlock, Contracts, IntTy, Local, Terminator, Ty};

        // Function with no float operations
        let func = Function {
            name: "no_floats".to_string(),
            params: vec![Local::new("x", Ty::Int(IntTy::I32))],
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
        };

        let vcs = generate_float_vcs(&func);
        assert_eq!(
            vcs.len(),
            0,
            "Function with no floats should produce no VCs"
        );
    }
}
