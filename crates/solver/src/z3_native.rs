//! Native Z3 API backend using the z3 crate.
//!
//! This module provides `Z3NativeSolver`, which uses the z3 crate's Rust bindings
//! to the Z3 C API. This eliminates subprocess overhead (~50ms/query) and enables
//! incremental solving (push/pop).
//!
//! ## Requirements
//!
//! This implementation requires Z3 to be installed on the system. The z3 crate
//! links against the system Z3 library.
//!
//! Install Z3:
//! - macOS: `brew install z3`
//! - Ubuntu/Debian: `apt-get install libz3-dev`
//! - Windows: Download from https://github.com/Z3Prover/z3/releases
//!
//! Note: The `bundled` feature (which compiles Z3 from source) is NOT used to avoid
//! large build times and disk space requirements. The subprocess backend remains
//! available as a fallback if Z3 native linking fails.

use std::collections::HashMap;

use rust_fv_smtlib::command::Command as SmtCmd;
use rust_fv_smtlib::script::Script;
use rust_fv_smtlib::sort::Sort;
use rust_fv_smtlib::term::Term;
use z3::ast::{Bool, BV};
use z3::{Config, SatResult, Solver};

use crate::error::SolverError;
use crate::model::Model;
use crate::result::SolverResult;

/// Native Z3 solver backend using the z3 crate API.
///
/// This implementation parses SMT-LIB Script AST into z3 native API calls.
/// z3 0.19 uses a global context model, so we don't need to manage Context explicitly.
pub struct Z3NativeSolver {
    _config: Config,
}

impl Z3NativeSolver {
    /// Create a new Z3 native solver with default configuration.
    pub fn new() -> Self {
        let config = Config::new();
        Self { _config: config }
    }

    /// Parse and solve an SMT script using the native Z3 API.
    fn solve_script(&self, script: &Script) -> Result<SolverResult, SolverError> {
        let start = std::time::Instant::now();

        // Create a fresh solver (z3 0.19 uses global context)
        let solver = Solver::new();

        // Symbol table for declared constants/functions
        let mut symbols: HashMap<String, Z3Value> = HashMap::new();

        // Process each command in the script
        for cmd in script.commands() {
            match cmd {
                SmtCmd::SetLogic(_) | SmtCmd::SetOption(_, _) => {
                    // Ignore logic/options -- z3 handles these internally
                }
                SmtCmd::DeclareConst(name, sort) => {
                    let value = create_const(name, sort)?;
                    symbols.insert(name.clone(), value);
                }
                SmtCmd::Assert(term) => {
                    let ast = translate_term(&symbols, term)?;
                    match ast {
                        Z3Value::Bool(b) => solver.assert(&b),
                        _ => {
                            return Err(SolverError::ParseError(
                                "Assert requires Bool term".to_string(),
                            ))
                        }
                    }
                }
                SmtCmd::CheckSat => {
                    // Will be handled after loop
                }
                SmtCmd::GetModel => {
                    // Will be handled after SAT result
                }
                _ => {
                    tracing::warn!("Unsupported SMT command: {:?}", cmd);
                }
            }
        }

        // Check satisfiability
        let result = match solver.check() {
            SatResult::Sat => {
                tracing::debug!("Z3 native: SAT in {:?}", start.elapsed());
                let model = solver.get_model().map(|m| extract_model(&m, &symbols));
                SolverResult::Sat(model)
            }
            SatResult::Unsat => {
                tracing::debug!("Z3 native: UNSAT in {:?}", start.elapsed());
                SolverResult::Unsat
            }
            SatResult::Unknown => {
                tracing::debug!("Z3 native: UNKNOWN in {:?}", start.elapsed());
                SolverResult::Unknown("unknown".to_string())
            }
        };

        Ok(result)
    }
}

impl Default for Z3NativeSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl crate::backend::SolverBackend for Z3NativeSolver {
    fn check_sat(&self, script: &Script) -> Result<SolverResult, SolverError> {
        self.solve_script(script)
    }
}

/// Z3 value wrapper supporting different AST types.
#[derive(Clone)]
enum Z3Value {
    Bool(Bool),
    BV(BV),
}

/// Create a Z3 constant of the given sort.
fn create_const(name: &str, sort: &Sort) -> Result<Z3Value, SolverError> {
    match sort {
        Sort::Bool => Ok(Z3Value::Bool(Bool::new_const(name))),
        Sort::BitVec(width) => Ok(Z3Value::BV(BV::new_const(name, *width))),
        Sort::Int => Err(SolverError::ParseError(
            "Int sort not yet supported in native backend".to_string(),
        )),
        _ => Err(SolverError::ParseError(format!(
            "Unsupported sort in native backend: {:?}",
            sort
        ))),
    }
}

/// Translate an SMT-LIB Term into a Z3 AST.
fn translate_term(symbols: &HashMap<String, Z3Value>, term: &Term) -> Result<Z3Value, SolverError> {
    match term {
        // Boolean literals
        Term::BoolLit(true) => Ok(Z3Value::Bool(Bool::from_bool(true))),
        Term::BoolLit(false) => Ok(Z3Value::Bool(Bool::from_bool(false))),

        // BitVec literals
        Term::BitVecLit(val, width) => {
            let unsigned = if *width >= 128 {
                *val as u64 // Truncate for very large widths
            } else {
                let mask = (1i128 << width) - 1;
                (val & mask) as u64
            };
            Ok(Z3Value::BV(BV::from_u64(unsigned, *width)))
        }

        // Variable reference
        Term::Const(name) => symbols
            .get(name)
            .cloned()
            .ok_or_else(|| SolverError::ParseError(format!("Undefined symbol: {}", name))),

        // Boolean operations
        Term::Not(a) => {
            let a_ast = translate_term(symbols, a)?;
            match a_ast {
                Z3Value::Bool(b) => Ok(Z3Value::Bool(b.not())),
                _ => Err(SolverError::ParseError("Not requires Bool".to_string())),
            }
        }
        Term::And(terms) => {
            let bools: Result<Vec<Bool>, SolverError> = terms
                .iter()
                .map(|t| match translate_term(symbols, t)? {
                    Z3Value::Bool(b) => Ok(b),
                    _ => Err(SolverError::ParseError("And requires Bool".to_string())),
                })
                .collect();
            let bools = bools?;
            let refs: Vec<&Bool> = bools.iter().collect();
            Ok(Z3Value::Bool(Bool::and(&refs)))
        }
        Term::Or(terms) => {
            let bools: Result<Vec<Bool>, SolverError> = terms
                .iter()
                .map(|t| match translate_term(symbols, t)? {
                    Z3Value::Bool(b) => Ok(b),
                    _ => Err(SolverError::ParseError("Or requires Bool".to_string())),
                })
                .collect();
            let bools = bools?;
            let refs: Vec<&Bool> = bools.iter().collect();
            Ok(Z3Value::Bool(Bool::or(&refs)))
        }
        Term::Implies(a, b) => {
            let a_ast = translate_term(symbols, a)?;
            let b_ast = translate_term(symbols, b)?;
            match (a_ast, b_ast) {
                (Z3Value::Bool(a_b), Z3Value::Bool(b_b)) => Ok(Z3Value::Bool(a_b.implies(&b_b))),
                _ => Err(SolverError::ParseError(
                    "Implies requires Bool".to_string(),
                )),
            }
        }

        // Equality
        Term::Eq(a, b) => {
            let a_ast = translate_term(symbols, a)?;
            let b_ast = translate_term(symbols, b)?;
            match (a_ast, b_ast) {
                (Z3Value::Bool(a_b), Z3Value::Bool(b_b)) => Ok(Z3Value::Bool(a_b.eq(&b_b))),
                (Z3Value::BV(a_bv), Z3Value::BV(b_bv)) => Ok(Z3Value::Bool(a_bv.eq(&b_bv))),
                _ => Err(SolverError::ParseError(
                    "Eq requires matching sorts".to_string(),
                )),
            }
        }

        // Bitvector arithmetic
        Term::BvAdd(a, b) => translate_bv_binary(symbols, a, b, |x, y| x.bvadd(&y)),
        Term::BvSub(a, b) => translate_bv_binary(symbols, a, b, |x, y| x.bvsub(&y)),
        Term::BvMul(a, b) => translate_bv_binary(symbols, a, b, |x, y| x.bvmul(&y)),
        Term::BvSDiv(a, b) => translate_bv_binary(symbols, a, b, |x, y| x.bvsdiv(&y)),
        Term::BvUDiv(a, b) => translate_bv_binary(symbols, a, b, |x, y| x.bvudiv(&y)),
        Term::BvSRem(a, b) => translate_bv_binary(symbols, a, b, |x, y| x.bvsrem(&y)),
        Term::BvURem(a, b) => translate_bv_binary(symbols, a, b, |x, y| x.bvurem(&y)),
        Term::BvNeg(a) => translate_bv_unary(symbols, a, |x| x.bvneg()),
        Term::BvAnd(a, b) => translate_bv_binary(symbols, a, b, |x, y| x.bvand(&y)),
        Term::BvOr(a, b) => translate_bv_binary(symbols, a, b, |x, y| x.bvor(&y)),
        Term::BvXor(a, b) => translate_bv_binary(symbols, a, b, |x, y| x.bvxor(&y)),
        Term::BvNot(a) => translate_bv_unary(symbols, a, |x| x.bvnot()),
        Term::BvShl(a, b) => translate_bv_binary(symbols, a, b, |x, y| x.bvshl(&y)),
        Term::BvLShr(a, b) => translate_bv_binary(symbols, a, b, |x, y| x.bvlshr(&y)),
        Term::BvAShr(a, b) => translate_bv_binary(symbols, a, b, |x, y| x.bvashr(&y)),

        // Bitvector comparisons
        Term::BvULt(a, b) => translate_bv_cmp(symbols, a, b, |x, y| x.bvult(&y)),
        Term::BvULe(a, b) => translate_bv_cmp(symbols, a, b, |x, y| x.bvule(&y)),
        Term::BvUGt(a, b) => translate_bv_cmp(symbols, a, b, |x, y| x.bvugt(&y)),
        Term::BvUGe(a, b) => translate_bv_cmp(symbols, a, b, |x, y| x.bvuge(&y)),
        Term::BvSLt(a, b) => translate_bv_cmp(symbols, a, b, |x, y| x.bvslt(&y)),
        Term::BvSLe(a, b) => translate_bv_cmp(symbols, a, b, |x, y| x.bvsle(&y)),
        Term::BvSGt(a, b) => translate_bv_cmp(symbols, a, b, |x, y| x.bvsgt(&y)),
        Term::BvSGe(a, b) => translate_bv_cmp(symbols, a, b, |x, y| x.bvsge(&y)),

        // Bitvector extensions
        Term::ZeroExtend(n, a) => translate_bv_unary(symbols, a, |x| x.zero_ext(*n)),
        Term::SignExtend(n, a) => translate_bv_unary(symbols, a, |x| x.sign_ext(*n)),

        // If-then-else
        Term::Ite(cond, then_val, else_val) => {
            let cond_ast = translate_term(symbols, cond)?;
            let then_ast = translate_term(symbols, then_val)?;
            let else_ast = translate_term(symbols, else_val)?;
            match (cond_ast, then_ast, else_ast) {
                (Z3Value::Bool(c), Z3Value::BV(t), Z3Value::BV(e)) => {
                    Ok(Z3Value::BV(c.ite(&t, &e)))
                }
                (Z3Value::Bool(c), Z3Value::Bool(t), Z3Value::Bool(e)) => {
                    Ok(Z3Value::Bool(c.ite(&t, &e)))
                }
                _ => Err(SolverError::ParseError(
                    "ITE requires Bool condition and matching branches".to_string(),
                )),
            }
        }

        _ => Err(SolverError::ParseError(format!(
            "Unsupported term in native backend: {:?}",
            term
        ))),
    }
}

/// Helper for bitvector binary operations.
fn translate_bv_binary<F>(
    symbols: &HashMap<String, Z3Value>,
    a: &Term,
    b: &Term,
    op: F,
) -> Result<Z3Value, SolverError>
where
    F: FnOnce(BV, BV) -> BV,
{
    let a_ast = translate_term(symbols, a)?;
    let b_ast = translate_term(symbols, b)?;
    match (a_ast, b_ast) {
        (Z3Value::BV(a_bv), Z3Value::BV(b_bv)) => Ok(Z3Value::BV(op(a_bv, b_bv))),
        _ => Err(SolverError::ParseError(
            "BV operation requires BV arguments".to_string(),
        )),
    }
}

/// Helper for bitvector unary operations.
fn translate_bv_unary<F>(symbols: &HashMap<String, Z3Value>, a: &Term, op: F) -> Result<Z3Value, SolverError>
where
    F: FnOnce(BV) -> BV,
{
    let a_ast = translate_term(symbols, a)?;
    match a_ast {
        Z3Value::BV(a_bv) => Ok(Z3Value::BV(op(a_bv))),
        _ => Err(SolverError::ParseError(
            "BV operation requires BV argument".to_string(),
        )),
    }
}

/// Helper for bitvector comparison operations.
fn translate_bv_cmp<F>(
    symbols: &HashMap<String, Z3Value>,
    a: &Term,
    b: &Term,
    op: F,
) -> Result<Z3Value, SolverError>
where
    F: FnOnce(BV, BV) -> Bool,
{
    let a_ast = translate_term(symbols, a)?;
    let b_ast = translate_term(symbols, b)?;
    match (a_ast, b_ast) {
        (Z3Value::BV(a_bv), Z3Value::BV(b_bv)) => Ok(Z3Value::Bool(op(a_bv, b_bv))),
        _ => Err(SolverError::ParseError(
            "BV comparison requires BV arguments".to_string(),
        )),
    }
}

/// Extract a model from Z3's native model representation.
fn extract_model(model: &z3::Model, symbols: &HashMap<String, Z3Value>) -> Model {
    let mut assignments = Vec::new();

    for (name, value) in symbols {
        let eval_result = match value {
            Z3Value::Bool(b) => model.eval(b, true).map(|v: Bool| v.to_string()),
            Z3Value::BV(bv) => model.eval(bv, true).map(|v: BV| v.to_string()),
        };

        if let Some(val_str) = eval_result {
            assignments.push((name.clone(), val_str));
        }
    }

    Model::with_assignments(assignments)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_fv_smtlib::command::Command as SmtCmd;
    use rust_fv_smtlib::sort::Sort;
    use rust_fv_smtlib::term::Term;

    #[test]
    fn test_basic_sat() {
        let solver = Z3NativeSolver::new();

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

        let result = solver.solve_script(&script).expect("solve failed");
        assert!(result.is_sat(), "Expected SAT");
        assert!(result.model().is_some(), "Expected model");
    }

    #[test]
    fn test_basic_unsat() {
        let solver = Z3NativeSolver::new();

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

        let result = solver.solve_script(&script).expect("solve failed");
        assert!(result.is_unsat(), "Expected UNSAT");
    }

    #[test]
    fn test_bitvector_overflow() {
        let solver = Z3NativeSolver::new();

        let mut script = Script::new();
        script.push(SmtCmd::SetLogic("QF_BV".to_string()));
        script.push(SmtCmd::DeclareConst("x".to_string(), Sort::BitVec(8)));
        script.push(SmtCmd::DeclareConst("y".to_string(), Sort::BitVec(8)));

        // x = 200, y = 100, x + y = 44 (overflow)
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

        let result = solver.solve_script(&script).expect("solve failed");
        assert!(result.is_sat(), "Expected SAT (overflow is modular)");
    }

    #[test]
    fn test_boolean_logic() {
        let solver = Z3NativeSolver::new();

        let mut script = Script::new();
        script.push(SmtCmd::SetLogic("QF_BV".to_string()));
        script.push(SmtCmd::DeclareConst("a".to_string(), Sort::Bool));
        script.push(SmtCmd::DeclareConst("b".to_string(), Sort::Bool));

        // (a AND b) => a
        script.push(SmtCmd::Assert(Term::Not(Box::new(Term::Implies(
            Box::new(Term::And(vec![
                Term::Const("a".to_string()),
                Term::Const("b".to_string()),
            ])),
            Box::new(Term::Const("a".to_string())),
        )))));

        let result = solver.solve_script(&script).expect("solve failed");
        assert!(result.is_unsat(), "Expected UNSAT (tautology)");
    }
}
