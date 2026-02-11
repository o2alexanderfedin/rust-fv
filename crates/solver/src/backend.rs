//! Abstraction over different SMT solver backends.
//!
//! This module provides the `SolverBackend` trait, which enables
//! pluggable backends: subprocess-based (Z3Solver) and native API (Z3NativeSolver).
//!
//! The factory function `create_default_backend` selects the appropriate backend
//! based on feature flags.

use rust_fv_smtlib::script::Script;

use crate::error::SolverError;
use crate::result::SolverResult;
use crate::solver::Z3Solver;

/// Trait abstracting over different SMT solver backends.
///
/// This trait allows the verification pipeline to use different solver
/// implementations transparently: subprocess-based (Z3Solver) or native API (Z3NativeSolver).
pub trait SolverBackend {
    /// Check satisfiability of the given SMT script.
    ///
    /// Returns:
    /// - `Ok(SolverResult::Sat(model))` if satisfiable (counterexample found)
    /// - `Ok(SolverResult::Unsat)` if unsatisfiable (property proved)
    /// - `Ok(SolverResult::Unknown(reason))` if solver couldn't determine
    /// - `Err(SolverError)` if the solver invocation failed
    fn check_sat(&self, script: &Script) -> Result<SolverResult, SolverError>;
}

/// Implement `SolverBackend` for the existing subprocess-based Z3Solver.
impl SolverBackend for Z3Solver {
    fn check_sat(&self, script: &Script) -> Result<SolverResult, SolverError> {
        // Delegate to the existing check_sat method
        self.check_sat(script)
    }
}

/// Create the default solver backend based on feature flags.
///
/// - If `z3-native` feature is enabled (default), returns `Z3NativeSolver`
/// - Otherwise, falls back to subprocess-based `Z3Solver`
///
/// This factory ensures the verification pipeline automatically uses
/// the most appropriate backend without manual configuration.
pub fn create_default_backend() -> Result<Box<dyn SolverBackend>, SolverError> {
    #[cfg(feature = "z3-native")]
    {
        use crate::z3_native::Z3NativeSolver;
        tracing::debug!("Using Z3 native API backend");
        Ok(Box::new(Z3NativeSolver::new()))
    }

    #[cfg(not(feature = "z3-native"))]
    {
        tracing::debug!("Using Z3 subprocess backend");
        let solver = Z3Solver::with_default_config()?;
        Ok(Box::new(solver))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_fv_smtlib::command::Command as SmtCmd;
    use rust_fv_smtlib::sort::Sort;
    use rust_fv_smtlib::term::Term;

    #[test]
    fn subprocess_backend_works() {
        let solver = Z3Solver::with_default_config().expect("Z3 not found");

        let mut script = Script::new();
        script.push(SmtCmd::SetLogic("QF_BV".to_string()));
        script.push(SmtCmd::DeclareConst("x".to_string(), Sort::BitVec(32)));
        script.push(SmtCmd::Assert(Term::BvUGt(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::BitVecLit(0, 32)),
        )));

        let result = solver.check_sat(&script).expect("check_sat failed");
        assert!(result.is_sat(), "Expected SAT result");
    }

    #[test]
    fn create_default_backend_succeeds() {
        let backend = create_default_backend();
        assert!(backend.is_ok(), "Default backend creation should succeed");
    }
}
