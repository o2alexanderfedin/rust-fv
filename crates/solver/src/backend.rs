//! Abstraction over different SMT solver backends.
//!
//! This module provides the `SolverBackend` trait, which enables
//! pluggable backends: subprocess-based (CliSolver for Z3/CVC5/Yices)
//! and native API (Z3NativeSolver).
//!
//! The factory functions `create_default_backend` and `create_backend`
//! select the appropriate backend based on feature flags and solver kind.

use rust_fv_smtlib::script::Script;

use crate::config::SolverKind;
use crate::error::SolverError;
use crate::result::SolverResult;
use crate::solver::CliSolver;

/// Trait abstracting over different SMT solver backends.
///
/// This trait allows the verification pipeline to use different solver
/// implementations transparently: subprocess-based (CliSolver) or native API (Z3NativeSolver).
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

/// Implement `SolverBackend` for the CLI-based solver (Z3, CVC5, Yices).
impl SolverBackend for CliSolver {
    fn check_sat(&self, script: &Script) -> Result<SolverResult, SolverError> {
        self.check_sat(script)
    }
}

/// Create a solver backend for the specified solver kind.
///
/// For Z3 with the `z3-native` feature enabled, returns the native API backend.
/// For all other cases (CVC5, Yices, or Z3 without native), returns a CLI backend.
pub fn create_backend(kind: SolverKind) -> Result<Box<dyn SolverBackend>, SolverError> {
    #[cfg(feature = "z3-native")]
    if kind == SolverKind::Z3 {
        use crate::z3_native::Z3NativeSolver;
        tracing::debug!("Using Z3 native API backend");
        return Ok(Box::new(Z3NativeSolver::new()));
    }

    tracing::debug!("Using {kind} subprocess backend");
    let solver = CliSolver::with_default_config_for(kind)?;
    Ok(Box::new(solver))
}

/// Create the default solver backend (Z3) based on feature flags.
///
/// - If `z3-native` feature is enabled (default), returns `Z3NativeSolver`
/// - Otherwise, falls back to subprocess-based `CliSolver`
///
/// This factory ensures the verification pipeline automatically uses
/// the most appropriate backend without manual configuration.
pub fn create_default_backend() -> Result<Box<dyn SolverBackend>, SolverError> {
    create_backend(SolverKind::Z3)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_fv_smtlib::command::Command as SmtCmd;
    use rust_fv_smtlib::sort::Sort;
    use rust_fv_smtlib::term::Term;

    #[test]
    fn subprocess_backend_works() {
        let solver = CliSolver::with_default_config().expect("Z3 not found");

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

    #[test]
    fn create_backend_z3_succeeds() {
        let backend = create_backend(SolverKind::Z3);
        assert!(backend.is_ok(), "Z3 backend creation should succeed");
    }

    #[test]
    fn create_backend_cvc5_fails_when_not_installed() {
        // CVC5 is not installed on this system
        let backend = create_backend(SolverKind::Cvc5);
        if backend.is_err() {
            // Expected: CVC5 not found
            let err = backend.err().unwrap();
            assert!(
                err.to_string().contains("CVC5"),
                "Error should mention CVC5"
            );
        }
        // If it succeeds, CVC5 was found -- that's fine too
    }

    #[test]
    fn create_backend_yices_fails_when_not_installed() {
        // Yices is not installed on this system
        let backend = create_backend(SolverKind::Yices);
        if backend.is_err() {
            let err = backend.err().unwrap();
            assert!(
                err.to_string().contains("Yices"),
                "Error should mention Yices"
            );
        }
    }
}
