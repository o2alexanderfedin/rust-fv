use std::fmt;
use std::path::PathBuf;

use crate::config::SolverKind;

/// Errors from solver interaction.
#[derive(Debug)]
pub enum SolverError {
    /// Solver binary not found at the specified path.
    NotFound(SolverKind, PathBuf),
    /// Process failed to start or crashed.
    ProcessError(String),
    /// Failed to parse solver output.
    ParseError(String),
    /// Timeout exceeded.
    Timeout,
}

impl fmt::Display for SolverError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SolverError::NotFound(kind, path) => {
                write!(f, "{kind} binary not found at: {}", path.display())
            }
            SolverError::ProcessError(msg) => write!(f, "Solver process error: {msg}"),
            SolverError::ParseError(msg) => write!(f, "Failed to parse solver output: {msg}"),
            SolverError::Timeout => write!(f, "Solver timeout exceeded"),
        }
    }
}

impl std::error::Error for SolverError {}

impl PartialEq for SolverError {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (SolverError::NotFound(k1, a), SolverError::NotFound(k2, b)) => k1 == k2 && a == b,
            (SolverError::ProcessError(a), SolverError::ProcessError(b)) => a == b,
            (SolverError::ParseError(a), SolverError::ParseError(b)) => a == b,
            (SolverError::Timeout, SolverError::Timeout) => true,
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn display_not_found() {
        let err = SolverError::NotFound(SolverKind::Z3, PathBuf::from("/no/z3"));
        assert_eq!(err.to_string(), "Z3 binary not found at: /no/z3");
    }

    #[test]
    fn display_not_found_cvc5() {
        let err = SolverError::NotFound(SolverKind::Cvc5, PathBuf::from("/no/cvc5"));
        assert_eq!(err.to_string(), "CVC5 binary not found at: /no/cvc5");
    }

    #[test]
    fn display_not_found_yices() {
        let err = SolverError::NotFound(SolverKind::Yices, PathBuf::from("/no/yices-smt2"));
        assert_eq!(err.to_string(), "Yices binary not found at: /no/yices-smt2");
    }

    #[test]
    fn display_process_error() {
        let err = SolverError::ProcessError("crashed".to_string());
        assert_eq!(err.to_string(), "Solver process error: crashed");
    }

    #[test]
    fn display_parse_error() {
        let err = SolverError::ParseError("bad output".to_string());
        assert_eq!(err.to_string(), "Failed to parse solver output: bad output");
    }

    #[test]
    fn display_timeout() {
        let err = SolverError::Timeout;
        assert_eq!(err.to_string(), "Solver timeout exceeded");
    }

    #[test]
    fn error_equality() {
        assert_eq!(SolverError::Timeout, SolverError::Timeout);
        assert_ne!(SolverError::Timeout, SolverError::ProcessError("x".into()));
    }
}
