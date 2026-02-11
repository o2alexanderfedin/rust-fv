use std::fmt;
use std::path::PathBuf;

/// Errors from solver interaction.
#[derive(Debug)]
pub enum SolverError {
    /// Z3 binary not found at the specified path.
    NotFound(PathBuf),
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
            SolverError::NotFound(path) => write!(f, "Z3 binary not found at: {}", path.display()),
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
            (SolverError::NotFound(a), SolverError::NotFound(b)) => a == b,
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
        let err = SolverError::NotFound(PathBuf::from("/no/z3"));
        assert_eq!(err.to_string(), "Z3 binary not found at: /no/z3");
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
