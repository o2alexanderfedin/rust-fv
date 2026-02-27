use std::fmt;
use std::path::PathBuf;

use crate::error::SolverError;

/// Supported SMT solver backends.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SolverKind {
    /// Z3 from Microsoft Research.
    Z3,
    /// CVC5 from Stanford/Iowa.
    Cvc5,
    /// Yices2 from SRI International.
    Yices,
}

impl SolverKind {
    /// Binary name used for PATH lookup.
    pub fn binary_name(&self) -> &'static str {
        match self {
            SolverKind::Z3 => "z3",
            SolverKind::Cvc5 => "cvc5",
            SolverKind::Yices => "yices-smt2",
        }
    }

    /// Common installation paths to check when PATH lookup fails.
    fn common_paths(&self) -> &'static [&'static str] {
        match self {
            SolverKind::Z3 => &["/opt/homebrew/bin/z3", "/usr/local/bin/z3", "/usr/bin/z3"],
            SolverKind::Cvc5 => &[
                "/opt/homebrew/bin/cvc5",
                "/usr/local/bin/cvc5",
                "/usr/bin/cvc5",
            ],
            SolverKind::Yices => &[
                "/opt/homebrew/bin/yices-smt2",
                "/usr/local/bin/yices-smt2",
                "/usr/bin/yices-smt2",
            ],
        }
    }

    /// Build solver-specific CLI arguments for stdin mode.
    pub fn stdin_args(&self) -> Vec<String> {
        match self {
            SolverKind::Z3 => vec!["-in".to_string()],
            SolverKind::Cvc5 => vec![
                "--lang".to_string(),
                "smt2".to_string(),
                "--produce-models".to_string(),
                "--incremental".to_string(),
            ],
            SolverKind::Yices => vec!["--incremental".to_string()],
        }
    }

    /// Build solver-specific timeout argument, if supported.
    pub fn timeout_arg(&self, timeout_ms: u64) -> Option<String> {
        if timeout_ms == 0 {
            return None;
        }
        match self {
            SolverKind::Z3 => Some(format!("-t:{timeout_ms}")),
            SolverKind::Cvc5 => Some(format!("--tlimit={timeout_ms}")),
            SolverKind::Yices => Some(format!("--timeout={}", timeout_ms / 1000)),
        }
    }
}

impl fmt::Display for SolverKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SolverKind::Z3 => write!(f, "Z3"),
            SolverKind::Cvc5 => write!(f, "CVC5"),
            SolverKind::Yices => write!(f, "Yices"),
        }
    }
}

impl std::str::FromStr for SolverKind {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "z3" => Ok(SolverKind::Z3),
            "cvc5" => Ok(SolverKind::Cvc5),
            "yices" | "yices2" | "yices-smt2" => Ok(SolverKind::Yices),
            _ => Err(format!(
                "Unknown solver: {s}. Valid options: z3, cvc5, yices"
            )),
        }
    }
}

/// Solver configuration.
#[derive(Debug, Clone)]
pub struct SolverConfig {
    /// Which solver to use.
    pub kind: SolverKind,
    /// Path to the solver binary.
    pub solver_path: PathBuf,
    /// Timeout in milliseconds (0 = no timeout).
    pub timeout_ms: u64,
    /// Additional solver arguments.
    pub extra_args: Vec<String>,
}

impl SolverConfig {
    /// Create a new config with the given solver kind and path.
    pub fn new(kind: SolverKind, solver_path: PathBuf) -> Self {
        Self {
            kind,
            solver_path,
            timeout_ms: 0,
            extra_args: Vec::new(),
        }
    }

    /// Create config with a specific timeout (in milliseconds).
    pub fn with_timeout(mut self, timeout_ms: u64) -> Self {
        self.timeout_ms = timeout_ms;
        self
    }

    /// Add extra arguments for the solver.
    pub fn with_extra_args(mut self, args: Vec<String>) -> Self {
        self.extra_args = args;
        self
    }

    /// Auto-detect solver location for the given kind.
    ///
    /// Tries `which <binary>` first, then checks common installation paths.
    pub fn auto_detect_for(kind: SolverKind) -> Result<Self, SolverError> {
        let binary = kind.binary_name();

        // Try `which` via PATH lookup
        if let Ok(output) = std::process::Command::new("which").arg(binary).output()
            && output.status.success()
        {
            let path_str = String::from_utf8_lossy(&output.stdout).trim().to_string();
            if !path_str.is_empty() {
                let path = PathBuf::from(&path_str);
                if path.exists() {
                    return Ok(Self::new(kind, path));
                }
            }
        }

        // Fall back to common paths
        for candidate in kind.common_paths() {
            let path = PathBuf::from(candidate);
            if path.exists() {
                return Ok(Self::new(kind, path));
            }
        }

        Err(SolverError::NotFound(kind, PathBuf::from(binary)))
    }

    /// Auto-detect Z3 location (convenience for backward compatibility).
    pub fn auto_detect() -> Result<Self, SolverError> {
        Self::auto_detect_for(SolverKind::Z3)
    }

    /// Build the full argument list for this solver invocation.
    pub fn build_args(&self) -> Vec<String> {
        let mut args = self.kind.stdin_args();

        if let Some(timeout_arg) = self.kind.timeout_arg(self.timeout_ms) {
            args.push(timeout_arg);
        }

        args.extend(self.extra_args.iter().cloned());
        args
    }

    /// Validate that the configured solver binary exists.
    pub fn validate(&self) -> Result<(), SolverError> {
        if !self.solver_path.exists() {
            return Err(SolverError::NotFound(self.kind, self.solver_path.clone()));
        }
        Ok(())
    }

    // Backward-compatible accessor
    #[doc(hidden)]
    pub fn z3_path(&self) -> &PathBuf {
        &self.solver_path
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_config() {
        let config = SolverConfig::new(SolverKind::Z3, PathBuf::from("/opt/homebrew/bin/z3"));
        assert_eq!(config.solver_path, PathBuf::from("/opt/homebrew/bin/z3"));
        assert_eq!(config.kind, SolverKind::Z3);
        assert_eq!(config.timeout_ms, 0);
        assert!(config.extra_args.is_empty());
    }

    #[test]
    fn builder_pattern() {
        let config = SolverConfig::new(SolverKind::Z3, PathBuf::from("/opt/homebrew/bin/z3"))
            .with_timeout(5000)
            .with_extra_args(vec!["-v:1".to_string()]);
        assert_eq!(config.timeout_ms, 5000);
        assert_eq!(config.extra_args, vec!["-v:1".to_string()]);
    }

    #[test]
    fn auto_detect_finds_z3() {
        // Z3 is installed on this system
        let config = SolverConfig::auto_detect();
        assert!(config.is_ok(), "Z3 should be auto-detected on this system");
        let config = config.unwrap();
        assert!(config.solver_path.exists());
        assert_eq!(config.kind, SolverKind::Z3);
    }

    #[test]
    fn validate_existing_binary() {
        // Use auto-detected z3 path (cross-platform: works on macOS, Linux CI, etc.)
        let config = SolverConfig::auto_detect().expect("Z3 must be installed for this test");
        assert!(config.validate().is_ok());
    }

    #[test]
    fn validate_missing_binary() {
        let config = SolverConfig::new(SolverKind::Z3, PathBuf::from("/nonexistent/z3"));
        let err = config.validate().unwrap_err();
        assert_eq!(
            err,
            SolverError::NotFound(SolverKind::Z3, PathBuf::from("/nonexistent/z3"))
        );
    }

    // ---- SolverKind tests ----

    #[test]
    fn solver_kind_binary_names() {
        assert_eq!(SolverKind::Z3.binary_name(), "z3");
        assert_eq!(SolverKind::Cvc5.binary_name(), "cvc5");
        assert_eq!(SolverKind::Yices.binary_name(), "yices-smt2");
    }

    #[test]
    fn solver_kind_display() {
        assert_eq!(SolverKind::Z3.to_string(), "Z3");
        assert_eq!(SolverKind::Cvc5.to_string(), "CVC5");
        assert_eq!(SolverKind::Yices.to_string(), "Yices");
    }

    #[test]
    fn solver_kind_from_str() {
        assert_eq!("z3".parse::<SolverKind>().unwrap(), SolverKind::Z3);
        assert_eq!("cvc5".parse::<SolverKind>().unwrap(), SolverKind::Cvc5);
        assert_eq!("yices".parse::<SolverKind>().unwrap(), SolverKind::Yices);
        assert_eq!("yices2".parse::<SolverKind>().unwrap(), SolverKind::Yices);
        assert_eq!(
            "yices-smt2".parse::<SolverKind>().unwrap(),
            SolverKind::Yices
        );
        assert!("unknown".parse::<SolverKind>().is_err());
    }

    #[test]
    fn solver_kind_stdin_args() {
        let z3_args = SolverKind::Z3.stdin_args();
        assert_eq!(z3_args, vec!["-in"]);

        let cvc5_args = SolverKind::Cvc5.stdin_args();
        assert!(cvc5_args.contains(&"--lang".to_string()));
        assert!(cvc5_args.contains(&"smt2".to_string()));
        assert!(cvc5_args.contains(&"--produce-models".to_string()));

        let yices_args = SolverKind::Yices.stdin_args();
        assert!(yices_args.contains(&"--incremental".to_string()));
    }

    #[test]
    fn solver_kind_timeout_args() {
        assert_eq!(
            SolverKind::Z3.timeout_arg(5000),
            Some("-t:5000".to_string())
        );
        assert_eq!(
            SolverKind::Cvc5.timeout_arg(5000),
            Some("--tlimit=5000".to_string())
        );
        assert_eq!(
            SolverKind::Yices.timeout_arg(5000),
            Some("--timeout=5".to_string())
        );
        assert_eq!(SolverKind::Z3.timeout_arg(0), None);
    }

    #[test]
    fn build_args_z3() {
        let config = SolverConfig::new(SolverKind::Z3, PathBuf::from("/usr/bin/z3"))
            .with_timeout(3000)
            .with_extra_args(vec!["-v:1".to_string()]);
        let args = config.build_args();
        assert_eq!(args, vec!["-in", "-t:3000", "-v:1"]);
    }

    #[test]
    fn build_args_cvc5() {
        let config =
            SolverConfig::new(SolverKind::Cvc5, PathBuf::from("/usr/bin/cvc5")).with_timeout(10000);
        let args = config.build_args();
        assert!(args.contains(&"--lang".to_string()));
        assert!(args.contains(&"--tlimit=10000".to_string()));
    }

    #[test]
    fn build_args_yices() {
        let config = SolverConfig::new(SolverKind::Yices, PathBuf::from("/usr/bin/yices-smt2"))
            .with_timeout(60000);
        let args = config.build_args();
        assert!(args.contains(&"--incremental".to_string()));
        assert!(args.contains(&"--timeout=60".to_string()));
    }
}
