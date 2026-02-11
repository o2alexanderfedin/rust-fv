use std::path::PathBuf;

use crate::error::SolverError;

/// Common locations where Z3 might be installed.
const Z3_COMMON_PATHS: &[&str] = &["/opt/homebrew/bin/z3", "/usr/local/bin/z3", "/usr/bin/z3"];

/// Solver configuration.
#[derive(Debug, Clone)]
pub struct SolverConfig {
    /// Path to the Z3 binary.
    pub z3_path: PathBuf,
    /// Timeout in milliseconds (0 = no timeout).
    pub timeout_ms: u64,
    /// Additional solver arguments.
    pub extra_args: Vec<String>,
}

impl SolverConfig {
    /// Create a new config with the given Z3 path.
    pub fn new(z3_path: PathBuf) -> Self {
        Self {
            z3_path,
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

    /// Auto-detect Z3 location.
    ///
    /// Tries `which z3` first, then checks common installation paths.
    pub fn auto_detect() -> Result<Self, SolverError> {
        // Try `which z3` via PATH lookup
        if let Ok(output) = std::process::Command::new("which").arg("z3").output()
            && output.status.success()
        {
            let path_str = String::from_utf8_lossy(&output.stdout).trim().to_string();
            if !path_str.is_empty() {
                let path = PathBuf::from(&path_str);
                if path.exists() {
                    return Ok(Self::new(path));
                }
            }
        }

        // Fall back to common paths
        for candidate in Z3_COMMON_PATHS {
            let path = PathBuf::from(candidate);
            if path.exists() {
                return Ok(Self::new(path));
            }
        }

        Err(SolverError::NotFound(PathBuf::from("z3")))
    }

    /// Validate that the configured Z3 binary exists.
    pub fn validate(&self) -> Result<(), SolverError> {
        if !self.z3_path.exists() {
            return Err(SolverError::NotFound(self.z3_path.clone()));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_config() {
        let config = SolverConfig::new(PathBuf::from("/opt/homebrew/bin/z3"));
        assert_eq!(config.z3_path, PathBuf::from("/opt/homebrew/bin/z3"));
        assert_eq!(config.timeout_ms, 0);
        assert!(config.extra_args.is_empty());
    }

    #[test]
    fn builder_pattern() {
        let config = SolverConfig::new(PathBuf::from("/opt/homebrew/bin/z3"))
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
        assert!(config.z3_path.exists());
    }

    #[test]
    fn validate_existing_binary() {
        let config = SolverConfig::new(PathBuf::from("/opt/homebrew/bin/z3"));
        assert!(config.validate().is_ok());
    }

    #[test]
    fn validate_missing_binary() {
        let config = SolverConfig::new(PathBuf::from("/nonexistent/z3"));
        let err = config.validate().unwrap_err();
        assert_eq!(err, SolverError::NotFound(PathBuf::from("/nonexistent/z3")));
    }
}
