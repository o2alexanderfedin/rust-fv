use crate::model::Model;

/// Result from the SMT solver.
#[derive(Debug, Clone, PartialEq)]
pub enum SolverResult {
    /// Formula is satisfiable (verification condition FAILED -- found counterexample).
    Sat(Option<Model>),
    /// Formula is unsatisfiable (verification condition PROVED).
    Unsat,
    /// Solver couldn't determine (timeout, resource limit, etc.).
    Unknown(String),
}

impl SolverResult {
    /// Returns `true` if the result is `Sat`.
    pub fn is_sat(&self) -> bool {
        matches!(self, SolverResult::Sat(_))
    }

    /// Returns `true` if the result is `Unsat`.
    pub fn is_unsat(&self) -> bool {
        matches!(self, SolverResult::Unsat)
    }

    /// Returns `true` if the result is `Unknown`.
    pub fn is_unknown(&self) -> bool {
        matches!(self, SolverResult::Unknown(_))
    }

    /// Returns the model if the result is `Sat` with a model.
    pub fn model(&self) -> Option<&Model> {
        match self {
            SolverResult::Sat(Some(model)) => Some(model),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sat_predicates() {
        let sat = SolverResult::Sat(None);
        assert!(sat.is_sat());
        assert!(!sat.is_unsat());
        assert!(!sat.is_unknown());
    }

    #[test]
    fn unsat_predicates() {
        let unsat = SolverResult::Unsat;
        assert!(!unsat.is_sat());
        assert!(unsat.is_unsat());
        assert!(!unsat.is_unknown());
    }

    #[test]
    fn unknown_predicates() {
        let unknown = SolverResult::Unknown("timeout".to_string());
        assert!(!unknown.is_sat());
        assert!(!unknown.is_unsat());
        assert!(unknown.is_unknown());
    }

    #[test]
    fn model_accessor() {
        let model = Model::with_assignments(vec![("x".to_string(), "5".to_string())]);
        let sat_with = SolverResult::Sat(Some(model.clone()));
        assert_eq!(sat_with.model(), Some(&model));

        let sat_without = SolverResult::Sat(None);
        assert_eq!(sat_without.model(), None);

        let unsat = SolverResult::Unsat;
        assert_eq!(unsat.model(), None);
    }
}
