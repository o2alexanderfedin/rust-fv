/// A model (counterexample) from the solver.
///
/// Contains variable assignments extracted from Z3's `(get-model)` output.
#[derive(Debug, Clone, PartialEq)]
pub struct Model {
    /// Variable assignments: `(name, value_string)` pairs.
    pub assignments: Vec<(String, String)>,
}

impl Model {
    /// Create a new empty model.
    pub fn new() -> Self {
        Self {
            assignments: Vec::new(),
        }
    }

    /// Create a model from assignment pairs.
    pub fn with_assignments(assignments: Vec<(String, String)>) -> Self {
        Self { assignments }
    }

    /// Look up a variable's value by name.
    pub fn get(&self, name: &str) -> Option<&str> {
        self.assignments
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, v)| v.as_str())
    }

    /// Return the number of assignments.
    pub fn len(&self) -> usize {
        self.assignments.len()
    }

    /// Return whether the model is empty.
    pub fn is_empty(&self) -> bool {
        self.assignments.is_empty()
    }
}

impl Default for Model {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_model() {
        let model = Model::new();
        assert!(model.is_empty());
        assert_eq!(model.len(), 0);
        assert_eq!(model.get("x"), None);
    }

    #[test]
    fn model_with_assignments() {
        let model = Model::with_assignments(vec![
            ("x".to_string(), "42".to_string()),
            ("y".to_string(), "true".to_string()),
        ]);
        assert_eq!(model.len(), 2);
        assert!(!model.is_empty());
        assert_eq!(model.get("x"), Some("42"));
        assert_eq!(model.get("y"), Some("true"));
        assert_eq!(model.get("z"), None);
    }

    #[test]
    fn default_is_empty() {
        let model = Model::default();
        assert!(model.is_empty());
    }
}
