//! Database of user-defined ghost predicates for bounded unfolding in separation logic.
//!
//! Ghost predicates are registered via `#[ghost_predicate]` and stored here
//! for use by the spec parser during VC generation.
use std::collections::HashMap;

/// A single registered ghost predicate.
#[derive(Debug, Clone)]
pub struct GhostPredicate {
    /// Formal parameter names (e.g., `["p", "n"]`).
    pub param_names: Vec<String>,
    /// Raw body string as serialized by the `ghost_predicate` proc-macro.
    pub body_raw: String,
}

/// Maps predicate name → [`GhostPredicate`] for bounded unfolding.
///
/// Built by `callbacks.rs` during `after_analysis()` from doc attributes,
/// then passed into the spec parser to expand ghost predicate calls.
#[derive(Debug, Clone, Default)]
pub struct GhostPredicateDatabase {
    predicates: HashMap<String, GhostPredicate>,
}

impl GhostPredicateDatabase {
    /// Create an empty database.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a ghost predicate.
    pub fn insert(&mut self, name: String, pred: GhostPredicate) {
        self.predicates.insert(name, pred);
    }

    /// Look up a ghost predicate by name.
    pub fn get(&self, name: &str) -> Option<&GhostPredicate> {
        self.predicates.get(name)
    }

    /// Check if a predicate is registered.
    pub fn contains(&self, name: &str) -> bool {
        self.predicates.contains_key(name)
    }

    /// Number of registered predicates.
    pub fn len(&self) -> usize {
        self.predicates.len()
    }

    /// True if no predicates are registered.
    pub fn is_empty(&self) -> bool {
        self.predicates.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_insert_and_get() {
        let mut db = GhostPredicateDatabase::new();
        db.insert(
            "foo".to_string(),
            GhostPredicate {
                param_names: vec!["p".to_string(), "n".to_string()],
                body_raw: "true".to_string(),
            },
        );
        assert!(db.contains("foo"));
        let pred = db.get("foo").unwrap();
        assert_eq!(pred.param_names, vec!["p", "n"]);
        assert_eq!(pred.body_raw, "true");
    }

    #[test]
    fn test_empty_db() {
        let db = GhostPredicateDatabase::new();
        assert!(db.is_empty());
        assert_eq!(db.len(), 0);
        assert!(db.get("any").is_none());
        assert!(!db.contains("any"));
    }

    #[test]
    fn test_multiple_predicates() {
        let mut db = GhostPredicateDatabase::new();
        db.insert(
            "pred_a".to_string(),
            GhostPredicate {
                param_names: vec!["x".to_string()],
                body_raw: "x > 0".to_string(),
            },
        );
        db.insert(
            "pred_b".to_string(),
            GhostPredicate {
                param_names: vec!["p".to_string(), "q".to_string()],
                body_raw: "true".to_string(),
            },
        );
        assert_eq!(db.len(), 2);
        assert!(db.contains("pred_a"));
        assert!(db.contains("pred_b"));
        assert!(!db.contains("pred_c"));
    }
}
