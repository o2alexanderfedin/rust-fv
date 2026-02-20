/// Database of function contracts for inter-procedural verification.
///
/// When verifying a function `foo` that calls `bar`, the VCGen looks up
/// `bar`'s contracts here and encodes:
///   1. Assert bar's preconditions (substituting actual arguments for formals)
///   2. Havoc the return value (declare unconstrained)
///   3. Assume bar's postconditions (with `result` bound to the destination)
///
/// This enables modular verification: each function is checked independently
/// using callee contracts as summaries, avoiding exponential blowup from
/// inlining callee bodies.
use std::collections::HashMap;

use crate::ir::{Contracts, Ty};

/// A function summary: contracts plus parameter metadata for argument substitution.
#[derive(Debug, Clone)]
pub struct FunctionSummary {
    /// The function's contracts (preconditions, postconditions, etc.)
    pub contracts: Contracts,
    /// Parameter names for argument substitution (e.g., ["_1", "_2"])
    pub param_names: Vec<String>,
    /// Parameter types for correct SMT encoding
    pub param_types: Vec<Ty>,
    /// Return type
    pub return_ty: Ty,
}

/// Maps function names to their contracts for inter-procedural verification.
///
/// The contract database is populated by the driver from HIR-extracted contracts,
/// then passed into the VCGen so that call sites can be encoded modularly.
#[derive(Debug, Clone, Default)]
pub struct ContractDatabase {
    contracts: HashMap<String, FunctionSummary>,
}

impl ContractDatabase {
    /// Create an empty contract database.
    pub fn new() -> Self {
        Self {
            contracts: HashMap::new(),
        }
    }

    /// Register a function's contracts in the database.
    pub fn insert(&mut self, name: String, summary: FunctionSummary) {
        self.contracts.insert(name, summary);
    }

    /// Look up a callee's contracts by function name.
    pub fn get(&self, name: &str) -> Option<&FunctionSummary> {
        self.contracts.get(name)
    }

    /// Check if a function has contracts in the database.
    pub fn contains(&self, name: &str) -> bool {
        self.contracts.contains_key(name)
    }

    /// Return the number of entries in the database.
    pub fn len(&self) -> usize {
        self.contracts.len()
    }

    /// Check if the database is empty.
    pub fn is_empty(&self) -> bool {
        self.contracts.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Contracts, IntTy, SpecExpr};

    #[test]
    fn empty_database() {
        let db = ContractDatabase::new();
        assert!(db.is_empty());
        assert_eq!(db.len(), 0);
        assert!(!db.contains("foo"));
        assert!(db.get("foo").is_none());
    }

    #[test]
    fn insert_and_get() {
        let mut db = ContractDatabase::new();
        db.insert(
            "add".to_string(),
            FunctionSummary {
                contracts: Contracts {
                    requires: vec![SpecExpr {
                        raw: "_1 > 0".to_string(),
                    }],
                    ensures: vec![SpecExpr {
                        raw: "result == _1 + _2".to_string(),
                    }],
                    invariants: vec![],
                    is_pure: true,
                    decreases: None,
                    fn_specs: vec![],
                },
                param_names: vec!["_1".to_string(), "_2".to_string()],
                param_types: vec![Ty::Int(IntTy::I32), Ty::Int(IntTy::I32)],
                return_ty: Ty::Int(IntTy::I32),
            },
        );

        assert!(!db.is_empty());
        assert_eq!(db.len(), 1);
        assert!(db.contains("add"));
        assert!(!db.contains("sub"));

        let summary = db.get("add").unwrap();
        assert_eq!(summary.contracts.requires.len(), 1);
        assert_eq!(summary.contracts.ensures.len(), 1);
        assert_eq!(summary.param_names.len(), 2);
    }

    #[test]
    fn multiple_entries() {
        let mut db = ContractDatabase::new();
        db.insert(
            "foo".to_string(),
            FunctionSummary {
                contracts: Contracts::default(),
                param_names: vec![],
                param_types: vec![],
                return_ty: Ty::Unit,
            },
        );
        db.insert(
            "bar".to_string(),
            FunctionSummary {
                contracts: Contracts::default(),
                param_names: vec!["_1".to_string()],
                param_types: vec![Ty::Int(IntTy::I32)],
                return_ty: Ty::Int(IntTy::I32),
            },
        );

        assert_eq!(db.len(), 2);
        assert!(db.contains("foo"));
        assert!(db.contains("bar"));
    }

    #[test]
    fn default_is_empty() {
        let db = ContractDatabase::default();
        assert!(db.is_empty());
    }
}
