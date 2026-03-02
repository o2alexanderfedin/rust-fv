//! Core data structures for standard library contract registry.

use std::collections::HashMap;

use crate::contract_db::FunctionSummary;
use crate::ir::SpecExpr;

/// Source of a standard library contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ContractSource {
    /// Built-in contract provided by the verification tool
    Builtin,
    /// User override of a built-in contract
    UserOverride,
    /// User extension (contract for stdlib item that doesn't have a builtin)
    UserExtension,
}

/// A formal specification for a standard library method.
#[derive(Debug, Clone)]
pub struct StdlibContract {
    /// Fully-qualified type path (e.g., "std::vec::Vec", "std::option::Option")
    pub type_path: String,
    /// Method name (e.g., "push", "pop", "len")
    pub method_name: String,
    /// The function summary (contracts + param metadata)
    pub summary: FunctionSummary,
    /// Where this contract came from
    pub source: ContractSource,
}

/// Registry of standard library contracts.
///
/// Provides:
/// - Built-in contracts for common stdlib types (Vec, Option, Result, etc.)
/// - User override mechanism for custom refinements
/// - User extension mechanism for additional stdlib items
/// - Query interface for contract lookup during verification
#[derive(Debug, Clone)]
pub struct StdlibContractRegistry {
    /// Contracts indexed by fully-qualified method name (e.g., "Vec::push")
    contracts: HashMap<String, StdlibContract>,
    /// Whether stdlib contracts are enabled (disable with --no-stdlib-contracts)
    enabled: bool,
}

impl StdlibContractRegistry {
    /// Create a new registry with stdlib contracts enabled.
    pub fn new() -> Self {
        Self {
            contracts: HashMap::new(),
            enabled: true,
        }
    }

    /// Create a new registry with stdlib contracts disabled.
    ///
    /// Used for `--no-stdlib-contracts` flag or when user wants full manual control.
    pub fn new_disabled() -> Self {
        Self {
            contracts: HashMap::new(),
            enabled: false,
        }
    }

    /// Register a stdlib contract.
    ///
    /// The contract is indexed by a key derived from the type path and method name.
    /// For example: "Vec::push", "Option::unwrap", "HashMap::insert".
    pub fn register(&mut self, contract: StdlibContract) {
        let key = self.make_key(&contract.type_path, &contract.method_name);
        self.contracts.insert(key, contract);
    }

    /// Look up a stdlib contract by method key.
    ///
    /// Returns `None` if:
    /// - Stdlib contracts are disabled
    /// - No contract is registered for this method
    pub fn get(&self, method_key: &str) -> Option<&StdlibContract> {
        if !self.enabled {
            return None;
        }
        self.contracts.get(method_key)
    }

    /// Override an existing contract with a user-provided one.
    ///
    /// This allows users to provide more precise contracts than the builtin ones
    /// for their specific use case.
    pub fn override_contract(&mut self, key: &str, contract: StdlibContract) {
        if self.enabled {
            self.contracts.insert(key.to_string(), contract);
        }
    }

    /// Extend a contract with additional preconditions and postconditions.
    ///
    /// This is additive: the extra conditions are AND-ed with the existing ones.
    pub fn extend_contract(
        &mut self,
        key: &str,
        extra_requires: Vec<SpecExpr>,
        extra_ensures: Vec<SpecExpr>,
    ) {
        if !self.enabled {
            return;
        }

        if let Some(contract) = self.contracts.get_mut(key) {
            contract.summary.contracts.requires.extend(extra_requires);
            contract.summary.contracts.ensures.extend(extra_ensures);
        }
    }

    /// Merge all stdlib contracts into a contract database.
    ///
    /// This is called during verification setup to make stdlib contracts
    /// available to the inter-procedural verification engine.
    pub fn merge_into(&self, db: &mut crate::contract_db::ContractDatabase) {
        if !self.enabled {
            return;
        }

        for (key, contract) in &self.contracts {
            db.insert(key.clone(), contract.summary.clone());
        }
    }

    /// Check if stdlib contracts are enabled.
    pub fn is_enabled(&self) -> bool {
        self.enabled
    }

    /// Return the number of registered contracts.
    pub fn len(&self) -> usize {
        self.contracts.len()
    }

    /// Check if the registry is empty.
    pub fn is_empty(&self) -> bool {
        self.contracts.is_empty()
    }

    /// Create a key for method lookup.
    ///
    /// Format: "{simplified_type}::{method}" where simplified_type is the
    /// last component of the type path (e.g., "Vec" from "std::vec::Vec").
    fn make_key(&self, type_path: &str, method_name: &str) -> String {
        let simplified = type_path.split("::").last().unwrap_or(type_path);
        format!("{}::{}", simplified, method_name)
    }
}

impl Default for StdlibContractRegistry {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Contracts, IntTy, Ty};

    #[test]
    fn test_new_creates_enabled_empty_registry() {
        let registry = StdlibContractRegistry::new();
        assert!(registry.is_enabled());
        assert_eq!(registry.len(), 0);
        assert!(registry.is_empty());
    }

    #[test]
    fn test_new_disabled_creates_disabled_registry() {
        let registry = StdlibContractRegistry::new_disabled();
        assert!(!registry.is_enabled());
        assert_eq!(registry.len(), 0);
    }

    #[test]
    fn test_register_and_get() {
        let mut registry = StdlibContractRegistry::new();

        let contract = StdlibContract {
            type_path: "std::vec::Vec".to_string(),
            method_name: "push".to_string(),
            summary: FunctionSummary {
                contracts: Contracts::default(),
                param_names: vec!["self".to_string(), "value".to_string()],
                param_types: vec![Ty::Unit, Ty::Int(IntTy::I32)],
                return_ty: Ty::Unit,
                alias_preconditions: vec![],
                is_inferred: false,
            },
            source: ContractSource::Builtin,
        };

        registry.register(contract.clone());
        assert_eq!(registry.len(), 1);

        let retrieved = registry.get("Vec::push");
        assert!(retrieved.is_some());
        assert_eq!(retrieved.unwrap().method_name, "push");
    }

    #[test]
    fn test_get_disabled_returns_none() {
        let mut registry = StdlibContractRegistry::new_disabled();

        let contract = StdlibContract {
            type_path: "std::option::Option".to_string(),
            method_name: "unwrap".to_string(),
            summary: FunctionSummary {
                contracts: Contracts::default(),
                param_names: vec!["self".to_string()],
                param_types: vec![Ty::Unit],
                return_ty: Ty::Int(IntTy::I32),
                alias_preconditions: vec![],
                is_inferred: false,
            },
            source: ContractSource::Builtin,
        };

        registry.register(contract);
        assert!(registry.get("Option::unwrap").is_none());
    }

    #[test]
    fn test_override_contract() {
        let mut registry = StdlibContractRegistry::new();

        let original = StdlibContract {
            type_path: "std::vec::Vec".to_string(),
            method_name: "len".to_string(),
            summary: FunctionSummary {
                contracts: Contracts {
                    requires: vec![],
                    ensures: vec![SpecExpr {
                        raw: "result >= 0".to_string(),
                    }],
                    invariants: vec![],
                    is_pure: true,
                    decreases: None,
                    fn_specs: vec![],
                    state_invariant: None,
                    is_inferred: false,
                },
                param_names: vec!["self".to_string()],
                param_types: vec![Ty::Unit],
                return_ty: Ty::Int(IntTy::I32),
                alias_preconditions: vec![],
                is_inferred: false,
            },
            source: ContractSource::Builtin,
        };

        registry.register(original);

        let override_contract = StdlibContract {
            type_path: "std::vec::Vec".to_string(),
            method_name: "len".to_string(),
            summary: FunctionSummary {
                contracts: Contracts {
                    requires: vec![],
                    ensures: vec![SpecExpr {
                        raw: "result <= capacity".to_string(),
                    }],
                    invariants: vec![],
                    is_pure: true,
                    decreases: None,
                    fn_specs: vec![],
                    state_invariant: None,
                    is_inferred: false,
                },
                param_names: vec!["self".to_string()],
                param_types: vec![Ty::Unit],
                return_ty: Ty::Int(IntTy::I32),
                alias_preconditions: vec![],
                is_inferred: false,
            },
            source: ContractSource::UserOverride,
        };

        registry.override_contract("Vec::len", override_contract);

        let retrieved = registry.get("Vec::len").unwrap();
        assert_eq!(retrieved.source, ContractSource::UserOverride);
        assert_eq!(retrieved.summary.contracts.ensures.len(), 1);
        assert_eq!(
            retrieved.summary.contracts.ensures[0].raw,
            "result <= capacity"
        );
    }

    #[test]
    fn test_extend_contract() {
        let mut registry = StdlibContractRegistry::new();

        let contract = StdlibContract {
            type_path: "std::vec::Vec".to_string(),
            method_name: "push".to_string(),
            summary: FunctionSummary {
                contracts: Contracts {
                    requires: vec![SpecExpr {
                        raw: "len < capacity".to_string(),
                    }],
                    ensures: vec![],
                    invariants: vec![],
                    is_pure: false,
                    decreases: None,
                    fn_specs: vec![],
                    state_invariant: None,
                    is_inferred: false,
                },
                param_names: vec!["self".to_string(), "value".to_string()],
                param_types: vec![Ty::Unit, Ty::Int(IntTy::I32)],
                return_ty: Ty::Unit,
                alias_preconditions: vec![],
                is_inferred: false,
            },
            source: ContractSource::Builtin,
        };

        registry.register(contract);

        registry.extend_contract(
            "Vec::push",
            vec![SpecExpr {
                raw: "self.valid()".to_string(),
            }],
            vec![SpecExpr {
                raw: "self.len() == old(self.len()) + 1".to_string(),
            }],
        );

        let retrieved = registry.get("Vec::push").unwrap();
        assert_eq!(retrieved.summary.contracts.requires.len(), 2);
        assert_eq!(retrieved.summary.contracts.ensures.len(), 1);
    }

    #[test]
    fn test_merge_into_contract_database() {
        let mut registry = StdlibContractRegistry::new();

        let contract = StdlibContract {
            type_path: "std::vec::Vec".to_string(),
            method_name: "push".to_string(),
            summary: FunctionSummary {
                contracts: Contracts::default(),
                param_names: vec!["self".to_string(), "value".to_string()],
                param_types: vec![Ty::Unit, Ty::Int(IntTy::I32)],
                return_ty: Ty::Unit,
                alias_preconditions: vec![],
                is_inferred: false,
            },
            source: ContractSource::Builtin,
        };

        registry.register(contract);

        let mut db = crate::contract_db::ContractDatabase::new();
        registry.merge_into(&mut db);

        assert!(db.contains("Vec::push"));
    }

    #[test]
    fn test_disabled_registry_blocks_merge() {
        let registry = StdlibContractRegistry::new_disabled();
        let mut db = crate::contract_db::ContractDatabase::new();

        registry.merge_into(&mut db);
        assert!(db.is_empty());
    }
}
