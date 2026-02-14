//! Standard library contracts for HashMap<K,V>.
//!
//! Mathematical map abstraction: HashMap is modeled as an abstract map function
//! `map_model: K -> Option<V>` where:
//! - Keys map to Some(value) if present, None if absent
//! - SMT encoding uses Array(K_sort, Option_sort(V_sort))
//! - Frame conditions ensure unmodified entries remain unchanged
//! - Length tracking via separate uninterpreted function
//!
//! IMPORTANT: HashMap iteration order is non-deterministic (hash function dependent).
//! We do NOT model iteration order - only the mathematical map abstraction.

use crate::contract_db::FunctionSummary;
use crate::ir::{Contracts, SpecExpr, Ty};
use crate::stdlib_contracts::{ContractSource, StdlibContract, StdlibContractRegistry};

/// Register all HashMap<K,V> contracts into the registry.
///
/// Contracts provided:
/// - `insert(key, value)` - Insert or update a key-value pair
/// - `get(key)` - Look up a value by key (pure)
/// - `remove(key)` - Remove a key-value pair
/// - `contains_key(key)` - Check if key exists (pure)
/// - `len()` - Return number of entries (pure)
/// - `is_empty()` - Check if map is empty (pure)
/// - `clear()` - Remove all entries
pub fn register_hashmap_contracts(registry: &mut StdlibContractRegistry) {
    register_insert(registry);
    register_get(registry);
    register_remove(registry);
    register_contains_key(registry);
    register_len(registry);
    register_is_empty(registry);
    register_clear(registry);
}

/// HashMap::insert(key, value) -> Option<V>
///
/// Mathematical contract:
/// - post: self.get(key) == Some(value)
/// - post: forall k != key: self.get(k) == old(self.get(k))  [frame condition]
/// - post: if old(self.contains_key(key)): self.len() == old(self.len())
/// - post: if !old(self.contains_key(key)): self.len() == old(self.len()) + 1
/// - post: result == old(self.get(key))
fn register_insert(registry: &mut StdlibContractRegistry) {
    let contract = StdlibContract {
        type_path: "std::collections::HashMap".to_string(),
        method_name: "insert".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![
                    // Postcondition 1: The inserted key maps to the new value
                    SpecExpr {
                        raw: "self.get(key) == Some(value)".to_string(),
                    },
                    // Postcondition 2: Frame condition - other keys unchanged
                    SpecExpr {
                        raw: "forall |k| k != key ==> self.get(k) == old(self.get(k))".to_string(),
                    },
                    // Postcondition 3: Length tracking (conditional on whether key was new)
                    SpecExpr {
                        raw: "old(self.contains_key(key)) ==> self.len() == old(self.len())"
                            .to_string(),
                    },
                    SpecExpr {
                        raw: "!old(self.contains_key(key)) ==> self.len() == old(self.len()) + 1"
                            .to_string(),
                    },
                    // Postcondition 4: Return value is old mapping (None if new key)
                    SpecExpr {
                        raw: "result == old(self.get(key))".to_string(),
                    },
                ],
                invariants: vec![],
                is_pure: false,
                decreases: None,
            },
            param_names: vec!["self".to_string(), "key".to_string(), "value".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit, Ty::Unit], // Polymorphic - actual types from context
            return_ty: Ty::Unit,                             // Option<V>
        },
        source: ContractSource::Builtin,
    };

    registry.register(contract);
}

/// HashMap::get(key) -> Option<&V>
///
/// Mathematical contract:
/// - pure: true (no side effects)
/// - post: result == self.map_model.lookup(key)
fn register_get(registry: &mut StdlibContractRegistry) {
    let contract = StdlibContract {
        type_path: "std::collections::HashMap".to_string(),
        method_name: "get".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![
                    // Pure lookup - result is the map's value for this key
                    SpecExpr {
                        raw: "result == self.map_model.lookup(key)".to_string(),
                    },
                ],
                invariants: vec![],
                is_pure: true,
                decreases: None,
            },
            param_names: vec!["self".to_string(), "key".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit],
            return_ty: Ty::Unit, // Option<&V>
        },
        source: ContractSource::Builtin,
    };

    registry.register(contract);
}

/// HashMap::remove(key) -> Option<V>
///
/// Mathematical contract:
/// - post: self.get(key) == None
/// - post: forall k != key: self.get(k) == old(self.get(k))  [frame condition]
/// - post: old(self.contains_key(key)) ==> self.len() == old(self.len()) - 1
/// - post: !old(self.contains_key(key)) ==> self.len() == old(self.len())
/// - post: result == old(self.get(key))
fn register_remove(registry: &mut StdlibContractRegistry) {
    let contract = StdlibContract {
        type_path: "std::collections::HashMap".to_string(),
        method_name: "remove".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![
                    // Postcondition 1: Key no longer present
                    SpecExpr {
                        raw: "self.get(key) == None".to_string(),
                    },
                    // Postcondition 2: Frame condition - other keys unchanged
                    SpecExpr {
                        raw: "forall |k| k != key ==> self.get(k) == old(self.get(k))".to_string(),
                    },
                    // Postcondition 3: Length tracking
                    SpecExpr {
                        raw: "old(self.contains_key(key)) ==> self.len() == old(self.len()) - 1"
                            .to_string(),
                    },
                    SpecExpr {
                        raw: "!old(self.contains_key(key)) ==> self.len() == old(self.len())"
                            .to_string(),
                    },
                    // Postcondition 4: Return value is old mapping
                    SpecExpr {
                        raw: "result == old(self.get(key))".to_string(),
                    },
                ],
                invariants: vec![],
                is_pure: false,
                decreases: None,
            },
            param_names: vec!["self".to_string(), "key".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit],
            return_ty: Ty::Unit, // Option<V>
        },
        source: ContractSource::Builtin,
    };

    registry.register(contract);
}

/// HashMap::contains_key(key) -> bool
///
/// Mathematical contract:
/// - pure: true
/// - post: result == self.get(key).is_some()
fn register_contains_key(registry: &mut StdlibContractRegistry) {
    let contract = StdlibContract {
        type_path: "std::collections::HashMap".to_string(),
        method_name: "contains_key".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "result == self.get(key).is_some()".to_string(),
                }],
                invariants: vec![],
                is_pure: true,
                decreases: None,
            },
            param_names: vec!["self".to_string(), "key".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit],
            return_ty: Ty::Bool,
        },
        source: ContractSource::Builtin,
    };

    registry.register(contract);
}

/// HashMap::len() -> usize
///
/// Mathematical contract:
/// - pure: true
/// - post: result >= 0
fn register_len(registry: &mut StdlibContractRegistry) {
    let contract = StdlibContract {
        type_path: "std::collections::HashMap".to_string(),
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
            },
            param_names: vec!["self".to_string()],
            param_types: vec![Ty::Unit],
            return_ty: Ty::Unit, // usize
        },
        source: ContractSource::Builtin,
    };

    registry.register(contract);
}

/// HashMap::is_empty() -> bool
///
/// Mathematical contract:
/// - pure: true
/// - post: result == (self.len() == 0)
fn register_is_empty(registry: &mut StdlibContractRegistry) {
    let contract = StdlibContract {
        type_path: "std::collections::HashMap".to_string(),
        method_name: "is_empty".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "result == (self.len() == 0)".to_string(),
                }],
                invariants: vec![],
                is_pure: true,
                decreases: None,
            },
            param_names: vec!["self".to_string()],
            param_types: vec![Ty::Unit],
            return_ty: Ty::Bool,
        },
        source: ContractSource::Builtin,
    };

    registry.register(contract);
}

/// HashMap::clear()
///
/// Mathematical contract:
/// - post: self.len() == 0
/// - post: forall k: self.get(k) == None
fn register_clear(registry: &mut StdlibContractRegistry) {
    let contract = StdlibContract {
        type_path: "std::collections::HashMap".to_string(),
        method_name: "clear".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![
                    // Postcondition 1: Map is empty
                    SpecExpr {
                        raw: "self.len() == 0".to_string(),
                    },
                    // Postcondition 2: All keys map to None
                    SpecExpr {
                        raw: "forall |k| self.get(k) == None".to_string(),
                    },
                ],
                invariants: vec![],
                is_pure: false,
                decreases: None,
            },
            param_names: vec!["self".to_string()],
            param_types: vec![Ty::Unit],
            return_ty: Ty::Unit,
        },
        source: ContractSource::Builtin,
    };

    registry.register(contract);
}
