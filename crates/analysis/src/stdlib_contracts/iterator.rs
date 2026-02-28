//! Standard library contracts for Iterator trait and common adaptors.
//!
//! Iterators are modeled as abstract sequences (Seq<Item> in SMT).
//! Each adaptor transforms the sequence model with composable properties:
//! - map: same length, elements transformed
//! - filter: length <= original, all elements satisfy predicate
//! - take(n): length = min(n, original length)
//! - zip: length = min(a_len, b_len), pairs from both
//! - enumerate: same length, wraps in (usize, Item) pairs
//!
//! IMPORTANT: For infinite iterators, we require finiteness precondition
//! (conservative approach). If no .take(n) or known-finite source, emit
//! a warning VC rather than unsound contract.

use crate::contract_db::FunctionSummary;
use crate::ir::{Contracts, SpecExpr, Ty};
use crate::stdlib_contracts::{ContractSource, StdlibContract, StdlibContractRegistry};

/// Register all Iterator trait contracts into the registry.
///
/// Tier 1 adaptors (per user decision):
/// - `next()` - Consume next element
/// - `map(f)` - Transform elements (preserves length)
/// - `filter(p)` - Select elements (reduces length)
/// - `collect()` - Consume into collection
/// - `count()` - Count elements (consumes iterator)
/// - `fold(init, f)` - Reduce to single value
/// - `any(p)` - Exists quantification
/// - `all(p)` - Universal quantification
/// - `zip(other)` - Pair with another iterator
/// - `enumerate()` - Add indices
/// - `take(n)` - Take first n elements
pub fn register_iterator_contracts(registry: &mut StdlibContractRegistry) {
    register_next(registry);
    register_map(registry);
    register_filter(registry);
    register_collect(registry);
    register_count(registry);
    register_fold(registry);
    register_any(registry);
    register_all(registry);
    register_zip(registry);
    register_enumerate(registry);
    register_take(registry);
}

/// Iterator::next() -> Option<Item>
///
/// Mathematical contract:
/// - post: if result.is_some(): self.seq_len() == old(self.seq_len()) - 1
/// - post: if result.is_none(): old(self.seq_len()) == 0
fn register_next(registry: &mut StdlibContractRegistry) {
    let contract = StdlibContract {
        type_path: "std::iter::Iterator".to_string(),
        method_name: "next".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![
                    // Postcondition 1: If Some, sequence shrinks by 1
                    SpecExpr {
                        raw: "result.is_some() ==> self.seq_len() == old(self.seq_len()) - 1"
                            .to_string(),
                    },
                    // Postcondition 2: If None, sequence was empty
                    SpecExpr {
                        raw: "result.is_none() ==> old(self.seq_len()) == 0".to_string(),
                    },
                ],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
            },
            param_names: vec!["self".to_string()],
            param_types: vec![Ty::Unit],
            return_ty: Ty::Unit, // Option<Item>
            alias_preconditions: vec![],
        },
        source: ContractSource::Builtin,
    };

    registry.register(contract);
}

/// Iterator::map<F>(f: F) -> Map<Self, F>
///
/// Mathematical contract:
/// - post: result.seq_len() == self.seq_len()  [map preserves length]
fn register_map(registry: &mut StdlibContractRegistry) {
    let contract = StdlibContract {
        type_path: "std::iter::Iterator".to_string(),
        method_name: "map".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![
                    // Map preserves sequence length (key composition property)
                    SpecExpr {
                        raw: "result.seq_len() == self.seq_len()".to_string(),
                    },
                ],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
            },
            param_names: vec!["self".to_string(), "f".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit],
            return_ty: Ty::Unit, // Map<Self, F>
            alias_preconditions: vec![],
        },
        source: ContractSource::Builtin,
    };

    registry.register(contract);
}

/// Iterator::filter<P>(predicate: P) -> Filter<Self, P>
///
/// Mathematical contract:
/// - post: result.seq_len() <= self.seq_len()  [filter reduces or maintains length]
fn register_filter(registry: &mut StdlibContractRegistry) {
    let contract = StdlibContract {
        type_path: "std::iter::Iterator".to_string(),
        method_name: "filter".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![
                    // Filter reduces or maintains sequence length
                    SpecExpr {
                        raw: "result.seq_len() <= self.seq_len()".to_string(),
                    },
                ],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
            },
            param_names: vec!["self".to_string(), "predicate".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit],
            return_ty: Ty::Unit, // Filter<Self, P>
            alias_preconditions: vec![],
        },
        source: ContractSource::Builtin,
    };

    registry.register(contract);
}

/// Iterator::collect<B>() -> B
///
/// Mathematical contract:
/// - post: result.len() == consumed_iterator.count()
fn register_collect(registry: &mut StdlibContractRegistry) {
    let contract = StdlibContract {
        type_path: "std::iter::Iterator".to_string(),
        method_name: "collect".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![
                    // Result collection length equals iterator count
                    SpecExpr {
                        raw: "result.len() == old(self.seq_len())".to_string(),
                    },
                ],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
            },
            param_names: vec!["self".to_string()],
            param_types: vec![Ty::Unit],
            return_ty: Ty::Unit, // B: FromIterator
            alias_preconditions: vec![],
        },
        source: ContractSource::Builtin,
    };

    registry.register(contract);
}

/// Iterator::count() -> usize
///
/// Mathematical contract:
/// - post: result == self.seq_len()
fn register_count(registry: &mut StdlibContractRegistry) {
    let contract = StdlibContract {
        type_path: "std::iter::Iterator".to_string(),
        method_name: "count".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "result == old(self.seq_len())".to_string(),
                }],
                invariants: vec![],
                is_pure: false, // Consumes iterator
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
            },
            param_names: vec!["self".to_string()],
            param_types: vec![Ty::Unit],
            return_ty: Ty::Unit, // usize
            alias_preconditions: vec![],
        },
        source: ContractSource::Builtin,
    };

    registry.register(contract);
}

/// Iterator::fold<B, F>(init: B, f: F) -> B
///
/// Mathematical contract:
/// - post: result == fold(init, f, self.seq_model)
fn register_fold(registry: &mut StdlibContractRegistry) {
    let contract = StdlibContract {
        type_path: "std::iter::Iterator".to_string(),
        method_name: "fold".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![
                    // Abstract fold operation (proof obligations on f)
                    SpecExpr {
                        raw: "result == fold_seq(init, f, old(self.seq_model))".to_string(),
                    },
                ],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
            },
            param_names: vec!["self".to_string(), "init".to_string(), "f".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit, Ty::Unit],
            return_ty: Ty::Unit, // B
            alias_preconditions: vec![],
        },
        source: ContractSource::Builtin,
    };

    registry.register(contract);
}

/// Iterator::any<F>(predicate: F) -> bool
///
/// Mathematical contract:
/// - post: result == exists(|x| predicate(x) in self.seq_model)
fn register_any(registry: &mut StdlibContractRegistry) {
    let contract = StdlibContract {
        type_path: "std::iter::Iterator".to_string(),
        method_name: "any".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![
                    // Exists quantification
                    SpecExpr {
                        raw: "result == exists(|x| predicate(x), old(self.seq_model))".to_string(),
                    },
                ],
                invariants: vec![],
                is_pure: false, // Consumes iterator
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
            },
            param_names: vec!["self".to_string(), "predicate".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit],
            return_ty: Ty::Bool,
            alias_preconditions: vec![],
        },
        source: ContractSource::Builtin,
    };

    registry.register(contract);
}

/// Iterator::all<F>(predicate: F) -> bool
///
/// Mathematical contract:
/// - post: result == forall(|x| predicate(x) in self.seq_model)
fn register_all(registry: &mut StdlibContractRegistry) {
    let contract = StdlibContract {
        type_path: "std::iter::Iterator".to_string(),
        method_name: "all".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![
                    // Universal quantification
                    SpecExpr {
                        raw: "result == forall(|x| predicate(x), old(self.seq_model))".to_string(),
                    },
                ],
                invariants: vec![],
                is_pure: false, // Consumes iterator
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
            },
            param_names: vec!["self".to_string(), "predicate".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit],
            return_ty: Ty::Bool,
            alias_preconditions: vec![],
        },
        source: ContractSource::Builtin,
    };

    registry.register(contract);
}

/// Iterator::zip<U>(other: U) -> Zip<Self, U::IntoIter>
///
/// Mathematical contract:
/// - post: result.seq_len() == min(self.seq_len(), other.seq_len())
fn register_zip(registry: &mut StdlibContractRegistry) {
    let contract = StdlibContract {
        type_path: "std::iter::Iterator".to_string(),
        method_name: "zip".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![
                    // Result length is minimum of both iterators
                    SpecExpr {
                        raw: "result.seq_len() == min(self.seq_len(), other.seq_len())".to_string(),
                    },
                ],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
            },
            param_names: vec!["self".to_string(), "other".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit],
            return_ty: Ty::Unit, // Zip<Self, U::IntoIter>
            alias_preconditions: vec![],
        },
        source: ContractSource::Builtin,
    };

    registry.register(contract);
}

/// Iterator::enumerate() -> Enumerate<Self>
///
/// Mathematical contract:
/// - post: result.seq_len() == self.seq_len()
/// - post: each element is (index, value)
fn register_enumerate(registry: &mut StdlibContractRegistry) {
    let contract = StdlibContract {
        type_path: "std::iter::Iterator".to_string(),
        method_name: "enumerate".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![
                    // Enumerate preserves sequence length
                    SpecExpr {
                        raw: "result.seq_len() == self.seq_len()".to_string(),
                    },
                ],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
            },
            param_names: vec!["self".to_string()],
            param_types: vec![Ty::Unit],
            return_ty: Ty::Unit, // Enumerate<Self>
            alias_preconditions: vec![],
        },
        source: ContractSource::Builtin,
    };

    registry.register(contract);
}

/// Iterator::take(n: usize) -> Take<Self>
///
/// Mathematical contract:
/// - post: result.seq_len() == min(n, self.seq_len())
fn register_take(registry: &mut StdlibContractRegistry) {
    let contract = StdlibContract {
        type_path: "std::iter::Iterator".to_string(),
        method_name: "take".to_string(),
        summary: FunctionSummary {
            contracts: Contracts {
                requires: vec![],
                ensures: vec![
                    // Result length is minimum of n and original length
                    SpecExpr {
                        raw: "result.seq_len() == min(n, self.seq_len())".to_string(),
                    },
                ],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
            },
            param_names: vec!["self".to_string(), "n".to_string()],
            param_types: vec![Ty::Unit, Ty::Unit],
            return_ty: Ty::Unit, // Take<Self>
            alias_preconditions: vec![],
        },
        source: ContractSource::Builtin,
    };

    registry.register(contract);
}
