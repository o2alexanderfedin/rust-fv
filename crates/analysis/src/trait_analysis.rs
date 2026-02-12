/// Trait analysis infrastructure for verification.
///
/// Provides trait database, sealed trait detection, and impl collection
/// functionality to support trait object and behavioral subtyping verification.
use std::collections::HashMap;

use crate::ir::{TraitDef, TraitImpl, TraitMethod};

/// Database of traits and their implementations for verification.
pub struct TraitDatabase {
    /// Map from trait name to trait definition
    traits: HashMap<String, TraitDef>,
    /// Map from trait name to list of implementations
    impls: HashMap<String, Vec<TraitImpl>>,
}

impl TraitDatabase {
    /// Create a new empty trait database.
    pub fn new() -> Self {
        Self {
            traits: HashMap::new(),
            impls: HashMap::new(),
        }
    }

    /// Register a trait definition in the database.
    pub fn register_trait(&mut self, def: TraitDef) {
        self.traits.insert(def.name.clone(), def);
    }

    /// Register a trait implementation in the database.
    pub fn register_impl(&mut self, impl_info: TraitImpl) {
        self.impls
            .entry(impl_info.trait_name.clone())
            .or_default()
            .push(impl_info);
    }

    /// Get a trait definition by name.
    pub fn get_trait(&self, name: &str) -> Option<&TraitDef> {
        self.traits.get(name)
    }

    /// Get all implementations of a trait by trait name.
    pub fn get_impls(&self, trait_name: &str) -> &[TraitImpl] {
        self.impls
            .get(trait_name)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    /// Check if a trait is sealed.
    pub fn is_sealed(&self, trait_name: &str) -> bool {
        self.traits
            .get(trait_name)
            .map(|def| def.is_sealed)
            .unwrap_or(false)
    }

    /// Get an iterator over all trait names in the database.
    pub fn trait_names(&self) -> impl Iterator<Item = &str> {
        self.traits.keys().map(|s| s.as_str())
    }
}

impl Default for TraitDatabase {
    fn default() -> Self {
        Self::new()
    }
}

/// Detect if a trait is sealed based on visibility and super-trait patterns.
///
/// A trait is considered sealed if:
/// - Visibility is `pub(crate)`, `pub(super)`, or private (empty string)
/// - Any super-trait name contains "Sealed" or starts with "private::"
pub fn detect_sealed_trait(visibility: &str, super_traits: &[String]) -> bool {
    // Check visibility-based sealing
    if visibility == "pub(crate)" || visibility == "pub(super)" || visibility.is_empty() {
        return true;
    }

    // Check super-trait sealed pattern
    super_traits
        .iter()
        .any(|t| t.contains("Sealed") || t.starts_with("private::"))
}

/// Collect all methods from a trait that have at least one contract specification.
///
/// Returns references to methods that have requires or ensures clauses.
pub fn collect_trait_methods(trait_def: &TraitDef) -> Vec<&TraitMethod> {
    trait_def
        .methods
        .iter()
        .filter(|m| !m.requires.is_empty() || !m.ensures.is_empty())
        .collect()
}

/// Find trait methods that are missing from an implementation.
///
/// Returns the names of trait methods not found in impl_info.method_names.
pub fn find_missing_impl_methods(trait_def: &TraitDef, impl_info: &TraitImpl) -> Vec<String> {
    trait_def
        .methods
        .iter()
        .filter(|m| !impl_info.method_names.contains(&m.name))
        .map(|m| m.name.clone())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{IntTy, SpecExpr, TraitMethod, Ty};

    // ====== TraitDatabase tests ======

    #[test]
    fn test_trait_database_new_empty() {
        let db = TraitDatabase::new();
        assert!(db.trait_names().collect::<Vec<_>>().is_empty());
    }

    #[test]
    fn test_trait_database_register_and_get() {
        let mut db = TraitDatabase::new();
        let trait_def = TraitDef {
            name: "Stack".to_string(),
            methods: vec![],
            is_sealed: false,
            super_traits: vec![],
        };
        db.register_trait(trait_def.clone());
        let retrieved = db.get_trait("Stack");
        assert!(retrieved.is_some());
        assert_eq!(retrieved.unwrap().name, "Stack");
    }

    #[test]
    fn test_trait_database_register_impl() {
        let mut db = TraitDatabase::new();
        let impl_info = TraitImpl {
            trait_name: "Stack".to_string(),
            impl_type: "VecStack".to_string(),
            method_names: vec!["push".to_string()],
        };
        db.register_impl(impl_info);
        let impls = db.get_impls("Stack");
        assert_eq!(impls.len(), 1);
        assert_eq!(impls[0].impl_type, "VecStack");
    }

    #[test]
    fn test_trait_database_get_impls_empty() {
        let db = TraitDatabase::new();
        let impls = db.get_impls("NonExistent");
        assert!(impls.is_empty());
    }

    #[test]
    fn test_trait_database_is_sealed() {
        let mut db = TraitDatabase::new();
        let sealed_trait = TraitDef {
            name: "Internal".to_string(),
            methods: vec![],
            is_sealed: true,
            super_traits: vec![],
        };
        db.register_trait(sealed_trait);
        assert!(db.is_sealed("Internal"));
    }

    #[test]
    fn test_trait_database_is_sealed_false() {
        let mut db = TraitDatabase::new();
        let public_trait = TraitDef {
            name: "Public".to_string(),
            methods: vec![],
            is_sealed: false,
            super_traits: vec![],
        };
        db.register_trait(public_trait);
        assert!(!db.is_sealed("Public"));
    }

    #[test]
    fn test_trait_database_trait_names() {
        let mut db = TraitDatabase::new();
        db.register_trait(TraitDef {
            name: "TraitA".to_string(),
            methods: vec![],
            is_sealed: false,
            super_traits: vec![],
        });
        db.register_trait(TraitDef {
            name: "TraitB".to_string(),
            methods: vec![],
            is_sealed: false,
            super_traits: vec![],
        });
        let names: Vec<&str> = db.trait_names().collect();
        assert_eq!(names.len(), 2);
        assert!(names.contains(&"TraitA"));
        assert!(names.contains(&"TraitB"));
    }

    #[test]
    fn test_trait_database_multiple_impls() {
        let mut db = TraitDatabase::new();
        db.register_impl(TraitImpl {
            trait_name: "Stack".to_string(),
            impl_type: "VecStack".to_string(),
            method_names: vec!["push".to_string()],
        });
        db.register_impl(TraitImpl {
            trait_name: "Stack".to_string(),
            impl_type: "ArrayStack".to_string(),
            method_names: vec!["push".to_string(), "pop".to_string()],
        });
        let impls = db.get_impls("Stack");
        assert_eq!(impls.len(), 2);
        assert!(impls.iter().any(|i| i.impl_type == "VecStack"));
        assert!(impls.iter().any(|i| i.impl_type == "ArrayStack"));
    }

    // ====== detect_sealed_trait tests ======

    #[test]
    fn test_detect_sealed_pub_crate() {
        assert!(detect_sealed_trait("pub(crate)", &[]));
    }

    #[test]
    fn test_detect_sealed_pub_super() {
        assert!(detect_sealed_trait("pub(super)", &[]));
    }

    #[test]
    fn test_detect_sealed_private() {
        assert!(detect_sealed_trait("", &[]));
    }

    #[test]
    fn test_detect_sealed_pub() {
        assert!(!detect_sealed_trait("pub", &[]));
    }

    #[test]
    fn test_detect_sealed_super_trait_pattern() {
        assert!(detect_sealed_trait("pub", &["Sealed".to_string()]));
    }

    #[test]
    fn test_detect_sealed_private_super_trait() {
        assert!(detect_sealed_trait("pub", &["private::Sealed".to_string()]));
    }

    // ====== collect_trait_methods tests ======

    #[test]
    fn test_collect_trait_methods_with_contracts() {
        let trait_def = TraitDef {
            name: "Test".to_string(),
            methods: vec![
                TraitMethod {
                    name: "method1".to_string(),
                    params: vec![],
                    return_ty: Ty::Unit,
                    requires: vec![SpecExpr {
                        raw: "true".to_string(),
                    }],
                    ensures: vec![],
                    is_pure: false,
                },
                TraitMethod {
                    name: "method2".to_string(),
                    params: vec![],
                    return_ty: Ty::Unit,
                    requires: vec![],
                    ensures: vec![SpecExpr {
                        raw: "true".to_string(),
                    }],
                    is_pure: false,
                },
                TraitMethod {
                    name: "method3".to_string(),
                    params: vec![],
                    return_ty: Ty::Unit,
                    requires: vec![],
                    ensures: vec![],
                    is_pure: false,
                },
            ],
            is_sealed: false,
            super_traits: vec![],
        };
        let methods = collect_trait_methods(&trait_def);
        assert_eq!(methods.len(), 2);
        assert!(methods.iter().any(|m| m.name == "method1"));
        assert!(methods.iter().any(|m| m.name == "method2"));
    }

    #[test]
    fn test_collect_trait_methods_all_contracted() {
        let trait_def = TraitDef {
            name: "Test".to_string(),
            methods: vec![
                TraitMethod {
                    name: "method1".to_string(),
                    params: vec![],
                    return_ty: Ty::Unit,
                    requires: vec![SpecExpr {
                        raw: "true".to_string(),
                    }],
                    ensures: vec![],
                    is_pure: false,
                },
                TraitMethod {
                    name: "method2".to_string(),
                    params: vec![],
                    return_ty: Ty::Unit,
                    requires: vec![],
                    ensures: vec![SpecExpr {
                        raw: "true".to_string(),
                    }],
                    is_pure: false,
                },
            ],
            is_sealed: false,
            super_traits: vec![],
        };
        let methods = collect_trait_methods(&trait_def);
        assert_eq!(methods.len(), 2);
    }

    #[test]
    fn test_collect_trait_methods_none_contracted() {
        let trait_def = TraitDef {
            name: "Test".to_string(),
            methods: vec![TraitMethod {
                name: "method1".to_string(),
                params: vec![],
                return_ty: Ty::Unit,
                requires: vec![],
                ensures: vec![],
                is_pure: false,
            }],
            is_sealed: false,
            super_traits: vec![],
        };
        let methods = collect_trait_methods(&trait_def);
        assert!(methods.is_empty());
    }

    // ====== find_missing_impl_methods tests ======

    #[test]
    fn test_find_missing_impl_methods_all_present() {
        let trait_def = TraitDef {
            name: "Stack".to_string(),
            methods: vec![TraitMethod {
                name: "push".to_string(),
                params: vec![],
                return_ty: Ty::Unit,
                requires: vec![],
                ensures: vec![],
                is_pure: false,
            }],
            is_sealed: false,
            super_traits: vec![],
        };
        let impl_info = TraitImpl {
            trait_name: "Stack".to_string(),
            impl_type: "VecStack".to_string(),
            method_names: vec!["push".to_string()],
        };
        let missing = find_missing_impl_methods(&trait_def, &impl_info);
        assert!(missing.is_empty());
    }

    #[test]
    fn test_find_missing_impl_methods_some_missing() {
        let trait_def = TraitDef {
            name: "Stack".to_string(),
            methods: vec![
                TraitMethod {
                    name: "push".to_string(),
                    params: vec![],
                    return_ty: Ty::Unit,
                    requires: vec![],
                    ensures: vec![],
                    is_pure: false,
                },
                TraitMethod {
                    name: "pop".to_string(),
                    params: vec![],
                    return_ty: Ty::Int(IntTy::I32),
                    requires: vec![],
                    ensures: vec![],
                    is_pure: false,
                },
            ],
            is_sealed: false,
            super_traits: vec![],
        };
        let impl_info = TraitImpl {
            trait_name: "Stack".to_string(),
            impl_type: "VecStack".to_string(),
            method_names: vec!["push".to_string()],
        };
        let missing = find_missing_impl_methods(&trait_def, &impl_info);
        assert_eq!(missing.len(), 1);
        assert_eq!(missing[0], "pop");
    }

    #[test]
    fn test_find_missing_impl_methods_all_missing() {
        let trait_def = TraitDef {
            name: "Stack".to_string(),
            methods: vec![
                TraitMethod {
                    name: "push".to_string(),
                    params: vec![],
                    return_ty: Ty::Unit,
                    requires: vec![],
                    ensures: vec![],
                    is_pure: false,
                },
                TraitMethod {
                    name: "pop".to_string(),
                    params: vec![],
                    return_ty: Ty::Int(IntTy::I32),
                    requires: vec![],
                    ensures: vec![],
                    is_pure: false,
                },
            ],
            is_sealed: false,
            super_traits: vec![],
        };
        let impl_info = TraitImpl {
            trait_name: "Stack".to_string(),
            impl_type: "VecStack".to_string(),
            method_names: vec![],
        };
        let missing = find_missing_impl_methods(&trait_def, &impl_info);
        assert_eq!(missing.len(), 2);
        assert!(missing.contains(&"push".to_string()));
        assert!(missing.contains(&"pop".to_string()));
    }
}
