/// Trait analysis infrastructure for verification.
///
/// Provides trait database, sealed trait detection, and impl collection
/// functionality to support trait object and behavioral subtyping verification.
use std::collections::HashMap;

use crate::ir::{TraitDef, TraitImpl, TraitMethod, Ty};

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

/// Check if a type implements the Drop trait.
///
/// Returns true for user-defined struct/named types that are marked with Drop
/// (detected via DropLocalInfo in the IR), and false for all primitive types
/// which never implement Drop.
///
/// For Named/Struct/Enum types, this uses conservative analysis: types populated
/// in `drop_locals` by the MIR converter have `has_drop: true`. This standalone
/// function provides a type-level check for use in VC generation.
pub fn has_drop_impl(ty: &Ty) -> bool {
    match ty {
        // Primitives never implement Drop
        Ty::Bool | Ty::Int(_) | Ty::Uint(_) | Ty::Float(_) | Ty::Char | Ty::Unit | Ty::Never => {
            false
        }
        // Specification-only types never implement Drop
        Ty::SpecInt | Ty::SpecNat => false,
        // References and raw pointers don't implement Drop themselves
        Ty::Ref(_, _) | Ty::RawPtr(_, _) | Ty::NonNull(_) => false,
        // Generic type parameters -- conservatively assume no Drop
        Ty::Generic(_) | Ty::ConstGeneric(_, _) => false,
        // Named/Struct/Enum/TraitObject types may implement Drop
        // The actual determination comes from DropLocalInfo.has_drop in the IR
        Ty::Named(_) | Ty::Struct(_, _) | Ty::Enum(_, _) | Ty::TraitObject(_) => true,
        // Tuples, arrays, slices -- Drop if any element has Drop (conservative: true)
        Ty::Tuple(elems) => elems.iter().any(has_drop_impl),
        Ty::Array(elem, _) | Ty::Slice(elem) => has_drop_impl(elem),
        // Closures may capture Drop types
        Ty::Closure(_) => true,
        // Union types may implement Drop (conservative: true for named unions)
        Ty::Union(_, _) => true,
    }
}

/// Check if a type implements the Unpin trait.
///
/// All primitive types are Unpin. Most standard types are Unpin by default.
/// Only types explicitly marked as `!Unpin` (e.g., self-referential types,
/// async state machines) are not Unpin.
///
/// Conservative for user types: Named types containing "!Unpin" or "PhantomPinned"
/// are treated as non-Unpin; all others are Unpin by default (matching Rust semantics
/// where Unpin is auto-implemented).
pub fn is_unpin(ty: &Ty) -> bool {
    match ty {
        // All primitives are Unpin
        Ty::Bool | Ty::Int(_) | Ty::Uint(_) | Ty::Float(_) | Ty::Char | Ty::Unit | Ty::Never => {
            true
        }
        Ty::SpecInt | Ty::SpecNat => true,
        // References are always Unpin (even &mut T where T: !Unpin)
        Ty::Ref(_, _) | Ty::RawPtr(_, _) | Ty::NonNull(_) => true,
        // Named types: check for PhantomPinned marker
        Ty::Named(name) => !name.contains("PhantomPinned") && !name.contains("!Unpin"),
        // Struct types: Unpin if all fields are Unpin
        Ty::Struct(name, fields) => {
            !name.contains("PhantomPinned")
                && !name.contains("!Unpin")
                && fields.iter().all(|(_, ty)| is_unpin(ty))
        }
        // Generic/ConstGeneric -- conservatively Unpin (Rust auto-trait default)
        Ty::Generic(_) | Ty::ConstGeneric(_, _) => true,
        // Tuples/arrays: Unpin if all elements are Unpin
        Ty::Tuple(elems) => elems.iter().all(is_unpin),
        Ty::Array(elem, _) | Ty::Slice(elem) => is_unpin(elem),
        // Enums, closures, trait objects, unions -- conservatively Unpin
        Ty::Enum(_, _) | Ty::Closure(_) | Ty::TraitObject(_) | Ty::Union(_, _) => true,
    }
}

/// Check if a type implements the Copy trait.
///
/// Returns true for types known to be Copy (primitives, references),
/// and false for types that are never Copy (mutable references, named types
/// that are typically not Copy).
///
/// For Named types, uses the convention that types containing "Copy" in their
/// name are treated as Copy for diagnostic purposes.
pub fn has_copy_impl(ty: &Ty) -> bool {
    match ty {
        // All numeric primitives and bool are Copy
        Ty::Bool | Ty::Int(_) | Ty::Uint(_) | Ty::Float(_) | Ty::Char | Ty::Unit => true,
        // Never type is vacuously Copy
        Ty::Never => true,
        // Shared references are Copy, mutable references are NOT Copy
        Ty::Ref(_, crate::ir::Mutability::Shared) => true,
        Ty::Ref(_, crate::ir::Mutability::Mutable) => false,
        // Raw pointers are Copy
        Ty::RawPtr(_, _) => true,
        // NonNull is Copy
        Ty::NonNull(_) => true,
        // Spec types are Copy (specification-only)
        Ty::SpecInt | Ty::SpecNat => true,
        // Named types: check for "Copy" pattern or known non-Copy types
        Ty::Named(name) => name.contains("Copy"),
        // Struct: Copy if all fields are Copy (and name doesn't indicate non-Copy)
        Ty::Struct(_, fields) => fields.iter().all(|(_, ty)| has_copy_impl(ty)),
        // Tuples are Copy if all elements are Copy
        Ty::Tuple(elems) => elems.iter().all(has_copy_impl),
        // Arrays are Copy if element type is Copy
        Ty::Array(elem, _) => has_copy_impl(elem),
        // Generic/ConstGeneric -- conservatively not Copy
        Ty::Generic(_) | Ty::ConstGeneric(_, _) => false,
        // Slices, enums, closures, trait objects, unions -- generally not Copy
        Ty::Slice(_) | Ty::Enum(_, _) | Ty::Closure(_) | Ty::TraitObject(_) | Ty::Union(_, _) => {
            false
        }
    }
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
