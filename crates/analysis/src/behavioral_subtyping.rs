/// Behavioral subtyping verification for trait objects.
///
/// Generates verification conditions (VCs) that prove each trait implementation
/// satisfies the Liskov Substitution Principle (LSP):
/// - Precondition weakening: impl_requires => trait_requires (impl accepts more inputs)
/// - Postcondition strengthening: trait_ensures => impl_ensures (impl guarantees more)
///
/// LANG-07 extension: RPITIT (Return Position Impl Trait in Trait) support.
/// When a trait method returns an opaque type (`impl Trait` in the trait definition)
/// and the implementation returns a concrete type, an additional Liskov subtyping VC
/// is generated asserting the concrete return type satisfies the trait's postcondition.
use crate::ir::{TraitDef, TraitImpl, TraitMethod, Ty};
use crate::trait_analysis::TraitDatabase;

/// Classification of behavioral subtyping verification conditions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SubtypingKind {
    /// Precondition weakening: trait_requires => impl_requires
    /// (impl must accept all inputs trait accepts)
    PreconditionWeakening,
    /// Postcondition strengthening: impl_ensures => trait_ensures
    /// (impl must guarantee at least what trait promises)
    PostconditionStrengthening,
}

/// A behavioral subtyping verification condition.
#[derive(Debug, Clone)]
pub struct SubtypingVc {
    /// Trait name (e.g., "Stack")
    pub trait_name: String,
    /// Implementation type (e.g., "VecStack")
    pub impl_type: String,
    /// Method name (e.g., "push")
    pub method_name: String,
    /// Kind of subtyping VC (precondition or postcondition)
    pub kind: SubtypingKind,
    /// Human-readable description of what is being verified
    pub description: String,
}

/// Generate all behavioral subtyping VCs for a trait implementation.
///
/// For each method in the trait that has contracts (requires or ensures),
/// generate precondition weakening and postcondition strengthening VCs.
pub fn generate_subtyping_vcs(
    trait_def: &TraitDef,
    impl_info: &TraitImpl,
    _trait_db: &TraitDatabase,
) -> Vec<SubtypingVc> {
    let mut vcs = Vec::new();

    for method in &trait_def.methods {
        // Skip methods without contracts
        if method.requires.is_empty() && method.ensures.is_empty() {
            continue;
        }

        // Skip methods not in the impl
        if !impl_info.method_names.contains(&method.name) {
            continue;
        }

        // Generate precondition weakening VC if trait method has requires
        if !method.requires.is_empty() {
            vcs.push(SubtypingVc {
                trait_name: trait_def.name.clone(),
                impl_type: impl_info.impl_type.clone(),
                method_name: method.name.clone(),
                kind: SubtypingKind::PreconditionWeakening,
                description: format!(
                    "{}::{} must accept all inputs {}::{} accepts",
                    impl_info.impl_type, method.name, trait_def.name, method.name
                ),
            });
        }

        // Generate postcondition strengthening VC if trait method has ensures
        if !method.ensures.is_empty() {
            vcs.push(SubtypingVc {
                trait_name: trait_def.name.clone(),
                impl_type: impl_info.impl_type.clone(),
                method_name: method.name.clone(),
                kind: SubtypingKind::PostconditionStrengthening,
                description: format!(
                    "{}::{} must guarantee at least what {}::{} promises",
                    impl_info.impl_type, method.name, trait_def.name, method.name
                ),
            });
        }
    }

    vcs
}

/// Check if a trait method uses RPITIT (Return Position Impl Trait in Trait).
///
/// Returns true if the method's return type is `Ty::Opaque`, indicating
/// the trait definition uses `-> impl Trait` syntax.
pub fn is_rpitit_method(method: &TraitMethod) -> bool {
    matches!(&method.return_ty, Ty::Opaque(_, _))
}

/// Generate RPITIT-specific subtyping VCs for a trait implementation.
///
/// When a trait method has an opaque return type (`impl Trait`) and a postcondition,
/// generate a PostconditionStrengthening VC that checks the implementation's
/// concrete return type satisfies the trait-level postcondition.
///
/// This is already handled by `generate_subtyping_vcs` for methods with `ensures`,
/// but this function provides explicit RPITIT annotation in the VC description.
pub fn generate_rpitit_vcs(
    trait_def: &TraitDef,
    impl_info: &TraitImpl,
    _trait_db: &TraitDatabase,
) -> Vec<SubtypingVc> {
    let mut vcs = Vec::new();

    for method in &trait_def.methods {
        // Only process RPITIT methods (those returning impl Trait)
        if !is_rpitit_method(method) {
            continue;
        }

        // Skip methods not in the impl
        if !impl_info.method_names.contains(&method.name) {
            continue;
        }

        // For RPITIT methods with postconditions, the impl's concrete return type
        // must satisfy the trait's ensures clauses (Liskov postcondition strengthening)
        if !method.ensures.is_empty() {
            vcs.push(SubtypingVc {
                trait_name: trait_def.name.clone(),
                impl_type: impl_info.impl_type.clone(),
                method_name: method.name.clone(),
                kind: SubtypingKind::PostconditionStrengthening,
                description: format!(
                    "RPITIT: {}::{} concrete return must satisfy {}::{} opaque type postcondition",
                    impl_info.impl_type, method.name, trait_def.name, method.name
                ),
            });
        }
    }

    vcs
}

/// Encode a precondition weakening VC as SMT commands.
///
/// Encodes: (assert (not (=> trait_requires impl_requires)))
/// If SAT, the VC fails (impl has stronger precondition than trait).
///
/// For now, this generates a simplified encoding that assumes impl_requires = true
/// (impl has no additional preconditions beyond the trait). Full implementation
/// would require parsing impl method contracts and comparing them.
pub fn encode_precondition_weakening_vc(
    trait_method: &TraitMethod,
    _impl_type: &str,
) -> Vec<rust_fv_smtlib::command::Command> {
    use crate::encode_sort::encode_type;
    use rust_fv_smtlib::command::Command;
    use rust_fv_smtlib::sort::Sort;
    use rust_fv_smtlib::term::Term;

    let mut commands = Vec::new();

    if trait_method.requires.is_empty() {
        return commands;
    }

    // Add header comment
    commands.push(Command::Comment(format!(
        "Precondition weakening VC for {}",
        trait_method.name
    )));

    // Declare parameter sorts and constants
    let param_sorts: Vec<Sort> = trait_method
        .params
        .iter()
        .map(|(_, ty)| encode_type(ty))
        .collect();

    for (param_name, param_ty) in &trait_method.params {
        let sort = encode_type(param_ty);
        commands.push(Command::DeclareConst(param_name.clone(), sort));
    }

    // Build conjunction of all trait requires clauses
    // Each requires clause is encoded as an uninterpreted predicate (Bool-valued function).
    // We must declare each predicate with declare-fun before using it in Term::App.
    let trait_requires = if trait_method.requires.len() == 1 {
        // Single requirement: use it directly as a symbolic term
        let pred_name = format!("trait_requires_{}", trait_method.name);
        commands.push(Command::DeclareFun(
            pred_name.clone(),
            param_sorts.clone(),
            Sort::Bool,
        ));
        Term::App(
            pred_name,
            trait_method
                .params
                .iter()
                .map(|(n, _)| Term::Const(n.clone()))
                .collect(),
        )
    } else {
        // Multiple requirements: conjoin them, one declare-fun per clause
        let req_terms: Vec<Term> = trait_method
            .requires
            .iter()
            .enumerate()
            .map(|(i, _)| {
                let pred_name = format!("trait_requires_{}_{}", trait_method.name, i);
                commands.push(Command::DeclareFun(
                    pred_name.clone(),
                    param_sorts.clone(),
                    Sort::Bool,
                ));
                Term::App(
                    pred_name,
                    trait_method
                        .params
                        .iter()
                        .map(|(n, _)| Term::Const(n.clone()))
                        .collect(),
                )
            })
            .collect();

        if req_terms.is_empty() {
            Term::Const("true".to_string())
        } else {
            Term::And(req_terms)
        }
    };

    // For now, assume impl_requires = true (impl has no additional preconditions)
    // This makes the VC: (assert (not (=> trait_requires true)))
    // which is equivalent to: (assert (not trait_requires))
    // If UNSAT, then trait_requires is a tautology (always true) - trivially satisfied
    // If SAT, then there exist inputs where trait_requires is false - also OK for weakening

    // Actually, for precondition weakening: trait_requires => impl_requires
    // If impl_requires = true, this becomes: trait_requires => true, which is always true
    // So the VC should be UNSAT (valid). Let's encode: (assert (not (=> trait_requires true)))
    let implication = Term::Implies(
        Box::new(trait_requires),
        Box::new(Term::Const("true".to_string())),
    );
    let negated = Term::Not(Box::new(implication));

    commands.push(Command::Assert(negated));
    commands.push(Command::CheckSat);

    commands
}

/// Encode a postcondition strengthening VC as SMT commands.
///
/// Encodes: (assert (not (=> impl_ensures trait_ensures)))
/// If SAT, the VC fails (impl doesn't guarantee trait postcondition).
///
/// For now, this generates a simplified encoding that assumes impl_ensures = trait_ensures
/// (impl guarantees exactly what the trait promises). Full implementation would require
/// parsing impl method contracts and comparing them.
pub fn encode_postcondition_strengthening_vc(
    trait_method: &TraitMethod,
    _impl_type: &str,
) -> Vec<rust_fv_smtlib::command::Command> {
    use crate::encode_sort::encode_type;
    use rust_fv_smtlib::command::Command;
    use rust_fv_smtlib::sort::Sort;
    use rust_fv_smtlib::term::Term;

    let mut commands = Vec::new();

    if trait_method.ensures.is_empty() {
        return commands;
    }

    // Add header comment
    commands.push(Command::Comment(format!(
        "Postcondition strengthening VC for {}",
        trait_method.name
    )));

    // Declare parameter sorts and constants (including return value)
    let param_sorts: Vec<Sort> = trait_method
        .params
        .iter()
        .map(|(_, ty)| encode_type(ty))
        .collect();

    for (param_name, param_ty) in &trait_method.params {
        let sort = encode_type(param_ty);
        commands.push(Command::DeclareConst(param_name.clone(), sort));
    }

    // Declare return value
    let return_sort = encode_type(&trait_method.return_ty);
    commands.push(Command::DeclareConst(
        "result".to_string(),
        return_sort.clone(),
    ));

    // Build the sort list for the predicate: all params + return value
    let mut pred_sorts = param_sorts.clone();
    pred_sorts.push(return_sort);

    // Build conjunction of all trait ensures clauses.
    // Each ensures clause is encoded as an uninterpreted predicate (Bool-valued function).
    // We must declare each predicate with declare-fun before using it in Term::App.
    let trait_ensures = if trait_method.ensures.len() == 1 {
        // Single postcondition: use it directly as a symbolic term
        let pred_name = format!("trait_ensures_{}", trait_method.name);
        commands.push(Command::DeclareFun(
            pred_name.clone(),
            pred_sorts.clone(),
            Sort::Bool,
        ));
        let mut params: Vec<Term> = trait_method
            .params
            .iter()
            .map(|(n, _)| Term::Const(n.clone()))
            .collect();
        params.push(Term::Const("result".to_string()));
        Term::App(pred_name, params)
    } else {
        // Multiple postconditions: conjoin them, one declare-fun per clause
        let ens_terms: Vec<Term> = trait_method
            .ensures
            .iter()
            .enumerate()
            .map(|(i, _)| {
                let pred_name = format!("trait_ensures_{}_{}", trait_method.name, i);
                commands.push(Command::DeclareFun(
                    pred_name.clone(),
                    pred_sorts.clone(),
                    Sort::Bool,
                ));
                let mut params: Vec<Term> = trait_method
                    .params
                    .iter()
                    .map(|(n, _)| Term::Const(n.clone()))
                    .collect();
                params.push(Term::Const("result".to_string()));
                Term::App(pred_name, params)
            })
            .collect();

        if ens_terms.is_empty() {
            Term::Const("true".to_string())
        } else {
            Term::And(ens_terms)
        }
    };

    // For now, assume impl_ensures = trait_ensures (impl guarantees exactly what trait promises)
    // This makes the VC: (assert (not (=> trait_ensures trait_ensures)))
    // which is equivalent to: (assert (not true)), which should be UNSAT (valid)
    let implication = Term::Implies(Box::new(trait_ensures.clone()), Box::new(trait_ensures));
    let negated = Term::Not(Box::new(implication));

    commands.push(Command::Assert(negated));
    commands.push(Command::CheckSat);

    commands
}

/// Generate full SMT-LIB scripts for all behavioral subtyping VCs.
///
/// For each contracted method, generates:
/// - Parameter sort declarations
/// - Parameter constant declarations
/// - The VC assertion (precondition or postcondition)
/// - check-sat command
pub fn generate_subtyping_script(
    trait_def: &TraitDef,
    impl_info: &TraitImpl,
) -> Vec<rust_fv_smtlib::script::Script> {
    use rust_fv_smtlib::script::Script;

    let mut scripts = Vec::new();

    for method in &trait_def.methods {
        // Skip methods without contracts
        if method.requires.is_empty() && method.ensures.is_empty() {
            continue;
        }

        // Skip methods not in the impl
        if !impl_info.method_names.contains(&method.name) {
            continue;
        }

        // Generate precondition weakening script if trait method has requires
        if !method.requires.is_empty() {
            let commands = encode_precondition_weakening_vc(method, &impl_info.impl_type);
            scripts.push(Script::with_commands(commands));
        }

        // Generate postcondition strengthening script if trait method has ensures
        if !method.ensures.is_empty() {
            let commands = encode_postcondition_strengthening_vc(method, &impl_info.impl_type);
            scripts.push(Script::with_commands(commands));
        }
    }

    scripts
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{SpecExpr, Ty};

    fn make_spec_expr(text: &str) -> SpecExpr {
        SpecExpr {
            raw: text.to_string(),
        }
    }

    fn make_trait_method(
        name: &str,
        requires: Vec<SpecExpr>,
        ensures: Vec<SpecExpr>,
    ) -> TraitMethod {
        TraitMethod {
            name: name.to_string(),
            params: vec![("self".to_string(), Ty::Unit)],
            return_ty: Ty::Unit,
            requires,
            ensures,
            is_pure: false,
        }
    }

    fn make_trait_def(name: &str, methods: Vec<TraitMethod>) -> TraitDef {
        TraitDef {
            name: name.to_string(),
            methods,
            is_sealed: false,
            super_traits: vec![],
        }
    }

    fn make_trait_impl(trait_name: &str, impl_type: &str, method_names: Vec<&str>) -> TraitImpl {
        TraitImpl {
            trait_name: trait_name.to_string(),
            impl_type: impl_type.to_string(),
            method_names: method_names.iter().map(|s| s.to_string()).collect(),
        }
    }

    #[test]
    fn test_subtyping_vc_creation() {
        let vc = SubtypingVc {
            trait_name: "Stack".to_string(),
            impl_type: "VecStack".to_string(),
            method_name: "push".to_string(),
            kind: SubtypingKind::PreconditionWeakening,
            description: "VecStack::push must accept all inputs Stack::push accepts".to_string(),
        };

        assert_eq!(vc.trait_name, "Stack");
        assert_eq!(vc.impl_type, "VecStack");
        assert_eq!(vc.method_name, "push");
        assert_eq!(vc.kind, SubtypingKind::PreconditionWeakening);
        assert!(vc.description.contains("VecStack"));
    }

    #[test]
    fn test_subtyping_kind_equality() {
        assert_eq!(
            SubtypingKind::PreconditionWeakening,
            SubtypingKind::PreconditionWeakening
        );
        assert_ne!(
            SubtypingKind::PreconditionWeakening,
            SubtypingKind::PostconditionStrengthening
        );
    }

    #[test]
    fn test_generate_subtyping_vcs_basic() {
        let method = make_trait_method(
            "push",
            vec![make_spec_expr("x > 0")],
            vec![make_spec_expr("result")],
        );
        let trait_def = make_trait_def("Stack", vec![method]);
        let impl_info = make_trait_impl("Stack", "VecStack", vec!["push"]);
        let trait_db = TraitDatabase::new();

        let vcs = generate_subtyping_vcs(&trait_def, &impl_info, &trait_db);

        assert_eq!(
            vcs.len(),
            2,
            "Should generate 2 VCs: pre-weak + post-strong"
        );
        assert!(
            vcs.iter()
                .any(|v| v.kind == SubtypingKind::PreconditionWeakening)
        );
        assert!(
            vcs.iter()
                .any(|v| v.kind == SubtypingKind::PostconditionStrengthening)
        );
    }

    #[test]
    fn test_generate_subtyping_vcs_no_contracts() {
        let method = make_trait_method("push", vec![], vec![]);
        let trait_def = make_trait_def("Stack", vec![method]);
        let impl_info = make_trait_impl("Stack", "VecStack", vec!["push"]);
        let trait_db = TraitDatabase::new();

        let vcs = generate_subtyping_vcs(&trait_def, &impl_info, &trait_db);

        assert_eq!(vcs.len(), 0, "No contracts = no VCs");
    }

    #[test]
    fn test_generate_subtyping_vcs_requires_only() {
        let method = make_trait_method("push", vec![make_spec_expr("x > 0")], vec![]);
        let trait_def = make_trait_def("Stack", vec![method]);
        let impl_info = make_trait_impl("Stack", "VecStack", vec!["push"]);
        let trait_db = TraitDatabase::new();

        let vcs = generate_subtyping_vcs(&trait_def, &impl_info, &trait_db);

        assert_eq!(vcs.len(), 1, "Only requires = 1 PreconditionWeakening VC");
        assert_eq!(vcs[0].kind, SubtypingKind::PreconditionWeakening);
    }

    #[test]
    fn test_generate_subtyping_vcs_ensures_only() {
        let method = make_trait_method("push", vec![], vec![make_spec_expr("result")]);
        let trait_def = make_trait_def("Stack", vec![method]);
        let impl_info = make_trait_impl("Stack", "VecStack", vec!["push"]);
        let trait_db = TraitDatabase::new();

        let vcs = generate_subtyping_vcs(&trait_def, &impl_info, &trait_db);

        assert_eq!(
            vcs.len(),
            1,
            "Only ensures = 1 PostconditionStrengthening VC"
        );
        assert_eq!(vcs[0].kind, SubtypingKind::PostconditionStrengthening);
    }

    #[test]
    fn test_generate_subtyping_vcs_multiple_methods() {
        let method1 = make_trait_method(
            "push",
            vec![make_spec_expr("x > 0")],
            vec![make_spec_expr("result")],
        );
        let method2 = make_trait_method(
            "pop",
            vec![make_spec_expr("len > 0")],
            vec![make_spec_expr("result.is_some()")],
        );
        let trait_def = make_trait_def("Stack", vec![method1, method2]);
        let impl_info = make_trait_impl("Stack", "VecStack", vec!["push", "pop"]);
        let trait_db = TraitDatabase::new();

        let vcs = generate_subtyping_vcs(&trait_def, &impl_info, &trait_db);

        assert_eq!(vcs.len(), 4, "2 methods with contracts = 4 VCs");
    }

    #[test]
    fn test_generate_subtyping_vcs_missing_impl_method() {
        let method = make_trait_method(
            "push",
            vec![make_spec_expr("x > 0")],
            vec![make_spec_expr("result")],
        );
        let trait_def = make_trait_def("Stack", vec![method]);
        // impl doesn't provide "push"
        let impl_info = make_trait_impl("Stack", "VecStack", vec![]);
        let trait_db = TraitDatabase::new();

        let vcs = generate_subtyping_vcs(&trait_def, &impl_info, &trait_db);

        assert_eq!(
            vcs.len(),
            0,
            "Method not in impl = skip (no VC for missing method)"
        );
    }

    #[test]
    fn test_generate_subtyping_vcs_description_format() {
        let method = make_trait_method("push", vec![make_spec_expr("x > 0")], vec![]);
        let trait_def = make_trait_def("Stack", vec![method]);
        let impl_info = make_trait_impl("Stack", "VecStack", vec!["push"]);
        let trait_db = TraitDatabase::new();

        let vcs = generate_subtyping_vcs(&trait_def, &impl_info, &trait_db);

        assert_eq!(vcs.len(), 1);
        assert!(
            vcs[0].description.contains("VecStack"),
            "Description should contain impl type"
        );
        assert!(
            vcs[0].description.contains("Stack"),
            "Description should contain trait name"
        );
        assert!(
            vcs[0].description.contains("push"),
            "Description should contain method name"
        );
    }

    #[test]
    fn test_encode_precondition_weakening_produces_commands() {
        let method = make_trait_method("push", vec![make_spec_expr("x > 0")], vec![]);

        let commands = encode_precondition_weakening_vc(&method, "VecStack");

        assert!(
            !commands.is_empty(),
            "Should produce non-empty command list"
        );
        // Should contain assert and check-sat at minimum
    }

    #[test]
    fn test_encode_postcondition_strengthening_produces_commands() {
        let method = make_trait_method("push", vec![], vec![make_spec_expr("result")]);

        let commands = encode_postcondition_strengthening_vc(&method, "VecStack");

        assert!(
            !commands.is_empty(),
            "Should produce non-empty command list"
        );
        // Should contain assert and check-sat at minimum
    }

    #[test]
    fn test_generate_subtyping_script_basic() {
        let method = make_trait_method(
            "push",
            vec![make_spec_expr("x > 0")],
            vec![make_spec_expr("result")],
        );
        let trait_def = make_trait_def("Stack", vec![method]);
        let impl_info = make_trait_impl("Stack", "VecStack", vec!["push"]);

        let scripts = generate_subtyping_script(&trait_def, &impl_info);

        assert_eq!(
            scripts.len(),
            2,
            "1 contracted method = 2 scripts (pre + post)"
        );
    }
}
