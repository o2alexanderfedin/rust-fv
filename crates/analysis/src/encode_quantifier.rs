//! Quantifier encoding with trigger inference for SMT instantiation control.
//!
//! When translating quantified specifications to SMT-LIB, we must provide
//! trigger patterns (also called instantiation patterns) that tell the SMT
//! solver when to instantiate the quantifier. Without triggers, the solver
//! may either:
//! - Not instantiate the quantifier at all (incomplete)
//! - Instantiate it infinitely (timeout)
//!
//! This module implements conservative trigger inference based on the Verus
//! approach: select function applications that cover all bound variables.

use std::collections::HashSet;

use rust_fv_smtlib::term::Term;

/// Infer trigger patterns for a quantifier body.
///
/// A valid trigger must:
/// 1. Be a function application (Term::App)
/// 2. Contain all bound variables (transitively through arguments)
/// 3. Not be a basic operator (=, +, -, etc.)
///
/// Returns a list of trigger groups. Each group is a list of terms that
/// together cover all bound variables. If no valid triggers are found,
/// returns an empty vector (caller should warn).
pub fn infer_triggers(body: &Term, bound_vars: &[String]) -> Vec<Vec<Term>> {
    let mut triggers = Vec::new();

    // Find all function applications in the body
    let candidates = find_trigger_candidates(body);

    // Filter candidates: must contain all bound variables
    for candidate in candidates {
        let vars = free_variables(&candidate);
        let bound_set: HashSet<_> = bound_vars.iter().collect();
        let candidate_vars: HashSet<_> = vars.iter().collect();

        // Check if this candidate covers all bound variables
        if bound_set.is_subset(&candidate_vars) {
            // Single trigger that covers everything
            triggers.push(vec![candidate]);
            break; // We found a covering trigger, use it
        }
    }

    triggers
}

/// Collect all free variables (Term::Const) in a term.
fn free_variables(term: &Term) -> HashSet<String> {
    let mut vars = HashSet::new();
    collect_free_variables(term, &mut vars);
    vars
}

fn collect_free_variables(term: &Term, vars: &mut HashSet<String>) {
    match term {
        Term::Const(name) => {
            vars.insert(name.clone());
        }
        Term::Not(inner) => collect_free_variables(inner, vars),
        Term::And(terms) | Term::Or(terms) | Term::Distinct(terms) => {
            for t in terms {
                collect_free_variables(t, vars);
            }
        }
        Term::Implies(a, b)
        | Term::Iff(a, b)
        | Term::Eq(a, b)
        | Term::BvAdd(a, b)
        | Term::BvSub(a, b)
        | Term::BvMul(a, b)
        | Term::BvSDiv(a, b)
        | Term::BvUDiv(a, b)
        | Term::BvSRem(a, b)
        | Term::BvURem(a, b)
        | Term::BvSLt(a, b)
        | Term::BvSLe(a, b)
        | Term::BvSGt(a, b)
        | Term::BvSGe(a, b)
        | Term::BvULt(a, b)
        | Term::BvULe(a, b)
        | Term::BvUGt(a, b)
        | Term::BvUGe(a, b)
        | Term::BvAnd(a, b)
        | Term::BvOr(a, b)
        | Term::BvXor(a, b)
        | Term::BvShl(a, b)
        | Term::BvLShr(a, b)
        | Term::BvAShr(a, b)
        | Term::Concat(a, b)
        | Term::IntAdd(a, b)
        | Term::IntSub(a, b)
        | Term::IntMul(a, b)
        | Term::IntDiv(a, b)
        | Term::IntMod(a, b)
        | Term::IntLt(a, b)
        | Term::IntLe(a, b)
        | Term::IntGt(a, b)
        | Term::IntGe(a, b)
        | Term::Select(a, b) => {
            collect_free_variables(a, vars);
            collect_free_variables(b, vars);
        }
        Term::Ite(cond, then_branch, else_branch) | Term::Store(cond, then_branch, else_branch) => {
            collect_free_variables(cond, vars);
            collect_free_variables(then_branch, vars);
            collect_free_variables(else_branch, vars);
        }
        Term::BvNeg(inner)
        | Term::BvNot(inner)
        | Term::ZeroExtend(_, inner)
        | Term::SignExtend(_, inner)
        | Term::Extract(_, _, inner)
        | Term::Bv2Int(inner)
        | Term::Int2Bv(_, inner)
        | Term::IntNeg(inner) => {
            collect_free_variables(inner, vars);
        }
        Term::Forall(_, body) | Term::Exists(_, body) => {
            // Don't descend into nested quantifiers for trigger inference
            collect_free_variables(body, vars);
        }
        Term::Let(bindings, body) => {
            for (_, t) in bindings {
                collect_free_variables(t, vars);
            }
            collect_free_variables(body, vars);
        }
        Term::App(_, args) => {
            for arg in args {
                collect_free_variables(arg, vars);
            }
        }
        Term::Annotated(body, _) => {
            collect_free_variables(body, vars);
        }
        Term::BoolLit(_) | Term::IntLit(_) | Term::BitVecLit(_, _) => {
            // Literals have no variables
        }
    }
}

/// Find all function applications (Term::App) that could serve as triggers.
///
/// We exclude basic operators and only consider user-defined functions.
fn find_trigger_candidates(term: &Term) -> Vec<Term> {
    let mut candidates = Vec::new();
    collect_trigger_candidates(term, &mut candidates);
    candidates
}

fn collect_trigger_candidates(term: &Term, candidates: &mut Vec<Term>) {
    match term {
        Term::App(_name, args) => {
            // Only user-defined functions (not built-in selectors/constructors)
            // For now, accept all Term::App as potential triggers
            // TODO: Filter out selectors like "Point-x" if needed
            if !args.is_empty() {
                candidates.push(term.clone());
            }
            // Also recurse into arguments
            for arg in args {
                collect_trigger_candidates(arg, candidates);
            }
        }
        Term::Not(inner) => collect_trigger_candidates(inner, candidates),
        Term::And(terms) | Term::Or(terms) | Term::Distinct(terms) => {
            for t in terms {
                collect_trigger_candidates(t, candidates);
            }
        }
        Term::Implies(a, b)
        | Term::Iff(a, b)
        | Term::Eq(a, b)
        | Term::BvAdd(a, b)
        | Term::BvSub(a, b)
        | Term::BvMul(a, b)
        | Term::BvSDiv(a, b)
        | Term::BvUDiv(a, b)
        | Term::BvSRem(a, b)
        | Term::BvURem(a, b)
        | Term::BvSLt(a, b)
        | Term::BvSLe(a, b)
        | Term::BvSGt(a, b)
        | Term::BvSGe(a, b)
        | Term::BvULt(a, b)
        | Term::BvULe(a, b)
        | Term::BvUGt(a, b)
        | Term::BvUGe(a, b)
        | Term::BvAnd(a, b)
        | Term::BvOr(a, b)
        | Term::BvXor(a, b)
        | Term::BvShl(a, b)
        | Term::BvLShr(a, b)
        | Term::BvAShr(a, b)
        | Term::Concat(a, b)
        | Term::IntAdd(a, b)
        | Term::IntSub(a, b)
        | Term::IntMul(a, b)
        | Term::IntDiv(a, b)
        | Term::IntMod(a, b)
        | Term::IntLt(a, b)
        | Term::IntLe(a, b)
        | Term::IntGt(a, b)
        | Term::IntGe(a, b)
        | Term::Select(a, b) => {
            collect_trigger_candidates(a, candidates);
            collect_trigger_candidates(b, candidates);
        }
        Term::Ite(cond, then_branch, else_branch) | Term::Store(cond, then_branch, else_branch) => {
            collect_trigger_candidates(cond, candidates);
            collect_trigger_candidates(then_branch, candidates);
            collect_trigger_candidates(else_branch, candidates);
        }
        Term::BvNeg(inner)
        | Term::BvNot(inner)
        | Term::ZeroExtend(_, inner)
        | Term::SignExtend(_, inner)
        | Term::Extract(_, _, inner)
        | Term::Bv2Int(inner)
        | Term::Int2Bv(_, inner)
        | Term::IntNeg(inner) => {
            collect_trigger_candidates(inner, candidates);
        }
        Term::Forall(_, body) | Term::Exists(_, body) => {
            collect_trigger_candidates(body, candidates);
        }
        Term::Let(bindings, body) => {
            for (_, t) in bindings {
                collect_trigger_candidates(t, candidates);
            }
            collect_trigger_candidates(body, candidates);
        }
        Term::Annotated(body, _) => {
            collect_trigger_candidates(body, candidates);
        }
        Term::BoolLit(_) | Term::IntLit(_) | Term::BitVecLit(_, _) | Term::Const(_) => {
            // No triggers in literals or bare variables
        }
    }
}

/// Annotate a quantifier term with inferred trigger patterns.
///
/// If the term is Term::Forall or Term::Exists, infers triggers and wraps
/// the body with Term::Annotated if triggers are found. If no triggers can
/// be inferred, logs a warning and returns the term unchanged.
pub fn annotate_quantifier(term: Term) -> Term {
    match term {
        Term::Forall(vars, body) => {
            let var_names: Vec<String> = vars.iter().map(|(name, _)| name.clone()).collect();
            let triggers = infer_triggers(&body, &var_names);

            if triggers.is_empty() {
                tracing::warn!(
                    "No trigger pattern found for forall quantifier over variables: {:?}",
                    var_names
                );
                Term::Forall(vars, body)
            } else {
                // Annotate the body with :pattern
                let annotated_body = Term::Annotated(
                    body,
                    vec![(
                        "pattern".to_string(),
                        triggers.into_iter().flatten().collect(),
                    )],
                );
                Term::Forall(vars, Box::new(annotated_body))
            }
        }
        Term::Exists(vars, body) => {
            let var_names: Vec<String> = vars.iter().map(|(name, _)| name.clone()).collect();
            let triggers = infer_triggers(&body, &var_names);

            if triggers.is_empty() {
                tracing::warn!(
                    "No trigger pattern found for exists quantifier over variables: {:?}",
                    var_names
                );
                Term::Exists(vars, body)
            } else {
                // Annotate the body with :pattern
                let annotated_body = Term::Annotated(
                    body,
                    vec![(
                        "pattern".to_string(),
                        triggers.into_iter().flatten().collect(),
                    )],
                );
                Term::Exists(vars, Box::new(annotated_body))
            }
        }
        other => other, // Not a quantifier, return as-is
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_fv_smtlib::sort::Sort;

    #[test]
    fn test_free_variables() {
        let term = Term::BvAdd(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::Const("y".to_string())),
        );
        let vars = free_variables(&term);
        assert_eq!(vars.len(), 2);
        assert!(vars.contains("x"));
        assert!(vars.contains("y"));
    }

    #[test]
    fn test_free_variables_nested() {
        let term = Term::Implies(
            Box::new(Term::BvSGt(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::IntLit(0)),
            )),
            Box::new(Term::App(
                "f".to_string(),
                vec![Term::Const("x".to_string())],
            )),
        );
        let vars = free_variables(&term);
        assert_eq!(vars.len(), 1);
        assert!(vars.contains("x"));
    }

    #[test]
    fn test_infer_trigger_app() {
        // Body: f(x) > 0
        let body = Term::BvSGt(
            Box::new(Term::App(
                "f".to_string(),
                vec![Term::Const("x".to_string())],
            )),
            Box::new(Term::IntLit(0)),
        );
        let triggers = infer_triggers(&body, &["x".to_string()]);
        assert_eq!(triggers.len(), 1);
        assert_eq!(triggers[0].len(), 1);
        // The trigger should be the f(x) application
        if let Term::App(name, _) = &triggers[0][0] {
            assert_eq!(name, "f");
        } else {
            panic!("Expected App trigger");
        }
    }

    #[test]
    fn test_infer_trigger_no_app() {
        // Body: x + 1 > 0 (no function application)
        let body = Term::BvSGt(
            Box::new(Term::BvAdd(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::IntLit(1)),
            )),
            Box::new(Term::IntLit(0)),
        );
        let triggers = infer_triggers(&body, &["x".to_string()]);
        assert!(triggers.is_empty(), "No valid trigger without function app");
    }

    #[test]
    fn test_annotate_forall() {
        // forall x. f(x) > 0
        let body = Term::BvSGt(
            Box::new(Term::App(
                "f".to_string(),
                vec![Term::Const("x".to_string())],
            )),
            Box::new(Term::IntLit(0)),
        );
        let forall_term = Term::Forall(vec![("x".to_string(), Sort::Int)], Box::new(body));

        let annotated = annotate_quantifier(forall_term);

        // Check that it's still a Forall
        if let Term::Forall(_vars, body) = annotated {
            // Check that the body is now Annotated
            if let Term::Annotated(_, annotations) = &*body {
                assert_eq!(annotations.len(), 1);
                assert_eq!(annotations[0].0, "pattern");
                assert!(!annotations[0].1.is_empty());
            } else {
                panic!("Expected Annotated body");
            }
        } else {
            panic!("Expected Forall term");
        }
    }

    #[test]
    fn test_annotate_no_trigger_warns() {
        // forall x. x > 0 (no function app)
        let body = Term::BvSGt(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::IntLit(0)),
        );
        let forall_term = Term::Forall(vec![("x".to_string(), Sort::Int)], Box::new(body.clone()));

        let annotated = annotate_quantifier(forall_term);

        // Should return unchanged (no annotation)
        if let Term::Forall(_vars, result_body) = annotated {
            // Body should NOT be Annotated
            assert!(
                !matches!(&*result_body, Term::Annotated(_, _)),
                "Body should not be annotated when no trigger found"
            );
        } else {
            panic!("Expected Forall term");
        }
    }

    // ====== infer_triggers edge cases ======

    #[test]
    fn test_infer_triggers_empty_bound_vars() {
        // Body: f(x) > 0 but no bound vars -> any App covers "all" (vacuously)
        let body = Term::BvSGt(
            Box::new(Term::App(
                "f".to_string(),
                vec![Term::Const("x".to_string())],
            )),
            Box::new(Term::IntLit(0)),
        );
        let triggers = infer_triggers(&body, &[]);
        // Empty bound vars: subset check is vacuously true, so trigger found
        assert_eq!(triggers.len(), 1);
    }

    #[test]
    fn test_infer_triggers_app_missing_bound_var() {
        // Body: f(x) > 0, bound vars = [x, y]
        // f(x) only covers x, not y -> no single trigger
        let body = Term::BvSGt(
            Box::new(Term::App(
                "f".to_string(),
                vec![Term::Const("x".to_string())],
            )),
            Box::new(Term::IntLit(0)),
        );
        let triggers = infer_triggers(&body, &["x".to_string(), "y".to_string()]);
        assert!(triggers.is_empty(), "f(x) does not cover bound var y");
    }

    #[test]
    fn test_infer_triggers_multiple_apps_picks_first_covering() {
        // Body: f(x, y) && g(x)
        // f(x, y) covers both x and y, g(x) only covers x
        // Should pick f(x, y) as the trigger
        let body = Term::And(vec![
            Term::App(
                "f".to_string(),
                vec![Term::Const("x".to_string()), Term::Const("y".to_string())],
            ),
            Term::App("g".to_string(), vec![Term::Const("x".to_string())]),
        ]);
        let triggers = infer_triggers(&body, &["x".to_string(), "y".to_string()]);
        assert_eq!(triggers.len(), 1);
        if let Term::App(name, _) = &triggers[0][0] {
            assert_eq!(name, "f");
        } else {
            panic!("Expected App trigger");
        }
    }

    #[test]
    fn test_infer_triggers_nested_app_in_implies() {
        // Body: (implies (f(x) > 0) (g(x) = 1))
        // bound vars = [x]. Both f(x) and g(x) cover x. Should pick f(x) (first).
        let body = Term::Implies(
            Box::new(Term::BvSGt(
                Box::new(Term::App(
                    "f".to_string(),
                    vec![Term::Const("x".to_string())],
                )),
                Box::new(Term::IntLit(0)),
            )),
            Box::new(Term::Eq(
                Box::new(Term::App(
                    "g".to_string(),
                    vec![Term::Const("x".to_string())],
                )),
                Box::new(Term::IntLit(1)),
            )),
        );
        let triggers = infer_triggers(&body, &["x".to_string()]);
        assert_eq!(triggers.len(), 1);
        if let Term::App(name, _) = &triggers[0][0] {
            assert_eq!(name, "f");
        } else {
            panic!("Expected App trigger");
        }
    }

    #[test]
    fn test_infer_triggers_zero_arg_app_not_trigger() {
        // Body with zero-arg App: zero-arg apps are filtered out by collect_trigger_candidates
        let body = Term::And(vec![
            Term::App("zero_arg".to_string(), vec![]),
            Term::Const("x".to_string()),
        ]);
        let triggers = infer_triggers(&body, &["x".to_string()]);
        assert!(triggers.is_empty(), "Zero-arg apps should not be triggers");
    }

    // ====== annotate_quantifier with Exists ======

    #[test]
    fn test_annotate_exists_with_trigger() {
        // exists x. f(x) > 0
        let body = Term::BvSGt(
            Box::new(Term::App(
                "f".to_string(),
                vec![Term::Const("x".to_string())],
            )),
            Box::new(Term::IntLit(0)),
        );
        let exists_term = Term::Exists(vec![("x".to_string(), Sort::Int)], Box::new(body));

        let annotated = annotate_quantifier(exists_term);

        if let Term::Exists(_vars, body) = annotated {
            if let Term::Annotated(_, annotations) = &*body {
                assert_eq!(annotations.len(), 1);
                assert_eq!(annotations[0].0, "pattern");
                assert!(!annotations[0].1.is_empty());
            } else {
                panic!("Expected Annotated body for Exists");
            }
        } else {
            panic!("Expected Exists term");
        }
    }

    #[test]
    fn test_annotate_exists_no_trigger() {
        // exists x. x > 0 (no function app)
        let body = Term::BvSGt(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::IntLit(0)),
        );
        let exists_term = Term::Exists(vec![("x".to_string(), Sort::Int)], Box::new(body));

        let annotated = annotate_quantifier(exists_term);

        if let Term::Exists(_vars, result_body) = annotated {
            assert!(
                !matches!(&*result_body, Term::Annotated(_, _)),
                "Exists body should not be annotated when no trigger found"
            );
        } else {
            panic!("Expected Exists term");
        }
    }

    // ====== annotate_quantifier non-quantifier passthrough ======

    #[test]
    fn test_annotate_non_quantifier_passthrough() {
        let term = Term::BoolLit(true);
        let result = annotate_quantifier(term.clone());
        // Should return as-is
        assert!(matches!(result, Term::BoolLit(true)));
    }

    #[test]
    fn test_annotate_const_passthrough() {
        let term = Term::Const("x".to_string());
        let result = annotate_quantifier(term);
        assert!(matches!(result, Term::Const(_)));
    }

    // ====== collect_trigger_candidates for various Term types ======

    #[test]
    fn test_candidates_from_ite() {
        // ite(true, f(x), g(y))
        let term = Term::Ite(
            Box::new(Term::BoolLit(true)),
            Box::new(Term::App(
                "f".to_string(),
                vec![Term::Const("x".to_string())],
            )),
            Box::new(Term::App(
                "g".to_string(),
                vec![Term::Const("y".to_string())],
            )),
        );
        let candidates = find_trigger_candidates(&term);
        assert_eq!(candidates.len(), 2);
    }

    #[test]
    fn test_candidates_from_not() {
        let term = Term::Not(Box::new(Term::App(
            "pred".to_string(),
            vec![Term::Const("x".to_string())],
        )));
        let candidates = find_trigger_candidates(&term);
        assert_eq!(candidates.len(), 1);
    }

    #[test]
    fn test_candidates_from_let_binding() {
        // let y = f(x) in g(y)
        let term = Term::Let(
            vec![(
                "y".to_string(),
                Term::App("f".to_string(), vec![Term::Const("x".to_string())]),
            )],
            Box::new(Term::App(
                "g".to_string(),
                vec![Term::Const("y".to_string())],
            )),
        );
        let candidates = find_trigger_candidates(&term);
        assert_eq!(candidates.len(), 2); // f(x) and g(y)
    }

    #[test]
    fn test_candidates_from_nested_quantifier() {
        // Nested forall: forall y. h(y)
        let term = Term::Forall(
            vec![("y".to_string(), Sort::Int)],
            Box::new(Term::App(
                "h".to_string(),
                vec![Term::Const("y".to_string())],
            )),
        );
        let candidates = find_trigger_candidates(&term);
        assert_eq!(candidates.len(), 1);
        if let Term::App(name, _) = &candidates[0] {
            assert_eq!(name, "h");
        } else {
            panic!("Expected App candidate");
        }
    }

    #[test]
    fn test_candidates_from_annotated() {
        let term = Term::Annotated(
            Box::new(Term::App(
                "f".to_string(),
                vec![Term::Const("x".to_string())],
            )),
            vec![("pattern".to_string(), vec![])],
        );
        let candidates = find_trigger_candidates(&term);
        assert_eq!(candidates.len(), 1);
    }

    #[test]
    fn test_candidates_literals_produce_none() {
        let term = Term::And(vec![
            Term::BoolLit(true),
            Term::IntLit(42),
            Term::BitVecLit(0, 32),
            Term::Const("x".to_string()),
        ]);
        let candidates = find_trigger_candidates(&term);
        assert!(candidates.is_empty());
    }

    #[test]
    fn test_candidates_nested_app_in_app() {
        // f(g(x)): should produce both f(g(x)) and g(x)
        let term = Term::App(
            "f".to_string(),
            vec![Term::App(
                "g".to_string(),
                vec![Term::Const("x".to_string())],
            )],
        );
        let candidates = find_trigger_candidates(&term);
        assert_eq!(candidates.len(), 2);
    }

    // ====== free_variables additional tests ======

    #[test]
    fn test_free_variables_ite() {
        let term = Term::Ite(
            Box::new(Term::Const("c".to_string())),
            Box::new(Term::Const("a".to_string())),
            Box::new(Term::Const("b".to_string())),
        );
        let vars = free_variables(&term);
        assert_eq!(vars.len(), 3);
        assert!(vars.contains("a"));
        assert!(vars.contains("b"));
        assert!(vars.contains("c"));
    }

    #[test]
    fn test_free_variables_let() {
        let term = Term::Let(
            vec![("y".to_string(), Term::Const("x".to_string()))],
            Box::new(Term::Const("y".to_string())),
        );
        let vars = free_variables(&term);
        assert!(vars.contains("x"));
        assert!(vars.contains("y"));
    }

    #[test]
    fn test_free_variables_app() {
        let term = Term::App(
            "f".to_string(),
            vec![Term::Const("a".to_string()), Term::Const("b".to_string())],
        );
        let vars = free_variables(&term);
        assert_eq!(vars.len(), 2);
        assert!(vars.contains("a"));
        assert!(vars.contains("b"));
    }

    #[test]
    fn test_free_variables_literals_have_none() {
        let term = Term::And(vec![
            Term::BoolLit(false),
            Term::IntLit(42),
            Term::BitVecLit(7, 8),
        ]);
        let vars = free_variables(&term);
        assert!(vars.is_empty());
    }

    #[test]
    fn test_free_variables_annotated() {
        let term = Term::Annotated(
            Box::new(Term::Const("z".to_string())),
            vec![("note".to_string(), vec![])],
        );
        let vars = free_variables(&term);
        assert_eq!(vars.len(), 1);
        assert!(vars.contains("z"));
    }

    #[test]
    fn test_free_variables_bvneg() {
        let term = Term::BvNeg(Box::new(Term::Const("x".to_string())));
        let vars = free_variables(&term);
        assert_eq!(vars.len(), 1);
        assert!(vars.contains("x"));
    }

    #[test]
    fn test_free_variables_distinct() {
        let term = Term::Distinct(vec![
            Term::Const("a".to_string()),
            Term::Const("b".to_string()),
            Term::Const("c".to_string()),
        ]);
        let vars = free_variables(&term);
        assert_eq!(vars.len(), 3);
    }
}
