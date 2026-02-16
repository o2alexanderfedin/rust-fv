//! Trigger validation for user-provided quantifier trigger patterns.
//!
//! Validates that user-specified triggers are safe and effective:
//! - No interpreted symbols (arithmetic, equality, array ops)
//! - No self-instantiation loops
//! - Complete variable coverage
//! - Reasonable trigger set count
//!
//! Produces rich error variants that carry context for Rustc-style diagnostics.

use std::collections::HashSet;

use rust_fv_smtlib::sort::Sort;
use rust_fv_smtlib::term::Term;

use crate::encode_quantifier::{free_variables, infer_triggers};

/// Errors detected during trigger validation.
#[derive(Debug, Clone)]
pub enum TriggerValidationError {
    /// Trigger contains an interpreted symbol (arithmetic, equality, array ops).
    InterpretedSymbol {
        trigger: Term,
        symbol: String,
        auto_inferred: Vec<Vec<Term>>,
    },
    /// Trigger causes a self-instantiation loop.
    SelfInstantiation { trigger: Term, loop_example: String },
    /// Trigger set does not cover all bound variables.
    IncompleteCoverage {
        trigger: Term,
        missing_vars: Vec<String>,
    },
    /// Too many trigger sets provided.
    TooManyTriggers { count: usize, limit: usize },
}

/// Validates user-provided trigger patterns for quantifiers.
pub struct TriggerValidator {
    /// Maximum number of trigger sets allowed.
    pub max_trigger_sets: usize,
}

impl Default for TriggerValidator {
    fn default() -> Self {
        Self {
            max_trigger_sets: 10,
        }
    }
}

impl TriggerValidator {
    /// Create a new TriggerValidator with the given maximum trigger set count.
    pub fn new(max_trigger_sets: usize) -> Self {
        Self { max_trigger_sets }
    }

    /// Validate trigger sets for a quantifier.
    ///
    /// Checks:
    /// 1. Trigger count does not exceed limit
    /// 2. No interpreted symbols in triggers
    /// 3. No self-instantiation loops
    /// 4. All bound variables are covered by each trigger set
    pub fn validate(
        &self,
        trigger_sets: &[Vec<Term>],
        bound_vars: &[(String, Sort)],
        body: &Term,
    ) -> Result<(), TriggerValidationError> {
        // Check trigger count limit
        if trigger_sets.len() > self.max_trigger_sets {
            return Err(TriggerValidationError::TooManyTriggers {
                count: trigger_sets.len(),
                limit: self.max_trigger_sets,
            });
        }

        let var_names: Vec<String> = bound_vars.iter().map(|(n, _)| n.clone()).collect();

        for trigger_set in trigger_sets {
            for trigger in trigger_set {
                // Check for interpreted symbols
                if let Some(symbol) = find_interpreted_symbol(trigger) {
                    let auto_inferred = infer_triggers(body, &var_names);
                    return Err(TriggerValidationError::InterpretedSymbol {
                        trigger: trigger.clone(),
                        symbol,
                        auto_inferred,
                    });
                }

                // Check for self-instantiation
                if detect_self_instantiation(trigger, bound_vars) {
                    let loop_example = demonstrate_loop(trigger, bound_vars);
                    return Err(TriggerValidationError::SelfInstantiation {
                        trigger: trigger.clone(),
                        loop_example,
                    });
                }
            }

            // Check variable coverage for this trigger set
            let mut covered_vars = HashSet::new();
            for trigger in trigger_set {
                let vars = free_variables(trigger);
                for v in &vars {
                    covered_vars.insert(v.clone());
                }
            }

            let bound_set: HashSet<String> = var_names.iter().cloned().collect();
            let missing: Vec<String> = bound_set.difference(&covered_vars).cloned().collect();

            if !missing.is_empty() {
                return Err(TriggerValidationError::IncompleteCoverage {
                    trigger: trigger_set.first().cloned().unwrap_or(Term::BoolLit(true)),
                    missing_vars: missing,
                });
            }
        }

        Ok(())
    }
}

/// Check if a term is or contains an interpreted symbol that makes it
/// unsuitable as a trigger.
///
/// Returns `Some(symbol_name)` if an interpreted symbol is found, `None` otherwise.
///
/// The top-level trigger must be a function application (Term::App). If the
/// trigger itself IS an arithmetic op, that is an interpreted symbol error.
/// For Term::App, we recurse into arguments only.
pub fn find_interpreted_symbol(term: &Term) -> Option<String> {
    match term {
        // Uninterpreted function application - OK at top level, check args
        Term::App(_, args) => {
            for arg in args {
                if let Some(sym) = find_interpreted_symbol(arg) {
                    return Some(sym);
                }
            }
            None
        }

        // Constants and literals are fine
        Term::Const(_) | Term::BoolLit(_) | Term::IntLit(_) | Term::BitVecLit(_, _) => None,

        // Bitvector arithmetic - interpreted
        Term::BvAdd(_, _) => Some("+".to_string()),
        Term::BvSub(_, _) => Some("-".to_string()),
        Term::BvMul(_, _) => Some("*".to_string()),
        Term::BvSDiv(_, _) => Some("/ (signed)".to_string()),
        Term::BvUDiv(_, _) => Some("/ (unsigned)".to_string()),

        // Integer arithmetic - interpreted
        Term::IntAdd(_, _) => Some("+ (int)".to_string()),
        Term::IntSub(_, _) => Some("- (int)".to_string()),
        Term::IntMul(_, _) => Some("* (int)".to_string()),
        Term::IntDiv(_, _) => Some("/ (int)".to_string()),

        // Equality - interpreted
        Term::Eq(_, _) => Some("==".to_string()),

        // Bitvector comparisons - interpreted
        Term::BvSLt(_, _) => Some("< (signed)".to_string()),
        Term::BvSLe(_, _) => Some("<= (signed)".to_string()),
        Term::BvSGt(_, _) => Some("> (signed)".to_string()),
        Term::BvSGe(_, _) => Some(">= (signed)".to_string()),
        Term::BvULt(_, _) => Some("< (unsigned)".to_string()),
        Term::BvULe(_, _) => Some("<= (unsigned)".to_string()),
        Term::BvUGt(_, _) => Some("> (unsigned)".to_string()),
        Term::BvUGe(_, _) => Some(">= (unsigned)".to_string()),

        // Integer comparisons - interpreted
        Term::IntLt(_, _) => Some("< (int)".to_string()),
        Term::IntLe(_, _) => Some("<= (int)".to_string()),
        Term::IntGt(_, _) => Some("> (int)".to_string()),
        Term::IntGe(_, _) => Some(">= (int)".to_string()),

        // Array operations - interpreted
        Term::Select(_, _) => Some("select (array theory)".to_string()),
        Term::Store(_, _, _) => Some("store (array theory)".to_string()),

        // Everything else is treated as interpreted if used as a trigger
        _ => Some("(other interpreted operation)".to_string()),
    }
}

/// Detect if a trigger pattern would cause self-instantiation.
///
/// A trigger self-instantiates when the outer function name appears
/// recursively within its own arguments (e.g., `f(f(x))`). This means
/// that instantiating the quantifier produces new ground terms that
/// match the trigger again, creating an infinite chain.
///
/// Conservative: may flag false positives, must not miss real loops.
pub fn detect_self_instantiation(trigger: &Term, _bound_vars: &[(String, Sort)]) -> bool {
    match trigger {
        Term::App(outer_name, args) => {
            // Check if any argument (recursively) contains an App with the same name
            // This is the classic self-instantiation pattern: f(...f(...)...)
            args.iter()
                .any(|arg| contains_app_with_name(arg, outer_name))
        }
        _ => false,
    }
}

/// Demonstrate an instantiation loop for a self-instantiating trigger.
///
/// Shows 3 steps of the loop as a string.
pub fn demonstrate_loop(trigger: &Term, bound_vars: &[(String, Sort)]) -> String {
    let step0 = format_term_compact(trigger);
    let step1_term = substitute_one_step(trigger, bound_vars);
    let step1 = format_term_compact(&step1_term);
    let step2_term = substitute_one_step(&step1_term, bound_vars);
    let step2 = format_term_compact(&step2_term);

    format!("{} -> {} -> {} -> ...", step0, step1, step2)
}

/// Format a term compactly in SMT-LIB-like notation.
pub fn format_term_compact(term: &Term) -> String {
    match term {
        Term::Const(name) => name.clone(),
        Term::App(name, args) => {
            if args.is_empty() {
                name.clone()
            } else {
                let arg_strs: Vec<String> = args.iter().map(format_term_compact).collect();
                format!("({}({}))", name, arg_strs.join(", "))
            }
        }
        Term::BvAdd(a, b) => format!(
            "(bvadd {} {})",
            format_term_compact(a),
            format_term_compact(b)
        ),
        Term::IntAdd(a, b) => format!("(+ {} {})", format_term_compact(a), format_term_compact(b)),
        Term::Eq(a, b) => format!("(= {} {})", format_term_compact(a), format_term_compact(b)),
        Term::Select(a, b) => format!(
            "(select {} {})",
            format_term_compact(a),
            format_term_compact(b)
        ),
        Term::IntLit(n) => n.to_string(),
        Term::BoolLit(b) => b.to_string(),
        Term::BitVecLit(v, w) => format!("(_ bv{} {})", v, w),
        _ => format!("{:?}", term),
    }
}

/// Format trigger sets compactly for display in diagnostic messages.
pub fn format_trigger_sets(sets: &[Vec<Term>]) -> String {
    let set_strs: Vec<String> = sets
        .iter()
        .map(|set| {
            let terms: Vec<String> = set.iter().map(format_term_compact).collect();
            format!("{{ {} }}", terms.join(", "))
        })
        .collect();
    set_strs.join("; ")
}

// --- Helper functions ---

/// Check if a term contains an App node with the given function name.
fn contains_app_with_name(term: &Term, name: &str) -> bool {
    match term {
        Term::App(n, args) => n == name || args.iter().any(|a| contains_app_with_name(a, name)),
        _ => false,
    }
}

/// One step of substitution for demonstrating loops.
/// Replaces each bound variable `x` with `f(x)` where f is the innermost
/// function wrapping a bound variable in the trigger.
fn substitute_one_step(term: &Term, bound_vars: &[(String, Sort)]) -> Term {
    let var_names: HashSet<&str> = bound_vars.iter().map(|(n, _)| n.as_str()).collect();

    // Get the innermost function wrapping a bound variable
    let outer_fn = match term {
        Term::App(_, args) => find_innermost_wrapping_fn(args, &var_names),
        _ => None,
    };

    substitute_one_step_inner(term, &var_names, outer_fn.as_deref())
}

fn find_innermost_wrapping_fn(args: &[Term], var_names: &HashSet<&str>) -> Option<String> {
    for arg in args {
        if let Term::App(name, inner_args) = arg {
            // Check if this app directly wraps a bound variable
            if inner_args.len() == 1
                && let Term::Const(v) = &inner_args[0]
                && var_names.contains(v.as_str())
            {
                return Some(name.clone());
            }
            // Recurse
            if let Some(found) = find_innermost_wrapping_fn(inner_args, var_names) {
                return Some(found);
            }
        }
    }
    None
}

fn substitute_one_step_inner(
    term: &Term,
    var_names: &HashSet<&str>,
    wrap_fn: Option<&str>,
) -> Term {
    match term {
        Term::Const(name) if var_names.contains(name.as_str()) => {
            if let Some(f) = wrap_fn {
                Term::App(f.to_string(), vec![Term::Const(name.clone())])
            } else {
                Term::App(format!("sym_{}", name), vec![Term::Const(name.clone())])
            }
        }
        Term::App(name, args) => {
            let new_args: Vec<Term> = args
                .iter()
                .map(|a| substitute_one_step_inner(a, var_names, wrap_fn))
                .collect();
            Term::App(name.clone(), new_args)
        }
        other => other.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ====== Interpreted symbols ======

    #[test]
    fn test_interpreted_symbol_bvadd() {
        let term = Term::BvAdd(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::Const("y".to_string())),
        );
        assert_eq!(find_interpreted_symbol(&term), Some("+".to_string()));
    }

    #[test]
    fn test_interpreted_symbol_eq() {
        let term = Term::Eq(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::Const("y".to_string())),
        );
        assert_eq!(find_interpreted_symbol(&term), Some("==".to_string()));
    }

    #[test]
    fn test_interpreted_symbol_intadd() {
        let term = Term::IntAdd(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::Const("y".to_string())),
        );
        assert_eq!(find_interpreted_symbol(&term), Some("+ (int)".to_string()));
    }

    #[test]
    fn test_interpreted_symbol_bvslt() {
        let term = Term::BvSLt(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::Const("y".to_string())),
        );
        assert_eq!(
            find_interpreted_symbol(&term),
            Some("< (signed)".to_string())
        );
    }

    #[test]
    fn test_interpreted_symbol_bvsle() {
        assert_eq!(
            find_interpreted_symbol(&Term::BvSLe(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::Const("y".to_string())),
            )),
            Some("<= (signed)".to_string())
        );
    }

    #[test]
    fn test_interpreted_symbol_bvsgt() {
        assert_eq!(
            find_interpreted_symbol(&Term::BvSGt(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::Const("y".to_string())),
            )),
            Some("> (signed)".to_string())
        );
    }

    #[test]
    fn test_interpreted_symbol_bvsge() {
        assert_eq!(
            find_interpreted_symbol(&Term::BvSGe(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::Const("y".to_string())),
            )),
            Some(">= (signed)".to_string())
        );
    }

    #[test]
    fn test_interpreted_symbol_bvult() {
        assert_eq!(
            find_interpreted_symbol(&Term::BvULt(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::Const("y".to_string())),
            )),
            Some("< (unsigned)".to_string())
        );
    }

    #[test]
    fn test_interpreted_symbol_bvule() {
        assert_eq!(
            find_interpreted_symbol(&Term::BvULe(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::Const("y".to_string())),
            )),
            Some("<= (unsigned)".to_string())
        );
    }

    #[test]
    fn test_interpreted_symbol_bvugt() {
        assert_eq!(
            find_interpreted_symbol(&Term::BvUGt(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::Const("y".to_string())),
            )),
            Some("> (unsigned)".to_string())
        );
    }

    #[test]
    fn test_interpreted_symbol_bvuge() {
        assert_eq!(
            find_interpreted_symbol(&Term::BvUGe(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::Const("y".to_string())),
            )),
            Some(">= (unsigned)".to_string())
        );
    }

    #[test]
    fn test_interpreted_symbol_select() {
        assert_eq!(
            find_interpreted_symbol(&Term::Select(
                Box::new(Term::Const("a".to_string())),
                Box::new(Term::Const("i".to_string())),
            )),
            Some("select (array theory)".to_string())
        );
    }

    #[test]
    fn test_interpreted_symbol_store() {
        assert_eq!(
            find_interpreted_symbol(&Term::Store(
                Box::new(Term::Const("a".to_string())),
                Box::new(Term::Const("i".to_string())),
                Box::new(Term::Const("v".to_string())),
            )),
            Some("store (array theory)".to_string())
        );
    }

    #[test]
    fn test_interpreted_symbol_app_clean() {
        let term = Term::App("f".to_string(), vec![Term::Const("x".to_string())]);
        assert_eq!(find_interpreted_symbol(&term), None);
    }

    #[test]
    fn test_interpreted_symbol_app_dirty_arg() {
        let term = Term::App(
            "f".to_string(),
            vec![Term::BvAdd(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::Const("y".to_string())),
            )],
        );
        assert_eq!(find_interpreted_symbol(&term), Some("+".to_string()));
    }

    #[test]
    fn test_interpreted_symbol_const() {
        assert_eq!(find_interpreted_symbol(&Term::Const("x".to_string())), None);
    }

    #[test]
    fn test_interpreted_symbol_literal() {
        assert_eq!(find_interpreted_symbol(&Term::IntLit(42)), None);
    }

    #[test]
    fn test_interpreted_symbol_bvsub() {
        assert_eq!(
            find_interpreted_symbol(&Term::BvSub(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::Const("y".to_string())),
            )),
            Some("-".to_string())
        );
    }

    #[test]
    fn test_interpreted_symbol_bvmul() {
        assert_eq!(
            find_interpreted_symbol(&Term::BvMul(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::Const("y".to_string())),
            )),
            Some("*".to_string())
        );
    }

    #[test]
    fn test_interpreted_symbol_bvsdiv() {
        assert_eq!(
            find_interpreted_symbol(&Term::BvSDiv(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::Const("y".to_string())),
            )),
            Some("/ (signed)".to_string())
        );
    }

    #[test]
    fn test_interpreted_symbol_bvudiv() {
        assert_eq!(
            find_interpreted_symbol(&Term::BvUDiv(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::Const("y".to_string())),
            )),
            Some("/ (unsigned)".to_string())
        );
    }

    #[test]
    fn test_interpreted_symbol_intsub() {
        assert_eq!(
            find_interpreted_symbol(&Term::IntSub(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::Const("y".to_string())),
            )),
            Some("- (int)".to_string())
        );
    }

    #[test]
    fn test_interpreted_symbol_intmul() {
        assert_eq!(
            find_interpreted_symbol(&Term::IntMul(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::Const("y".to_string())),
            )),
            Some("* (int)".to_string())
        );
    }

    #[test]
    fn test_interpreted_symbol_intdiv() {
        assert_eq!(
            find_interpreted_symbol(&Term::IntDiv(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::Const("y".to_string())),
            )),
            Some("/ (int)".to_string())
        );
    }

    #[test]
    fn test_interpreted_symbol_intlt() {
        assert_eq!(
            find_interpreted_symbol(&Term::IntLt(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::Const("y".to_string())),
            )),
            Some("< (int)".to_string())
        );
    }

    #[test]
    fn test_interpreted_symbol_intle() {
        assert_eq!(
            find_interpreted_symbol(&Term::IntLe(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::Const("y".to_string())),
            )),
            Some("<= (int)".to_string())
        );
    }

    #[test]
    fn test_interpreted_symbol_intgt() {
        assert_eq!(
            find_interpreted_symbol(&Term::IntGt(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::Const("y".to_string())),
            )),
            Some("> (int)".to_string())
        );
    }

    #[test]
    fn test_interpreted_symbol_intge() {
        assert_eq!(
            find_interpreted_symbol(&Term::IntGe(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::Const("y".to_string())),
            )),
            Some(">= (int)".to_string())
        );
    }

    #[test]
    fn test_interpreted_symbol_bool_lit() {
        assert_eq!(find_interpreted_symbol(&Term::BoolLit(true)), None);
    }

    #[test]
    fn test_interpreted_symbol_bitvec_lit() {
        assert_eq!(find_interpreted_symbol(&Term::BitVecLit(42, 32)), None);
    }

    // ====== Self-instantiation ======

    #[test]
    fn test_self_instantiation_simple_app() {
        // f(x) with bound var x: no self-instantiation
        let trigger = Term::App("f".to_string(), vec![Term::Const("x".to_string())]);
        let bound_vars = vec![("x".to_string(), Sort::Int)];
        assert!(!detect_self_instantiation(&trigger, &bound_vars));
    }

    #[test]
    fn test_self_instantiation_nested_safe() {
        // f(g(x)) with bound var x: g doesn't produce f-shaped terms
        let trigger = Term::App(
            "f".to_string(),
            vec![Term::App(
                "g".to_string(),
                vec![Term::Const("x".to_string())],
            )],
        );
        let bound_vars = vec![("x".to_string(), Sort::Int)];
        assert!(!detect_self_instantiation(&trigger, &bound_vars));
    }

    #[test]
    fn test_self_instantiation_loop() {
        // f(f(x)) with bound var x: f appears in its own args -> self-instantiation
        let trigger = Term::App(
            "f".to_string(),
            vec![Term::App(
                "f".to_string(),
                vec![Term::Const("x".to_string())],
            )],
        );
        let bound_vars = vec![("x".to_string(), Sort::Int)];
        assert!(detect_self_instantiation(&trigger, &bound_vars));
    }

    #[test]
    fn test_demonstrate_loop_produces_string() {
        let trigger = Term::App(
            "f".to_string(),
            vec![Term::App(
                "f".to_string(),
                vec![Term::Const("x".to_string())],
            )],
        );
        let bound_vars = vec![("x".to_string(), Sort::Int)];
        let demo = demonstrate_loop(&trigger, &bound_vars);
        assert!(demo.contains("->"));
        assert!(demo.contains("..."));
    }

    // ====== Coverage ======

    #[test]
    fn test_coverage_complete() {
        let validator = TriggerValidator::default();
        let trigger_sets = vec![vec![Term::App(
            "f".to_string(),
            vec![Term::Const("x".to_string()), Term::Const("y".to_string())],
        )]];
        let bound_vars = vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)];
        let body = Term::BoolLit(true);
        assert!(
            validator
                .validate(&trigger_sets, &bound_vars, &body)
                .is_ok()
        );
    }

    #[test]
    fn test_coverage_incomplete() {
        let validator = TriggerValidator::default();
        let trigger_sets = vec![vec![Term::App(
            "f".to_string(),
            vec![Term::Const("x".to_string())],
        )]];
        let bound_vars = vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)];
        let body = Term::BoolLit(true);
        let result = validator.validate(&trigger_sets, &bound_vars, &body);
        assert!(result.is_err());
        if let Err(TriggerValidationError::IncompleteCoverage { missing_vars, .. }) = result {
            assert!(missing_vars.contains(&"y".to_string()));
        } else {
            panic!("Expected IncompleteCoverage error");
        }
    }

    #[test]
    fn test_coverage_multi_trigger_set() {
        let validator = TriggerValidator::default();
        let trigger_sets = vec![vec![
            Term::App("f".to_string(), vec![Term::Const("x".to_string())]),
            Term::App("g".to_string(), vec![Term::Const("y".to_string())]),
        ]];
        let bound_vars = vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)];
        let body = Term::BoolLit(true);
        assert!(
            validator
                .validate(&trigger_sets, &bound_vars, &body)
                .is_ok()
        );
    }

    // ====== Trigger limit ======

    #[test]
    fn test_too_many_triggers() {
        let validator = TriggerValidator::default();
        let trigger_sets: Vec<Vec<Term>> = (0..11)
            .map(|_| {
                vec![Term::App(
                    "f".to_string(),
                    vec![Term::Const("x".to_string())],
                )]
            })
            .collect();
        let bound_vars = vec![("x".to_string(), Sort::Int)];
        let body = Term::BoolLit(true);
        let result = validator.validate(&trigger_sets, &bound_vars, &body);
        assert!(result.is_err());
        if let Err(TriggerValidationError::TooManyTriggers { count, limit }) = result {
            assert_eq!(count, 11);
            assert_eq!(limit, 10);
        } else {
            panic!("Expected TooManyTriggers error");
        }
    }

    #[test]
    fn test_within_limit() {
        let validator = TriggerValidator::default();
        let trigger_sets: Vec<Vec<Term>> = (0..10)
            .map(|_| {
                vec![Term::App(
                    "f".to_string(),
                    vec![Term::Const("x".to_string())],
                )]
            })
            .collect();
        let bound_vars = vec![("x".to_string(), Sort::Int)];
        let body = Term::BoolLit(true);
        assert!(
            validator
                .validate(&trigger_sets, &bound_vars, &body)
                .is_ok()
        );
    }

    // ====== Integration tests ======

    #[test]
    fn test_validate_valid_trigger() {
        let validator = TriggerValidator::default();
        let trigger_sets = vec![vec![Term::App(
            "f".to_string(),
            vec![Term::Const("x".to_string())],
        )]];
        let bound_vars = vec![("x".to_string(), Sort::Int)];
        let body = Term::App("f".to_string(), vec![Term::Const("x".to_string())]);
        assert!(
            validator
                .validate(&trigger_sets, &bound_vars, &body)
                .is_ok()
        );
    }

    #[test]
    fn test_validate_interpreted_with_suggestion() {
        let validator = TriggerValidator::default();
        let trigger_sets = vec![vec![Term::BvAdd(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::Const("y".to_string())),
        )]];
        let bound_vars = vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)];
        let body = Term::App(
            "f".to_string(),
            vec![Term::Const("x".to_string()), Term::Const("y".to_string())],
        );
        let result = validator.validate(&trigger_sets, &bound_vars, &body);
        assert!(result.is_err());
        if let Err(TriggerValidationError::InterpretedSymbol {
            symbol,
            auto_inferred,
            ..
        }) = result
        {
            assert_eq!(symbol, "+");
            assert!(!auto_inferred.is_empty());
        } else {
            panic!("Expected InterpretedSymbol error");
        }
    }

    // ====== Format helpers ======

    #[test]
    fn test_format_term_compact_app() {
        let term = Term::App("f".to_string(), vec![Term::Const("x".to_string())]);
        let formatted = format_term_compact(&term);
        assert!(formatted.contains("f"));
        assert!(formatted.contains("x"));
    }

    #[test]
    fn test_format_trigger_sets_display() {
        let sets = vec![
            vec![Term::App(
                "f".to_string(),
                vec![Term::Const("x".to_string())],
            )],
            vec![Term::App(
                "g".to_string(),
                vec![Term::Const("y".to_string())],
            )],
        ];
        let formatted = format_trigger_sets(&sets);
        assert!(formatted.contains("f"));
        assert!(formatted.contains("g"));
    }

    // ====== Validator constructor ======

    #[test]
    fn test_validator_default() {
        let v = TriggerValidator::default();
        assert_eq!(v.max_trigger_sets, 10);
    }

    #[test]
    fn test_validator_new() {
        let v = TriggerValidator::new(5);
        assert_eq!(v.max_trigger_sets, 5);
    }
}
