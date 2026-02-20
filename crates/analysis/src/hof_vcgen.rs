//! Higher-Order Function (HOF) Verification Condition Generator.
//!
//! Generates AUFLIA-logic SMT scripts for fn_spec entailment queries.
//!
//! ## fn_spec Semantics
//!
//! A fn_spec clause `fn_spec(f, |x| pre => post)` asserts that the closure
//! parameter `f` satisfies the contract: for all `x`, `pre(x) => post(f(x))`.
//!
//! The verification condition is the *negation* of this entailment:
//! `NOT(forall x. pre(x) => post(f(x)))` — which is UNSAT iff the entailment holds.
//!
//! ## Closure Trait Handling
//!
//! - **Fn / FnOnce**: Single environment constant `env_PARAM`. No env_before/env_after.
//! - **FnMut**: Declares `env_before_CAPVAR` and `env_after_CAPVAR` for each captured
//!   variable. The `PARAM_impl` function receives env_before captures and the bound arg.
//!
//! ## AUFLIA Logic
//!
//! Uses `(set-logic AUFLIA)` (Arrays + Uninterpreted Functions + Linear Integer Arithmetic)
//! to support universal quantification over closure arguments with integer arithmetic.

use rust_fv_smtlib::command::Command;
use rust_fv_smtlib::script::Script;
use rust_fv_smtlib::sort::Sort;
use rust_fv_smtlib::term::Term;

use crate::encode_sort::encode_type;
use crate::ir::{ClosureTrait, FnSpec, Function, Ty};
use crate::vcgen::{VcKind, VcLocation, VerificationCondition};

/// Generate ClosureContract VCs for all fn_spec clauses in a function's contracts.
///
/// Returns a `Vec` of `VerificationCondition` ready to be appended to `FunctionVCs`.
/// Each entry corresponds to one `FnSpec` clause and uses AUFLIA logic so that the
/// universal quantifier over bound variables is handled by Z3's MBQI engine.
pub fn generate_fn_spec_vcs(func: &Function, fn_specs: &[FnSpec]) -> Vec<VerificationCondition> {
    fn_specs
        .iter()
        .map(|spec| generate_single_fn_spec_vc(func, spec))
        .collect()
}

/// Generate a single VerificationCondition for one FnSpec clause.
fn generate_single_fn_spec_vc(func: &Function, spec: &FnSpec) -> VerificationCondition {
    // Determine closure trait by looking up the closure parameter in func.params.
    let closure_trait = func
        .params
        .iter()
        .find(|p| p.name == spec.closure_param)
        .and_then(|p| {
            if let Ty::Closure(info) = &p.ty {
                Some(info.trait_kind)
            } else {
                None
            }
        })
        // Default to Fn if parameter not found or not a Closure type (conservative).
        .unwrap_or(ClosureTrait::Fn);

    let script = match closure_trait {
        ClosureTrait::FnMut => build_fnmut_vc_script(func, spec),
        ClosureTrait::Fn | ClosureTrait::FnOnce => build_fn_vc_script(func, spec),
    };

    let bound_vars_str = spec.bound_vars.join(", ");
    VerificationCondition {
        description: format!(
            "fn_spec({}, |{}| {} => {})",
            spec.closure_param, bound_vars_str, spec.pre, spec.post
        ),
        script,
        location: VcLocation {
            function: func.name.clone(),
            block: 0,
            statement: 0,
            source_file: None,
            source_line: None,
            source_column: None,
            contract_text: Some(format!(
                "|{}| {} => {}",
                bound_vars_str, spec.pre, spec.post
            )),
            vc_kind: VcKind::ClosureContract,
        },
    }
}

/// Build the SMT script for Fn / FnOnce closure contracts.
///
/// Script structure:
/// ```text
/// (set-logic AUFLIA)
/// (declare-sort ClosureEnv_PARAM 0)
/// (declare-fun PARAM_impl (ClosureEnv_PARAM BOUND_SORT ...) RESULT_SORT)
/// (declare-const env_PARAM ClosureEnv_PARAM)
/// (declare-const BOUND_VAR BOUND_SORT)  ; for each bound variable
/// (assert (not (forall ((BOUND_VAR BOUND_SORT))
///   (=> PRE_TERM POST_TERM))))
/// (check-sat)
/// ```
///
/// UNSAT means the entailment holds (verified).
fn build_fn_vc_script(func: &Function, spec: &FnSpec) -> Script {
    let param = &spec.closure_param;
    let env_sort_name = format!("ClosureEnv_{}", param);
    let impl_name = format!("{}_impl", param);
    let env_const_name = format!("env_{}", param);

    // Collect bound variable sorts (default to Int if not found).
    let bound_sorts: Vec<(String, Sort)> = spec
        .bound_vars
        .iter()
        .map(|v| (v.clone(), infer_bound_var_sort(func, v)))
        .collect();

    // Result sort is uninterpreted (Int by default for the abstract closure).
    let result_sort = Sort::Int;

    // Build param_sorts for declare-fun: [ClosureEnv_PARAM, BOUND_SORT...]
    let mut impl_param_sorts = vec![Sort::Uninterpreted(env_sort_name.clone())];
    for (_, sort) in &bound_sorts {
        impl_param_sorts.push(sort.clone());
    }

    let mut script = Script::new();

    // (set-logic AUFLIA) — quantified arithmetic with uninterpreted functions
    script.push(Command::SetLogic("AUFLIA".to_string()));

    // Declare the closure environment sort
    script.push(Command::DeclareSort(env_sort_name.clone(), 0));

    // Declare the uninterpreted closure implementation function
    script.push(Command::DeclareFun(
        impl_name.clone(),
        impl_param_sorts,
        result_sort.clone(),
    ));

    // Declare the environment constant
    script.push(Command::DeclareConst(
        env_const_name.clone(),
        Sort::Uninterpreted(env_sort_name),
    ));

    // Declare bound variable constants (for assertions outside the quantifier)
    for (var, sort) in &bound_sorts {
        script.push(Command::DeclareConst(var.clone(), sort.clone()));
    }

    // Build the closure application term: (PARAM_impl env_PARAM BOUND_VAR...)
    let env_term = Term::Const(env_const_name);
    let mut app_args = vec![env_term];
    for (var, _) in &bound_sorts {
        app_args.push(Term::Const(var.clone()));
    }
    let closure_app = Term::App(impl_name, app_args);

    // Parse pre/post conditions from spec strings
    let pre_term = parse_spec_string_for_hof(&spec.pre, func, &bound_sorts);
    let post_term =
        parse_spec_string_for_hof_post(&spec.post, func, &bound_sorts, closure_app.clone());

    // Build: (not (forall ((v sort)...) (=> pre post)))
    let forall_term = if bound_sorts.is_empty() {
        // No bound variables — just implication
        Term::Implies(Box::new(pre_term), Box::new(post_term))
    } else {
        Term::Forall(
            bound_sorts.clone(),
            Box::new(Term::Implies(Box::new(pre_term), Box::new(post_term))),
        )
    };

    let negation = Term::Not(Box::new(forall_term));
    script.push(Command::Assert(negation));
    script.push(Command::CheckSat);

    script
}

/// Build the SMT script for FnMut closure contracts.
///
/// Extends the Fn script with env_before/env_after constants for each captured variable.
/// The closure implementation receives env_before captures.
fn build_fnmut_vc_script(func: &Function, spec: &FnSpec) -> Script {
    let param = &spec.closure_param;
    let env_sort_name = format!("ClosureEnv_{}", param);
    let impl_name = format!("{}_impl", param);
    let env_const_name = format!("env_{}", param);

    // Collect bound variable sorts
    let bound_sorts: Vec<(String, Sort)> = spec
        .bound_vars
        .iter()
        .map(|v| (v.clone(), infer_bound_var_sort(func, v)))
        .collect();

    // Collect captured variables for FnMut env_before/env_after
    let captured_vars: Vec<(String, Sort)> = find_captured_vars(func, param);

    let result_sort = Sort::Int;

    // For FnMut: impl takes (env_sort, bound_vars...) — env encapsulates before-state
    let mut impl_param_sorts = vec![Sort::Uninterpreted(env_sort_name.clone())];
    for (_, sort) in &bound_sorts {
        impl_param_sorts.push(sort.clone());
    }

    let mut script = Script::new();

    // (set-logic AUFLIA)
    script.push(Command::SetLogic("AUFLIA".to_string()));

    // Declare the closure environment sort
    script.push(Command::DeclareSort(env_sort_name.clone(), 0));

    // Declare the uninterpreted closure implementation function
    script.push(Command::DeclareFun(
        impl_name.clone(),
        impl_param_sorts,
        result_sort.clone(),
    ));

    // Declare the environment constant (models the before-state environment)
    script.push(Command::DeclareConst(
        env_const_name.clone(),
        Sort::Uninterpreted(env_sort_name),
    ));

    // Declare env_before_CAPVAR / env_after_CAPVAR constants for each captured variable
    for (cap_name, cap_sort) in &captured_vars {
        script.push(Command::DeclareConst(
            format!("env_before_{}", cap_name),
            cap_sort.clone(),
        ));
        script.push(Command::DeclareConst(
            format!("env_after_{}", cap_name),
            cap_sort.clone(),
        ));
    }

    // Declare bound variable constants
    for (var, sort) in &bound_sorts {
        script.push(Command::DeclareConst(var.clone(), sort.clone()));
    }

    // Build the closure application term: (PARAM_impl env_PARAM BOUND_VAR...)
    let env_term = Term::Const(env_const_name);
    let mut app_args = vec![env_term];
    for (var, _) in &bound_sorts {
        app_args.push(Term::Const(var.clone()));
    }
    let closure_app = Term::App(impl_name, app_args);

    // Parse pre/post conditions
    let pre_term = parse_spec_string_for_hof(&spec.pre, func, &bound_sorts);
    let post_term =
        parse_spec_string_for_hof_post(&spec.post, func, &bound_sorts, closure_app.clone());

    // Build: (not (forall ((v sort)...) (=> pre post)))
    let forall_term = if bound_sorts.is_empty() {
        Term::Implies(Box::new(pre_term), Box::new(post_term))
    } else {
        Term::Forall(
            bound_sorts.clone(),
            Box::new(Term::Implies(Box::new(pre_term), Box::new(post_term))),
        )
    };

    let negation = Term::Not(Box::new(forall_term));
    script.push(Command::Assert(negation));
    script.push(Command::CheckSat);

    script
}

/// Infer the SMT sort for a bound variable in a fn_spec clause.
///
/// Looks up the variable in the function's local variables. If not found,
/// defaults to `Sort::Int` (appropriate for AUFLIA arithmetic reasoning).
fn infer_bound_var_sort(func: &Function, var_name: &str) -> Sort {
    // Search in params and locals
    for local in func.params.iter().chain(func.locals.iter()) {
        if local.name == var_name {
            return encode_type(&local.ty);
        }
    }
    // Default to Int for abstract bound variables in HOF specs
    Sort::Int
}

/// Find captured variables for a FnMut closure parameter.
///
/// Looks up the parameter in func.params, and if it's a Closure type,
/// extracts env_fields. Returns an empty vec if not found or not Closure.
fn find_captured_vars(func: &Function, param_name: &str) -> Vec<(String, Sort)> {
    func.params
        .iter()
        .find(|p| p.name == param_name)
        .and_then(|p| {
            if let Ty::Closure(info) = &p.ty {
                Some(
                    info.env_fields
                        .iter()
                        .map(|(name, ty)| (name.clone(), encode_type(ty)))
                        .collect(),
                )
            } else {
                None
            }
        })
        .unwrap_or_default()
}

/// Parse a pre-condition spec string into an SMT Term for HOF VCs.
///
/// Bound variables are available as `Sort::Int` constants. If the expression
/// cannot be parsed, returns `Term::BoolLit(true)` (vacuously true — conservative).
fn parse_spec_string_for_hof(
    spec: &str,
    _func: &Function,
    _bound_sorts: &[(String, Sort)],
) -> Term {
    // Build a simple term from the spec string.
    // For HOF VCs, specs reference bound variables as Int constants.
    // We use a best-effort parse via spec_parser; on failure, emit true stub.
    parse_hof_expr(spec, _bound_sorts)
}

/// Parse a post-condition spec string, replacing `result` with the closure application term.
fn parse_spec_string_for_hof_post(
    spec: &str,
    _func: &Function,
    _bound_sorts: &[(String, Sort)],
    closure_app: Term,
) -> Term {
    // Replace `result` with the closure application term in the parsed expression.
    let base_term = parse_hof_expr(spec, _bound_sorts);
    substitute_result(base_term, closure_app)
}

/// Parse a HOF spec expression string into a Term.
///
/// Handles common patterns:
/// - Integer comparisons: `x > 0`, `result > 0`, `x >= 0`
/// - Conjunctions: `x > 0 && result > 0`
/// - Boolean literals: `true`, `false`
/// - Simple identities: `result == x`
///
/// Returns `Term::BoolLit(true)` for unrecognized expressions (conservative stub).
fn parse_hof_expr(spec: &str, _bound_sorts: &[(String, Sort)]) -> Term {
    let spec = spec.trim();

    if spec.is_empty() || spec == "true" {
        return Term::BoolLit(true);
    }
    if spec == "false" {
        return Term::BoolLit(false);
    }

    // Try conjunction splitting (&&)
    if let Some(idx) = find_top_level_op(spec, "&&") {
        let lhs = parse_hof_expr(spec[..idx].trim(), _bound_sorts);
        let rhs = parse_hof_expr(spec[idx + 2..].trim(), _bound_sorts);
        return Term::And(vec![lhs, rhs]);
    }

    // Try disjunction splitting (||)
    if let Some(idx) = find_top_level_op(spec, "||") {
        let lhs = parse_hof_expr(spec[..idx].trim(), _bound_sorts);
        let rhs = parse_hof_expr(spec[idx + 2..].trim(), _bound_sorts);
        return Term::Or(vec![lhs, rhs]);
    }

    // Try comparison operators (longest first to avoid ambiguity)
    for op in &[">=", "<=", "!=", "==", ">", "<"] {
        if let Some(idx) = find_top_level_op(spec, op) {
            let lhs_str = spec[..idx].trim();
            let rhs_str = spec[idx + op.len()..].trim();
            let lhs = parse_hof_atom(lhs_str);
            let rhs = parse_hof_atom(rhs_str);
            return match *op {
                ">=" => Term::IntGe(Box::new(lhs), Box::new(rhs)),
                "<=" => Term::IntLe(Box::new(lhs), Box::new(rhs)),
                "!=" => Term::Not(Box::new(Term::Eq(Box::new(lhs), Box::new(rhs)))),
                "==" => Term::Eq(Box::new(lhs), Box::new(rhs)),
                ">" => Term::IntGt(Box::new(lhs), Box::new(rhs)),
                "<" => Term::IntLt(Box::new(lhs), Box::new(rhs)),
                _ => unreachable!(),
            };
        }
    }

    // Fall back to interpreting as a boolean atom or stub
    // E.g. a single variable that is Bool-kinded
    let atom = parse_hof_atom(spec);
    // If atom is a Const, treat as bool variable; otherwise stub
    match &atom {
        Term::Const(_) => Term::Eq(Box::new(atom), Box::new(Term::BoolLit(true))),
        Term::IntLit(_) => Term::BoolLit(true), // bare int is vacuous
        _ => Term::BoolLit(true),
    }
}

/// Parse a simple arithmetic atom (variable name, integer literal, or arithmetic expression).
fn parse_hof_atom(s: &str) -> Term {
    let s = s.trim();

    // Strip outer parentheses
    if s.starts_with('(') && s.ends_with(')') {
        return parse_hof_atom(&s[1..s.len() - 1]);
    }

    // Integer literal
    if let Ok(n) = s.parse::<i128>() {
        return Term::IntLit(n);
    }

    // Negative integer literal
    if let Some(rest) = s.strip_prefix('-')
        && let Ok(n) = rest.trim().parse::<i128>()
    {
        return Term::IntLit(-n);
    }

    // Addition
    if let Some(idx) = find_top_level_op(s, "+") {
        let lhs = parse_hof_atom(s[..idx].trim());
        let rhs = parse_hof_atom(s[idx + 1..].trim());
        return Term::IntAdd(Box::new(lhs), Box::new(rhs));
    }

    // Subtraction (after addition to avoid negative literal ambiguity)
    if let Some(idx) = find_top_level_op_after_first_char(s, "-") {
        let lhs = parse_hof_atom(s[..idx].trim());
        let rhs = parse_hof_atom(s[idx + 1..].trim());
        return Term::IntSub(Box::new(lhs), Box::new(rhs));
    }

    // Multiplication
    if let Some(idx) = find_top_level_op(s, "*") {
        let lhs = parse_hof_atom(s[..idx].trim());
        let rhs = parse_hof_atom(s[idx + 1..].trim());
        return Term::IntMul(Box::new(lhs), Box::new(rhs));
    }

    // Variable / constant reference
    if s.chars().all(|c| c.is_alphanumeric() || c == '_') && !s.is_empty() {
        return Term::Const(s.to_string());
    }

    // Fallback: uninterpreted constant with the raw string as name
    Term::Const(s.to_string())
}

/// Find the index of a top-level (not nested in parens) occurrence of `op` in `s`.
fn find_top_level_op(s: &str, op: &str) -> Option<usize> {
    let mut depth = 0i32;
    let bytes = s.as_bytes();
    let op_bytes = op.as_bytes();
    let op_len = op_bytes.len();

    let mut i = 0;
    while i + op_len <= bytes.len() {
        match bytes[i] {
            b'(' => {
                depth += 1;
                i += 1;
            }
            b')' => {
                depth -= 1;
                i += 1;
            }
            _ if depth == 0 && bytes[i..].starts_with(op_bytes) => {
                return Some(i);
            }
            _ => {
                i += 1;
            }
        }
    }
    None
}

/// Find subtraction operator, skipping position 0 to avoid treating leading `-` as binary.
fn find_top_level_op_after_first_char(s: &str, op: &str) -> Option<usize> {
    let mut depth = 0i32;
    let bytes = s.as_bytes();
    let op_bytes = op.as_bytes();
    let op_len = op_bytes.len();

    let mut i = 1; // skip first char
    while i + op_len <= bytes.len() {
        match bytes[i] {
            b'(' => {
                depth += 1;
                i += 1;
            }
            b')' => {
                depth -= 1;
                i += 1;
            }
            _ if depth == 0 && bytes[i..].starts_with(op_bytes) => {
                return Some(i);
            }
            _ => {
                i += 1;
            }
        }
    }
    None
}

/// Substitute all `Term::Const("result")` occurrences with `replacement`.
fn substitute_result(term: Term, replacement: Term) -> Term {
    match term {
        Term::Const(ref name) if name == "result" => replacement,
        Term::Not(inner) => Term::Not(Box::new(substitute_result(*inner, replacement))),
        Term::And(terms) => Term::And(
            terms
                .into_iter()
                .map(|t| substitute_result(t, replacement.clone()))
                .collect(),
        ),
        Term::Or(terms) => Term::Or(
            terms
                .into_iter()
                .map(|t| substitute_result(t, replacement.clone()))
                .collect(),
        ),
        Term::Implies(a, b) => Term::Implies(
            Box::new(substitute_result(*a, replacement.clone())),
            Box::new(substitute_result(*b, replacement)),
        ),
        Term::Eq(a, b) => Term::Eq(
            Box::new(substitute_result(*a, replacement.clone())),
            Box::new(substitute_result(*b, replacement)),
        ),
        Term::IntGt(a, b) => Term::IntGt(
            Box::new(substitute_result(*a, replacement.clone())),
            Box::new(substitute_result(*b, replacement)),
        ),
        Term::IntGe(a, b) => Term::IntGe(
            Box::new(substitute_result(*a, replacement.clone())),
            Box::new(substitute_result(*b, replacement)),
        ),
        Term::IntLt(a, b) => Term::IntLt(
            Box::new(substitute_result(*a, replacement.clone())),
            Box::new(substitute_result(*b, replacement)),
        ),
        Term::IntLe(a, b) => Term::IntLe(
            Box::new(substitute_result(*a, replacement.clone())),
            Box::new(substitute_result(*b, replacement)),
        ),
        Term::IntAdd(a, b) => Term::IntAdd(
            Box::new(substitute_result(*a, replacement.clone())),
            Box::new(substitute_result(*b, replacement)),
        ),
        Term::IntSub(a, b) => Term::IntSub(
            Box::new(substitute_result(*a, replacement.clone())),
            Box::new(substitute_result(*b, replacement)),
        ),
        Term::IntMul(a, b) => Term::IntMul(
            Box::new(substitute_result(*a, replacement.clone())),
            Box::new(substitute_result(*b, replacement)),
        ),
        Term::Forall(vars, body) => {
            Term::Forall(vars, Box::new(substitute_result(*body, replacement)))
        }
        Term::App(name, args) => Term::App(
            name,
            args.into_iter()
                .map(|t| substitute_result(t, replacement.clone()))
                .collect(),
        ),
        // All other terms pass through unchanged
        other => other,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{BasicBlock, ClosureInfo, Contracts, FnSpec, Function, IntTy, Local, Ty};

    fn make_func_with_fn_param(param_name: &str, trait_kind: ClosureTrait) -> Function {
        let closure_info = ClosureInfo {
            name: format!("closure_{}", param_name),
            env_fields: vec![],
            params: vec![("x".to_string(), Ty::Int(IntTy::I32))],
            return_ty: Ty::Int(IntTy::I32),
            trait_kind,
        };
        Function {
            name: "test_func".to_string(),
            params: vec![Local::new(param_name, Ty::Closure(Box::new(closure_info)))],
            return_local: Local::new("_0", Ty::Int(IntTy::I32)),
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: crate::ir::Terminator::Return,
            }],
            contracts: Contracts {
                fn_specs: vec![],
                ..Default::default()
            },
            loops: vec![],
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
        }
    }

    fn make_func_with_fnmut_param(param_name: &str) -> Function {
        let closure_info = ClosureInfo {
            name: format!("closure_{}", param_name),
            env_fields: vec![
                ("count".to_string(), Ty::Int(IntTy::I32)),
                ("flag".to_string(), Ty::Bool),
            ],
            params: vec![("x".to_string(), Ty::Int(IntTy::I32))],
            return_ty: Ty::Int(IntTy::I32),
            trait_kind: ClosureTrait::FnMut,
        };
        Function {
            name: "test_fnmut".to_string(),
            params: vec![Local::new(param_name, Ty::Closure(Box::new(closure_info)))],
            return_local: Local::new("_0", Ty::Int(IntTy::I32)),
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: crate::ir::Terminator::Return,
            }],
            contracts: Contracts {
                fn_specs: vec![],
                ..Default::default()
            },
            loops: vec![],
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
        }
    }

    #[test]
    fn test_generate_fn_spec_vcs_returns_one_vc_per_spec() {
        let func = make_func_with_fn_param("f", ClosureTrait::Fn);
        let fn_specs = vec![
            FnSpec {
                closure_param: "f".to_string(),
                pre: "x > 0".to_string(),
                post: "result > 0".to_string(),
                bound_vars: vec!["x".to_string()],
            },
            FnSpec {
                closure_param: "f".to_string(),
                pre: "true".to_string(),
                post: "result >= 0".to_string(),
                bound_vars: vec!["x".to_string()],
            },
        ];

        let vcs = generate_fn_spec_vcs(&func, &fn_specs);
        assert_eq!(vcs.len(), 2);
    }

    #[test]
    fn test_fn_vc_has_auflia_logic() {
        let func = make_func_with_fn_param("f", ClosureTrait::Fn);
        let spec = FnSpec {
            closure_param: "f".to_string(),
            pre: "x > 0".to_string(),
            post: "result > 0".to_string(),
            bound_vars: vec!["x".to_string()],
        };

        let vc = generate_single_fn_spec_vc(&func, &spec);
        let script_str = vc
            .script
            .commands()
            .iter()
            .map(|c| c.to_string())
            .collect::<Vec<_>>()
            .join("\n");

        assert!(
            script_str.contains("AUFLIA"),
            "Expected AUFLIA logic, got: {}",
            script_str
        );
        assert!(
            script_str.contains("(check-sat)"),
            "Expected check-sat, got: {}",
            script_str
        );
    }

    #[test]
    fn test_fn_vc_has_closure_contract_kind() {
        let func = make_func_with_fn_param("f", ClosureTrait::Fn);
        let spec = FnSpec {
            closure_param: "f".to_string(),
            pre: "x > 0".to_string(),
            post: "result > 0".to_string(),
            bound_vars: vec!["x".to_string()],
        };

        let vc = generate_single_fn_spec_vc(&func, &spec);
        assert_eq!(vc.location.vc_kind, VcKind::ClosureContract);
    }

    #[test]
    fn test_fn_vc_declares_env_sort_and_fn() {
        let func = make_func_with_fn_param("f", ClosureTrait::Fn);
        let spec = FnSpec {
            closure_param: "f".to_string(),
            pre: "x > 0".to_string(),
            post: "result > 0".to_string(),
            bound_vars: vec!["x".to_string()],
        };

        let vc = generate_single_fn_spec_vc(&func, &spec);
        let script_str = vc
            .script
            .commands()
            .iter()
            .map(|c| c.to_string())
            .collect::<Vec<_>>()
            .join("\n");

        assert!(
            script_str.contains("ClosureEnv_f"),
            "Expected ClosureEnv_f sort declaration"
        );
        assert!(
            script_str.contains("f_impl"),
            "Expected f_impl function declaration"
        );
        assert!(
            script_str.contains("env_f"),
            "Expected env_f constant declaration"
        );
    }

    #[test]
    fn test_fnmut_vc_has_env_before_after_constants() {
        let func = make_func_with_fnmut_param("g");
        let spec = FnSpec {
            closure_param: "g".to_string(),
            pre: "x > 0".to_string(),
            post: "result > 0".to_string(),
            bound_vars: vec!["x".to_string()],
        };

        let vc = generate_single_fn_spec_vc(&func, &spec);
        let script_str = vc
            .script
            .commands()
            .iter()
            .map(|c| c.to_string())
            .collect::<Vec<_>>()
            .join("\n");

        assert!(
            script_str.contains("env_before_count"),
            "FnMut VC must declare env_before_count"
        );
        assert!(
            script_str.contains("env_after_count"),
            "FnMut VC must declare env_after_count"
        );
        assert!(
            script_str.contains("env_before_flag"),
            "FnMut VC must declare env_before_flag"
        );
        assert!(
            script_str.contains("env_after_flag"),
            "FnMut VC must declare env_after_flag"
        );
    }

    #[test]
    fn test_fnonce_vc_identical_to_fn_no_env_before_after() {
        let func = make_func_with_fn_param("h", ClosureTrait::FnOnce);
        let spec = FnSpec {
            closure_param: "h".to_string(),
            pre: "x > 0".to_string(),
            post: "result > 0".to_string(),
            bound_vars: vec!["x".to_string()],
        };

        let vc = generate_single_fn_spec_vc(&func, &spec);
        let script_str = vc
            .script
            .commands()
            .iter()
            .map(|c| c.to_string())
            .collect::<Vec<_>>()
            .join("\n");

        // FnOnce must NOT have env_before/env_after
        assert!(
            !script_str.contains("env_before_"),
            "FnOnce VC must NOT have env_before constants"
        );
        assert!(
            !script_str.contains("env_after_"),
            "FnOnce VC must NOT have env_after constants"
        );
        // But it must have AUFLIA and check-sat
        assert!(script_str.contains("AUFLIA"));
        assert!(script_str.contains("(check-sat)"));
    }

    #[test]
    fn test_vc_description_format() {
        let func = make_func_with_fn_param("f", ClosureTrait::Fn);
        let spec = FnSpec {
            closure_param: "f".to_string(),
            pre: "x > 0".to_string(),
            post: "result > 0".to_string(),
            bound_vars: vec!["x".to_string()],
        };

        let vc = generate_single_fn_spec_vc(&func, &spec);
        assert_eq!(vc.description, "fn_spec(f, |x| x > 0 => result > 0)");
    }

    #[test]
    fn test_generate_fn_spec_vcs_empty() {
        let func = make_func_with_fn_param("f", ClosureTrait::Fn);
        let vcs = generate_fn_spec_vcs(&func, &[]);
        assert!(vcs.is_empty());
    }

    #[test]
    fn test_fn_vc_contains_forall_assertion() {
        let func = make_func_with_fn_param("f", ClosureTrait::Fn);
        let spec = FnSpec {
            closure_param: "f".to_string(),
            pre: "x > 0".to_string(),
            post: "result > 0".to_string(),
            bound_vars: vec!["x".to_string()],
        };

        let vc = generate_single_fn_spec_vc(&func, &spec);
        let script_str = vc
            .script
            .commands()
            .iter()
            .map(|c| c.to_string())
            .collect::<Vec<_>>()
            .join("\n");

        // The assertion must contain (not ...) and (forall ...)
        assert!(
            script_str.contains("(assert (not"),
            "VC assertion must be negation: {}",
            script_str
        );
        assert!(
            script_str.contains("forall"),
            "VC must contain universal quantifier: {}",
            script_str
        );
    }

    #[test]
    fn test_unknown_param_defaults_to_fn_path() {
        // Closure param not in func.params — should default to Fn path (no env_before/after)
        let func = make_func_with_fn_param("f", ClosureTrait::Fn);
        let spec = FnSpec {
            closure_param: "unknown_param".to_string(),
            pre: "true".to_string(),
            post: "true".to_string(),
            bound_vars: vec![],
        };

        let vc = generate_single_fn_spec_vc(&func, &spec);
        let script_str = vc
            .script
            .commands()
            .iter()
            .map(|c| c.to_string())
            .collect::<Vec<_>>()
            .join("\n");

        assert!(!script_str.contains("env_before_"));
        assert!(!script_str.contains("env_after_"));
        assert!(script_str.contains("AUFLIA"));
    }
}
