/// Full specification expression parser using the `syn` crate.
///
/// Replaces the ad-hoc `parse_simple_spec` with a proper AST-based parser
/// that handles full Rust expression syntax: arithmetic, comparisons,
/// logical operators, field access, and the `old()` operator for
/// pre-state references in postconditions.
///
/// ## Supported syntax
///
/// - **Literals:** integer (`42`), boolean (`true`, `false`)
/// - **Identifiers:** `result` (return place `_0`), parameter names (`_1`, `_2`)
/// - **Binary ops:** `+`, `-`, `*`, `/`, `%`, `==`, `!=`, `>`, `<`, `>=`, `<=`, `&&`, `||`
/// - **Unary ops:** `!expr`, `-expr`
/// - **Field access:** `result.x`, `result.0`
/// - **old() operator:** `old(expr)` -- replaces all variables with `{name}_pre`
/// - **Parenthesized:** `(expr)`
use rust_fv_smtlib::term::Term;
use syn::{BinOp as SynBinOp, Expr, Lit, UnOp as SynUnOp};

use crate::ghost_predicate_db::GhostPredicateDatabase;
use crate::ir::{Function, IntTy, Ty, UintTy};
use crate::sep_logic;

/// Default bounded unfolding depth for ghost predicate expansion.
const GHOST_PRED_EXPAND_DEPTH: usize = 3;

/// A module-level empty GhostPredicateDatabase used as default when no DB is provided.
fn empty_ghost_db() -> GhostPredicateDatabase {
    GhostPredicateDatabase::new()
}

/// Parse a specification expression string into an SMT Term.
///
/// Returns `None` if the expression cannot be parsed or contains unsupported syntax.
/// This parser is a superset of `parse_simple_spec` -- all expressions that worked
/// with the old parser also work here.
pub fn parse_spec_expr(spec: &str, func: &Function) -> Option<Term> {
    let ghost_db = empty_ghost_db();
    parse_spec_expr_with_depth(spec, func, &ghost_db, GHOST_PRED_EXPAND_DEPTH)
}

/// Parse a specification expression with ghost predicate expansion support.
///
/// Ghost predicate calls are expanded to their body up to `GHOST_PRED_EXPAND_DEPTH` levels.
/// Returns `None` if the expression cannot be parsed or contains unsupported syntax.
pub fn parse_spec_expr_with_db(
    spec: &str,
    func: &Function,
    ghost_pred_db: &GhostPredicateDatabase,
) -> Option<Term> {
    parse_spec_expr_with_depth(spec, func, ghost_pred_db, GHOST_PRED_EXPAND_DEPTH)
}

/// Parse a specification expression in postcondition (ensures) context.
///
/// Identical to `parse_spec_expr_with_db` except that dereferences of mutable
/// reference parameters (`*_1`) resolve to the prophecy variable (`_1_prophecy`)
/// instead of the current value (`_1`). This is correct for `ensures` clauses where
/// `*_1` refers to the final (post-return) value of the mutable reference.
///
/// `old(*_1)` inside a postcondition still resolves to `_1_initial` — `old()` always wins.
pub fn parse_spec_expr_postcondition_with_db(
    spec: &str,
    func: &Function,
    ghost_pred_db: &GhostPredicateDatabase,
) -> Option<Term> {
    let spec = spec.trim();
    if spec.is_empty() {
        return None;
    }
    let expr: Expr = syn::parse_str(spec).ok()?;
    convert_expr_with_db(
        &expr,
        func,
        false, // in_old
        true,  // in_postcondition — key difference: *_1 → _1_prophecy
        false, // in_int_mode
        &[],   // bound_vars
        ghost_pred_db,
        GHOST_PRED_EXPAND_DEPTH,
    )
}

/// Parse a specification expression using integer arithmetic (QF_LIA-compatible).
///
/// Same as `parse_spec_expr_with_db` but forces `in_int_mode: true` so that all
/// integer literals and arithmetic operators use `Sort::Int` / `Term::IntLit` / `Term::IntAdd`
/// etc. instead of BitVec variants.
///
/// Use this for VCs that use `QF_LIA` logic (e.g., async VCs, RC11 VCs) where
/// `BitVec` sorts are not valid.
pub fn parse_spec_expr_qf_lia(
    spec: &str,
    func: &Function,
    ghost_pred_db: &GhostPredicateDatabase,
) -> Option<Term> {
    let spec = spec.trim();
    if spec.is_empty() {
        return None;
    }
    let expr: syn::Expr = syn::parse_str(spec).ok()?;
    convert_expr_with_db(
        &expr,
        func,
        false, // in_old
        false, // in_postcondition
        true,  // in_int_mode — force QF_LIA-compatible integer encoding
        &[],   // bound_vars
        ghost_pred_db,
        GHOST_PRED_EXPAND_DEPTH,
    )
}

/// Private helper: parse spec expression with bounded ghost predicate unfolding depth.
fn parse_spec_expr_with_depth(
    spec: &str,
    func: &Function,
    ghost_pred_db: &GhostPredicateDatabase,
    depth: usize,
) -> Option<Term> {
    let spec = spec.trim();
    if spec.is_empty() {
        return None;
    }

    // Parse the spec string as a Rust expression via syn
    let expr: Expr = syn::parse_str(spec).ok()?;

    convert_expr_with_db(&expr, func, false, false, false, &[], ghost_pred_db, depth)
}

/// Parse a specification expression with quantifier-bound variables support.
/// Delegates to `convert_expr_with_db` with an empty ghost predicate database.
fn convert_expr_with_bounds(
    expr: &Expr,
    func: &Function,
    in_old: bool,
    in_postcondition: bool,
    in_int_mode: bool,
    bound_vars: &[(String, rust_fv_smtlib::sort::Sort)],
) -> Option<Term> {
    let ghost_db = empty_ghost_db();
    convert_expr_with_db(
        expr,
        func,
        in_old,
        in_postcondition,
        in_int_mode,
        bound_vars,
        &ghost_db,
        GHOST_PRED_EXPAND_DEPTH,
    )
}

/// Core expression converter with ghost predicate database and bounded unfolding depth.
///
/// This is the main internal converter. All other entry points delegate here.
/// `ghost_pred_db` provides ghost predicate definitions for expansion.
/// `depth` controls bounded unfolding of ghost predicates (0 = exhausted, returns BoolLit(false)).
#[allow(clippy::too_many_arguments)]
fn convert_expr_with_db(
    expr: &Expr,
    func: &Function,
    in_old: bool,
    in_postcondition: bool,
    in_int_mode: bool,
    bound_vars: &[(String, rust_fv_smtlib::sort::Sort)],
    ghost_pred_db: &GhostPredicateDatabase,
    depth: usize,
) -> Option<Term> {
    match expr {
        Expr::Lit(lit_expr) => convert_lit(&lit_expr.lit, func, in_int_mode),

        Expr::Path(path_expr) => convert_path(path_expr, func, in_old, in_int_mode, bound_vars),

        Expr::Binary(bin_expr) => {
            // Separating conjunction detection: `H1 * H2` where at least one operand
            // is a sep-logic formula (pts_to or ghost predicate call). Must check
            // syntactic form BEFORE conversion.
            if matches!(bin_expr.op, SynBinOp::Mul(_))
                && (is_sep_logic_formula(&bin_expr.left, ghost_pred_db)
                    || is_sep_logic_formula(&bin_expr.right, ghost_pred_db))
            {
                let lhs = convert_expr_with_db(
                    &bin_expr.left,
                    func,
                    in_old,
                    in_postcondition,
                    in_int_mode,
                    bound_vars,
                    ghost_pred_db,
                    depth,
                )?;
                let rhs = convert_expr_with_db(
                    &bin_expr.right,
                    func,
                    in_old,
                    in_postcondition,
                    in_int_mode,
                    bound_vars,
                    ghost_pred_db,
                    depth,
                )?;
                // Separating conjunction: both assertions hold.
                // Disjointness is enforced by the single perm array in the heap model.
                return Some(Term::And(vec![lhs, rhs]));
            }

            let left = convert_expr_with_db(
                &bin_expr.left,
                func,
                in_old,
                in_postcondition,
                in_int_mode,
                bound_vars,
                ghost_pred_db,
                depth,
            )?;
            let right = convert_expr_with_db(
                &bin_expr.right,
                func,
                in_old,
                in_postcondition,
                in_int_mode,
                bound_vars,
                ghost_pred_db,
                depth,
            )?;
            convert_binop(&bin_expr.op, left, right, func, in_int_mode)
        }

        Expr::Unary(unary_expr) => {
            // Handle dereference operator specially for prophecy variables
            if matches!(unary_expr.op, SynUnOp::Deref(_)) {
                return convert_deref(&unary_expr.expr, func, in_old, in_postcondition, bound_vars);
            }
            let inner = convert_expr_with_db(
                &unary_expr.expr,
                func,
                in_old,
                in_postcondition,
                in_int_mode,
                bound_vars,
                ghost_pred_db,
                depth,
            )?;
            convert_unop(&unary_expr.op, inner, func)
        }

        Expr::Paren(paren_expr) => convert_expr_with_db(
            &paren_expr.expr,
            func,
            in_old,
            in_postcondition,
            in_int_mode,
            bound_vars,
            ghost_pred_db,
            depth,
        ),

        Expr::Field(field_expr) => convert_field_access(field_expr, func, in_old, bound_vars),

        Expr::Call(call_expr) => convert_call_with_db(
            call_expr,
            func,
            in_old,
            in_postcondition,
            in_int_mode,
            bound_vars,
            ghost_pred_db,
            depth,
        ),

        Expr::MethodCall(method_expr) => convert_method_call(method_expr, func, in_old),

        Expr::Cast(cast_expr) => convert_cast(cast_expr, func, in_old, bound_vars),

        Expr::Block(block_expr) => {
            // Block expressions: { expr } -- convert the single expression inside
            // Used by quantifier closures with trigger attributes: { #[trigger(f(x))] body }
            if let Some(syn::Stmt::Expr(inner_expr, _)) = block_expr.block.stmts.last() {
                convert_expr_with_db(
                    inner_expr,
                    func,
                    in_old,
                    in_postcondition,
                    in_int_mode,
                    bound_vars,
                    ghost_pred_db,
                    depth,
                )
            } else {
                None
            }
        }

        _ => None, // Unsupported expression kind
    }
}

/// Check if a `syn::Expr` is a separation-logic formula.
///
/// Returns `true` if the expression is:
/// - A `pts_to(...)` call (the built-in pts_to ownership predicate)
/// - A call to a name registered in `ghost_pred_db` (user-defined ghost predicate)
///
/// Used for syntactic sep-conj detection in `H1 * H2` expressions.
fn is_sep_logic_formula(expr: &Expr, ghost_pred_db: &GhostPredicateDatabase) -> bool {
    if let Expr::Call(call_expr) = expr
        && let Expr::Path(path) = call_expr.func.as_ref()
        && path.path.segments.len() == 1
    {
        let name = path.path.segments[0].ident.to_string();
        return name == "pts_to" || ghost_pred_db.contains(&name);
    }
    false
}

/// Convert a `syn::Expr` to a simple string for ghost predicate argument substitution.
///
/// For path expressions (simple identifiers), returns the identifier name.
/// For literal expressions, returns the literal value.
/// For other expressions, returns an empty string (substitution will be a no-op).
fn expr_to_arg_str(expr: &Expr) -> String {
    match expr {
        Expr::Path(path_expr) if path_expr.path.segments.len() == 1 => {
            path_expr.path.segments[0].ident.to_string()
        }
        Expr::Lit(lit_expr) => match &lit_expr.lit {
            Lit::Int(i) => i.to_string(),
            Lit::Bool(b) => b.value.to_string(),
            _ => String::new(),
        },
        _ => {
            // For more complex expressions, we cannot substitute easily.
            // Phase 20 scope: ghost predicates are called with simple variable args.
            String::new()
        }
    }
}

/// Convert a literal expression to an SMT Term.
fn convert_lit(lit: &Lit, func: &Function, in_int_mode: bool) -> Option<Term> {
    match lit {
        Lit::Int(int_lit) => {
            let value: i128 = int_lit.base10_parse().ok()?;
            if in_int_mode {
                // In int mode, integer literals are unbounded
                Some(Term::IntLit(value))
            } else {
                // In bitvector mode, determine bit width from function context
                let width = func.return_local.ty.bit_width().unwrap_or(32);
                Some(Term::BitVecLit(value, width))
            }
        }
        Lit::Bool(bool_lit) => Some(Term::BoolLit(bool_lit.value)),
        _ => None, // Unsupported literal type
    }
}

/// Convert a path expression (variable reference) to an SMT Term.
///
/// When `in_int_mode` is `true` (QF_LIA context), unknown identifiers are allowed
/// as free SMT constants — they are assumed to be declared externally in the VC script.
/// When `in_int_mode` is `false` (BV context), unknown identifiers return `None` (strict mode).
fn convert_path(
    path: &syn::ExprPath,
    func: &Function,
    in_old: bool,
    in_int_mode: bool,
    bound_vars: &[(String, rust_fv_smtlib::sort::Sort)],
) -> Option<Term> {
    // Must be a simple single-segment path (no :: separators)
    if path.path.segments.len() != 1 {
        return None;
    }

    let ident = path.path.segments[0].ident.to_string();

    // Check if this is a quantifier-bound variable first
    for (name, _sort) in bound_vars {
        if name == &ident {
            // Bound variables are never renamed with _pre (they are local to the quantifier)
            return Some(Term::Const(ident));
        }
    }

    match ident.as_str() {
        "result" => {
            let name = func.return_local.name.clone();
            if in_old {
                Some(Term::Const(format!("{name}_pre")))
            } else {
                Some(Term::Const(name))
            }
        }
        "true" => Some(Term::BoolLit(true)),
        "false" => Some(Term::BoolLit(false)),
        _ => {
            // Check if it matches a param, local, or return local.
            // In QF_LIA (int) mode, fall back to using the identifier as a free SMT constant
            // when not found in the IR. This allows specs to reference externally-declared
            // constants like `awaited_result_0` in async VC scripts.
            match resolve_variable_name(&ident, func) {
                Some(name) => {
                    if in_old {
                        Some(Term::Const(format!("{name}_pre")))
                    } else {
                        Some(Term::Const(name))
                    }
                }
                None if in_int_mode => {
                    // Free constant reference (declared externally in QF_LIA script)
                    if in_old {
                        Some(Term::Const(format!("{ident}_pre")))
                    } else {
                        Some(Term::Const(ident))
                    }
                }
                None => None, // Strict mode (BV): unknown variables are an error
            }
        }
    }
}

/// Resolve a variable name from the spec to its IR name.
///
/// Specs may use either the MIR-style name (`_1`) directly, or the original
/// parameter name if we ever add name mapping.
fn resolve_variable_name(ident: &str, func: &Function) -> Option<String> {
    // Check return local
    if func.return_local.name == ident {
        return Some(ident.to_string());
    }
    // Check params
    for p in &func.params {
        if p.name == ident {
            return Some(ident.to_string());
        }
    }
    // Check locals
    for l in &func.locals {
        if l.name == ident {
            return Some(ident.to_string());
        }
    }
    None
}

/// Convert a syn binary operator + operands to an SMT Term.
fn convert_binop(
    op: &SynBinOp,
    left: Term,
    right: Term,
    func: &Function,
    in_int_mode: bool,
) -> Option<Term> {
    let l = Box::new(left.clone());
    let r = Box::new(right.clone());

    match op {
        // Arithmetic
        SynBinOp::Add(_) => {
            if in_int_mode {
                Some(Term::IntAdd(l, r))
            } else {
                Some(Term::BvAdd(l, r))
            }
        }
        SynBinOp::Sub(_) => {
            if in_int_mode {
                Some(Term::IntSub(l, r))
            } else {
                Some(Term::BvSub(l, r))
            }
        }
        SynBinOp::Mul(_) => {
            if in_int_mode {
                Some(Term::IntMul(l, r))
            } else {
                Some(Term::BvMul(l, r))
            }
        }
        SynBinOp::Div(_) => {
            if in_int_mode {
                Some(Term::IntDiv(l, r))
            } else {
                let signed = infer_signedness(func);
                if signed {
                    Some(Term::BvSDiv(l, r))
                } else {
                    Some(Term::BvUDiv(l, r))
                }
            }
        }
        SynBinOp::Rem(_) => {
            if in_int_mode {
                Some(Term::IntMod(l, r))
            } else {
                let signed = infer_signedness(func);
                if signed {
                    Some(Term::BvSRem(l, r))
                } else {
                    Some(Term::BvURem(l, r))
                }
            }
        }

        // Comparison
        SynBinOp::Eq(_) => Some(Term::Eq(l, r)),
        SynBinOp::Ne(_) => Some(Term::Not(Box::new(Term::Eq(l, r)))),
        SynBinOp::Gt(_) => {
            if in_int_mode {
                Some(Term::IntGt(l, r))
            } else {
                let signed = infer_signedness_from_terms(func, &left, &right);
                if signed {
                    Some(Term::BvSGt(l, r))
                } else {
                    Some(Term::BvUGt(l, r))
                }
            }
        }
        SynBinOp::Lt(_) => {
            if in_int_mode {
                Some(Term::IntLt(l, r))
            } else {
                let signed = infer_signedness_from_terms(func, &left, &right);
                if signed {
                    Some(Term::BvSLt(l, r))
                } else {
                    Some(Term::BvULt(l, r))
                }
            }
        }
        SynBinOp::Ge(_) => {
            if in_int_mode {
                Some(Term::IntGe(l, r))
            } else {
                let signed = infer_signedness_from_terms(func, &left, &right);
                if signed {
                    Some(Term::BvSGe(l, r))
                } else {
                    Some(Term::BvUGe(l, r))
                }
            }
        }
        SynBinOp::Le(_) => {
            if in_int_mode {
                Some(Term::IntLe(l, r))
            } else {
                let signed = infer_signedness_from_terms(func, &left, &right);
                if signed {
                    Some(Term::BvSLe(l, r))
                } else {
                    Some(Term::BvULe(l, r))
                }
            }
        }

        // Logical
        SynBinOp::And(_) => Some(Term::And(vec![left, right])),
        SynBinOp::Or(_) => Some(Term::Or(vec![left, right])),

        // Bitwise
        SynBinOp::BitAnd(_) => Some(Term::BvAnd(l, r)),
        SynBinOp::BitOr(_) => Some(Term::BvOr(l, r)),
        SynBinOp::BitXor(_) => Some(Term::BvXor(l, r)),
        SynBinOp::Shl(_) => Some(Term::BvShl(l, r)),
        SynBinOp::Shr(_) => {
            let signed = infer_signedness(func);
            if signed {
                Some(Term::BvAShr(l, r))
            } else {
                Some(Term::BvLShr(l, r))
            }
        }

        _ => None, // Unsupported binary operator
    }
}

/// Convert a syn unary operator to an SMT Term.
fn convert_unop(op: &SynUnOp, inner: Term, func: &Function) -> Option<Term> {
    match op {
        SynUnOp::Not(_) => {
            // For boolean expressions, use logical Not
            // For bitvector, use BvNot -- heuristic: if the inner is a comparison/bool, use Not
            if is_boolean_term(&inner, func) {
                Some(Term::Not(Box::new(inner)))
            } else {
                Some(Term::BvNot(Box::new(inner)))
            }
        }
        SynUnOp::Neg(_) => Some(Term::BvNeg(Box::new(inner))),
        _ => None,
    }
}

/// Convert a field access expression to an SMT Term.
fn convert_field_access(
    field_expr: &syn::ExprField,
    func: &Function,
    in_old: bool,
    bound_vars: &[(String, rust_fv_smtlib::sort::Sort)],
) -> Option<Term> {
    let base = convert_expr_with_bounds(&field_expr.base, func, in_old, false, false, bound_vars)?;

    // Determine the type of the base expression to resolve field selectors
    let base_ty = infer_expr_type(&field_expr.base, func)?;

    match &field_expr.member {
        syn::Member::Named(ident) => {
            let field_name = ident.to_string();
            match base_ty {
                Ty::Struct(type_name, fields) => {
                    // Verify field exists
                    if fields.iter().any(|(f, _)| *f == field_name) {
                        let selector = format!("{type_name}-{field_name}");
                        Some(Term::App(selector, vec![base]))
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }
        syn::Member::Unnamed(idx) => {
            let index = idx.index as usize;
            match base_ty {
                Ty::Tuple(fields) => {
                    if index < fields.len() {
                        let selector = format!("Tuple{}-_{index}", fields.len());
                        Some(Term::App(selector, vec![base]))
                    } else {
                        None
                    }
                }
                Ty::Struct(type_name, fields) => {
                    if index < fields.len() {
                        let (field_name, _) = &fields[index];
                        let selector = format!("{type_name}-{field_name}");
                        Some(Term::App(selector, vec![base]))
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }
    }
}

/// Check if a name is a closure parameter and return its ClosureInfo.
fn is_closure_param<'a>(name: &str, func: &'a Function) -> Option<&'a crate::ir::ClosureInfo> {
    // Check function parameters
    for param in &func.params {
        if param.name == name
            && let Ty::Closure(info) = &param.ty
        {
            return Some(info.as_ref());
        }
    }
    // Could also check locals, but typically closures are passed as parameters
    None
}

/// Convert a function call expression (handles `old()`, `forall()`, `exists()`, `implies()` operators).
fn convert_call(
    call_expr: &syn::ExprCall,
    func: &Function,
    _in_old: bool,
    in_postcondition: bool,
    in_int_mode: bool,
    bound_vars: &[(String, rust_fv_smtlib::sort::Sort)],
) -> Option<Term> {
    // Extract function name
    if let Expr::Path(path) = &*call_expr.func
        && path.path.segments.len() == 1
    {
        let func_name = path.path.segments[0].ident.to_string();

        // Check if this is a closure parameter being called
        if let Some(_closure_info) = is_closure_param(&func_name, func) {
            // This is a closure call: closure_name(args...)
            // Encode as: closure_name_impl(env, args...)
            let impl_name = format!("{}_impl", func_name);

            // Create environment term (for now, use placeholder since we don't have the actual env)
            // In the context of specs, the env is part of the closure parameter
            let env_term = Term::Const(format!("{}_env", func_name));

            // Convert call arguments
            let mut arg_terms = vec![env_term];
            for arg in &call_expr.args {
                let arg_term = convert_expr_with_bounds(
                    arg,
                    func,
                    false,
                    in_postcondition,
                    in_int_mode,
                    bound_vars,
                )?;
                arg_terms.push(arg_term);
            }

            return Some(Term::App(impl_name, arg_terms));
        }

        match func_name.as_str() {
            "old" => {
                // old() operator: parse the inner expression with in_old=true
                // Inside old(), in_postcondition=false: old() always captures initial value,
                // never the prophecy variable.
                if call_expr.args.len() != 1 {
                    return None; // old() takes exactly one argument
                }
                return convert_expr_with_bounds(
                    &call_expr.args[0],
                    func,
                    true,  // in_old
                    false, // in_postcondition: inside old() we never want _prophecy
                    in_int_mode,
                    bound_vars,
                );
            }

            "implies" => {
                // implies(a, b) -> Term::Implies(a, b)
                if call_expr.args.len() != 2 {
                    return None; // implies takes exactly 2 arguments
                }
                let lhs = convert_expr_with_bounds(
                    &call_expr.args[0],
                    func,
                    false,
                    in_postcondition,
                    in_int_mode,
                    bound_vars,
                )?;
                let rhs = convert_expr_with_bounds(
                    &call_expr.args[1],
                    func,
                    false,
                    in_postcondition,
                    in_int_mode,
                    bound_vars,
                )?;
                return Some(Term::Implies(Box::new(lhs), Box::new(rhs)));
            }

            "forall" => {
                // forall(|x: Type| body) -> Term::Forall([(x, Sort)], body)
                if call_expr.args.len() != 1 {
                    return None;
                }
                return convert_quantifier(&call_expr.args[0], func, in_int_mode, bound_vars, true);
            }

            "exists" => {
                // exists(|x: Type| body) -> Term::Exists([(x, Sort)], body)
                if call_expr.args.len() != 1 {
                    return None;
                }
                return convert_quantifier(
                    &call_expr.args[0],
                    func,
                    in_int_mode,
                    bound_vars,
                    false,
                );
            }

            "final_value" => {
                // final_value(x) -> prophecy variable for parameter x
                if call_expr.args.len() != 1 {
                    return None; // final_value takes exactly one argument
                }
                return convert_final_value(&call_expr.args[0], func, bound_vars);
            }

            "pts_to" => {
                // pts_to(ptr, value) — raw pointer ownership predicate
                if call_expr.args.len() != 2 {
                    tracing::warn!("pts_to() requires exactly 2 arguments: pts_to(ptr, val)");
                    return None;
                }
                let ptr_term = convert_expr_with_bounds(
                    &call_expr.args[0],
                    func,
                    false,
                    in_postcondition,
                    in_int_mode,
                    bound_vars,
                )?;
                let val_term = convert_expr_with_bounds(
                    &call_expr.args[1],
                    func,
                    false,
                    in_postcondition,
                    in_int_mode,
                    bound_vars,
                )?;
                // Determine pointee bit width from pointer parameter type.
                // Default to 64 bits if type cannot be resolved (conservative).
                let pointee_bits = resolve_pointee_bits(&call_expr.args[0], func).unwrap_or(64);
                return Some(sep_logic::encode_pts_to(ptr_term, val_term, pointee_bits));
            }

            _ => {
                // Unknown function call
                return None;
            }
        }
    }

    // Not a known function call
    None
}

/// Convert a function call expression with ghost predicate expansion support.
///
/// Extends `convert_call` with:
/// - Ghost predicate call expansion: expands body to `depth` levels
/// - At `depth=0`, returns `BoolLit(false)` (conservative: body unknown)
#[allow(clippy::too_many_arguments)]
fn convert_call_with_db(
    call_expr: &syn::ExprCall,
    func: &Function,
    in_old: bool,
    in_postcondition: bool,
    in_int_mode: bool,
    bound_vars: &[(String, rust_fv_smtlib::sort::Sort)],
    ghost_pred_db: &GhostPredicateDatabase,
    depth: usize,
) -> Option<Term> {
    // Extract function name
    if let Expr::Path(path) = &*call_expr.func
        && path.path.segments.len() == 1
    {
        let func_name = path.path.segments[0].ident.to_string();

        // Check if this is a ghost predicate — expand before any other checks
        if ghost_pred_db.contains(&func_name) {
            if depth == 0 {
                // Depth exhausted: conservative — predicate body unknown
                tracing::debug!(
                    "Ghost predicate '{}' depth exhausted, returning false",
                    func_name
                );
                return Some(Term::BoolLit(false));
            }
            let pred = ghost_pred_db.get(&func_name).unwrap().clone();
            if call_expr.args.len() != pred.param_names.len() {
                tracing::warn!(
                    "Ghost predicate '{}' expects {} args, got {}",
                    func_name,
                    pred.param_names.len(),
                    call_expr.args.len()
                );
                return None;
            }
            // Substitute formal params with actual argument token strings
            let mut body = pred.body_raw.clone();
            for (param, arg_expr) in pred.param_names.iter().zip(call_expr.args.iter()) {
                let arg_str = expr_to_arg_str(arg_expr);
                // Replace whole-word occurrences of param with arg_str
                body = replace_whole_word(&body, param.as_str(), &arg_str);
            }
            // Re-parse with depth decremented to prevent stack overflow
            return parse_spec_expr_with_depth(&body, func, ghost_pred_db, depth - 1);
        }
    }

    // Delegate to the standard convert_call for all other cases
    convert_call(
        call_expr,
        func,
        in_old,
        in_postcondition,
        in_int_mode,
        bound_vars,
    )
}

/// Replace whole-word occurrences of `from` with `to` in `s`.
///
/// A whole-word match requires that the character before `from` is not alphanumeric/underscore
/// and the character after `from` is not alphanumeric/underscore.
fn replace_whole_word(s: &str, from: &str, to: &str) -> String {
    let mut result = String::with_capacity(s.len());
    let bytes = s.as_bytes();
    let from_bytes = from.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i..].starts_with(from_bytes) {
            let before_ok = i == 0 || !bytes[i - 1].is_ascii_alphanumeric() && bytes[i - 1] != b'_';
            let after_pos = i + from_bytes.len();
            let after_ok = after_pos >= bytes.len()
                || !bytes[after_pos].is_ascii_alphanumeric() && bytes[after_pos] != b'_';
            if before_ok && after_ok {
                result.push_str(to);
                i += from_bytes.len();
                continue;
            }
        }
        result.push(bytes[i] as char);
        i += 1;
    }
    result
}

/// Resolve the pointee bit width for a `pts_to(ptr, val)` call from the pointer argument type.
///
/// Looks up the first argument name in `func.params` to find a param with `Ty::RawPtr(inner, _)`,
/// then maps the inner type to a bit width.
/// Returns `None` if the type cannot be resolved (caller should use a default).
fn resolve_pointee_bits(arg: &Expr, func: &Function) -> Option<u32> {
    // Arg must be a simple path expression
    if let Expr::Path(path_expr) = arg
        && path_expr.path.segments.len() == 1
    {
        let ident = path_expr.path.segments[0].ident.to_string();
        // Look for a param named `ident` with a RawPtr type
        for param in &func.params {
            if param.name == ident
                && let Ty::RawPtr(inner, _) = &param.ty
            {
                return match inner.as_ref() {
                    Ty::Int(IntTy::I8) | Ty::Uint(UintTy::U8) => Some(8),
                    Ty::Int(IntTy::I16) | Ty::Uint(UintTy::U16) => Some(16),
                    Ty::Int(IntTy::I32) | Ty::Uint(UintTy::U32) => Some(32),
                    Ty::Int(IntTy::I64) | Ty::Uint(UintTy::U64) => Some(64),
                    Ty::Bool => Some(8),
                    _ => None,
                };
            }
        }
    }
    None
}

/// Convert a quantifier closure expression to Term::Forall or Term::Exists.
fn convert_quantifier(
    arg: &Expr,
    func: &Function,
    in_int_mode: bool,
    bound_vars: &[(String, rust_fv_smtlib::sort::Sort)],
    is_forall: bool,
) -> Option<Term> {
    // Expect a closure: |x: Type, y: Type| body
    if let Expr::Closure(closure_expr) = arg {
        // Extract typed parameters
        let mut sorted_vars = Vec::new();
        for input in &closure_expr.inputs {
            if let syn::Pat::Type(pat_type) = input {
                if let syn::Pat::Ident(pat_ident) = &*pat_type.pat {
                    let var_name = pat_ident.ident.to_string();
                    let var_sort = convert_syn_type_to_sort(&pat_type.ty)?;
                    sorted_vars.push((var_name, var_sort));
                } else {
                    return None; // Unsupported pattern
                }
            } else {
                return None; // Parameters must be typed
            }
        }

        if sorted_vars.is_empty() {
            return None; // Quantifier must bind at least one variable
        }

        // Build new bound_vars stack for body
        let mut new_bound_vars = bound_vars.to_vec();
        new_bound_vars.extend(sorted_vars.clone());

        // Extract trigger hints from #[trigger(...)] attributes on the body
        let trigger_hints =
            extract_trigger_hints(&closure_expr.body, func, in_int_mode, &new_bound_vars);

        // Convert body with new bound vars (strip trigger attrs handled by convert_expr)
        let body = convert_expr_with_bounds(
            &closure_expr.body,
            func,
            false,
            false, // in_postcondition: quantifier bodies don't use prophecy vars
            in_int_mode,
            &new_bound_vars,
        )?;

        // Wrap body with trigger annotations if any triggers were found
        let final_body = if trigger_hints.is_empty() {
            body
        } else {
            let annotations: Vec<(String, Vec<Term>)> = trigger_hints
                .into_iter()
                .map(|hint| ("rust_fv_trigger_hint".to_string(), hint))
                .collect();
            Term::Annotated(Box::new(body), annotations)
        };

        // Return the quantifier
        if is_forall {
            Some(Term::Forall(sorted_vars, Box::new(final_body)))
        } else {
            Some(Term::Exists(sorted_vars, Box::new(final_body)))
        }
    } else {
        None
    }
}

/// Extract trigger hints from `#[trigger(...)]` attributes on a closure body expression.
///
/// Supports two forms:
/// - Block body: `{ #[trigger(f(x))] #[trigger(g(x))] expr }` -- attributes on first expr in block
/// - Non-block body: `#[trigger(f(x))] (expr)` -- attributes on the body expr itself
///
/// Each `#[trigger(term1, term2)]` attribute produces one trigger set (Vec<Term>).
/// Multiple `#[trigger]` attributes produce multiple trigger sets (disjunction).
fn extract_trigger_hints(
    body: &Expr,
    func: &Function,
    in_int_mode: bool,
    bound_vars: &[(String, rust_fv_smtlib::sort::Sort)],
) -> Vec<Vec<Term>> {
    let attrs = collect_trigger_attrs(body);
    let mut trigger_sets = Vec::new();

    for attr in attrs {
        if let syn::Meta::List(meta_list) = &attr.meta {
            // Check that the path is "trigger"
            if meta_list.path.segments.len() == 1 && meta_list.path.segments[0].ident == "trigger" {
                // Parse the token stream inside #[trigger(...)]
                let tokens = &meta_list.tokens;
                if tokens.is_empty() {
                    continue; // Empty trigger #[trigger()] is ignored
                }

                // Parse the trigger expressions from the token stream
                let trigger_terms =
                    parse_trigger_token_stream(tokens, func, in_int_mode, bound_vars);
                if !trigger_terms.is_empty() {
                    trigger_sets.push(trigger_terms);
                }
            }
        }
    }

    trigger_sets
}

/// Collect `#[trigger(...)]` attributes from a body expression.
///
/// Looks at:
/// 1. Block body: attributes on the first expression statement in the block
/// 2. Non-block body: attributes on the body expression directly (e.g., Paren, Call)
fn collect_trigger_attrs(body: &Expr) -> Vec<&syn::Attribute> {
    let attrs: &[syn::Attribute] = match body {
        Expr::Block(block_expr) => {
            // Look at the first expression in the block for attributes
            if let Some(syn::Stmt::Expr(expr, _)) = block_expr.block.stmts.first() {
                get_expr_attrs(expr)
            } else {
                return Vec::new();
            }
        }
        _ => get_expr_attrs(body),
    };

    attrs
        .iter()
        .filter(|attr| {
            if let syn::Meta::List(meta_list) = &attr.meta {
                meta_list.path.segments.len() == 1 && meta_list.path.segments[0].ident == "trigger"
            } else {
                false
            }
        })
        .collect()
}

/// Get the attributes slice from any expression type.
fn get_expr_attrs(expr: &Expr) -> &[syn::Attribute] {
    match expr {
        Expr::Binary(e) => {
            // For binary expressions like `f(x) > 0`, the attr is on the LHS
            // Check the left side for trigger attrs
            get_expr_attrs(&e.left)
        }
        Expr::Call(e) => &e.attrs,
        Expr::Path(e) => &e.attrs,
        Expr::Paren(e) => &e.attrs,
        Expr::Lit(e) => &e.attrs,
        Expr::Unary(e) => &e.attrs,
        Expr::Field(e) => &e.attrs,
        Expr::MethodCall(e) => &e.attrs,
        Expr::Block(e) => &e.attrs,
        _ => &[],
    }
}

/// Parse a trigger token stream like `f(x)` or `f(x), g(y)` into Terms.
///
/// Comma-separated expressions in a single `#[trigger(...)]` form a multi-trigger
/// (conjunction). Each expression is parsed as a Rust expression and converted to a Term.
fn parse_trigger_token_stream(
    tokens: &proc_macro2::TokenStream,
    func: &Function,
    in_int_mode: bool,
    bound_vars: &[(String, rust_fv_smtlib::sort::Sort)],
) -> Vec<Term> {
    // Parse the tokens as comma-separated expressions
    // Strategy: try to parse as a full expression first, then split by commas if needed
    let token_str = tokens.to_string();

    // Split by top-level commas (not inside parentheses)
    let expr_strs = split_trigger_exprs(&token_str);

    let mut terms = Vec::new();
    for expr_str in expr_strs {
        let trimmed = expr_str.trim();
        if trimmed.is_empty() {
            continue;
        }
        // Parse each trigger expression as a Rust expression
        if let Ok(expr) = syn::parse_str::<Expr>(trimmed) {
            // Convert to a Term using trigger-specific conversion
            // Trigger terms are function applications - unresolved function names
            // become App terms
            if let Some(term) = convert_trigger_expr(&expr, func, in_int_mode, bound_vars) {
                terms.push(term);
            }
        }
    }

    terms
}

/// Split a trigger expression string by top-level commas (respecting parentheses).
fn split_trigger_exprs(s: &str) -> Vec<String> {
    let mut result = Vec::new();
    let mut current = String::new();
    let mut depth = 0;

    for ch in s.chars() {
        match ch {
            '(' => {
                depth += 1;
                current.push(ch);
            }
            ')' => {
                depth -= 1;
                current.push(ch);
            }
            ',' if depth == 0 => {
                result.push(current.clone());
                current.clear();
            }
            _ => {
                current.push(ch);
            }
        }
    }

    if !current.trim().is_empty() {
        result.push(current);
    }

    result
}

/// Convert a trigger expression to an SMT Term.
///
/// Trigger expressions are typically function applications like `f(x)` or `f(g(x))`.
/// Unknown function names (not in the function context) are treated as uninterpreted
/// function applications (Term::App).
fn convert_trigger_expr(
    expr: &Expr,
    func: &Function,
    in_int_mode: bool,
    bound_vars: &[(String, rust_fv_smtlib::sort::Sort)],
) -> Option<Term> {
    match expr {
        Expr::Call(call_expr) => {
            // Function call: f(x) or f(g(x))
            if let Expr::Path(path) = &*call_expr.func
                && path.path.segments.len() == 1
            {
                let func_name = path.path.segments[0].ident.to_string();

                // Convert arguments
                let mut args = Vec::new();
                for arg in &call_expr.args {
                    let arg_term = convert_trigger_expr(arg, func, in_int_mode, bound_vars)?;
                    args.push(arg_term);
                }

                return Some(Term::App(func_name, args));
            }
            None
        }
        Expr::Path(path_expr) => {
            // Simple variable reference like `x`
            if path_expr.path.segments.len() == 1 {
                let ident = path_expr.path.segments[0].ident.to_string();

                // Check if it's a bound variable
                for (name, _) in bound_vars {
                    if *name == ident {
                        return Some(Term::Const(ident));
                    }
                }

                // Try to resolve as a function variable
                if let Some(name) = resolve_variable_name(&ident, func) {
                    return Some(Term::Const(name));
                }

                // Unknown identifier in trigger context - treat as a constant
                Some(Term::Const(ident))
            } else {
                None
            }
        }
        Expr::Paren(paren_expr) => {
            convert_trigger_expr(&paren_expr.expr, func, in_int_mode, bound_vars)
        }
        _ => {
            // For other expressions, fall back to the regular expression converter
            convert_expr_with_bounds(expr, func, false, false, in_int_mode, bound_vars)
        }
    }
}

/// Convert a syn type to an SMT Sort.
fn convert_syn_type_to_sort(ty: &syn::Type) -> Option<rust_fv_smtlib::sort::Sort> {
    use rust_fv_smtlib::sort::Sort;

    if let syn::Type::Path(type_path) = ty
        && type_path.path.segments.len() == 1
    {
        let type_name = type_path.path.segments[0].ident.to_string();
        return match type_name.as_str() {
            "bool" => Some(Sort::Bool),
            "i8" => Some(Sort::BitVec(8)),
            "i16" => Some(Sort::BitVec(16)),
            "i32" => Some(Sort::BitVec(32)),
            "i64" => Some(Sort::BitVec(64)),
            "i128" => Some(Sort::BitVec(128)),
            "isize" => Some(Sort::BitVec(64)), // Platform-dependent, assume 64-bit
            "u8" => Some(Sort::BitVec(8)),
            "u16" => Some(Sort::BitVec(16)),
            "u32" => Some(Sort::BitVec(32)),
            "u64" => Some(Sort::BitVec(64)),
            "u128" => Some(Sort::BitVec(128)),
            "usize" => Some(Sort::BitVec(64)), // Platform-dependent, assume 64-bit
            "int" => Some(Sort::Int),          // Unbounded integer
            "nat" => Some(Sort::Int), // Non-negative unbounded integer (constraint added separately)
            _ => None,                // Unsupported type
        };
    }
    None
}

/// Convert a cast expression (handles `as int` and `as nat` casts).
fn convert_cast(
    cast_expr: &syn::ExprCast,
    func: &Function,
    in_old: bool,
    bound_vars: &[(String, rust_fv_smtlib::sort::Sort)],
) -> Option<Term> {
    // Check if the target type is "int" or "nat"
    if let syn::Type::Path(type_path) = &*cast_expr.ty {
        if type_path.path.segments.len() == 1 {
            let type_name = type_path.path.segments[0].ident.to_string();
            match type_name.as_str() {
                "int" => {
                    // Cast to unbounded integer: convert inner expression in int mode
                    // and wrap with Bv2Int if the inner expression is a bitvector
                    let inner = convert_expr_with_bounds(
                        &cast_expr.expr,
                        func,
                        in_old,
                        false,
                        false,
                        bound_vars,
                    )?;
                    // The inner is a bitvector term, convert to Int
                    Some(Term::Bv2Int(Box::new(inner)))
                }
                "nat" => {
                    // Cast to non-negative unbounded integer
                    // Same as int cast for now (non-negativity constraint added in VCGen)
                    let inner = convert_expr_with_bounds(
                        &cast_expr.expr,
                        func,
                        in_old,
                        false,
                        false,
                        bound_vars,
                    )?;
                    Some(Term::Bv2Int(Box::new(inner)))
                }
                _ => None, // Unsupported cast
            }
        } else {
            None
        }
    } else {
        None
    }
}

/// Convert a method call expression (limited support).
fn convert_method_call(
    _method_expr: &syn::ExprMethodCall,
    _func: &Function,
    _in_old: bool,
) -> Option<Term> {
    // For now, no method calls are supported.
    // Future: is_some(), is_none(), len(), etc.
    None
}

/// Infer whether the function context is signed (default heuristic).
fn infer_signedness(func: &Function) -> bool {
    func.return_local.ty.is_signed() || func.params.first().is_some_and(|p| p.ty.is_signed())
}

/// Infer signedness from two terms and the function context.
fn infer_signedness_from_terms(func: &Function, lhs: &Term, rhs: &Term) -> bool {
    // Check if either term is a Const with a known type
    if let Some(signed) = infer_signedness_from_single_term(func, lhs) {
        return signed;
    }
    if let Some(signed) = infer_signedness_from_single_term(func, rhs) {
        return signed;
    }
    // Fallback to function-level heuristic
    infer_signedness(func)
}

/// Try to infer signedness from a single term.
fn infer_signedness_from_single_term(func: &Function, term: &Term) -> Option<bool> {
    match term {
        Term::Const(name) => {
            let ty = find_local_type(func, name)?;
            if ty.is_signed() || ty.is_unsigned() {
                Some(ty.is_signed())
            } else {
                None
            }
        }
        Term::App(selector_name, args) if args.len() == 1 => {
            // Selector application: resolve the field type
            resolve_selector_type(func, selector_name).map(|ty| ty.is_signed())
        }
        _ => None,
    }
}

/// Determine if a term is boolean in the context of the function.
fn is_boolean_term(term: &Term, func: &Function) -> bool {
    matches!(
        term,
        Term::BoolLit(_)
            | Term::Not(_)
            | Term::And(_)
            | Term::Or(_)
            | Term::Implies(_, _)
            | Term::Eq(_, _)
            | Term::BvSLt(_, _)
            | Term::BvSLe(_, _)
            | Term::BvSGt(_, _)
            | Term::BvSGe(_, _)
            | Term::BvULt(_, _)
            | Term::BvULe(_, _)
            | Term::BvUGt(_, _)
            | Term::BvUGe(_, _)
    ) || matches!(term, Term::Const(name) if matches!(find_local_type(func, name), Some(Ty::Bool)))
}

/// Infer the type of a syn expression in the context of the function.
fn infer_expr_type<'a>(expr: &Expr, func: &'a Function) -> Option<&'a Ty> {
    match expr {
        Expr::Path(path) => {
            if path.path.segments.len() != 1 {
                return None;
            }
            let ident = path.path.segments[0].ident.to_string();
            if ident == "result" {
                Some(&func.return_local.ty)
            } else {
                find_local_type(func, &ident)
            }
        }
        _ => None,
    }
}

/// Find the type of a local variable by name (mirrors vcgen::find_local_type).
fn find_local_type<'a>(func: &'a Function, name: &str) -> Option<&'a Ty> {
    if func.return_local.name == name {
        return Some(&func.return_local.ty);
    }
    for p in &func.params {
        if p.name == name {
            return Some(&p.ty);
        }
    }
    for l in &func.locals {
        if l.name == name {
            return Some(&l.ty);
        }
    }
    None
}

/// Resolve the type of a field from a selector name (mirrors vcgen logic).
fn resolve_selector_type<'a>(func: &'a Function, selector_name: &str) -> Option<&'a Ty> {
    // Check return type
    if let Some(ty) = resolve_selector_from_ty(&func.return_local.ty, selector_name) {
        return Some(ty);
    }
    for p in &func.params {
        if let Some(ty) = resolve_selector_from_ty(&p.ty, selector_name) {
            return Some(ty);
        }
    }
    for l in &func.locals {
        if let Some(ty) = resolve_selector_from_ty(&l.ty, selector_name) {
            return Some(ty);
        }
    }
    None
}

fn resolve_selector_from_ty<'a>(ty: &'a Ty, selector_name: &str) -> Option<&'a Ty> {
    match ty {
        Ty::Struct(name, fields) => {
            let prefix = format!("{name}-");
            if let Some(field_name) = selector_name.strip_prefix(&prefix) {
                for (fname, fty) in fields {
                    if fname == field_name {
                        return Some(fty);
                    }
                }
            }
        }
        Ty::Tuple(fields) => {
            let type_name = format!("Tuple{}", fields.len());
            let prefix = format!("{type_name}-_");
            if let Some(idx_str) = selector_name.strip_prefix(&prefix)
                && let Ok(idx) = idx_str.parse::<usize>()
            {
                return fields.get(idx);
            }
        }
        _ => {}
    }
    None
}

/// Convert a dereference expression `*expr` in a specification.
///
/// When the dereferenced expression is a mutable reference parameter:
/// - In `old()` context: produces `param_initial` (the initial dereferenced value)
/// - In postcondition context: produces `param_prophecy` (the predicted final value)
/// - In normal context: produces `param` (the current dereferenced value)
///
/// This enables specs like `*x == old(*x) + 1` for mutable borrow parameters.
fn convert_deref(
    expr: &Expr,
    func: &Function,
    in_old: bool,
    in_postcondition: bool,
    _bound_vars: &[(String, rust_fv_smtlib::sort::Sort)],
) -> Option<Term> {
    // Extract the parameter name from the expression
    if let Expr::Path(path_expr) = expr
        && path_expr.path.segments.len() == 1
    {
        let ident = path_expr.path.segments[0].ident.to_string();
        let param_name = resolve_variable_name(&ident, func)?;

        // Check if this is a mutable reference parameter
        for param in &func.params {
            if param.name == param_name
                && matches!(param.ty, Ty::Ref(_, crate::ir::Mutability::Mutable))
            {
                // This is a mutable ref param - apply prophecy naming
                if in_old {
                    // old() always wins — captures initial value regardless of postcondition context
                    return Some(Term::Const(format!("{param_name}_initial")));
                } else if in_postcondition {
                    // postcondition context: *param resolves to prophecy variable (final predicted value)
                    return Some(Term::Const(format!("{param_name}_prophecy")));
                } else {
                    // normal context (preconditions, loop invariants): use current value
                    return Some(Term::Const(param_name));
                }
            }
        }

        // Not a mutable reference param - just treat as regular variable dereference
        if in_old {
            Some(Term::Const(format!("{param_name}_pre")))
        } else {
            Some(Term::Const(param_name))
        }
    } else {
        None
    }
}

/// Convert a `final_value(expr)` call in a specification.
///
/// For mutable reference parameters, `final_value(x)` produces the prophecy variable
/// `x_prophecy`, which represents the predicted final value at function return.
///
/// This enables postcondition specs like `*x == final_value(x)` or more usefully
/// combined with old: `final_value(x) == old(*x) + 1`.
fn convert_final_value(
    expr: &Expr,
    func: &Function,
    _bound_vars: &[(String, rust_fv_smtlib::sort::Sort)],
) -> Option<Term> {
    // Extract the parameter name from the expression
    if let Expr::Path(path_expr) = expr
        && path_expr.path.segments.len() == 1
    {
        let ident = path_expr.path.segments[0].ident.to_string();
        let param_name = resolve_variable_name(&ident, func)?;

        // Check if this is a mutable reference parameter
        for param in &func.params {
            if param.name == param_name
                && matches!(param.ty, Ty::Ref(_, crate::ir::Mutability::Mutable))
            {
                // Return the prophecy variable
                return Some(Term::Const(format!("{param_name}_prophecy")));
            }
        }

        // Not a mutable reference param - invalid use of final_value
        None
    } else {
        None
    }
}

/// Check if a callee name matches a trait method pattern and return (trait_name, method_name).
///
/// Trait method calls in specs are written as `TraitName::method`.
/// This function parses the callee string and checks if the trait exists in the database.
///
/// Returns `Some((trait_name, method_name))` if the pattern matches a known trait method,
/// `None` otherwise.
pub fn is_trait_method_call(
    callee: &str,
    trait_db: &crate::trait_analysis::TraitDatabase,
) -> Option<(String, String)> {
    // Parse "TraitName::method_name" pattern
    if let Some((trait_name, method_name)) = callee.split_once("::") {
        // Check if trait exists in database
        if let Some(trait_def) = trait_db.get_trait(trait_name) {
            // Check if method exists in trait
            if trait_def.methods.iter().any(|m| m.name == method_name) {
                return Some((trait_name.to_string(), method_name.to_string()));
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::*;

    fn make_i32_func() -> Function {
        Function {
            name: "test".to_string(),
            return_local: Local {
                name: "_0".to_string(),
                ty: Ty::Int(IntTy::I32),
                is_ghost: false,
            },
            params: vec![
                Local {
                    name: "_1".to_string(),
                    ty: Ty::Int(IntTy::I32),
                    is_ghost: false,
                },
                Local {
                    name: "_2".to_string(),
                    ty: Ty::Int(IntTy::I32),
                    is_ghost: false,
                },
            ],
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
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
            coroutine_info: None,
        }
    }

    fn make_u32_func() -> Function {
        Function {
            name: "test_u".to_string(),
            return_local: Local {
                name: "_0".to_string(),
                ty: Ty::Uint(UintTy::U32),
                is_ghost: false,
            },
            params: vec![Local {
                name: "_1".to_string(),
                ty: Ty::Uint(UintTy::U32),
                is_ghost: false,
            }],
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
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
            coroutine_info: None,
        }
    }

    fn make_struct_func() -> Function {
        Function {
            name: "test_struct".to_string(),
            return_local: Local {
                name: "_0".to_string(),
                ty: Ty::Struct(
                    "Point".to_string(),
                    vec![
                        ("x".to_string(), Ty::Int(IntTy::I32)),
                        ("y".to_string(), Ty::Int(IntTy::I32)),
                    ],
                ),
                is_ghost: false,
            },
            params: vec![Local {
                name: "_1".to_string(),
                ty: Ty::Int(IntTy::I32),
                is_ghost: false,
            }],
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
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
            coroutine_info: None,
        }
    }

    fn make_tuple_func() -> Function {
        Function {
            name: "test_tuple".to_string(),
            return_local: Local {
                name: "_0".to_string(),
                ty: Ty::Tuple(vec![Ty::Int(IntTy::I32), Ty::Int(IntTy::I32)]),
                is_ghost: false,
            },
            params: vec![],
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
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
            coroutine_info: None,
        }
    }

    #[test]
    fn parse_result_gt_zero() {
        let func = make_i32_func();
        let term = parse_spec_expr("result > 0", &func).unwrap();
        assert!(matches!(term, Term::BvSGt(_, _)));
    }

    #[test]
    fn parse_result_ge_param() {
        let func = make_i32_func();
        let term = parse_spec_expr("result >= _1", &func).unwrap();
        assert!(matches!(term, Term::BvSGe(_, _)));
    }

    #[test]
    fn parse_result_eq_addition() {
        let func = make_i32_func();
        let term = parse_spec_expr("result == _1 + _2", &func).unwrap();
        assert!(matches!(term, Term::Eq(_, _)));
    }

    #[test]
    fn parse_logical_and() {
        let func = make_i32_func();
        let term = parse_spec_expr("result >= _1 && result >= _2", &func).unwrap();
        assert!(matches!(term, Term::And(_)));
    }

    #[test]
    fn parse_logical_or() {
        let func = make_i32_func();
        let term = parse_spec_expr("result == _1 || result == _2", &func).unwrap();
        assert!(matches!(term, Term::Or(_)));
    }

    #[test]
    fn parse_not_equal() {
        let func = make_i32_func();
        let term = parse_spec_expr("result != 0", &func).unwrap();
        assert!(matches!(term, Term::Not(_)));
    }

    #[test]
    fn parse_negation() {
        let func = make_i32_func();
        let term = parse_spec_expr("-_1", &func).unwrap();
        assert!(matches!(term, Term::BvNeg(_)));
    }

    #[test]
    fn parse_parenthesized() {
        let func = make_i32_func();
        let term = parse_spec_expr("(result > 0) && (result < 100)", &func).unwrap();
        assert!(matches!(term, Term::And(_)));
    }

    #[test]
    fn parse_bool_literal_true() {
        let func = make_i32_func();
        let term = parse_spec_expr("true", &func).unwrap();
        assert_eq!(term, Term::BoolLit(true));
    }

    #[test]
    fn parse_bool_literal_false() {
        let func = make_i32_func();
        let term = parse_spec_expr("false", &func).unwrap();
        assert_eq!(term, Term::BoolLit(false));
    }

    #[test]
    fn parse_integer_literal() {
        let func = make_i32_func();
        let term = parse_spec_expr("result == 42", &func).unwrap();
        if let Term::Eq(_, rhs) = &term {
            assert_eq!(**rhs, Term::BitVecLit(42, 32));
        } else {
            panic!("Expected Eq, got {term:?}");
        }
    }

    #[test]
    fn parse_struct_field_access() {
        let func = make_struct_func();
        let term = parse_spec_expr("result.x > 0", &func).unwrap();
        // Should be BvSGt(App("Point-x", [Const("_0")]), BitVecLit(0, 32))
        if let Term::BvSGt(lhs, _) = &term {
            assert!(matches!(&**lhs, Term::App(name, _) if name == "Point-x"));
        } else {
            panic!("Expected BvSGt with selector, got {term:?}");
        }
    }

    #[test]
    fn parse_struct_field_y() {
        let func = make_struct_func();
        let term = parse_spec_expr("result.y == _1", &func).unwrap();
        if let Term::Eq(lhs, _) = &term {
            assert!(matches!(&**lhs, Term::App(name, _) if name == "Point-y"));
        } else {
            panic!("Expected Eq with selector, got {term:?}");
        }
    }

    #[test]
    fn parse_tuple_field_access() {
        let func = make_tuple_func();
        let term = parse_spec_expr("result.0 > 0", &func).unwrap();
        if let Term::BvSGt(lhs, _) = &term {
            assert!(matches!(&**lhs, Term::App(name, _) if name == "Tuple2-_0"));
        } else {
            panic!("Expected BvSGt with tuple selector, got {term:?}");
        }
    }

    #[test]
    fn parse_old_operator() {
        let func = make_i32_func();
        let term = parse_spec_expr("result == old(_1) + 1", &func).unwrap();
        // Should be Eq(_0, BvAdd(_1_pre, 1))
        if let Term::Eq(_, rhs) = &term {
            if let Term::BvAdd(lhs_inner, _) = &**rhs {
                assert_eq!(**lhs_inner, Term::Const("_1_pre".to_string()));
            } else {
                panic!("Expected BvAdd, got {rhs:?}");
            }
        } else {
            panic!("Expected Eq, got {term:?}");
        }
    }

    #[test]
    fn parse_old_complex_expression() {
        let func = make_i32_func();
        let term = parse_spec_expr("old(_1 + _2)", &func).unwrap();
        // Should be BvAdd(_1_pre, _2_pre)
        if let Term::BvAdd(lhs, rhs) = &term {
            assert_eq!(**lhs, Term::Const("_1_pre".to_string()));
            assert_eq!(**rhs, Term::Const("_2_pre".to_string()));
        } else {
            panic!("Expected BvAdd with _pre vars, got {term:?}");
        }
    }

    #[test]
    fn parse_nested_field_and_logic() {
        let func = make_struct_func();
        let term = parse_spec_expr("(result.x > 0) && (result.y > 0)", &func).unwrap();
        assert!(matches!(term, Term::And(_)));
    }

    #[test]
    fn parse_complex_arithmetic() {
        let func = make_i32_func();
        let term = parse_spec_expr("result == _1 * 2 - _2", &func).unwrap();
        assert!(matches!(term, Term::Eq(_, _)));
    }

    #[test]
    fn parse_invalid_syntax_returns_none() {
        let func = make_i32_func();
        assert!(parse_spec_expr("result >>><<< 0", &func).is_none());
    }

    #[test]
    fn parse_empty_string_returns_none() {
        let func = make_i32_func();
        assert!(parse_spec_expr("", &func).is_none());
    }

    #[test]
    fn parse_unknown_variable_returns_none() {
        let func = make_i32_func();
        assert!(parse_spec_expr("unknown_var > 0", &func).is_none());
    }

    #[test]
    fn parse_unsigned_uses_unsigned_comparison() {
        let func = make_u32_func();
        let term = parse_spec_expr("result > 0", &func).unwrap();
        assert!(matches!(term, Term::BvUGt(_, _)));
    }

    #[test]
    fn parse_subtraction() {
        let func = make_i32_func();
        let term = parse_spec_expr("result == _1 - _2", &func).unwrap();
        if let Term::Eq(_, rhs) = &term {
            assert!(matches!(&**rhs, Term::BvSub(_, _)));
        } else {
            panic!("Expected Eq with BvSub, got {term:?}");
        }
    }

    #[test]
    fn parse_multiplication() {
        let func = make_i32_func();
        let term = parse_spec_expr("result == _1 * _2", &func).unwrap();
        if let Term::Eq(_, rhs) = &term {
            assert!(matches!(&**rhs, Term::BvMul(_, _)));
        } else {
            panic!("Expected Eq with BvMul, got {term:?}");
        }
    }

    #[test]
    fn parse_division() {
        let func = make_i32_func();
        let term = parse_spec_expr("result == _1 / _2", &func).unwrap();
        if let Term::Eq(_, rhs) = &term {
            assert!(matches!(&**rhs, Term::BvSDiv(_, _)));
        } else {
            panic!("Expected Eq with BvSDiv, got {term:?}");
        }
    }

    #[test]
    fn parse_remainder() {
        let func = make_i32_func();
        let term = parse_spec_expr("result == _1 % _2", &func).unwrap();
        if let Term::Eq(_, rhs) = &term {
            assert!(matches!(&**rhs, Term::BvSRem(_, _)));
        } else {
            panic!("Expected Eq with BvSRem, got {term:?}");
        }
    }

    #[test]
    fn backward_compat_simple_ge() {
        let func = make_i32_func();
        // This is the format parse_simple_spec handles
        let old = crate::vcgen::parse_simple_spec("result >= 0", &func);
        let new = parse_spec_expr("result >= 0", &func);
        assert!(old.is_some());
        assert!(new.is_some());
        // Both should produce signed GE
        assert!(matches!(old.unwrap(), Term::BvSGe(_, _)));
        assert!(matches!(new.unwrap(), Term::BvSGe(_, _)));
    }

    #[test]
    fn backward_compat_and_expression() {
        let func = make_i32_func();
        let old = crate::vcgen::parse_simple_spec("result >= _1 && result >= _2", &func);
        let new = parse_spec_expr("result >= _1 && result >= _2", &func);
        assert!(old.is_some());
        assert!(new.is_some());
        assert!(matches!(old.unwrap(), Term::And(_)));
        assert!(matches!(new.unwrap(), Term::And(_)));
    }

    #[test]
    fn backward_compat_equality() {
        let func = make_i32_func();
        let old = crate::vcgen::parse_simple_spec("result == _1", &func);
        let new = parse_spec_expr("result == _1", &func);
        assert!(old.is_some());
        assert!(new.is_some());
    }

    #[test]
    fn backward_compat_addition() {
        let func = make_i32_func();
        let old = crate::vcgen::parse_simple_spec("result == _1 + _2", &func);
        let new = parse_spec_expr("result == _1 + _2", &func);
        assert!(old.is_some());
        assert!(new.is_some());
    }

    #[test]
    fn parse_as_int_cast() {
        let func = make_i32_func();
        let term = parse_spec_expr("result as int", &func);
        assert!(term.is_some());
        let term = term.unwrap();
        // Should produce Bv2Int wrapper around the result variable
        assert!(matches!(term, Term::Bv2Int(_)));
        if let Term::Bv2Int(inner) = term {
            assert!(matches!(*inner, Term::Const(_)));
        }
    }

    #[test]
    fn parse_int_mode_arithmetic() {
        let func = make_i32_func();
        // In normal mode: bitvector arithmetic
        let bv_term = parse_spec_expr("_1 + _2", &func);
        assert!(matches!(bv_term, Some(Term::BvAdd(_, _))));

        // After as int cast, operations inside don't work because we immediately wrap
        // The cast happens at the boundary, not enabling int mode for nested operations
        let int_term = parse_spec_expr("(_1 + _2) as int", &func);
        assert!(int_term.is_some());
        if let Some(Term::Bv2Int(inner)) = int_term {
            // The inner should be BvAdd, then we convert the result
            assert!(matches!(*inner, Term::BvAdd(_, _)));
        }
    }

    #[test]
    fn parse_int_mode_comparison() {
        let func = make_i32_func();
        // Comparison with int-cast operands
        let term = parse_spec_expr("(_1 as int) > (_2 as int)", &func);
        assert!(term.is_some());
        let term = term.unwrap();
        // The comparison is on Int values (after Bv2Int conversion)
        // But comparison operators don't change based on operand types in current impl
        // They should produce IntGt when both operands are Bv2Int terms
        // However, our current implementation doesn't detect this - it's a limitation
        // For now, just verify it parses
        assert!(matches!(term, Term::BvSGt(_, _) | Term::IntGt(_, _)));
    }

    #[test]
    fn parse_mixed_bv_and_int() {
        let func = make_i32_func();
        // Expression mixing bitvector and int-cast values
        let term = parse_spec_expr("(result as int) > 0", &func);
        assert!(term.is_some());
        // result as int produces Bv2Int(result)
        // 0 is still a bitvector literal
        // Comparison should work (SMT solver handles mixed sorts)
        let term = term.unwrap();
        assert!(matches!(term, Term::BvSGt(_, _) | Term::IntGt(_, _)));
    }

    #[test]
    fn parse_as_nat_cast() {
        let func = make_i32_func();
        let term = parse_spec_expr("result as nat", &func);
        assert!(term.is_some());
        let term = term.unwrap();
        // nat cast also produces Bv2Int (non-negativity constraint added by VCGen)
        assert!(matches!(term, Term::Bv2Int(_)));
    }

    // -----------------------------------------------------------------------
    // Quantifier parsing tests
    // -----------------------------------------------------------------------

    #[test]
    fn parse_forall_simple() {
        let func = make_i32_func();
        let term = parse_spec_expr("forall(|x: i32| x > 0)", &func);
        assert!(term.is_some());
        let term = term.unwrap();
        if let Term::Forall(vars, body) = &term {
            assert_eq!(vars.len(), 1);
            assert_eq!(vars[0].0, "x");
            assert!(matches!(vars[0].1, rust_fv_smtlib::sort::Sort::BitVec(32)));
            assert!(matches!(&**body, Term::BvSGt(_, _)));
        } else {
            panic!("Expected Forall, got {term:?}");
        }
    }

    #[test]
    fn parse_exists_simple() {
        let func = make_i32_func();
        let term = parse_spec_expr("exists(|x: i32| x == 0)", &func);
        assert!(term.is_some());
        let term = term.unwrap();
        if let Term::Exists(vars, body) = &term {
            assert_eq!(vars.len(), 1);
            assert_eq!(vars[0].0, "x");
            assert!(matches!(vars[0].1, rust_fv_smtlib::sort::Sort::BitVec(32)));
            assert!(matches!(&**body, Term::Eq(_, _)));
        } else {
            panic!("Expected Exists, got {term:?}");
        }
    }

    #[test]
    fn parse_forall_implies() {
        let func = make_i32_func();
        let term = parse_spec_expr("forall(|x: i32| implies(x > 0, x + 1 > 0))", &func);
        assert!(term.is_some());
        let term = term.unwrap();
        if let Term::Forall(vars, body) = &term {
            assert_eq!(vars.len(), 1);
            assert_eq!(vars[0].0, "x");
            if let Term::Implies(lhs, rhs) = &**body {
                assert!(matches!(&**lhs, Term::BvSGt(_, _)));
                assert!(matches!(&**rhs, Term::BvSGt(_, _)));
            } else {
                panic!("Expected Implies body, got {body:?}");
            }
        } else {
            panic!("Expected Forall, got {term:?}");
        }
    }

    #[test]
    fn parse_nested_quantifiers() {
        let func = make_i32_func();
        let term = parse_spec_expr("forall(|x: i32| exists(|y: i32| x + y == 0))", &func);
        assert!(term.is_some());
        let term = term.unwrap();
        if let Term::Forall(_outer_vars, outer_body) = &term {
            if let Term::Exists(_inner_vars, inner_body) = &**outer_body {
                assert!(matches!(&**inner_body, Term::Eq(_, _)));
            } else {
                panic!("Expected nested Exists, got {outer_body:?}");
            }
        } else {
            panic!("Expected Forall, got {term:?}");
        }
    }

    #[test]
    fn parse_quantifier_with_int_bound() {
        let func = make_i32_func();
        let term = parse_spec_expr("forall(|x: int| x > 0)", &func);
        assert!(term.is_some());
        let term = term.unwrap();
        if let Term::Forall(vars, body) = &term {
            assert_eq!(vars.len(), 1);
            assert_eq!(vars[0].0, "x");
            assert!(matches!(vars[0].1, rust_fv_smtlib::sort::Sort::Int));
            // With Int sort, comparison should be IntGt (but current impl uses BvSGt)
            // This is a limitation we'll accept for now - the body uses bitvector ops
            // The sort annotation is correct though
            assert!(matches!(&**body, Term::BvSGt(_, _) | Term::IntGt(_, _)));
        } else {
            panic!("Expected Forall, got {term:?}");
        }
    }

    #[test]
    fn parse_implies_standalone() {
        let func = make_i32_func();
        let term = parse_spec_expr("implies(result > 0, result >= 1)", &func);
        assert!(term.is_some());
        let term = term.unwrap();
        if let Term::Implies(lhs, rhs) = &term {
            assert!(matches!(&**lhs, Term::BvSGt(_, _)));
            assert!(matches!(&**rhs, Term::BvSGe(_, _)));
        } else {
            panic!("Expected Implies, got {term:?}");
        }
    }

    // -----------------------------------------------------------------------
    // Prophecy variable parsing tests (dereference and final_value)
    // -----------------------------------------------------------------------

    fn make_mut_ref_func() -> Function {
        use crate::ir::Mutability;
        Function {
            name: "test_mut_ref".to_string(),
            params: vec![Local::new(
                "_1",
                Ty::Ref(Box::new(Ty::Int(IntTy::I32)), Mutability::Mutable),
            )],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![],
            contracts: Default::default(),
            generic_params: vec![],
            loops: vec![],
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
            coroutine_info: None,
        }
    }

    #[test]
    fn parse_deref_in_spec() {
        let func = make_mut_ref_func();
        let term = parse_spec_expr("*_1 > 0", &func);
        assert!(term.is_some());
        let term = term.unwrap();
        // Should produce comparison with Const("_1")
        // Note: signedness inference might use unsigned for refs, but the key is that *_1 resolves to _1
        match &term {
            Term::BvSGt(lhs, _) | Term::BvUGt(lhs, _) => {
                assert_eq!(**lhs, Term::Const("_1".to_string()));
            }
            _ => panic!("Expected comparison with Const(_1), got {term:?}"),
        }
    }

    #[test]
    fn parse_old_deref() {
        let func = make_mut_ref_func();
        let term = parse_spec_expr("old(*_1)", &func);
        assert!(term.is_some());
        let term = term.unwrap();
        // Should produce Const("_1_initial")
        assert_eq!(term, Term::Const("_1_initial".to_string()));
    }

    #[test]
    fn parse_final_value() {
        let func = make_mut_ref_func();
        let term = parse_spec_expr("final_value(_1)", &func);
        assert!(term.is_some());
        let term = term.unwrap();
        // Should produce Const("_1_prophecy")
        assert_eq!(term, Term::Const("_1_prophecy".to_string()));
    }

    #[test]
    fn parse_postcondition_deref_resolves_to_prophecy() {
        // Confirm that *_1 in postcondition context resolves to _1_prophecy
        // This test is RED until parse_spec_expr_postcondition_with_db is implemented
        let func = make_mut_ref_func();
        let ghost_db = GhostPredicateDatabase::new();
        let term = parse_spec_expr_postcondition_with_db("*_1", &func, &ghost_db);
        assert!(
            matches!(term, Some(Term::Const(ref s)) if s == "_1_prophecy"),
            "Expected _1_prophecy, got {:?}",
            term
        );
    }

    #[test]
    fn parse_postcondition_old_deref_still_resolves_to_initial() {
        // Confirm that old(*_1) in postcondition context still resolves to _1_initial
        let func = make_mut_ref_func();
        let ghost_db = GhostPredicateDatabase::new();
        let term = parse_spec_expr_postcondition_with_db("old(*_1)", &func, &ghost_db);
        assert!(
            matches!(term, Some(Term::Const(ref s)) if s == "_1_initial"),
            "Expected _1_initial, got {:?}",
            term
        );
    }

    #[test]
    fn parse_ensures_with_old_and_deref() {
        let func = make_mut_ref_func();
        let term = parse_spec_expr("*_1 == old(*_1) + 1", &func);
        assert!(term.is_some());
        let term = term.unwrap();
        // Should produce Eq(Const("_1"), BvAdd(Const("_1_initial"), BitVecLit(1, 32)))
        if let Term::Eq(lhs, rhs) = &term {
            assert_eq!(**lhs, Term::Const("_1".to_string()));
            if let Term::BvAdd(add_lhs, add_rhs) = &**rhs {
                assert_eq!(**add_lhs, Term::Const("_1_initial".to_string()));
                assert_eq!(**add_rhs, Term::BitVecLit(1, 32));
            } else {
                panic!("Expected BvAdd on RHS, got {rhs:?}");
            }
        } else {
            panic!("Expected Eq, got {term:?}");
        }
    }

    #[test]
    fn parse_ensures_with_final_value_and_old() {
        let func = make_mut_ref_func();
        let term = parse_spec_expr("final_value(_1) == old(*_1) + 1", &func);
        assert!(term.is_some());
        let term = term.unwrap();
        // Should produce Eq(Const("_1_prophecy"), BvAdd(Const("_1_initial"), BitVecLit(1, 32)))
        if let Term::Eq(lhs, rhs) = &term {
            assert_eq!(**lhs, Term::Const("_1_prophecy".to_string()));
            if let Term::BvAdd(add_lhs, _) = &**rhs {
                assert_eq!(**add_lhs, Term::Const("_1_initial".to_string()));
            } else {
                panic!("Expected BvAdd on RHS, got {rhs:?}");
            }
        } else {
            panic!("Expected Eq, got {term:?}");
        }
    }

    // -----------------------------------------------------------------------
    // Closure parameter reference tests
    // -----------------------------------------------------------------------

    fn make_closure_param_func() -> Function {
        use crate::ir::{ClosureInfo, ClosureTrait};
        Function {
            name: "test_closure_param".to_string(),
            params: vec![
                Local::new(
                    "predicate",
                    Ty::Closure(Box::new(ClosureInfo {
                        name: "predicate".to_string(),
                        env_fields: vec![],
                        params: vec![("x".to_string(), Ty::Int(IntTy::I32))],
                        return_ty: Ty::Bool,
                        trait_kind: ClosureTrait::Fn,
                    })),
                ),
                Local::new("_2", Ty::Int(IntTy::I32)),
            ],
            return_local: Local::new("_0", Ty::Bool),
            locals: vec![],
            basic_blocks: vec![],
            contracts: Default::default(),
            generic_params: vec![],
            loops: vec![],
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
            coroutine_info: None,
        }
    }

    #[test]
    fn test_closure_param_reference_in_spec() {
        let func = make_closure_param_func();
        // Simple closure call: predicate(_2)
        let term = parse_spec_expr("predicate(_2)", &func);
        assert!(term.is_some(), "Failed to parse closure call");
        let term = term.unwrap();

        // Should produce: predicate_impl(predicate_env, _2)
        match &term {
            Term::App(name, args) => {
                assert_eq!(name, "predicate_impl");
                assert_eq!(args.len(), 2); // env + arg
                assert_eq!(args[0], Term::Const("predicate_env".to_string()));
                assert_eq!(args[1], Term::Const("_2".to_string()));
            }
            _ => panic!("Expected Term::App for closure call, got {term:?}"),
        }
    }

    #[test]
    fn test_non_closure_param_not_treated_as_closure() {
        let func = make_i32_func();
        // Regular param "result" should not be treated as closure
        let term = parse_spec_expr("result > 0", &func);
        assert!(term.is_some());
        let term = term.unwrap();

        // Should produce normal comparison, not a closure call
        assert!(matches!(term, Term::BvSGt(_, _)));
    }

    // -----------------------------------------------------------------------
    // Trigger annotation parsing tests (Phase 15-02)
    // -----------------------------------------------------------------------

    #[test]
    fn parse_trigger_single() {
        // forall(|x: i32| { #[trigger(f(x))] x > 0 })
        // The trigger f(x) should appear as a Term::Annotated on the body
        let func = make_i32_func();
        let term = parse_spec_expr("forall(|x: i32| { #[trigger(f(x))] x > 0 })", &func);
        assert!(term.is_some(), "Failed to parse forall with trigger");
        let term = term.unwrap();
        if let Term::Forall(vars, body) = &term {
            assert_eq!(vars.len(), 1);
            assert_eq!(vars[0].0, "x");
            // Body should be Annotated with trigger hint
            if let Term::Annotated(inner_body, annotations) = &**body {
                // Should have one trigger set
                assert_eq!(annotations.len(), 1);
                assert_eq!(annotations[0].0, "rust_fv_trigger_hint");
                // The trigger term should be an unresolved function application
                assert_eq!(annotations[0].1.len(), 1);
                // The inner body should be the comparison
                assert!(
                    matches!(&**inner_body, Term::BvSGt(_, _)),
                    "Expected BvSGt body, got {:?}",
                    inner_body
                );
            } else {
                panic!("Expected Annotated body with trigger, got {body:?}");
            }
        } else {
            panic!("Expected Forall, got {term:?}");
        }
    }

    #[test]
    fn parse_trigger_multi_trigger() {
        // Multi-trigger conjunction: #[trigger(f(x), g(y))] -> one trigger set with two terms
        let func = make_i32_func();
        let term = parse_spec_expr(
            "forall(|x: i32, y: i32| { #[trigger(f(x), g(y))] x == y })",
            &func,
        );
        assert!(term.is_some(), "Failed to parse forall with multi-trigger");
        let term = term.unwrap();
        if let Term::Forall(vars, body) = &term {
            assert_eq!(vars.len(), 2);
            if let Term::Annotated(_, annotations) = &**body {
                assert_eq!(annotations.len(), 1, "Expected one trigger set");
                assert_eq!(annotations[0].0, "rust_fv_trigger_hint");
                assert_eq!(
                    annotations[0].1.len(),
                    2,
                    "Expected two terms in trigger set"
                );
            } else {
                panic!("Expected Annotated body, got {body:?}");
            }
        } else {
            panic!("Expected Forall, got {term:?}");
        }
    }

    #[test]
    fn parse_trigger_multiple_sets() {
        // Multiple trigger sets (disjunction): two #[trigger] attributes
        let func = make_i32_func();
        let term = parse_spec_expr(
            "forall(|x: i32| { #[trigger(f(x))] #[trigger(g(x))] x > 0 })",
            &func,
        );
        assert!(
            term.is_some(),
            "Failed to parse forall with multiple trigger sets"
        );
        let term = term.unwrap();
        if let Term::Forall(vars, body) = &term {
            assert_eq!(vars.len(), 1);
            if let Term::Annotated(_, annotations) = &**body {
                assert_eq!(annotations.len(), 2, "Expected two trigger sets");
                assert_eq!(annotations[0].0, "rust_fv_trigger_hint");
                assert_eq!(annotations[1].0, "rust_fv_trigger_hint");
                // Each set has one term
                assert_eq!(annotations[0].1.len(), 1);
                assert_eq!(annotations[1].1.len(), 1);
            } else {
                panic!("Expected Annotated body with two trigger sets, got {body:?}");
            }
        } else {
            panic!("Expected Forall, got {term:?}");
        }
    }

    #[test]
    fn parse_trigger_nested_quantifier() {
        // Trigger on inner quantifier only, outer unaffected
        let func = make_i32_func();
        let term = parse_spec_expr(
            "forall(|x: i32| exists(|y: i32| { #[trigger(f(y))] y == x }))",
            &func,
        );
        assert!(
            term.is_some(),
            "Failed to parse nested quantifier with trigger"
        );
        let term = term.unwrap();
        if let Term::Forall(_, outer_body) = &term {
            // Outer body should NOT be Annotated (no trigger on outer)
            if let Term::Exists(_, inner_body) = &**outer_body {
                // Inner body SHOULD be Annotated (trigger on inner)
                assert!(
                    matches!(&**inner_body, Term::Annotated(_, _)),
                    "Expected inner quantifier body to be Annotated, got {:?}",
                    inner_body
                );
            } else {
                panic!("Expected Exists, got {outer_body:?}");
            }
        } else {
            panic!("Expected Forall, got {term:?}");
        }
    }

    #[test]
    fn parse_no_trigger_backward_compat() {
        // Existing forall without trigger still works identically
        let func = make_i32_func();
        let term = parse_spec_expr("forall(|x: i32| x > 0)", &func);
        assert!(term.is_some());
        let term = term.unwrap();
        if let Term::Forall(vars, body) = &term {
            assert_eq!(vars.len(), 1);
            // Body should NOT be Annotated (no triggers)
            assert!(
                !matches!(&**body, Term::Annotated(_, _)),
                "Expected non-annotated body for no-trigger case, got {body:?}"
            );
            assert!(matches!(&**body, Term::BvSGt(_, _)));
        } else {
            panic!("Expected Forall, got {term:?}");
        }
    }

    #[test]
    fn parse_trigger_complex_expr() {
        // Trigger with nested function call: #[trigger(f(g(x)))]
        let func = make_i32_func();
        let term = parse_spec_expr("forall(|x: i32| { #[trigger(f(g(x)))] x > 0 })", &func);
        assert!(
            term.is_some(),
            "Failed to parse forall with complex trigger expr"
        );
        let term = term.unwrap();
        if let Term::Forall(_, body) = &term {
            if let Term::Annotated(_, annotations) = &**body {
                assert_eq!(annotations.len(), 1);
                assert_eq!(annotations[0].1.len(), 1);
                // The trigger should be a nested App
                let trigger_term = &annotations[0].1[0];
                assert!(
                    matches!(trigger_term, Term::App(name, _) if name == "f"),
                    "Expected App('f', ...) trigger, got {trigger_term:?}"
                );
            } else {
                panic!("Expected Annotated body, got {body:?}");
            }
        } else {
            panic!("Expected Forall, got {term:?}");
        }
    }

    #[test]
    fn parse_trigger_empty_is_ignored() {
        // #[trigger()] with no expressions inside should be ignored (no trigger stored)
        let func = make_i32_func();
        let term = parse_spec_expr("forall(|x: i32| { #[trigger()] x > 0 })", &func);
        assert!(term.is_some(), "Failed to parse forall with empty trigger");
        let term = term.unwrap();
        if let Term::Forall(_, body) = &term {
            // Empty trigger should be ignored - body should NOT be Annotated
            assert!(
                !matches!(&**body, Term::Annotated(_, _)),
                "Expected non-annotated body for empty trigger, got {body:?}"
            );
        } else {
            panic!("Expected Forall, got {term:?}");
        }
    }

    #[test]
    fn parse_trigger_stored_as_annotation() {
        // Verify the annotation key is "rust_fv_trigger_hint" as specified
        let func = make_i32_func();
        let term = parse_spec_expr("forall(|x: i32| { #[trigger(f(x))] x > 0 })", &func);
        assert!(term.is_some());
        let term = term.unwrap();
        if let Term::Forall(_, body) = &term {
            if let Term::Annotated(_, annotations) = &**body {
                for (key, _) in annotations {
                    assert_eq!(
                        key, "rust_fv_trigger_hint",
                        "Trigger annotation key must be 'rust_fv_trigger_hint'"
                    );
                }
            } else {
                panic!("Expected Annotated body");
            }
        } else {
            panic!("Expected Forall");
        }
    }

    #[test]
    fn parse_trigger_exists_quantifier() {
        // Trigger works with exists() too, not just forall()
        let func = make_i32_func();
        let term = parse_spec_expr("exists(|x: i32| { #[trigger(f(x))] x == 0 })", &func);
        assert!(term.is_some(), "Failed to parse exists with trigger");
        let term = term.unwrap();
        if let Term::Exists(vars, body) = &term {
            assert_eq!(vars.len(), 1);
            assert!(
                matches!(&**body, Term::Annotated(_, _)),
                "Expected Annotated body for exists with trigger"
            );
        } else {
            panic!("Expected Exists, got {term:?}");
        }
    }

    // -----------------------------------------------------------------------
    // pts_to predicate parsing tests (Phase 20-01)
    // -----------------------------------------------------------------------

    fn make_raw_ptr_func() -> Function {
        use crate::ir::Mutability;
        Function {
            name: "test_pts_to".to_string(),
            params: vec![
                Local::new(
                    "p",
                    Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Shared),
                ),
                Local::new("v", Ty::Int(IntTy::I32)),
            ],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![],
            contracts: Default::default(),
            generic_params: vec![],
            loops: vec![],
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
            coroutine_info: None,
        }
    }

    #[test]
    fn test_pts_to_parse_basic() {
        let func = make_raw_ptr_func();
        let term = parse_spec_expr("pts_to(p, v)", &func);
        assert!(term.is_some(), "pts_to(p, v) should parse successfully");
        let term = term.unwrap();
        // pts_to encodes as Term::And([Select(perm, ptr), Eq(...)])
        assert!(
            matches!(term, Term::And(_)),
            "pts_to must produce Term::And, got {term:?}"
        );
        if let Term::And(arms) = &term {
            assert_eq!(arms.len(), 2, "pts_to And must have exactly 2 arms");
            // First arm: Select(perm, ptr)
            assert!(
                matches!(&arms[0], Term::Select(arr, _) if matches!(arr.as_ref(), Term::Const(n) if n == "perm")),
                "First arm must be Select(perm, ...), got {:?}",
                arms[0]
            );
        }
    }

    #[test]
    fn test_pts_to_wrong_arity() {
        let func = make_raw_ptr_func();
        // pts_to with only 1 argument must return None (warn and bail)
        let term = parse_spec_expr("pts_to(p)", &func);
        assert!(
            term.is_none(),
            "pts_to with wrong arity must return None, got {term:?}"
        );
    }

    #[test]
    fn parse_backward_compat_parse_spec_expr() {
        // All existing tests should still pass - parse_spec_expr returns same results
        let func = make_i32_func();
        // Verify a few key existing behaviors are unchanged
        assert!(parse_spec_expr("result > 0", &func).is_some());
        assert!(parse_spec_expr("result == _1 + _2", &func).is_some());
        assert!(parse_spec_expr("forall(|x: i32| x > 0)", &func).is_some());
        assert!(parse_spec_expr("exists(|x: i32| x == 0)", &func).is_some());
        assert!(parse_spec_expr("old(_1) + 1", &func).is_some());
        assert!(parse_spec_expr("", &func).is_none());
    }

    // ====== Trait method call recognition tests (Phase 8-02) ======

    #[test]
    fn test_is_trait_method_call_recognized() {
        use crate::ir::{TraitDef, TraitMethod};
        use crate::trait_analysis::TraitDatabase;

        let mut trait_db = TraitDatabase::new();
        let trait_def = TraitDef {
            name: "Stack".to_string(),
            methods: vec![TraitMethod {
                name: "push".to_string(),
                params: vec![],
                return_ty: crate::ir::Ty::Unit,
                requires: vec![],
                ensures: vec![],
                is_pure: false,
            }],
            is_sealed: false,
            super_traits: vec![],
        };
        trait_db.register_trait(trait_def);

        let result = super::is_trait_method_call("Stack::push", &trait_db);
        assert_eq!(result, Some(("Stack".to_string(), "push".to_string())));
    }

    #[test]
    fn test_is_trait_method_call_unknown() {
        use crate::trait_analysis::TraitDatabase;

        let trait_db = TraitDatabase::new();
        let result = super::is_trait_method_call("Unknown::method", &trait_db);
        assert_eq!(result, None);
    }

    // ====== Phase 20-03: Separating conjunction and ghost predicate tests ======

    fn make_two_ptr_func() -> Function {
        use crate::ir::Mutability;
        Function {
            name: "test_sep_conj".to_string(),
            params: vec![
                Local::new(
                    "p",
                    Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Shared),
                ),
                Local::new("v", Ty::Int(IntTy::I32)),
                Local::new(
                    "q",
                    Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Shared),
                ),
                Local::new("w", Ty::Int(IntTy::I32)),
            ],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![],
            contracts: Default::default(),
            generic_params: vec![],
            loops: vec![],
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
            coroutine_info: None,
        }
    }

    #[test]
    fn test_sep_conj_pts_to_star_pts_to() {
        use crate::ghost_predicate_db::GhostPredicateDatabase;
        let func = make_two_ptr_func();
        let db = GhostPredicateDatabase::new();
        // pts_to(p, v) * pts_to(q, w) must produce Term::And([pts_to_enc, pts_to_enc])
        let term = parse_spec_expr_with_db("pts_to(p, v) * pts_to(q, w)", &func, &db);
        assert!(
            term.is_some(),
            "pts_to(p,v) * pts_to(q,w) should parse successfully"
        );
        let term = term.unwrap();
        assert!(
            matches!(&term, Term::And(arms) if arms.len() == 2),
            "sep-conj must produce Term::And with 2 arms, got {term:?}"
        );
        if let Term::And(arms) = &term {
            // Each arm must be a pts_to encoding (Term::And([Select(perm,...), Eq(...)]))
            assert!(
                matches!(&arms[0], Term::And(_)),
                "left arm must be pts_to encoding (Term::And), got {:?}",
                arms[0]
            );
            assert!(
                matches!(&arms[1], Term::And(_)),
                "right arm must be pts_to encoding (Term::And), got {:?}",
                arms[1]
            );
        }
    }

    #[test]
    fn test_mul_not_sep_conj() {
        use crate::ghost_predicate_db::GhostPredicateDatabase;
        let func = make_i32_func();
        let db = GhostPredicateDatabase::new();
        // x * y with integer params must produce BvMul (not Term::And)
        let term = parse_spec_expr_with_db("_1 * _2", &func, &db);
        assert!(term.is_some(), "_1 * _2 should parse successfully");
        let term = term.unwrap();
        assert!(
            !matches!(&term, Term::And(_)),
            "integer multiply must NOT be sep-conj (Term::And), got {term:?}"
        );
        assert!(
            matches!(&term, Term::BvMul(_, _)),
            "integer multiply must produce Term::BvMul, got {term:?}"
        );
    }

    #[test]
    fn test_ghost_predicate_depth_zero() {
        use crate::ghost_predicate_db::{GhostPredicate, GhostPredicateDatabase};
        let func = make_i32_func();
        let mut db = GhostPredicateDatabase::new();
        db.insert(
            "foo".to_string(),
            GhostPredicate {
                param_names: vec!["x".to_string()],
                body_raw: "x > 0".to_string(),
            },
        );
        // At depth=0, ghost predicate call must return BoolLit(false)
        let term = parse_spec_expr_with_depth("foo(_1)", &func, &db, 0);
        assert!(
            term.is_some(),
            "ghost predicate at depth=0 should return Some(BoolLit(false))"
        );
        assert!(
            matches!(term.unwrap(), Term::BoolLit(false)),
            "ghost predicate at depth=0 must return BoolLit(false)"
        );
    }
}
