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

use crate::ir::{Function, Ty};

/// Parse a specification expression string into an SMT Term.
///
/// Returns `None` if the expression cannot be parsed or contains unsupported syntax.
/// This parser is a superset of `parse_simple_spec` -- all expressions that worked
/// with the old parser also work here.
pub fn parse_spec_expr(spec: &str, func: &Function) -> Option<Term> {
    let spec = spec.trim();
    if spec.is_empty() {
        return None;
    }

    // Parse the spec string as a Rust expression via syn
    let expr: Expr = syn::parse_str(spec).ok()?;

    convert_expr(&expr, func, false)
}

/// Parse a specification expression with old()-state renaming.
///
/// When `in_old` is true, all variable references are suffixed with `_pre`.
fn convert_expr(expr: &Expr, func: &Function, in_old: bool) -> Option<Term> {
    match expr {
        Expr::Lit(lit_expr) => convert_lit(&lit_expr.lit, func),

        Expr::Path(path_expr) => convert_path(path_expr, func, in_old),

        Expr::Binary(bin_expr) => {
            let left = convert_expr(&bin_expr.left, func, in_old)?;
            let right = convert_expr(&bin_expr.right, func, in_old)?;
            convert_binop(&bin_expr.op, left, right, func)
        }

        Expr::Unary(unary_expr) => {
            let inner = convert_expr(&unary_expr.expr, func, in_old)?;
            convert_unop(&unary_expr.op, inner, func)
        }

        Expr::Paren(paren_expr) => convert_expr(&paren_expr.expr, func, in_old),

        Expr::Field(field_expr) => convert_field_access(field_expr, func, in_old),

        Expr::Call(call_expr) => convert_call(call_expr, func, in_old),

        Expr::MethodCall(method_expr) => convert_method_call(method_expr, func, in_old),

        _ => None, // Unsupported expression kind
    }
}

/// Convert a literal expression to an SMT Term.
fn convert_lit(lit: &Lit, func: &Function) -> Option<Term> {
    match lit {
        Lit::Int(int_lit) => {
            let value: i128 = int_lit.base10_parse().ok()?;
            // Determine bit width from function context (return type or default 32)
            let width = func.return_local.ty.bit_width().unwrap_or(32);
            Some(Term::BitVecLit(value, width))
        }
        Lit::Bool(bool_lit) => Some(Term::BoolLit(bool_lit.value)),
        _ => None, // Unsupported literal type
    }
}

/// Convert a path expression (variable reference) to an SMT Term.
fn convert_path(path: &syn::ExprPath, func: &Function, in_old: bool) -> Option<Term> {
    // Must be a simple single-segment path (no :: separators)
    if path.path.segments.len() != 1 {
        return None;
    }

    let ident = path.path.segments[0].ident.to_string();

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
            // Check if it matches a param, local, or return local
            let name = resolve_variable_name(&ident, func)?;
            if in_old {
                Some(Term::Const(format!("{name}_pre")))
            } else {
                Some(Term::Const(name))
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
fn convert_binop(op: &SynBinOp, left: Term, right: Term, func: &Function) -> Option<Term> {
    let l = Box::new(left.clone());
    let r = Box::new(right.clone());

    match op {
        // Arithmetic
        SynBinOp::Add(_) => Some(Term::BvAdd(l, r)),
        SynBinOp::Sub(_) => Some(Term::BvSub(l, r)),
        SynBinOp::Mul(_) => Some(Term::BvMul(l, r)),
        SynBinOp::Div(_) => {
            let signed = infer_signedness(func);
            if signed {
                Some(Term::BvSDiv(l, r))
            } else {
                Some(Term::BvUDiv(l, r))
            }
        }
        SynBinOp::Rem(_) => {
            let signed = infer_signedness(func);
            if signed {
                Some(Term::BvSRem(l, r))
            } else {
                Some(Term::BvURem(l, r))
            }
        }

        // Comparison
        SynBinOp::Eq(_) => Some(Term::Eq(l, r)),
        SynBinOp::Ne(_) => Some(Term::Not(Box::new(Term::Eq(l, r)))),
        SynBinOp::Gt(_) => {
            let signed = infer_signedness_from_terms(func, &left, &right);
            if signed {
                Some(Term::BvSGt(l, r))
            } else {
                Some(Term::BvUGt(l, r))
            }
        }
        SynBinOp::Lt(_) => {
            let signed = infer_signedness_from_terms(func, &left, &right);
            if signed {
                Some(Term::BvSLt(l, r))
            } else {
                Some(Term::BvULt(l, r))
            }
        }
        SynBinOp::Ge(_) => {
            let signed = infer_signedness_from_terms(func, &left, &right);
            if signed {
                Some(Term::BvSGe(l, r))
            } else {
                Some(Term::BvUGe(l, r))
            }
        }
        SynBinOp::Le(_) => {
            let signed = infer_signedness_from_terms(func, &left, &right);
            if signed {
                Some(Term::BvSLe(l, r))
            } else {
                Some(Term::BvULe(l, r))
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
) -> Option<Term> {
    let base = convert_expr(&field_expr.base, func, in_old)?;

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

/// Convert a function call expression (handles `old()` operator).
fn convert_call(call_expr: &syn::ExprCall, func: &Function, _in_old: bool) -> Option<Term> {
    // Check if this is old(expr) call
    if let Expr::Path(path) = &*call_expr.func
        && path.path.segments.len() == 1
        && path.path.segments[0].ident == "old"
    {
        // old() operator: parse the inner expression with in_old=true
        if call_expr.args.len() != 1 {
            return None; // old() takes exactly one argument
        }
        return convert_expr(&call_expr.args[0], func, true);
    }

    // Not a known function call
    None
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
            },
            params: vec![
                Local {
                    name: "_1".to_string(),
                    ty: Ty::Int(IntTy::I32),
                },
                Local {
                    name: "_2".to_string(),
                    ty: Ty::Int(IntTy::I32),
                },
            ],
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            loops: vec![],
        }
    }

    fn make_u32_func() -> Function {
        Function {
            name: "test_u".to_string(),
            return_local: Local {
                name: "_0".to_string(),
                ty: Ty::Uint(UintTy::U32),
            },
            params: vec![Local {
                name: "_1".to_string(),
                ty: Ty::Uint(UintTy::U32),
            }],
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            loops: vec![],
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
            },
            params: vec![Local {
                name: "_1".to_string(),
                ty: Ty::Int(IntTy::I32),
            }],
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            loops: vec![],
        }
    }

    fn make_tuple_func() -> Function {
        Function {
            name: "test_tuple".to_string(),
            return_local: Local {
                name: "_0".to_string(),
                ty: Ty::Tuple(vec![Ty::Int(IntTy::I32), Ty::Int(IntTy::I32)]),
            },
            params: vec![],
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            loops: vec![],
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
}
