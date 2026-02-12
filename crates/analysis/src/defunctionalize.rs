//! Defunctionalization transformation for closures.
//!
//! Implements Reynolds (1972) defunctionalization pattern adapted for Rust closures:
//! - Transforms higher-order closure calls into first-order function calls
//! - Encodes closure environments as SMT datatypes
//! - Handles Fn/FnMut/FnOnce trait distinctions
//!
//! ## Pattern
//!
//! Given a closure with captured variables:
//! ```rust
//! let x = 5;
//! let add = |y| x + y;  // Captures x
//! let result = add(3);
//! ```
//!
//! Defunctionalization produces:
//! 1. Environment datatype: `(declare-datatype ClosureEnv_add ((mk-ClosureEnv_add (x Int))))`
//! 2. First-order function: `(define-fun add_impl ((env ClosureEnv_add) (y Int)) Int (+ (x env) y))`
//! 3. Defunctionalized call: `(add_impl env #x00000003)`

use rust_fv_smtlib::command::Command;
use rust_fv_smtlib::sort::Sort;
use rust_fv_smtlib::term::Term;

use crate::encode_sort::encode_type;
use crate::ir::{ClosureInfo, ClosureTrait, Operand};

/// Encoding of a closure after defunctionalization.
#[derive(Debug, Clone)]
pub struct ClosureEncoding {
    /// SMT datatype name for the closure environment (e.g., "ClosureEnv_add")
    pub env_datatype_name: String,
    /// Environment constructor name (e.g., "mk-ClosureEnv_add")
    pub env_constructor: String,
    /// Field selectors with their sorts: (selector_name, field_sort)
    pub env_selectors: Vec<(String, Sort)>,
    /// First-order function name (e.g., "add_impl")
    pub defunctionalized_name: String,
    /// Parameter sorts: [env_sort, param1_sort, param2_sort, ...]
    pub param_sorts: Vec<Sort>,
    /// Return type sort
    pub return_sort: Sort,
    /// Closure trait kind (Fn/FnMut/FnOnce)
    pub trait_kind: ClosureTrait,
}

/// Defunctionalize a closure call into first-order encoding.
///
/// Takes a closure's type information and produces the encoding structure
/// needed to represent it in SMT as a first-order function with explicit
/// environment parameter.
pub fn defunctionalize_closure_call(info: &ClosureInfo, _call_args: &[Operand]) -> ClosureEncoding {
    let env_datatype_name = info.name.clone();
    let env_constructor = format!("mk-{}", info.name);
    let defunctionalized_name = format!("{}_impl", info.name);

    // Build environment field selectors
    let mut env_selectors = Vec::new();
    for (field_name, field_ty) in &info.env_fields {
        let selector_name = format!("{}-{}", info.name, field_name);
        let field_sort = encode_type(field_ty);
        env_selectors.push((selector_name, field_sort));
    }

    // Build parameter sorts: [env_datatype, param_types...]
    let mut param_sorts = vec![Sort::Datatype(env_datatype_name.clone())];
    for (_param_name, param_ty) in &info.params {
        param_sorts.push(encode_type(param_ty));
    }

    let return_sort = encode_type(&info.return_ty);

    ClosureEncoding {
        env_datatype_name,
        env_constructor,
        env_selectors,
        defunctionalized_name,
        param_sorts,
        return_sort,
        trait_kind: info.trait_kind,
    }
}

/// Build SMT function definition for a closure.
///
/// Generates `(define-fun name ((env EnvSort) (p1 S1) ...) RetSort body_term)`.
/// For FnMut closures, prophecy variables for mutable captures should be
/// added by the caller.
pub fn build_closure_function_body(encoding: &ClosureEncoding, _body_term: Term) -> Vec<Command> {
    // For now, we generate a declare-fun (uninterpreted function)
    // The actual body encoding happens in vcgen when we have the closure definition
    vec![Command::DeclareFun(
        encoding.defunctionalized_name.clone(),
        encoding.param_sorts.clone(),
        encoding.return_sort.clone(),
    )]
}

/// Encode a closure call as a first-order function application.
///
/// Returns `(closure_impl env arg1 arg2 ...)` term.
pub fn encode_closure_call_term(
    encoding: &ClosureEncoding,
    env_term: Term,
    arg_terms: Vec<Term>,
) -> Term {
    let mut all_args = vec![env_term];
    all_args.extend(arg_terms);
    Term::App(encoding.defunctionalized_name.clone(), all_args)
}

/// Encode a closure as an uninterpreted function.
///
/// Used when the closure body is not visible (e.g., closure passed as parameter).
/// Generates `(declare-fun closure_impl (env_sort param_sorts...) return_sort)`.
pub fn encode_closure_as_uninterpreted(info: &ClosureInfo) -> Vec<Command> {
    let encoding = defunctionalize_closure_call(info, &[]);
    vec![Command::DeclareFun(
        encoding.defunctionalized_name,
        encoding.param_sorts,
        encoding.return_sort,
    )]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{IntTy, Ty};

    #[test]
    fn test_defunctionalize_fn_closure() {
        // Closure: |z: i32| -> i32 with env { x: i32, y: i32 }
        let info = ClosureInfo {
            name: "closure_add".to_string(),
            env_fields: vec![
                ("x".to_string(), Ty::Int(IntTy::I32)),
                ("y".to_string(), Ty::Int(IntTy::I32)),
            ],
            params: vec![("z".to_string(), Ty::Int(IntTy::I32))],
            return_ty: Ty::Int(IntTy::I32),
            trait_kind: ClosureTrait::Fn,
        };

        let encoding = defunctionalize_closure_call(&info, &[]);

        assert_eq!(encoding.env_datatype_name, "closure_add");
        assert_eq!(encoding.env_constructor, "mk-closure_add");
        assert_eq!(encoding.defunctionalized_name, "closure_add_impl");
        assert_eq!(encoding.trait_kind, ClosureTrait::Fn);

        // Check env selectors
        assert_eq!(encoding.env_selectors.len(), 2);
        assert_eq!(encoding.env_selectors[0].0, "closure_add-x");
        assert_eq!(encoding.env_selectors[1].0, "closure_add-y");

        // Check param sorts: [env_datatype, z: i32]
        assert_eq!(encoding.param_sorts.len(), 2);
        assert_eq!(
            encoding.param_sorts[0],
            Sort::Datatype("closure_add".to_string())
        );
        assert_eq!(encoding.param_sorts[1], Sort::BitVec(32));

        // Check return sort
        assert_eq!(encoding.return_sort, Sort::BitVec(32));
    }

    #[test]
    fn test_defunctionalize_fnmut_closure() {
        // FnMut closure: |x: i32| -> () with mutable capture count: i32
        let info = ClosureInfo {
            name: "closure_increment".to_string(),
            env_fields: vec![("count".to_string(), Ty::Int(IntTy::I32))],
            params: vec![("x".to_string(), Ty::Int(IntTy::I32))],
            return_ty: Ty::Unit,
            trait_kind: ClosureTrait::FnMut,
        };

        let encoding = defunctionalize_closure_call(&info, &[]);

        assert_eq!(encoding.trait_kind, ClosureTrait::FnMut);
        assert_eq!(encoding.env_datatype_name, "closure_increment");
        assert_eq!(encoding.defunctionalized_name, "closure_increment_impl");
    }

    #[test]
    fn test_defunctionalize_fnonce_closure() {
        // FnOnce closure: || -> i32 with moved capture data
        let info = ClosureInfo {
            name: "closure_consume".to_string(),
            env_fields: vec![("data".to_string(), Ty::Int(IntTy::I32))],
            params: vec![],
            return_ty: Ty::Int(IntTy::I32),
            trait_kind: ClosureTrait::FnOnce,
        };

        let encoding = defunctionalize_closure_call(&info, &[]);

        assert_eq!(encoding.trait_kind, ClosureTrait::FnOnce);
        assert_eq!(encoding.param_sorts.len(), 1); // Only env, no other params
    }

    #[test]
    fn test_encode_closure_call_term() {
        let info = ClosureInfo {
            name: "closure_add".to_string(),
            env_fields: vec![("x".to_string(), Ty::Int(IntTy::I32))],
            params: vec![("z".to_string(), Ty::Int(IntTy::I32))],
            return_ty: Ty::Int(IntTy::I32),
            trait_kind: ClosureTrait::Fn,
        };

        let encoding = defunctionalize_closure_call(&info, &[]);
        let env_term = Term::Const("env".to_string());
        let arg_term = Term::BitVecLit(3, 32);

        let call_term = encode_closure_call_term(&encoding, env_term, vec![arg_term.clone()]);

        match call_term {
            Term::App(name, args) => {
                assert_eq!(name, "closure_add_impl");
                assert_eq!(args.len(), 2);
                assert_eq!(args[0], Term::Const("env".to_string()));
                assert_eq!(args[1], arg_term);
            }
            _ => panic!("Expected Term::App"),
        }
    }

    #[test]
    fn test_encode_closure_as_uninterpreted() {
        let info = ClosureInfo {
            name: "predicate".to_string(),
            env_fields: vec![],
            params: vec![("x".to_string(), Ty::Int(IntTy::I32))],
            return_ty: Ty::Bool,
            trait_kind: ClosureTrait::Fn,
        };

        let commands = encode_closure_as_uninterpreted(&info);

        assert_eq!(commands.len(), 1);
        match &commands[0] {
            Command::DeclareFun(name, param_sorts, return_sort) => {
                assert_eq!(name, "predicate_impl");
                assert_eq!(param_sorts.len(), 2); // env + x param
                assert_eq!(*return_sort, Sort::Bool);
            }
            _ => panic!("Expected DeclareFun command"),
        }
    }

    #[test]
    fn test_defunctionalize_empty_env() {
        // Closure with no captures: || -> i32
        let info = ClosureInfo {
            name: "closure_const".to_string(),
            env_fields: vec![],
            params: vec![],
            return_ty: Ty::Int(IntTy::I32),
            trait_kind: ClosureTrait::Fn,
        };

        let encoding = defunctionalize_closure_call(&info, &[]);

        assert_eq!(encoding.env_selectors.len(), 0);
        assert_eq!(encoding.param_sorts.len(), 1); // Only the empty env
        assert_eq!(
            encoding.param_sorts[0],
            Sort::Datatype("closure_const".to_string())
        );
    }

    #[test]
    fn test_defunctionalize_multi_field_env() {
        // Closure with 3 captures
        let info = ClosureInfo {
            name: "closure_multi".to_string(),
            env_fields: vec![
                ("a".to_string(), Ty::Int(IntTy::I32)),
                ("b".to_string(), Ty::Bool),
                ("c".to_string(), Ty::Int(IntTy::I64)),
            ],
            params: vec![],
            return_ty: Ty::Unit,
            trait_kind: ClosureTrait::Fn,
        };

        let encoding = defunctionalize_closure_call(&info, &[]);

        assert_eq!(encoding.env_selectors.len(), 3);
        assert_eq!(encoding.env_selectors[0].0, "closure_multi-a");
        assert_eq!(encoding.env_selectors[0].1, Sort::BitVec(32));
        assert_eq!(encoding.env_selectors[1].0, "closure_multi-b");
        assert_eq!(encoding.env_selectors[1].1, Sort::Bool);
        assert_eq!(encoding.env_selectors[2].0, "closure_multi-c");
        assert_eq!(encoding.env_selectors[2].1, Sort::BitVec(64));
    }
}
