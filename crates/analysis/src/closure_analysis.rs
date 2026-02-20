//! Closure analysis infrastructure for detecting and analyzing closures in IR.
//!
//! This module provides:
//! - ClosureCallSite: Represents a closure call site in the IR
//! - extract_closure_info: Extract all closure types from a function
//! - detect_closure_calls: Find all closure call sites in a function
//! - classify_closure_trait: Determine Fn/FnMut/FnOnce from callee name
//! - validate_fnonce_single_call: Detect FnOnce closures called more than once
use crate::ir::{ClosureInfo, ClosureTrait, Function, Operand, Place, Terminator, Ty};

/// A closure call site detected in the IR.
#[derive(Debug, Clone)]
pub struct ClosureCallSite {
    /// Which closure is being called
    pub closure_name: String,
    /// Arguments passed to the closure (excluding environment)
    pub args: Vec<Operand>,
    /// Where the return value is stored
    pub destination: Place,
    /// Which basic block the call occurs in
    pub block_idx: usize,
    /// What Fn trait the closure implements
    pub trait_kind: ClosureTrait,
}

/// Extract all closure types from a function's parameters and locals.
pub fn extract_closure_info(func: &Function) -> Vec<&ClosureInfo> {
    let mut closures = Vec::new();

    // Check return local
    if let Ty::Closure(info) = &func.return_local.ty {
        closures.push(info.as_ref());
    }

    // Check parameters
    for param in &func.params {
        if let Ty::Closure(info) = &param.ty {
            closures.push(info.as_ref());
        }
    }

    // Check locals
    for local in &func.locals {
        if let Ty::Closure(info) = &local.ty {
            closures.push(info.as_ref());
        }
    }

    closures
}

/// Detect all closure call sites in a function.
pub fn detect_closure_calls(func: &Function) -> Vec<ClosureCallSite> {
    let mut call_sites = Vec::new();

    for (block_idx, block) in func.basic_blocks.iter().enumerate() {
        if let Terminator::Call {
            func: callee_name,
            args,
            destination,
            ..
        } = &block.terminator
        {
            // Check if this is a closure call (Fn::call, FnMut::call_mut, FnOnce::call_once)
            if let Some(trait_kind) = classify_closure_trait(callee_name) {
                // Extract closure name from args (first arg is the closure itself)
                let closure_name =
                    if let Some(Operand::Copy(place) | Operand::Move(place)) = args.first() {
                        place.local.clone()
                    } else {
                        callee_name.clone()
                    };

                call_sites.push(ClosureCallSite {
                    closure_name,
                    args: args.clone(),
                    destination: destination.clone(),
                    block_idx,
                    trait_kind,
                });
            }
        }
    }

    call_sites
}

/// Classify closure trait from callee name.
pub fn classify_closure_trait(callee_name: &str) -> Option<ClosureTrait> {
    // Check for FnOnce first (most specific)
    if callee_name.contains("call_once") {
        return Some(ClosureTrait::FnOnce);
    }

    // Then FnMut (specific substring)
    if callee_name.contains("call_mut") {
        return Some(ClosureTrait::FnMut);
    }

    // Finally Fn (just "call" without "call_mut" or "call_once")
    if callee_name.contains("call") {
        return Some(ClosureTrait::Fn);
    }

    None
}

/// Validate that FnOnce closures are called at most once.
/// Returns error messages for each violation.
pub fn validate_fnonce_single_call(func: &Function) -> Vec<String> {
    let mut errors = Vec::new();
    let call_sites = detect_closure_calls(func);

    // Group calls by closure name
    let mut fnonce_calls: std::collections::HashMap<String, Vec<usize>> =
        std::collections::HashMap::new();

    for call_site in &call_sites {
        if call_site.trait_kind == ClosureTrait::FnOnce {
            fnonce_calls
                .entry(call_site.closure_name.clone())
                .or_default()
                .push(call_site.block_idx);
        }
    }

    // Check for multiple calls
    for (closure_name, blocks) in fnonce_calls {
        if blocks.len() > 1 {
            errors.push(format!(
                "FnOnce closure '{}' called {} times (blocks: {:?}), but can only be called once",
                closure_name,
                blocks.len(),
                blocks
            ));
        }
    }

    errors
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{BasicBlock, Contracts, IntTy, Local, Terminator, Ty};

    // ====== classify_closure_trait tests ======

    #[test]
    fn test_classify_fn_call() {
        assert_eq!(classify_closure_trait("Fn::call"), Some(ClosureTrait::Fn));
        assert_eq!(
            classify_closure_trait("std::ops::Fn::call"),
            Some(ClosureTrait::Fn)
        );
    }

    #[test]
    fn test_classify_fnmut_call() {
        assert_eq!(
            classify_closure_trait("FnMut::call_mut"),
            Some(ClosureTrait::FnMut)
        );
        assert_eq!(
            classify_closure_trait("std::ops::FnMut::call_mut"),
            Some(ClosureTrait::FnMut)
        );
    }

    #[test]
    fn test_classify_fnonce_call() {
        assert_eq!(
            classify_closure_trait("FnOnce::call_once"),
            Some(ClosureTrait::FnOnce)
        );
        assert_eq!(
            classify_closure_trait("std::ops::FnOnce::call_once"),
            Some(ClosureTrait::FnOnce)
        );
    }

    #[test]
    fn test_classify_unknown() {
        assert_eq!(classify_closure_trait("random_func"), None);
        assert_eq!(classify_closure_trait("add"), None);
    }

    #[test]
    fn test_classify_call_mut_not_fn() {
        // "call_mut" should NOT classify as Fn (it should be FnMut)
        let result = classify_closure_trait("FnMut::call_mut");
        assert_eq!(result, Some(ClosureTrait::FnMut));
        assert_ne!(result, Some(ClosureTrait::Fn));
    }

    // ====== extract_closure_info tests ======

    #[test]
    fn test_extract_closure_info_from_params() {
        let closure_info = ClosureInfo {
            name: "test_closure".to_string(),
            env_fields: vec![],
            params: vec![("x".to_string(), Ty::Int(IntTy::I32))],
            return_ty: Ty::Int(IntTy::I32),
            trait_kind: ClosureTrait::Fn,
        };

        let func = Function {
            name: "test".to_string(),
            params: vec![Local::new(
                "_1",
                Ty::Closure(Box::new(closure_info.clone())),
            )],
            return_local: Local::new("_0", Ty::Unit),
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
        };

        let result = extract_closure_info(&func);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].name, "test_closure");
    }

    #[test]
    fn test_extract_closure_info_empty() {
        let func = Function {
            name: "test".to_string(),
            params: vec![Local::new("_1", Ty::Int(IntTy::I32))],
            return_local: Local::new("_0", Ty::Unit),
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
        };

        let result = extract_closure_info(&func);
        assert!(result.is_empty());
    }

    // ====== detect_closure_calls tests ======

    #[test]
    fn test_detect_closure_calls() {
        let func = Function {
            name: "test".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Call {
                    func: "Fn::call".to_string(),
                    args: vec![Operand::Copy(Place::local("_1"))],
                    destination: Place::local("_2"),
                    target: 1,
                },
            }],
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
        };

        let result = detect_closure_calls(&func);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].closure_name, "_1");
        assert_eq!(result[0].trait_kind, ClosureTrait::Fn);
    }

    // ====== validate_fnonce_single_call tests ======

    #[test]
    fn test_validate_fnonce_single_call_ok() {
        let func = Function {
            name: "test".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Call {
                    func: "FnOnce::call_once".to_string(),
                    args: vec![Operand::Copy(Place::local("_1"))],
                    destination: Place::local("_2"),
                    target: 1,
                },
            }],
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
        };

        let errors = validate_fnonce_single_call(&func);
        assert!(errors.is_empty());
    }

    #[test]
    fn test_validate_fnonce_double_call() {
        let func = Function {
            name: "test".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "FnOnce::call_once".to_string(),
                        args: vec![Operand::Copy(Place::local("_1"))],
                        destination: Place::local("_2"),
                        target: 1,
                    },
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "FnOnce::call_once".to_string(),
                        args: vec![Operand::Copy(Place::local("_1"))],
                        destination: Place::local("_3"),
                        target: 2,
                    },
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
            ],
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
        };

        let errors = validate_fnonce_single_call(&func);
        assert_eq!(errors.len(), 1);
        assert!(errors[0].contains("_1"));
        assert!(errors[0].contains("2 times"));
    }
}
