/// Prophecy variable encoding for mutable borrow reasoning.
///
/// This module implements Creusot/RustHornBelt-style prophecy variables to enable
/// specification and verification of properties about the final value of mutable borrows.
///
/// ## Problem
/// When a function takes `&mut T`, we need to verify properties like:
/// ```rust,ignore
/// #[ensures(*x == old(*x) + 1)]
/// fn increment(x: &mut i32) { *x += 1; }
/// ```
///
/// At function entry, we don't know the final value of `*x` at return. Prophecy
/// variables solve this by introducing a "predicted future value" that is constrained
/// at function return to equal the actual final value.
///
/// ## Encoding
/// For each `&mut T` parameter `param`:
/// - Declare `param_initial: T` -- the initial dereferenced value
/// - Declare `param_prophecy: T` -- the predicted final dereferenced value
/// - At entry: assert `param_initial == *param` (capture pre-state)
/// - At return: assert `param_final == param_prophecy` (resolve prophecy)
///
/// In specifications:
/// - `old(*param)` resolves to `param_initial`
/// - `final_value(param)` or `*param` (in postcondition context) resolves to `param_prophecy`
use std::collections::HashMap;

use rust_fv_smtlib::command::Command;
use rust_fv_smtlib::term::Term;

use crate::encode_sort::encode_type;
use crate::ir::{Function, Mutability, ProphecyInfo, Ty};

/// Detect all mutable reference parameters and create prophecy metadata.
///
/// Scans function parameters for `Ty::Ref(inner, Mutability::Mutable)` types
/// and creates a ProphecyInfo for each one.
pub fn detect_prophecies(func: &Function) -> Vec<ProphecyInfo> {
    let mut prophecies = Vec::new();

    for param in &func.params {
        if let Ty::Ref(inner_ty, Mutability::Mutable) = &param.ty {
            prophecies.push(ProphecyInfo {
                param_name: param.name.clone(),
                initial_var: format!("{}_initial", param.name),
                prophecy_var: format!("{}_prophecy", param.name),
                inner_ty: (**inner_ty).clone(),
                deref_level: 0,
            });
        }
    }

    prophecies
}

/// Generate SMT declarations for prophecy variables.
///
/// For each prophecy, this generates:
/// 1. `(declare-const param_initial Sort)` -- initial value at function entry
/// 2. `(declare-const param_prophecy Sort)` -- predicted final value
/// 3. `(assert (= param_initial *param))` -- snapshot the initial dereferenced value
///
/// The initial value snapshot constraint ensures that `old(*param)` in specs
/// resolves to the correct pre-state value.
pub fn prophecy_declarations(prophecies: &[ProphecyInfo]) -> Vec<Command> {
    let mut commands = Vec::new();

    for prophecy in prophecies {
        let sort = encode_type(&prophecy.inner_ty);

        // Declare initial value variable
        commands.push(Command::DeclareConst(
            prophecy.initial_var.clone(),
            sort.clone(),
        ));

        // Declare prophecy (final value) variable
        commands.push(Command::DeclareConst(prophecy.prophecy_var.clone(), sort));

        // Assert initial value equals current dereferenced param
        // This captures the pre-state: param_initial = *param
        commands.push(Command::Assert(Term::Eq(
            Box::new(Term::Const(prophecy.initial_var.clone())),
            Box::new(Term::Const(prophecy.param_name.clone())),
        )));
    }

    commands
}

/// Generate SMT assertions to resolve prophecies at function return.
///
/// For each prophecy, generate:
/// `(assert (= param_final param_prophecy))`
///
/// where `param_final` is the actual final value of the mutable reference at the
/// return point. If `final_values` map contains an entry for the param, use that;
/// otherwise, assume the param's current value is the final value.
///
/// This constraint enforces that the prophecy prediction matches reality at return.
pub fn prophecy_resolutions(
    prophecies: &[ProphecyInfo],
    final_values: &HashMap<String, Term>,
) -> Vec<Command> {
    let mut commands = Vec::new();

    for prophecy in prophecies {
        // Determine the actual final value at this return point
        let final_value = final_values
            .get(&prophecy.param_name)
            .cloned()
            .unwrap_or_else(|| Term::Const(prophecy.param_name.clone()));

        // Assert prophecy equals actual final value
        commands.push(Command::Assert(Term::Eq(
            Box::new(final_value),
            Box::new(Term::Const(prophecy.prophecy_var.clone())),
        )));
    }

    commands
}

/// Detect nested prophecies for nested mutable borrow parameters (&mut &mut T).
///
/// For each mutable reference parameter, walks the type structure to identify
/// nested layers of &mut references. Each layer gets its own prophecy variable.
///
/// Naming convention:
/// - deref_level 0: {param}_initial, {param}_prophecy
/// - deref_level 1: {param}_deref_initial, {param}_deref_prophecy
/// - deref_level N (N>1): {param}_deref{N}_initial, {param}_deref{N}_prophecy
pub fn detect_nested_prophecies(func: &Function) -> Vec<ProphecyInfo> {
    let mut prophecies = Vec::new();

    for param in &func.params {
        let mut current_ty = &param.ty;
        let mut level = 0;

        // Walk through nested &mut references
        while let Ty::Ref(inner_ty, Mutability::Mutable) = current_ty {
            let (initial_var, prophecy_var) = if level == 0 {
                (
                    format!("{}_initial", param.name),
                    format!("{}_prophecy", param.name),
                )
            } else if level == 1 {
                (
                    format!("{}_deref_initial", param.name),
                    format!("{}_deref_prophecy", param.name),
                )
            } else {
                (
                    format!("{}_deref{}_initial", param.name, level),
                    format!("{}_deref{}_prophecy", param.name, level),
                )
            };

            prophecies.push(ProphecyInfo {
                param_name: param.name.clone(),
                initial_var,
                prophecy_var,
                inner_ty: (**inner_ty).clone(),
                deref_level: level,
            });

            current_ty = inner_ty;
            level += 1;
        }
    }

    prophecies
}

/// Generate SMT declarations for nested prophecy variables.
///
/// Same as prophecy_declarations but aware of deref_level for variable naming.
/// For deref_level > 0, the initial value constraint links to the parent prophecy's
/// current state rather than the parameter directly (this linking is done in VCGen in Plan 02).
///
/// For now, all levels declare independent constants.
pub fn nested_prophecy_declarations(prophecies: &[ProphecyInfo]) -> Vec<Command> {
    let mut commands = Vec::new();

    for prophecy in prophecies {
        let sort = encode_type(&prophecy.inner_ty);

        // Declare initial value variable
        commands.push(Command::DeclareConst(
            prophecy.initial_var.clone(),
            sort.clone(),
        ));

        // Declare prophecy (final value) variable
        commands.push(Command::DeclareConst(prophecy.prophecy_var.clone(), sort));

        // For deref_level 0, assert initial value equals the parameter
        // For deref_level > 0, the constraint will be added by VCGen in Plan 02
        if prophecy.deref_level == 0 {
            commands.push(Command::Assert(Term::Eq(
                Box::new(Term::Const(prophecy.initial_var.clone())),
                Box::new(Term::Const(prophecy.param_name.clone())),
            )));
        }
    }

    commands
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Contracts, IntTy, Local};
    use rust_fv_smtlib::sort::Sort;

    fn make_func_with_mut_ref() -> Function {
        Function {
            name: "test_mut".to_string(),
            params: vec![Local::new(
                "_1",
                Ty::Ref(Box::new(Ty::Int(IntTy::I32)), Mutability::Mutable),
            )],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![],
            contracts: Default::default(),
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

    fn make_func_with_shared_ref() -> Function {
        Function {
            name: "test_shared".to_string(),
            params: vec![Local::new(
                "_1",
                Ty::Ref(Box::new(Ty::Int(IntTy::I32)), Mutability::Shared),
            )],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![],
            contracts: Default::default(),
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

    fn make_func_with_multiple_mut_refs() -> Function {
        Function {
            name: "test_multiple".to_string(),
            params: vec![
                Local::new(
                    "_1",
                    Ty::Ref(Box::new(Ty::Int(IntTy::I32)), Mutability::Mutable),
                ),
                Local::new(
                    "_2",
                    Ty::Ref(Box::new(Ty::Int(IntTy::I64)), Mutability::Mutable),
                ),
            ],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![],
            contracts: Default::default(),
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
    fn test_detect_prophecies_mut_ref() {
        let func = make_func_with_mut_ref();
        let prophecies = detect_prophecies(&func);

        assert_eq!(prophecies.len(), 1);
        assert_eq!(prophecies[0].param_name, "_1");
        assert_eq!(prophecies[0].initial_var, "_1_initial");
        assert_eq!(prophecies[0].prophecy_var, "_1_prophecy");
        assert_eq!(prophecies[0].inner_ty, Ty::Int(IntTy::I32));
    }

    #[test]
    fn test_detect_prophecies_no_mut() {
        let func = make_func_with_shared_ref();
        let prophecies = detect_prophecies(&func);

        assert_eq!(prophecies.len(), 0);
    }

    #[test]
    fn test_detect_prophecies_multiple() {
        let func = make_func_with_multiple_mut_refs();
        let prophecies = detect_prophecies(&func);

        assert_eq!(prophecies.len(), 2);
        assert_eq!(prophecies[0].param_name, "_1");
        assert_eq!(prophecies[0].inner_ty, Ty::Int(IntTy::I32));
        assert_eq!(prophecies[1].param_name, "_2");
        assert_eq!(prophecies[1].inner_ty, Ty::Int(IntTy::I64));
    }

    #[test]
    fn test_prophecy_declarations() {
        let func = make_func_with_mut_ref();
        let prophecies = detect_prophecies(&func);
        let commands = prophecy_declarations(&prophecies);

        // Should generate: DeclareConst initial, DeclareConst prophecy, Assert initial = param
        assert_eq!(commands.len(), 3);

        // Check first command: declare initial
        match &commands[0] {
            Command::DeclareConst(name, sort) => {
                assert_eq!(name, "_1_initial");
                assert_eq!(*sort, Sort::BitVec(32));
            }
            _ => panic!("Expected DeclareConst for initial var"),
        }

        // Check second command: declare prophecy
        match &commands[1] {
            Command::DeclareConst(name, sort) => {
                assert_eq!(name, "_1_prophecy");
                assert_eq!(*sort, Sort::BitVec(32));
            }
            _ => panic!("Expected DeclareConst for prophecy var"),
        }

        // Check third command: assert initial = param
        match &commands[2] {
            Command::Assert(term) => match term {
                Term::Eq(lhs, rhs) => {
                    assert_eq!(**lhs, Term::Const("_1_initial".to_string()));
                    assert_eq!(**rhs, Term::Const("_1".to_string()));
                }
                _ => panic!("Expected Eq term"),
            },
            _ => panic!("Expected Assert command"),
        }
    }

    #[test]
    fn test_prophecy_resolutions() {
        let func = make_func_with_mut_ref();
        let prophecies = detect_prophecies(&func);

        // Case 1: No explicit final values (param unchanged)
        let final_values = HashMap::new();
        let commands = prophecy_resolutions(&prophecies, &final_values);

        assert_eq!(commands.len(), 1);
        match &commands[0] {
            Command::Assert(term) => match term {
                Term::Eq(lhs, rhs) => {
                    assert_eq!(**lhs, Term::Const("_1".to_string()));
                    assert_eq!(**rhs, Term::Const("_1_prophecy".to_string()));
                }
                _ => panic!("Expected Eq term"),
            },
            _ => panic!("Expected Assert command"),
        }

        // Case 2: Explicit final value provided
        let mut final_values = HashMap::new();
        final_values.insert("_1".to_string(), Term::BitVecLit(42, 32));
        let commands = prophecy_resolutions(&prophecies, &final_values);

        assert_eq!(commands.len(), 1);
        match &commands[0] {
            Command::Assert(term) => match term {
                Term::Eq(lhs, rhs) => {
                    assert_eq!(**lhs, Term::BitVecLit(42, 32));
                    assert_eq!(**rhs, Term::Const("_1_prophecy".to_string()));
                }
                _ => panic!("Expected Eq term"),
            },
            _ => panic!("Expected Assert command"),
        }
    }

    // ====== Nested prophecy tests ======

    #[test]
    fn test_detect_nested_prophecies_simple() {
        let func = make_func_with_mut_ref();
        let prophecies = detect_nested_prophecies(&func);
        assert_eq!(prophecies.len(), 1);
        assert_eq!(prophecies[0].deref_level, 0);
        assert_eq!(prophecies[0].prophecy_var, "_1_prophecy");
    }

    #[test]
    fn test_detect_nested_prophecies_nested() {
        // &mut &mut i32
        let func = Function {
            name: "nested".to_string(),
            params: vec![Local::new(
                "_1",
                Ty::Ref(
                    Box::new(Ty::Ref(Box::new(Ty::Int(IntTy::I32)), Mutability::Mutable)),
                    Mutability::Mutable,
                ),
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
        let prophecies = detect_nested_prophecies(&func);
        assert_eq!(prophecies.len(), 2);
        assert_eq!(prophecies[0].deref_level, 0);
        assert_eq!(prophecies[0].prophecy_var, "_1_prophecy");
        assert_eq!(prophecies[1].deref_level, 1);
        assert_eq!(prophecies[1].prophecy_var, "_1_deref_prophecy");
    }

    #[test]
    fn test_detect_nested_prophecies_triple() {
        // &mut &mut &mut i32
        let func = Function {
            name: "triple_nested".to_string(),
            params: vec![Local::new(
                "_1",
                Ty::Ref(
                    Box::new(Ty::Ref(
                        Box::new(Ty::Ref(Box::new(Ty::Int(IntTy::I32)), Mutability::Mutable)),
                        Mutability::Mutable,
                    )),
                    Mutability::Mutable,
                ),
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
        let prophecies = detect_nested_prophecies(&func);
        assert_eq!(prophecies.len(), 3);
        assert_eq!(prophecies[0].deref_level, 0);
        assert_eq!(prophecies[1].deref_level, 1);
        assert_eq!(prophecies[2].deref_level, 2);
        assert_eq!(prophecies[2].prophecy_var, "_1_deref2_prophecy");
    }

    #[test]
    fn test_detect_nested_prophecies_shared_no_prophecy() {
        // &i32 (shared reference, no prophecy)
        let func = Function {
            name: "shared_ref".to_string(),
            params: vec![Local::new(
                "_1",
                Ty::Ref(Box::new(Ty::Int(IntTy::I32)), Mutability::Shared),
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
        let prophecies = detect_nested_prophecies(&func);
        assert_eq!(prophecies.len(), 0);
    }

    #[test]
    fn test_nested_prophecy_naming_level0() {
        let func = make_func_with_mut_ref();
        let prophecies = detect_nested_prophecies(&func);
        assert_eq!(prophecies[0].initial_var, "_1_initial");
        assert_eq!(prophecies[0].prophecy_var, "_1_prophecy");
    }

    #[test]
    fn test_nested_prophecy_naming_level1() {
        let func = Function {
            name: "nested".to_string(),
            params: vec![Local::new(
                "_1",
                Ty::Ref(
                    Box::new(Ty::Ref(Box::new(Ty::Int(IntTy::I32)), Mutability::Mutable)),
                    Mutability::Mutable,
                ),
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
        let prophecies = detect_nested_prophecies(&func);
        assert_eq!(prophecies[1].initial_var, "_1_deref_initial");
        assert_eq!(prophecies[1].prophecy_var, "_1_deref_prophecy");
    }

    #[test]
    fn test_nested_prophecy_declarations() {
        let func = Function {
            name: "nested".to_string(),
            params: vec![Local::new(
                "_1",
                Ty::Ref(
                    Box::new(Ty::Ref(Box::new(Ty::Int(IntTy::I32)), Mutability::Mutable)),
                    Mutability::Mutable,
                ),
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
        let prophecies = detect_nested_prophecies(&func);
        let commands = nested_prophecy_declarations(&prophecies);

        // For 2 levels: 2 * (DeclareConst initial + DeclareConst prophecy) + 1 Assert (level 0 only)
        // = 4 DeclareConst + 1 Assert = 5 commands
        assert_eq!(commands.len(), 5);

        // Check that DeclareConst and Assert commands are present
        let declare_count = commands
            .iter()
            .filter(|c| matches!(c, Command::DeclareConst(_, _)))
            .count();
        let assert_count = commands
            .iter()
            .filter(|c| matches!(c, Command::Assert(_)))
            .count();
        assert_eq!(declare_count, 4);
        assert_eq!(assert_count, 1);
    }

    #[test]
    fn test_prophecy_info_deref_level_default() {
        // Existing code (detect_prophecies) should produce deref_level=0
        let func = make_func_with_mut_ref();
        let prophecies = detect_prophecies(&func);
        assert_eq!(prophecies[0].deref_level, 0);
    }
}
