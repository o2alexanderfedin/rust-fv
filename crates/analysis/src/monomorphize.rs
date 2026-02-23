/// Monomorphization support for generic functions.
///
/// Generic functions (e.g., `fn max<T: Ord>(a: T, b: T) -> T`) are verified
/// by generating separate verification conditions for each concrete type
/// instantiation at call sites. This mirrors Rust's own monomorphization
/// strategy and avoids the complexity of parametric reasoning.
///
/// The `MonomorphizationRegistry` tracks which concrete types are used at
/// each call site, and `substitute_generics` replaces generic type parameters
/// with concrete types throughout the function's IR.
use std::collections::HashMap;

use crate::ir::{BasicBlock, Function, GenericParam, Local, Rvalue, Statement, Terminator, Ty};

/// Maps generic type parameter names to concrete types for a single instantiation.
#[derive(Debug, Clone)]
pub struct TypeInstantiation {
    /// Maps generic param name to concrete type: e.g., {"T" -> Ty::Int(IntTy::I32)}
    pub substitutions: HashMap<String, Ty>,
    /// Human-readable label: e.g., "max::<i32>"
    pub label: String,
}

impl TypeInstantiation {
    /// Create a new type instantiation with the given substitutions and label.
    pub fn new(substitutions: HashMap<String, Ty>, label: String) -> Self {
        Self {
            substitutions,
            label,
        }
    }
}

/// Registry of concrete type instantiations for generic functions.
///
/// Tracks which concrete types are used at each call site for generic functions,
/// enabling per-instantiation verification condition generation.
#[derive(Debug, Clone, Default)]
pub struct MonomorphizationRegistry {
    /// Maps function name to its concrete instantiations
    instantiations: HashMap<String, Vec<TypeInstantiation>>,
}

impl MonomorphizationRegistry {
    /// Create a new empty registry.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a concrete type instantiation for a function.
    pub fn register(&mut self, func_name: &str, inst: TypeInstantiation) {
        self.instantiations
            .entry(func_name.to_string())
            .or_default()
            .push(inst);
    }

    /// Get all registered instantiations for a function.
    ///
    /// Returns an empty slice if no instantiations are registered.
    pub fn get_instantiations(&self, func_name: &str) -> &[TypeInstantiation] {
        self.instantiations
            .get(func_name)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }
}

/// Substitute generic type parameters with concrete types throughout a function.
///
/// Returns a new function with all `Ty::Generic(name)` replaced by the concrete
/// type from the instantiation. The resulting function is non-generic (generic_params
/// is empty) and has a name incorporating the instantiation label.
pub fn substitute_generics(func: &Function, inst: &TypeInstantiation) -> Function {
    let mut result = func.clone();

    // Update function name to include instantiation label
    result.name = format!("{}{}", func.name, inst.label);

    // Substitute types in parameters
    result.params = func
        .params
        .iter()
        .map(|p| Local {
            name: p.name.clone(),
            ty: substitute_ty(&p.ty, &inst.substitutions),
            is_ghost: p.is_ghost,
        })
        .collect();

    // Substitute type in return local
    result.return_local = Local {
        name: func.return_local.name.clone(),
        ty: substitute_ty(&func.return_local.ty, &inst.substitutions),
        is_ghost: func.return_local.is_ghost,
    };

    // Substitute types in locals
    result.locals = func
        .locals
        .iter()
        .map(|l| Local {
            name: l.name.clone(),
            ty: substitute_ty(&l.ty, &inst.substitutions),
            is_ghost: l.is_ghost,
        })
        .collect();

    // Substitute types in basic blocks (statements and terminators)
    result.basic_blocks = func
        .basic_blocks
        .iter()
        .map(|bb| substitute_basic_block(bb, &inst.substitutions))
        .collect();

    // Clear generic_params (result is concrete)
    result.generic_params = Vec::new();

    result
}

/// Substitute generic types in a basic block.
fn substitute_basic_block(bb: &BasicBlock, subs: &HashMap<String, Ty>) -> BasicBlock {
    BasicBlock {
        statements: bb
            .statements
            .iter()
            .map(|stmt| substitute_statement(stmt, subs))
            .collect(),
        terminator: substitute_terminator(&bb.terminator, subs),
    }
}

/// Substitute generic types in a statement.
fn substitute_statement(stmt: &Statement, subs: &HashMap<String, Ty>) -> Statement {
    match stmt {
        Statement::Assign(place, rvalue) => {
            Statement::Assign(place.clone(), substitute_rvalue(rvalue, subs))
        }
        Statement::Nop => Statement::Nop,
    }
}

/// Substitute generic types in a terminator.
fn substitute_terminator(term: &Terminator, _subs: &HashMap<String, Ty>) -> Terminator {
    // Note: Terminators don't currently contain type information that needs substitution.
    // This function exists for symmetry with statements and future extensibility.
    match term {
        Terminator::Return => Terminator::Return,
        Terminator::Goto(target) => Terminator::Goto(*target),
        Terminator::SwitchInt {
            discr,
            targets,
            otherwise,
        } => Terminator::SwitchInt {
            discr: discr.clone(),
            targets: targets.clone(),
            otherwise: *otherwise,
        },
        Terminator::Call {
            func,
            args,
            destination,
            target,
        } => Terminator::Call {
            func: func.clone(),
            args: args.clone(),
            destination: destination.clone(),
            target: *target,
        },
        Terminator::Assert {
            cond,
            expected,
            target,
            kind,
        } => Terminator::Assert {
            cond: cond.clone(),
            expected: *expected,
            target: *target,
            kind: kind.clone(),
        },
        Terminator::Unreachable => Terminator::Unreachable,
    }
}

/// Substitute generic types in an rvalue.
fn substitute_rvalue(rvalue: &Rvalue, subs: &HashMap<String, Ty>) -> Rvalue {
    match rvalue {
        Rvalue::Use(op) => Rvalue::Use(op.clone()),
        Rvalue::BinaryOp(op, lhs, rhs) => Rvalue::BinaryOp(*op, lhs.clone(), rhs.clone()),
        Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
            Rvalue::CheckedBinaryOp(*op, lhs.clone(), rhs.clone())
        }
        Rvalue::UnaryOp(op, operand) => Rvalue::UnaryOp(*op, operand.clone()),
        Rvalue::Cast(kind, operand, ty) => {
            Rvalue::Cast(kind.clone(), operand.clone(), substitute_ty(ty, subs))
        }
        Rvalue::Ref(mutability, place) => Rvalue::Ref(*mutability, place.clone()),
        Rvalue::Aggregate(kind, operands) => Rvalue::Aggregate(kind.clone(), operands.clone()),
        Rvalue::Len(place) => Rvalue::Len(place.clone()),
        Rvalue::Discriminant(place) => Rvalue::Discriminant(place.clone()),
    }
}

/// Substitute generic types in a type.
///
/// Recursively walks the type structure, replacing `Ty::Generic(name)` with
/// the concrete type from the substitution map.
fn substitute_ty(ty: &Ty, subs: &HashMap<String, Ty>) -> Ty {
    match ty {
        Ty::Generic(name) => subs
            .get(name)
            .cloned()
            .unwrap_or_else(|| panic!("Missing substitution for generic type parameter: {}", name)),
        Ty::Ref(inner, mutability) => Ty::Ref(Box::new(substitute_ty(inner, subs)), *mutability),
        Ty::RawPtr(inner, mutability) => {
            Ty::RawPtr(Box::new(substitute_ty(inner, subs)), *mutability)
        }
        Ty::Tuple(fields) => Ty::Tuple(fields.iter().map(|f| substitute_ty(f, subs)).collect()),
        Ty::Array(elem, n) => Ty::Array(Box::new(substitute_ty(elem, subs)), *n),
        Ty::Slice(elem) => Ty::Slice(Box::new(substitute_ty(elem, subs))),
        Ty::Struct(name, fields) => Ty::Struct(
            name.clone(),
            fields
                .iter()
                .map(|(fname, fty)| (fname.clone(), substitute_ty(fty, subs)))
                .collect(),
        ),
        Ty::Enum(name, variants) => Ty::Enum(
            name.clone(),
            variants
                .iter()
                .map(|(vname, vtys)| {
                    (
                        vname.clone(),
                        vtys.iter().map(|vty| substitute_ty(vty, subs)).collect(),
                    )
                })
                .collect(),
        ),
        // All other types are unchanged
        _ => ty.clone(),
    }
}

/// Generate constraints for trait bounds on a generic type parameter.
///
/// For example, `T: Ord` with `T = i32` indicates the concrete type supports
/// comparison operators. This is used to validate that concrete types satisfy
/// trait bounds.
///
/// Returns a list of supported operations (for documentation/validation purposes).
pub fn trait_bound_constraints(generic: &GenericParam, concrete_ty: &Ty) -> Vec<String> {
    let mut constraints = Vec::new();

    for bound in &generic.trait_bounds {
        match bound.as_str() {
            "Ord" | "PartialOrd" => {
                // Concrete type must support comparison operators
                if concrete_ty.is_integer() {
                    constraints.push(format!(
                        "Type {} supports comparison operators ({})",
                        generic.name,
                        if concrete_ty.is_signed() {
                            "signed"
                        } else {
                            "unsigned"
                        }
                    ));
                }
            }
            "Clone" | "Copy" => {
                // No verification impact (informational only)
                constraints.push(format!(
                    "Type {} supports {} semantics",
                    generic.name, bound
                ));
            }
            _ => {
                // Unknown trait bound (informational)
                constraints.push(format!("Type {} implements {}", generic.name, bound));
            }
        }
    }

    constraints
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Contracts, IntTy, SpecExpr, UintTy};

    #[test]
    fn test_substitute_generics_simple() {
        // fn foo<T>(x: T) -> T
        let func = Function {
            name: "foo".to_string(),
            params: vec![Local::new("_1", Ty::Generic("T".to_string()))],
            return_local: Local::new("_0", Ty::Generic("T".to_string())),
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            loops: vec![],
            generic_params: vec![GenericParam {
                name: "T".to_string(),
                trait_bounds: vec![],
            }],
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
        };

        let mut subs = HashMap::new();
        subs.insert("T".to_string(), Ty::Int(IntTy::I32));
        let inst = TypeInstantiation::new(subs, "::<i32>".to_string());

        let result = substitute_generics(&func, &inst);

        assert_eq!(result.name, "foo::<i32>");
        assert_eq!(result.params[0].ty, Ty::Int(IntTy::I32));
        assert_eq!(result.return_local.ty, Ty::Int(IntTy::I32));
        assert!(result.generic_params.is_empty());
    }

    #[test]
    fn test_substitute_generics_ref() {
        // fn bar<T>(x: &T, y: &mut T) -> T
        let func = Function {
            name: "bar".to_string(),
            params: vec![
                Local::new(
                    "_1",
                    Ty::Ref(
                        Box::new(Ty::Generic("T".to_string())),
                        crate::ir::Mutability::Shared,
                    ),
                ),
                Local::new(
                    "_2",
                    Ty::Ref(
                        Box::new(Ty::Generic("T".to_string())),
                        crate::ir::Mutability::Mutable,
                    ),
                ),
            ],
            return_local: Local::new("_0", Ty::Generic("T".to_string())),
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            loops: vec![],
            generic_params: vec![GenericParam {
                name: "T".to_string(),
                trait_bounds: vec![],
            }],
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
        };

        let mut subs = HashMap::new();
        subs.insert("T".to_string(), Ty::Uint(UintTy::U64));
        let inst = TypeInstantiation::new(subs, "::<u64>".to_string());

        let result = substitute_generics(&func, &inst);

        assert_eq!(result.name, "bar::<u64>");
        assert_eq!(
            result.params[0].ty,
            Ty::Ref(
                Box::new(Ty::Uint(UintTy::U64)),
                crate::ir::Mutability::Shared
            )
        );
        assert_eq!(
            result.params[1].ty,
            Ty::Ref(
                Box::new(Ty::Uint(UintTy::U64)),
                crate::ir::Mutability::Mutable
            )
        );
        assert_eq!(result.return_local.ty, Ty::Uint(UintTy::U64));
    }

    #[test]
    fn test_substitute_generics_tuple() {
        // fn baz<T>(x: (T, T)) -> T
        let func = Function {
            name: "baz".to_string(),
            params: vec![Local::new(
                "_1",
                Ty::Tuple(vec![
                    Ty::Generic("T".to_string()),
                    Ty::Generic("T".to_string()),
                ]),
            )],
            return_local: Local::new("_0", Ty::Generic("T".to_string())),
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            loops: vec![],
            generic_params: vec![GenericParam {
                name: "T".to_string(),
                trait_bounds: vec![],
            }],
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
        };

        let mut subs = HashMap::new();
        subs.insert("T".to_string(), Ty::Int(IntTy::I32));
        let inst = TypeInstantiation::new(subs, "::<i32>".to_string());

        let result = substitute_generics(&func, &inst);

        assert_eq!(
            result.params[0].ty,
            Ty::Tuple(vec![Ty::Int(IntTy::I32), Ty::Int(IntTy::I32)])
        );
    }

    #[test]
    fn test_registry_register_and_get() {
        let mut registry = MonomorphizationRegistry::new();

        let mut subs1 = HashMap::new();
        subs1.insert("T".to_string(), Ty::Int(IntTy::I32));
        let inst1 = TypeInstantiation::new(subs1, "::<i32>".to_string());

        let mut subs2 = HashMap::new();
        subs2.insert("T".to_string(), Ty::Uint(UintTy::U64));
        let inst2 = TypeInstantiation::new(subs2, "::<u64>".to_string());

        registry.register("max", inst1);
        registry.register("max", inst2);

        let instantiations = registry.get_instantiations("max");
        assert_eq!(instantiations.len(), 2);
        assert_eq!(instantiations[0].label, "::<i32>");
        assert_eq!(instantiations[1].label, "::<u64>");

        let empty = registry.get_instantiations("nonexistent");
        assert!(empty.is_empty());
    }

    #[test]
    fn test_substitute_preserves_contracts() {
        // fn foo<T>(x: T) -> T { ensures(result == x) }
        let func = Function {
            name: "foo".to_string(),
            params: vec![Local::new("_1", Ty::Generic("T".to_string()))],
            return_local: Local::new("_0", Ty::Generic("T".to_string())),
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "result == _1".to_string(),
                }],
                invariants: vec![],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
            },
            loops: vec![],
            generic_params: vec![GenericParam {
                name: "T".to_string(),
                trait_bounds: vec![],
            }],
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
        };

        let mut subs = HashMap::new();
        subs.insert("T".to_string(), Ty::Int(IntTy::I32));
        let inst = TypeInstantiation::new(subs, "::<i32>".to_string());

        let result = substitute_generics(&func, &inst);

        // Contracts should be preserved (not modified by type substitution)
        assert_eq!(result.contracts.ensures.len(), 1);
        assert_eq!(result.contracts.ensures[0].raw, "result == _1");
    }

    #[test]
    fn test_generic_function_label() {
        let func = Function {
            name: "max".to_string(),
            params: vec![
                Local::new("_1", Ty::Generic("T".to_string())),
                Local::new("_2", Ty::Generic("T".to_string())),
            ],
            return_local: Local::new("_0", Ty::Generic("T".to_string())),
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            loops: vec![],
            generic_params: vec![GenericParam {
                name: "T".to_string(),
                trait_bounds: vec!["Ord".to_string()],
            }],
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
        };

        let mut subs = HashMap::new();
        subs.insert("T".to_string(), Ty::Int(IntTy::I32));
        let inst = TypeInstantiation::new(subs, "::<i32>".to_string());

        let result = substitute_generics(&func, &inst);

        assert_eq!(result.name, "max::<i32>");
    }

    #[test]
    fn test_trait_bound_constraints() {
        let generic = GenericParam {
            name: "T".to_string(),
            trait_bounds: vec!["Ord".to_string(), "Clone".to_string()],
        };

        let constraints = trait_bound_constraints(&generic, &Ty::Int(IntTy::I32));
        assert_eq!(constraints.len(), 2);
        assert!(constraints[0].contains("comparison operators"));
        assert!(constraints[0].contains("signed"));
        assert!(constraints[1].contains("Clone"));
    }

    // ====== substitute_statement: Nop arm ======

    #[test]
    fn test_substitute_statement_nop() {
        let subs = HashMap::new();
        let result = substitute_statement(&Statement::Nop, &subs);
        assert!(matches!(result, Statement::Nop));
    }

    // ====== substitute_terminator: all arms ======

    #[test]
    fn test_substitute_terminator_return() {
        let subs = HashMap::new();
        let result = substitute_terminator(&Terminator::Return, &subs);
        assert!(matches!(result, Terminator::Return));
    }

    #[test]
    fn test_substitute_terminator_goto() {
        let subs = HashMap::new();
        let result = substitute_terminator(&Terminator::Goto(3), &subs);
        assert!(matches!(result, Terminator::Goto(3)));
    }

    #[test]
    fn test_substitute_terminator_switch_int() {
        use crate::ir::Operand;
        let subs = HashMap::new();
        let term = Terminator::SwitchInt {
            discr: Operand::Copy(crate::ir::Place::local("_1")),
            targets: vec![(0, 1), (1, 2)],
            otherwise: 3,
        };
        let result = substitute_terminator(&term, &subs);
        if let Terminator::SwitchInt {
            targets, otherwise, ..
        } = result
        {
            assert_eq!(targets.len(), 2);
            assert_eq!(targets[0], (0, 1));
            assert_eq!(targets[1], (1, 2));
            assert_eq!(otherwise, 3);
        } else {
            panic!("Expected SwitchInt");
        }
    }

    #[test]
    fn test_substitute_terminator_call() {
        use crate::ir::Operand;
        let subs = HashMap::new();
        let term = Terminator::Call {
            func: "some_func".to_string(),
            args: vec![
                Operand::Copy(crate::ir::Place::local("_1")),
                Operand::Copy(crate::ir::Place::local("_2")),
            ],
            destination: crate::ir::Place::local("_0"),
            target: 1,
        };
        let result = substitute_terminator(&term, &subs);
        if let Terminator::Call {
            func,
            args,
            destination,
            target,
        } = result
        {
            assert_eq!(func, "some_func");
            assert_eq!(args.len(), 2);
            assert_eq!(destination.local, "_0");
            assert_eq!(target, 1);
        } else {
            panic!("Expected Call");
        }
    }

    #[test]
    fn test_substitute_terminator_assert() {
        use crate::ir::{AssertKind, Operand};
        let subs = HashMap::new();
        let term = Terminator::Assert {
            cond: Operand::Copy(crate::ir::Place::local("_3")),
            expected: true,
            target: 5,
            kind: AssertKind::UserAssert,
        };
        let result = substitute_terminator(&term, &subs);
        if let Terminator::Assert {
            expected,
            target,
            kind,
            ..
        } = result
        {
            assert!(expected);
            assert_eq!(target, 5);
            assert!(matches!(kind, AssertKind::UserAssert));
        } else {
            panic!("Expected Assert");
        }
    }

    #[test]
    fn test_substitute_terminator_unreachable() {
        let subs = HashMap::new();
        let result = substitute_terminator(&Terminator::Unreachable, &subs);
        assert!(matches!(result, Terminator::Unreachable));
    }

    // ====== substitute_rvalue: all uncovered arms ======

    #[test]
    fn test_substitute_rvalue_checked_binary_op() {
        use crate::ir::{BinOp, Operand};
        let subs = HashMap::new();
        let rvalue = Rvalue::CheckedBinaryOp(
            BinOp::Add,
            Operand::Copy(crate::ir::Place::local("_1")),
            Operand::Copy(crate::ir::Place::local("_2")),
        );
        let result = substitute_rvalue(&rvalue, &subs);
        assert!(matches!(result, Rvalue::CheckedBinaryOp(BinOp::Add, _, _)));
    }

    #[test]
    fn test_substitute_rvalue_unary_op() {
        use crate::ir::{Operand, UnOp};
        let subs = HashMap::new();
        let rvalue = Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(crate::ir::Place::local("_1")));
        let result = substitute_rvalue(&rvalue, &subs);
        assert!(matches!(result, Rvalue::UnaryOp(UnOp::Neg, _)));
    }

    #[test]
    fn test_substitute_rvalue_cast_with_generic() {
        use crate::ir::Operand;
        let mut subs = HashMap::new();
        subs.insert("T".to_string(), Ty::Int(IntTy::I64));
        let rvalue = Rvalue::Cast(
            crate::ir::CastKind::IntToInt,
            Operand::Copy(crate::ir::Place::local("_1")),
            Ty::Generic("T".to_string()),
        );
        let result = substitute_rvalue(&rvalue, &subs);
        if let Rvalue::Cast(_, _, ty) = result {
            assert_eq!(ty, Ty::Int(IntTy::I64));
        } else {
            panic!("Expected Cast");
        }
    }

    #[test]
    fn test_substitute_rvalue_ref() {
        let subs = HashMap::new();
        let rvalue = Rvalue::Ref(crate::ir::Mutability::Shared, crate::ir::Place::local("_1"));
        let result = substitute_rvalue(&rvalue, &subs);
        if let Rvalue::Ref(m, place) = result {
            assert_eq!(m, crate::ir::Mutability::Shared);
            assert_eq!(place.local, "_1");
        } else {
            panic!("Expected Ref");
        }
    }

    #[test]
    fn test_substitute_rvalue_aggregate() {
        use crate::ir::{AggregateKind, Operand};
        let subs = HashMap::new();
        let rvalue = Rvalue::Aggregate(
            AggregateKind::Tuple,
            vec![
                Operand::Copy(crate::ir::Place::local("_1")),
                Operand::Copy(crate::ir::Place::local("_2")),
            ],
        );
        let result = substitute_rvalue(&rvalue, &subs);
        if let Rvalue::Aggregate(kind, ops) = result {
            assert!(matches!(kind, AggregateKind::Tuple));
            assert_eq!(ops.len(), 2);
        } else {
            panic!("Expected Aggregate");
        }
    }

    #[test]
    fn test_substitute_rvalue_len() {
        let subs = HashMap::new();
        let rvalue = Rvalue::Len(crate::ir::Place::local("_1"));
        let result = substitute_rvalue(&rvalue, &subs);
        if let Rvalue::Len(place) = result {
            assert_eq!(place.local, "_1");
        } else {
            panic!("Expected Len");
        }
    }

    #[test]
    fn test_substitute_rvalue_discriminant() {
        let subs = HashMap::new();
        let rvalue = Rvalue::Discriminant(crate::ir::Place::local("_1"));
        let result = substitute_rvalue(&rvalue, &subs);
        if let Rvalue::Discriminant(place) = result {
            assert_eq!(place.local, "_1");
        } else {
            panic!("Expected Discriminant");
        }
    }

    // ====== substitute_ty: uncovered type arms ======

    #[test]
    fn test_substitute_ty_raw_ptr() {
        let mut subs = HashMap::new();
        subs.insert("T".to_string(), Ty::Int(IntTy::I32));
        let ty = Ty::RawPtr(
            Box::new(Ty::Generic("T".to_string())),
            crate::ir::Mutability::Shared,
        );
        let result = substitute_ty(&ty, &subs);
        assert_eq!(
            result,
            Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), crate::ir::Mutability::Shared)
        );
    }

    #[test]
    fn test_substitute_ty_raw_ptr_mutable() {
        let mut subs = HashMap::new();
        subs.insert("T".to_string(), Ty::Uint(UintTy::U8));
        let ty = Ty::RawPtr(
            Box::new(Ty::Generic("T".to_string())),
            crate::ir::Mutability::Mutable,
        );
        let result = substitute_ty(&ty, &subs);
        assert_eq!(
            result,
            Ty::RawPtr(
                Box::new(Ty::Uint(UintTy::U8)),
                crate::ir::Mutability::Mutable
            )
        );
    }

    #[test]
    fn test_substitute_ty_array() {
        let mut subs = HashMap::new();
        subs.insert("T".to_string(), Ty::Int(IntTy::I32));
        let ty = Ty::Array(Box::new(Ty::Generic("T".to_string())), 10);
        let result = substitute_ty(&ty, &subs);
        assert_eq!(result, Ty::Array(Box::new(Ty::Int(IntTy::I32)), 10));
    }

    #[test]
    fn test_substitute_ty_slice() {
        let mut subs = HashMap::new();
        subs.insert("T".to_string(), Ty::Bool);
        let ty = Ty::Slice(Box::new(Ty::Generic("T".to_string())));
        let result = substitute_ty(&ty, &subs);
        assert_eq!(result, Ty::Slice(Box::new(Ty::Bool)));
    }

    #[test]
    fn test_substitute_ty_struct() {
        let mut subs = HashMap::new();
        subs.insert("T".to_string(), Ty::Int(IntTy::I64));
        let ty = Ty::Struct(
            "MyStruct".to_string(),
            vec![
                ("x".to_string(), Ty::Generic("T".to_string())),
                ("y".to_string(), Ty::Bool),
            ],
        );
        let result = substitute_ty(&ty, &subs);
        assert_eq!(
            result,
            Ty::Struct(
                "MyStruct".to_string(),
                vec![
                    ("x".to_string(), Ty::Int(IntTy::I64)),
                    ("y".to_string(), Ty::Bool),
                ]
            )
        );
    }

    #[test]
    fn test_substitute_ty_struct_nested_generic() {
        let mut subs = HashMap::new();
        subs.insert("T".to_string(), Ty::Uint(UintTy::U32));
        let ty = Ty::Struct(
            "Pair".to_string(),
            vec![
                ("first".to_string(), Ty::Generic("T".to_string())),
                (
                    "second".to_string(),
                    Ty::Ref(
                        Box::new(Ty::Generic("T".to_string())),
                        crate::ir::Mutability::Shared,
                    ),
                ),
            ],
        );
        let result = substitute_ty(&ty, &subs);
        assert_eq!(
            result,
            Ty::Struct(
                "Pair".to_string(),
                vec![
                    ("first".to_string(), Ty::Uint(UintTy::U32)),
                    (
                        "second".to_string(),
                        Ty::Ref(
                            Box::new(Ty::Uint(UintTy::U32)),
                            crate::ir::Mutability::Shared
                        )
                    ),
                ]
            )
        );
    }

    #[test]
    fn test_substitute_ty_enum() {
        let mut subs = HashMap::new();
        subs.insert("T".to_string(), Ty::Int(IntTy::I32));
        let ty = Ty::Enum(
            "Option".to_string(),
            vec![
                ("None".to_string(), vec![]),
                ("Some".to_string(), vec![Ty::Generic("T".to_string())]),
            ],
        );
        let result = substitute_ty(&ty, &subs);
        assert_eq!(
            result,
            Ty::Enum(
                "Option".to_string(),
                vec![
                    ("None".to_string(), vec![]),
                    ("Some".to_string(), vec![Ty::Int(IntTy::I32)]),
                ]
            )
        );
    }

    #[test]
    fn test_substitute_ty_enum_multiple_fields() {
        let mut subs = HashMap::new();
        subs.insert("T".to_string(), Ty::Bool);
        subs.insert("E".to_string(), Ty::Int(IntTy::I32));
        let ty = Ty::Enum(
            "Result".to_string(),
            vec![
                ("Ok".to_string(), vec![Ty::Generic("T".to_string())]),
                ("Err".to_string(), vec![Ty::Generic("E".to_string())]),
            ],
        );
        let result = substitute_ty(&ty, &subs);
        assert_eq!(
            result,
            Ty::Enum(
                "Result".to_string(),
                vec![
                    ("Ok".to_string(), vec![Ty::Bool]),
                    ("Err".to_string(), vec![Ty::Int(IntTy::I32)]),
                ]
            )
        );
    }

    #[test]
    fn test_substitute_ty_non_generic_unchanged() {
        let subs = HashMap::new();
        // Non-generic types should pass through unchanged
        assert_eq!(substitute_ty(&Ty::Bool, &subs), Ty::Bool);
        assert_eq!(substitute_ty(&Ty::Unit, &subs), Ty::Unit);
        assert_eq!(substitute_ty(&Ty::Never, &subs), Ty::Never);
        assert_eq!(substitute_ty(&Ty::Char, &subs), Ty::Char);
        assert_eq!(
            substitute_ty(&Ty::Int(IntTy::I32), &subs),
            Ty::Int(IntTy::I32)
        );
        assert_eq!(
            substitute_ty(&Ty::Uint(UintTy::U64), &subs),
            Ty::Uint(UintTy::U64)
        );
        assert_eq!(
            substitute_ty(&Ty::Named("Foo".to_string()), &subs),
            Ty::Named("Foo".to_string())
        );
        assert_eq!(substitute_ty(&Ty::SpecInt, &subs), Ty::SpecInt);
        assert_eq!(substitute_ty(&Ty::SpecNat, &subs), Ty::SpecNat);
    }

    // ====== substitute_generics with basic blocks ======

    #[test]
    fn test_substitute_generics_with_basic_blocks() {
        use crate::ir::Operand;
        // Function with basic blocks containing Nop, Assign, Goto, Call, Assert, Unreachable
        let func = Function {
            name: "complex".to_string(),
            params: vec![Local::new("_1", Ty::Generic("T".to_string()))],
            return_local: Local::new("_0", Ty::Generic("T".to_string())),
            locals: vec![Local::new("_2", Ty::Generic("T".to_string()))],
            basic_blocks: vec![
                BasicBlock {
                    statements: vec![
                        Statement::Nop,
                        Statement::Assign(
                            crate::ir::Place::local("_2"),
                            Rvalue::Use(Operand::Copy(crate::ir::Place::local("_1"))),
                        ),
                    ],
                    terminator: Terminator::Goto(1),
                },
                BasicBlock {
                    statements: vec![Statement::Assign(
                        crate::ir::Place::local("_0"),
                        Rvalue::Use(Operand::Copy(crate::ir::Place::local("_2"))),
                    )],
                    terminator: Terminator::Return,
                },
            ],
            contracts: Contracts::default(),
            loops: vec![],
            generic_params: vec![GenericParam {
                name: "T".to_string(),
                trait_bounds: vec![],
            }],
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
        };

        let mut subs = HashMap::new();
        subs.insert("T".to_string(), Ty::Int(IntTy::I32));
        let inst = TypeInstantiation::new(subs, "::<i32>".to_string());

        let result = substitute_generics(&func, &inst);

        // Check locals are substituted
        assert_eq!(result.locals[0].ty, Ty::Int(IntTy::I32));
        // Check basic blocks are traversed
        assert_eq!(result.basic_blocks.len(), 2);
        assert_eq!(result.basic_blocks[0].statements.len(), 2);
        assert!(matches!(
            result.basic_blocks[0].statements[0],
            Statement::Nop
        ));
        assert!(matches!(
            result.basic_blocks[0].terminator,
            Terminator::Goto(1)
        ));
        assert!(matches!(
            result.basic_blocks[1].terminator,
            Terminator::Return
        ));
    }

    #[test]
    fn test_substitute_generics_with_call_and_assert_blocks() {
        use crate::ir::{AssertKind, Operand};
        let func = Function {
            name: "with_call".to_string(),
            params: vec![Local::new("_1", Ty::Generic("T".to_string()))],
            return_local: Local::new("_0", Ty::Generic("T".to_string())),
            locals: vec![],
            basic_blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "helper".to_string(),
                        args: vec![Operand::Copy(crate::ir::Place::local("_1"))],
                        destination: crate::ir::Place::local("_0"),
                        target: 1,
                    },
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(crate::ir::Place::local("_0")),
                        expected: true,
                        target: 2,
                        kind: AssertKind::UserAssert,
                    },
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Unreachable,
                },
            ],
            contracts: Contracts::default(),
            loops: vec![],
            generic_params: vec![GenericParam {
                name: "T".to_string(),
                trait_bounds: vec![],
            }],
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
        };

        let mut subs = HashMap::new();
        subs.insert("T".to_string(), Ty::Bool);
        let inst = TypeInstantiation::new(subs, "::<bool>".to_string());

        let result = substitute_generics(&func, &inst);

        assert_eq!(result.name, "with_call::<bool>");
        assert_eq!(result.params[0].ty, Ty::Bool);
        assert_eq!(result.basic_blocks.len(), 3);

        // Verify Call terminator
        if let Terminator::Call {
            func: f, target, ..
        } = &result.basic_blocks[0].terminator
        {
            assert_eq!(f, "helper");
            assert_eq!(*target, 1);
        } else {
            panic!("Expected Call terminator");
        }

        // Verify Assert terminator
        if let Terminator::Assert {
            expected, target, ..
        } = &result.basic_blocks[1].terminator
        {
            assert!(*expected);
            assert_eq!(*target, 2);
        } else {
            panic!("Expected Assert terminator");
        }

        // Verify Unreachable terminator
        assert!(matches!(
            result.basic_blocks[2].terminator,
            Terminator::Unreachable
        ));
    }

    #[test]
    fn test_substitute_generics_with_switch_int() {
        use crate::ir::Operand;
        let func = Function {
            name: "switcher".to_string(),
            params: vec![Local::new("_1", Ty::Generic("T".to_string()))],
            return_local: Local::new("_0", Ty::Generic("T".to_string())),
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(crate::ir::Place::local("_1")),
                    targets: vec![(0, 1), (1, 2)],
                    otherwise: 3,
                },
            }],
            contracts: Contracts::default(),
            loops: vec![],
            generic_params: vec![GenericParam {
                name: "T".to_string(),
                trait_bounds: vec![],
            }],
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
        };

        let mut subs = HashMap::new();
        subs.insert("T".to_string(), Ty::Int(IntTy::I32));
        let inst = TypeInstantiation::new(subs, "::<i32>".to_string());

        let result = substitute_generics(&func, &inst);

        if let Terminator::SwitchInt {
            targets, otherwise, ..
        } = &result.basic_blocks[0].terminator
        {
            assert_eq!(targets.len(), 2);
            assert_eq!(*otherwise, 3);
        } else {
            panic!("Expected SwitchInt");
        }
    }

    // ====== substitute_rvalue with basic blocks: rvalue variants ======

    #[test]
    fn test_substitute_basic_block_with_checked_binary_op() {
        use crate::ir::{BinOp, Operand};
        let mut subs = HashMap::new();
        subs.insert("T".to_string(), Ty::Int(IntTy::I32));
        let bb = BasicBlock {
            statements: vec![Statement::Assign(
                crate::ir::Place::local("_3"),
                Rvalue::CheckedBinaryOp(
                    BinOp::Add,
                    Operand::Copy(crate::ir::Place::local("_1")),
                    Operand::Copy(crate::ir::Place::local("_2")),
                ),
            )],
            terminator: Terminator::Return,
        };
        let result = substitute_basic_block(&bb, &subs);
        assert_eq!(result.statements.len(), 1);
        if let Statement::Assign(_, Rvalue::CheckedBinaryOp(op, _, _)) = &result.statements[0] {
            assert_eq!(*op, BinOp::Add);
        } else {
            panic!("Expected CheckedBinaryOp");
        }
    }

    #[test]
    fn test_substitute_basic_block_with_cast() {
        use crate::ir::Operand;
        let mut subs = HashMap::new();
        subs.insert("T".to_string(), Ty::Int(IntTy::I64));
        let bb = BasicBlock {
            statements: vec![Statement::Assign(
                crate::ir::Place::local("_2"),
                Rvalue::Cast(
                    crate::ir::CastKind::IntToInt,
                    Operand::Copy(crate::ir::Place::local("_1")),
                    Ty::Generic("T".to_string()),
                ),
            )],
            terminator: Terminator::Return,
        };
        let result = substitute_basic_block(&bb, &subs);
        if let Statement::Assign(_, Rvalue::Cast(_, _, ty)) = &result.statements[0] {
            assert_eq!(*ty, Ty::Int(IntTy::I64));
        } else {
            panic!("Expected Cast with substituted type");
        }
    }

    #[test]
    fn test_substitute_basic_block_with_ref_and_aggregate() {
        use crate::ir::{AggregateKind, Operand};
        let subs = HashMap::new();
        let bb = BasicBlock {
            statements: vec![
                Statement::Assign(
                    crate::ir::Place::local("_2"),
                    Rvalue::Ref(
                        crate::ir::Mutability::Mutable,
                        crate::ir::Place::local("_1"),
                    ),
                ),
                Statement::Assign(
                    crate::ir::Place::local("_3"),
                    Rvalue::Aggregate(
                        AggregateKind::Tuple,
                        vec![Operand::Copy(crate::ir::Place::local("_1"))],
                    ),
                ),
                Statement::Assign(
                    crate::ir::Place::local("_4"),
                    Rvalue::Len(crate::ir::Place::local("_1")),
                ),
                Statement::Assign(
                    crate::ir::Place::local("_5"),
                    Rvalue::Discriminant(crate::ir::Place::local("_1")),
                ),
            ],
            terminator: Terminator::Return,
        };
        let result = substitute_basic_block(&bb, &subs);
        assert_eq!(result.statements.len(), 4);
        assert!(matches!(
            &result.statements[0],
            Statement::Assign(_, Rvalue::Ref(crate::ir::Mutability::Mutable, _))
        ));
        assert!(matches!(
            &result.statements[1],
            Statement::Assign(_, Rvalue::Aggregate(AggregateKind::Tuple, _))
        ));
        assert!(matches!(
            &result.statements[2],
            Statement::Assign(_, Rvalue::Len(_))
        ));
        assert!(matches!(
            &result.statements[3],
            Statement::Assign(_, Rvalue::Discriminant(_))
        ));
    }

    // ====== trait_bound_constraints: unsigned and unknown bounds ======

    #[test]
    fn test_trait_bound_constraints_unsigned() {
        let generic = GenericParam {
            name: "T".to_string(),
            trait_bounds: vec!["PartialOrd".to_string()],
        };
        let constraints = trait_bound_constraints(&generic, &Ty::Uint(UintTy::U32));
        assert_eq!(constraints.len(), 1);
        assert!(constraints[0].contains("comparison operators"));
        assert!(constraints[0].contains("unsigned"));
    }

    #[test]
    fn test_trait_bound_constraints_copy() {
        let generic = GenericParam {
            name: "T".to_string(),
            trait_bounds: vec!["Copy".to_string()],
        };
        let constraints = trait_bound_constraints(&generic, &Ty::Int(IntTy::I32));
        assert_eq!(constraints.len(), 1);
        assert!(constraints[0].contains("Copy"));
        assert!(constraints[0].contains("semantics"));
    }

    #[test]
    fn test_trait_bound_constraints_unknown_trait() {
        let generic = GenericParam {
            name: "T".to_string(),
            trait_bounds: vec!["Display".to_string()],
        };
        let constraints = trait_bound_constraints(&generic, &Ty::Int(IntTy::I32));
        assert_eq!(constraints.len(), 1);
        assert!(constraints[0].contains("implements"));
        assert!(constraints[0].contains("Display"));
    }

    #[test]
    fn test_trait_bound_constraints_ord_non_integer() {
        let generic = GenericParam {
            name: "T".to_string(),
            trait_bounds: vec!["Ord".to_string()],
        };
        // Non-integer type: Ord won't produce a constraint
        let constraints = trait_bound_constraints(&generic, &Ty::Bool);
        assert!(constraints.is_empty());
    }

    #[test]
    fn test_trait_bound_constraints_empty_bounds() {
        let generic = GenericParam {
            name: "T".to_string(),
            trait_bounds: vec![],
        };
        let constraints = trait_bound_constraints(&generic, &Ty::Int(IntTy::I32));
        assert!(constraints.is_empty());
    }

    #[test]
    fn test_trait_bound_constraints_multiple_unknown() {
        let generic = GenericParam {
            name: "T".to_string(),
            trait_bounds: vec![
                "Serialize".to_string(),
                "Deserialize".to_string(),
                "Clone".to_string(),
            ],
        };
        let constraints = trait_bound_constraints(&generic, &Ty::Int(IntTy::I32));
        assert_eq!(constraints.len(), 3);
        assert!(constraints[0].contains("implements"));
        assert!(constraints[0].contains("Serialize"));
        assert!(constraints[1].contains("implements"));
        assert!(constraints[1].contains("Deserialize"));
        assert!(constraints[2].contains("Clone"));
        assert!(constraints[2].contains("semantics"));
    }

    // ====== substitute_generics preserves ghost locals ======

    #[test]
    fn test_substitute_generics_preserves_ghost_flag() {
        let func = Function {
            name: "ghosted".to_string(),
            params: vec![Local {
                name: "_1".to_string(),
                ty: Ty::Generic("T".to_string()),
                is_ghost: true,
            }],
            return_local: Local::new("_0", Ty::Generic("T".to_string())),
            locals: vec![Local {
                name: "_2".to_string(),
                ty: Ty::Generic("T".to_string()),
                is_ghost: true,
            }],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            loops: vec![],
            generic_params: vec![GenericParam {
                name: "T".to_string(),
                trait_bounds: vec![],
            }],
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
        };

        let mut subs = HashMap::new();
        subs.insert("T".to_string(), Ty::Int(IntTy::I32));
        let inst = TypeInstantiation::new(subs, "::<i32>".to_string());

        let result = substitute_generics(&func, &inst);

        assert!(result.params[0].is_ghost);
        assert!(result.locals[0].is_ghost);
        assert!(!result.return_local.is_ghost);
    }
}
