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
            },
            loops: vec![],
            generic_params: vec![GenericParam {
                name: "T".to_string(),
                trait_bounds: vec![],
            }],
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
}
