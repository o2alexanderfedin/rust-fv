/// Encode Rust types as SMT-LIB sorts.
use std::collections::HashSet;

use rust_fv_smtlib::command::{Command, DatatypeVariant};
use rust_fv_smtlib::sort::Sort;

use crate::ir::{FloatTy, Function, Ty};

/// Convert a Rust type to an SMT-LIB sort.
///
/// # Encoding Strategy
///
/// - `bool` → `Bool`
/// - `i8..i128, isize` → `(_ BitVec N)` (signed operations used)
/// - `u8..u128, usize` → `(_ BitVec N)` (unsigned operations used)
/// - `char` → `(_ BitVec 32)` (Unicode scalar value)
/// - `f32` → `(_ FloatingPoint 8 24)`
/// - `f64` → `(_ FloatingPoint 11 53)`
/// - `()` / `Never` → `Bool` (unit types represented as trivial)
/// - `[T; N]` → `(Array (_ BitVec 64) T_sort)` (index by bitvec)
/// - `&[T]` / `&T` → same as T (references are transparent for values)
/// - Tuples → uninterpreted sort (TODO: datatypes in Phase 2)
/// - Structs → uninterpreted sort (TODO: datatypes in Phase 2)
/// - Enums → uninterpreted sort (TODO: datatypes in Phase 2)
pub fn encode_type(ty: &Ty) -> Sort {
    match ty {
        Ty::Bool => Sort::Bool,

        Ty::Int(ity) => Sort::BitVec(ity.bit_width()),
        Ty::Uint(uty) => Sort::BitVec(uty.bit_width()),
        Ty::Char => Sort::BitVec(32),

        Ty::Float(fty) => encode_float(fty),

        Ty::Unit | Ty::Never => Sort::Bool,

        Ty::Array(elem_ty, _) => {
            let idx_sort = Sort::BitVec(64);
            let elem_sort = encode_type(elem_ty);
            Sort::Array(Box::new(idx_sort), Box::new(elem_sort))
        }

        Ty::Slice(elem_ty) => {
            let idx_sort = Sort::BitVec(64);
            let elem_sort = encode_type(elem_ty);
            Sort::Array(Box::new(idx_sort), Box::new(elem_sort))
        }

        // References are transparent: encode the pointee type
        Ty::Ref(inner, _) => encode_type(inner),

        // Raw pointers treated as bitvectors (addresses)
        Ty::RawPtr(_, _) => Sort::BitVec(64),

        Ty::Tuple(fields) if fields.is_empty() => Sort::Bool,
        Ty::Tuple(fields) => {
            tracing::trace!(len = fields.len(), "Encoding tuple as datatype sort");
            Sort::Datatype(format!("Tuple{}", fields.len()))
        }

        Ty::Struct(name, _) => {
            tracing::trace!(struct_name = %name, "Encoding struct as datatype sort");
            Sort::Datatype(name.clone())
        }
        Ty::Enum(name, _) => {
            tracing::trace!(enum_name = %name, "Encoding enum as datatype sort");
            Sort::Datatype(name.clone())
        }
        Ty::Named(name) => {
            tracing::trace!(type_name = %name, "Encoding named type as uninterpreted sort");
            Sort::Uninterpreted(name.clone())
        }
        Ty::SpecInt | Ty::SpecNat => {
            tracing::trace!("Encoding spec integer as unbounded Int");
            Sort::Int
        }
        Ty::Generic(name) => {
            panic!(
                "Cannot encode generic type parameter '{}' -- must be monomorphized first",
                name
            )
        }
        Ty::Closure(info) => {
            tracing::trace!(closure_name = %info.name, "Encoding closure as datatype sort");
            Sort::Datatype(info.name.clone())
        }
        Ty::TraitObject(trait_name) => {
            tracing::trace!(trait_name = %trait_name, "Encoding trait object as uninterpreted sort");
            Sort::Uninterpreted(trait_name.clone())
        }
    }
}

fn encode_float(fty: &FloatTy) -> Sort {
    match fty {
        FloatTy::F32 => Sort::Float(8, 24),
        FloatTy::F64 => Sort::Float(11, 53),
    }
}

/// Collect all datatype declarations needed for a function's types.
///
/// Scans the return type, all parameter types, and all local types for
/// struct, tuple, and enum types. Each unique type name produces one
/// `DeclareDatatype` command.
///
/// These commands must appear in the SMT-LIB script BEFORE any variable
/// declarations that use the datatype sorts.
pub fn collect_datatype_declarations(func: &Function) -> Vec<Command> {
    let mut seen = HashSet::new();
    let mut declarations = Vec::new();

    // Collect types from all function locals
    let all_types = std::iter::once(&func.return_local.ty)
        .chain(func.params.iter().map(|p| &p.ty))
        .chain(func.locals.iter().map(|l| &l.ty));

    for ty in all_types {
        collect_from_type(ty, &mut seen, &mut declarations);
    }

    declarations
}

/// Recursively collect datatype declarations from a type.
fn collect_from_type(ty: &Ty, seen: &mut HashSet<String>, declarations: &mut Vec<Command>) {
    match ty {
        Ty::Struct(name, fields) => {
            if seen.insert(name.clone()) {
                // Recurse into field types first (they may be datatypes too)
                for (_field_name, field_ty) in fields {
                    collect_from_type(field_ty, seen, declarations);
                }
                let variant = DatatypeVariant {
                    constructor: format!("mk-{name}"),
                    fields: fields
                        .iter()
                        .map(|(field_name, field_ty)| {
                            (format!("{name}-{field_name}"), encode_type(field_ty))
                        })
                        .collect(),
                };
                declarations.push(Command::DeclareDatatype {
                    name: name.clone(),
                    variants: vec![variant],
                });
            }
        }
        Ty::Tuple(fields) if !fields.is_empty() => {
            let type_name = format!("Tuple{}", fields.len());
            if seen.insert(type_name.clone()) {
                // Recurse into element types
                for field_ty in fields {
                    collect_from_type(field_ty, seen, declarations);
                }
                let variant = DatatypeVariant {
                    constructor: format!("mk-{type_name}"),
                    fields: fields
                        .iter()
                        .enumerate()
                        .map(|(idx, field_ty)| {
                            (format!("{type_name}-_{idx}"), encode_type(field_ty))
                        })
                        .collect(),
                };
                declarations.push(Command::DeclareDatatype {
                    name: type_name,
                    variants: vec![variant],
                });
            }
        }
        Ty::Enum(name, variants) => {
            if seen.insert(name.clone()) {
                // Recurse into variant field types
                for (_variant_name, variant_fields) in variants {
                    for field_ty in variant_fields {
                        collect_from_type(field_ty, seen, declarations);
                    }
                }
                let dt_variants: Vec<DatatypeVariant> = variants
                    .iter()
                    .map(|(variant_name, variant_fields)| DatatypeVariant {
                        constructor: format!("mk-{variant_name}"),
                        fields: variant_fields
                            .iter()
                            .enumerate()
                            .map(|(idx, field_ty)| {
                                (format!("{variant_name}-{idx}"), encode_type(field_ty))
                            })
                            .collect(),
                    })
                    .collect();
                declarations.push(Command::DeclareDatatype {
                    name: name.clone(),
                    variants: dt_variants,
                });
            }
        }
        Ty::Closure(info) => {
            if seen.insert(info.name.clone()) {
                // Recurse into environment field types
                for (_field_name, field_ty) in &info.env_fields {
                    collect_from_type(field_ty, seen, declarations);
                }
                // Closure is encoded as a datatype with environment fields
                // (params and return type are not part of the environment structure)
                let variant = DatatypeVariant {
                    constructor: format!("mk-{}", info.name),
                    fields: info
                        .env_fields
                        .iter()
                        .map(|(field_name, field_ty)| {
                            (format!("{}-{field_name}", info.name), encode_type(field_ty))
                        })
                        .collect(),
                };
                declarations.push(Command::DeclareDatatype {
                    name: info.name.clone(),
                    variants: vec![variant],
                });
            }
        }
        // Recurse into composite types that may contain datatypes
        Ty::Array(elem_ty, _) | Ty::Slice(elem_ty) => {
            collect_from_type(elem_ty, seen, declarations);
        }
        Ty::Ref(inner, _) | Ty::RawPtr(inner, _) => {
            collect_from_type(inner, seen, declarations);
        }
        _ => {}
    }
}

/// Get the bit width used for a type in SMT encoding.
pub fn type_bit_width(ty: &Ty) -> Option<u32> {
    match ty {
        Ty::Bool => Some(1),
        Ty::Int(ity) => Some(ity.bit_width()),
        Ty::Uint(uty) => Some(uty.bit_width()),
        Ty::Char => Some(32),
        _ => None,
    }
}

/// Determine if a type should use signed bitvector operations.
pub fn is_signed_type(ty: &Ty) -> bool {
    matches!(ty, Ty::Int(_))
}

/// Encode a sealed trait as an SMT datatype (sum type) over known implementations.
///
/// This generates a DeclareDatatype command with one variant per implementation.
/// Each variant has:
/// - Constructor: `{TraitName}_{ImplType}`
/// - Selector: `as-{ImplType}` that projects to the implementation type sort
///
/// Example for `trait Stack` with impls `VecStack` and `ArrayStack`:
/// ```smt
/// (declare-datatype Stack
///   ((Stack_VecStack (as-VecStack VecStack))
///    (Stack_ArrayStack (as-ArrayStack ArrayStack))))
/// ```
pub fn encode_sealed_trait_sum_type(trait_name: &str, impl_types: &[String]) -> Command {
    let variants: Vec<DatatypeVariant> = impl_types
        .iter()
        .map(|impl_type| {
            DatatypeVariant {
                constructor: format!("{}_{}", trait_name, impl_type),
                // Single field per variant with selector name "as-{ImplType}"
                // and sort as the impl type (which will be Sort::Datatype(impl_type) or Sort::Uninterpreted(impl_type))
                fields: vec![(
                    format!("as-{}", impl_type),
                    Sort::Uninterpreted(impl_type.clone()),
                )],
            }
        })
        .collect();

    Command::DeclareDatatype {
        name: trait_name.to_string(),
        variants,
    }
}

// === Unit tests ===

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{IntTy, UintTy};
    use rust_fv_smtlib::sort::Sort;

    #[test]
    fn bool_encodes_to_bool() {
        assert_eq!(encode_type(&Ty::Bool), Sort::Bool);
    }

    #[test]
    fn i32_encodes_to_bv32() {
        assert_eq!(encode_type(&Ty::Int(IntTy::I32)), Sort::BitVec(32));
    }

    #[test]
    fn u64_encodes_to_bv64() {
        assert_eq!(encode_type(&Ty::Uint(UintTy::U64)), Sort::BitVec(64));
    }

    #[test]
    fn i8_encodes_to_bv8() {
        assert_eq!(encode_type(&Ty::Int(IntTy::I8)), Sort::BitVec(8));
    }

    #[test]
    fn i128_encodes_to_bv128() {
        assert_eq!(encode_type(&Ty::Int(IntTy::I128)), Sort::BitVec(128));
    }

    #[test]
    fn char_encodes_to_bv32() {
        assert_eq!(encode_type(&Ty::Char), Sort::BitVec(32));
    }

    #[test]
    fn f32_encodes_to_fp8_24() {
        assert_eq!(encode_type(&Ty::Float(FloatTy::F32)), Sort::Float(8, 24));
    }

    #[test]
    fn f64_encodes_to_fp11_53() {
        assert_eq!(encode_type(&Ty::Float(FloatTy::F64)), Sort::Float(11, 53));
    }

    #[test]
    fn unit_encodes_to_bool() {
        assert_eq!(encode_type(&Ty::Unit), Sort::Bool);
    }

    #[test]
    fn never_encodes_to_bool() {
        assert_eq!(encode_type(&Ty::Never), Sort::Bool);
    }

    #[test]
    fn array_i32_encodes_to_array_bv64_bv32() {
        let ty = Ty::Array(Box::new(Ty::Int(IntTy::I32)), 10);
        let expected = Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(32)));
        assert_eq!(encode_type(&ty), expected);
    }

    #[test]
    fn slice_u8_encodes_to_array_bv64_bv8() {
        let ty = Ty::Slice(Box::new(Ty::Uint(UintTy::U8)));
        let expected = Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8)));
        assert_eq!(encode_type(&ty), expected);
    }

    #[test]
    fn ref_is_transparent() {
        use crate::ir::Mutability;
        let inner = Ty::Int(IntTy::I32);
        let ref_ty = Ty::Ref(Box::new(inner.clone()), Mutability::Shared);
        assert_eq!(encode_type(&ref_ty), encode_type(&inner));
    }

    #[test]
    fn raw_ptr_encodes_to_bv64() {
        use crate::ir::Mutability;
        let ty = Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Shared);
        assert_eq!(encode_type(&ty), Sort::BitVec(64));
    }

    #[test]
    fn struct_encodes_to_datatype() {
        let ty = Ty::Struct("Vec".to_string(), vec![]);
        assert_eq!(encode_type(&ty), Sort::Datatype("Vec".to_string()));
    }

    #[test]
    fn tuple_encodes_to_datatype() {
        let ty = Ty::Tuple(vec![Ty::Int(IntTy::I32), Ty::Bool]);
        assert_eq!(encode_type(&ty), Sort::Datatype("Tuple2".to_string()));
    }

    #[test]
    fn enum_encodes_to_datatype() {
        let ty = Ty::Enum("Color".to_string(), vec![]);
        assert_eq!(encode_type(&ty), Sort::Datatype("Color".to_string()));
    }

    #[test]
    fn collect_struct_datatype_declaration() {
        let func = Function {
            name: "test".to_string(),
            return_local: crate::ir::Local {
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
            params: vec![],
            locals: vec![],
            basic_blocks: vec![],
            contracts: Default::default(),
            generic_params: vec![],
            prophecies: vec![],
            loops: vec![],
        };
        let decls = collect_datatype_declarations(&func);
        assert_eq!(decls.len(), 1);
        if let Command::DeclareDatatype { name, variants } = &decls[0] {
            assert_eq!(name, "Point");
            assert_eq!(variants.len(), 1);
            assert_eq!(variants[0].constructor, "mk-Point");
            assert_eq!(variants[0].fields.len(), 2);
            assert_eq!(variants[0].fields[0].0, "Point-x");
            assert_eq!(variants[0].fields[1].0, "Point-y");
        } else {
            panic!("Expected DeclareDatatype");
        }
    }

    #[test]
    fn collect_no_duplicates() {
        let point_ty = Ty::Struct(
            "Point".to_string(),
            vec![
                ("x".to_string(), Ty::Int(IntTy::I32)),
                ("y".to_string(), Ty::Int(IntTy::I32)),
            ],
        );
        let func = Function {
            name: "test".to_string(),
            return_local: crate::ir::Local {
                name: "_0".to_string(),
                ty: point_ty.clone(),
                is_ghost: false,
            },
            params: vec![crate::ir::Local {
                name: "_1".to_string(),
                ty: point_ty,
                is_ghost: false,
            }],
            locals: vec![],
            basic_blocks: vec![],
            contracts: Default::default(),
            generic_params: vec![],
            prophecies: vec![],
            loops: vec![],
        };
        let decls = collect_datatype_declarations(&func);
        assert_eq!(decls.len(), 1, "Should not duplicate Point declaration");
    }

    #[test]
    fn collect_tuple_datatype_declaration() {
        let func = Function {
            name: "test".to_string(),
            return_local: crate::ir::Local {
                name: "_0".to_string(),
                ty: Ty::Tuple(vec![Ty::Int(IntTy::I32), Ty::Bool]),
                is_ghost: false,
            },
            params: vec![],
            locals: vec![],
            basic_blocks: vec![],
            contracts: Default::default(),
            generic_params: vec![],
            prophecies: vec![],
            loops: vec![],
        };
        let decls = collect_datatype_declarations(&func);
        assert_eq!(decls.len(), 1);
        if let Command::DeclareDatatype { name, variants } = &decls[0] {
            assert_eq!(name, "Tuple2");
            assert_eq!(variants[0].constructor, "mk-Tuple2");
            assert_eq!(variants[0].fields[0].0, "Tuple2-_0");
            assert_eq!(variants[0].fields[1].0, "Tuple2-_1");
        } else {
            panic!("Expected DeclareDatatype");
        }
    }

    #[test]
    fn collect_enum_datatype_declaration() {
        let func = Function {
            name: "test".to_string(),
            return_local: crate::ir::Local {
                name: "_0".to_string(),
                ty: Ty::Enum(
                    "Option_i32".to_string(),
                    vec![
                        ("None".to_string(), vec![]),
                        ("Some".to_string(), vec![Ty::Int(IntTy::I32)]),
                    ],
                ),
                is_ghost: false,
            },
            params: vec![],
            locals: vec![],
            basic_blocks: vec![],
            contracts: Default::default(),
            generic_params: vec![],
            prophecies: vec![],
            loops: vec![],
        };
        let decls = collect_datatype_declarations(&func);
        assert_eq!(decls.len(), 1);
        if let Command::DeclareDatatype { name, variants } = &decls[0] {
            assert_eq!(name, "Option_i32");
            assert_eq!(variants.len(), 2);
            assert_eq!(variants[0].constructor, "mk-None");
            assert_eq!(variants[0].fields.len(), 0);
            assert_eq!(variants[1].constructor, "mk-Some");
            assert_eq!(variants[1].fields.len(), 1);
            assert_eq!(variants[1].fields[0].0, "Some-0");
        } else {
            panic!("Expected DeclareDatatype");
        }
    }

    #[test]
    fn signed_type_detection() {
        assert!(is_signed_type(&Ty::Int(IntTy::I32)));
        assert!(!is_signed_type(&Ty::Uint(UintTy::U32)));
        assert!(!is_signed_type(&Ty::Bool));
    }

    // ====== Ty::Closure encoding tests (Phase 7) ======

    #[test]
    fn test_closure_encodes_to_datatype() {
        use crate::ir::{ClosureInfo, ClosureTrait};
        let info = ClosureInfo {
            name: "closure_add".to_string(),
            env_fields: vec![("x".to_string(), Ty::Int(IntTy::I32))],
            params: vec![("y".to_string(), Ty::Int(IntTy::I32))],
            return_ty: Ty::Int(IntTy::I32),
            trait_kind: ClosureTrait::Fn,
        };
        let closure_ty = Ty::Closure(Box::new(info));
        assert_eq!(
            encode_type(&closure_ty),
            Sort::Datatype("closure_add".to_string())
        );
    }

    #[test]
    fn test_collect_closure_datatype_declaration() {
        use crate::ir::{ClosureInfo, ClosureTrait};
        let closure_info = ClosureInfo {
            name: "test_closure".to_string(),
            env_fields: vec![
                ("captured_x".to_string(), Ty::Int(IntTy::I32)),
                ("captured_y".to_string(), Ty::Bool),
            ],
            params: vec![("arg".to_string(), Ty::Int(IntTy::I32))],
            return_ty: Ty::Int(IntTy::I32),
            trait_kind: ClosureTrait::Fn,
        };

        let func = Function {
            name: "test".to_string(),
            return_local: crate::ir::Local {
                name: "_0".to_string(),
                ty: Ty::Unit,
                is_ghost: false,
            },
            params: vec![crate::ir::Local {
                name: "_1".to_string(),
                ty: Ty::Closure(Box::new(closure_info)),
                is_ghost: false,
            }],
            locals: vec![],
            basic_blocks: vec![],
            contracts: Default::default(),
            generic_params: vec![],
            prophecies: vec![],
            loops: vec![],
        };

        let decls = collect_datatype_declarations(&func);
        assert_eq!(decls.len(), 1);
        if let Command::DeclareDatatype { name, variants } = &decls[0] {
            assert_eq!(name, "test_closure");
            assert_eq!(variants.len(), 1);
            assert_eq!(variants[0].constructor, "mk-test_closure");
            assert_eq!(
                variants[0].fields.len(),
                2,
                "Should have 2 environment fields"
            );
            assert_eq!(variants[0].fields[0].0, "test_closure-captured_x");
            assert_eq!(variants[0].fields[0].1, Sort::BitVec(32));
            assert_eq!(variants[0].fields[1].0, "test_closure-captured_y");
            assert_eq!(variants[0].fields[1].1, Sort::Bool);
        } else {
            panic!("Expected DeclareDatatype");
        }
    }

    #[test]
    fn test_closure_env_field_types_encoded() {
        use crate::ir::{ClosureInfo, ClosureTrait};
        let closure_info = ClosureInfo {
            name: "multi_type_closure".to_string(),
            env_fields: vec![
                ("i32_field".to_string(), Ty::Int(IntTy::I32)),
                ("bool_field".to_string(), Ty::Bool),
                ("u64_field".to_string(), Ty::Uint(UintTy::U64)),
            ],
            params: vec![],
            return_ty: Ty::Unit,
            trait_kind: ClosureTrait::FnMut,
        };

        let func = Function {
            name: "test".to_string(),
            return_local: crate::ir::Local {
                name: "_0".to_string(),
                ty: Ty::Closure(Box::new(closure_info)),
                is_ghost: false,
            },
            params: vec![],
            locals: vec![],
            basic_blocks: vec![],
            contracts: Default::default(),
            generic_params: vec![],
            prophecies: vec![],
            loops: vec![],
        };

        let decls = collect_datatype_declarations(&func);
        assert_eq!(decls.len(), 1);
        if let Command::DeclareDatatype { name: _, variants } = &decls[0] {
            let variant = &variants[0];
            assert_eq!(variant.fields.len(), 3);
            assert_eq!(variant.fields[0].1, Sort::BitVec(32)); // i32 -> BitVec(32)
            assert_eq!(variant.fields[1].1, Sort::Bool); // bool -> Bool
            assert_eq!(variant.fields[2].1, Sort::BitVec(64)); // u64 -> BitVec(64)
        } else {
            panic!("Expected DeclareDatatype");
        }
    }

    // ====== Ty::TraitObject encoding tests (Phase 8) ======

    #[test]
    fn test_encode_type_trait_object() {
        let trait_obj = Ty::TraitObject("Stack".to_string());
        assert_eq!(
            encode_type(&trait_obj),
            Sort::Uninterpreted("Stack".to_string())
        );
    }

    // ====== Sealed trait sum type encoding tests (Phase 8-02) ======

    #[test]
    fn test_encode_sealed_trait_sum_type_two_impls() {
        let impl_types = vec!["VecStack".to_string(), "ArrayStack".to_string()];
        let cmd = super::encode_sealed_trait_sum_type("Stack", &impl_types);

        if let Command::DeclareDatatype { name, variants } = cmd {
            assert_eq!(name, "Stack");
            assert_eq!(variants.len(), 2);
            assert_eq!(variants[0].constructor, "Stack_VecStack");
            assert_eq!(variants[1].constructor, "Stack_ArrayStack");
        } else {
            panic!("Expected DeclareDatatype command");
        }
    }

    #[test]
    fn test_encode_sealed_trait_sum_type_single_impl() {
        let impl_types = vec!["SingleImpl".to_string()];
        let cmd = super::encode_sealed_trait_sum_type("MyTrait", &impl_types);

        if let Command::DeclareDatatype { name, variants } = cmd {
            assert_eq!(name, "MyTrait");
            assert_eq!(variants.len(), 1);
            assert_eq!(variants[0].constructor, "MyTrait_SingleImpl");
        } else {
            panic!("Expected DeclareDatatype command");
        }
    }

    #[test]
    fn test_encode_sealed_trait_sum_type_three_impls() {
        let impl_types = vec![
            "ImplA".to_string(),
            "ImplB".to_string(),
            "ImplC".to_string(),
        ];
        let cmd = super::encode_sealed_trait_sum_type("Trait", &impl_types);

        if let Command::DeclareDatatype { name, variants } = cmd {
            assert_eq!(name, "Trait");
            assert_eq!(variants.len(), 3);
            assert_eq!(variants[0].constructor, "Trait_ImplA");
            assert_eq!(variants[1].constructor, "Trait_ImplB");
            assert_eq!(variants[2].constructor, "Trait_ImplC");
            // Check that each variant has the correct selector pattern
            assert_eq!(variants[0].fields.len(), 1);
            assert_eq!(variants[0].fields[0].0, "as-ImplA");
        } else {
            panic!("Expected DeclareDatatype command");
        }
    }
}
