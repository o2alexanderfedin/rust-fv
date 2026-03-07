/// Tests for const generic parameter verification (LANG-01).
///
/// Covers: Ty::ConstGeneric IR variant, Ty::Union variant, VcKind new variants,
/// SMT sort encoding, MIR extraction, monomorphization, spec parser resolution.
use rust_fv_analysis::ir::{
    BasicBlock, Contracts, DropLocalInfo, Function, GenericParam, IntTy, Local, PinGhostState,
    Terminator, Ty, UintTy, UnionGhostState,
};
use rust_fv_analysis::vcgen::VcKind;

// === Task 1: IR type construction and sort encoding ===

#[test]
fn const_generic_ty_constructs_and_pattern_matches() {
    let ty = Ty::ConstGeneric("N".to_string(), Box::new(Ty::Uint(UintTy::Usize)));
    match &ty {
        Ty::ConstGeneric(name, inner) => {
            assert_eq!(name, "N");
            assert_eq!(**inner, Ty::Uint(UintTy::Usize));
        }
        _ => panic!("Expected Ty::ConstGeneric"),
    }
}

#[test]
fn const_generic_bool_ty_constructs() {
    let ty = Ty::ConstGeneric("B".to_string(), Box::new(Ty::Bool));
    match &ty {
        Ty::ConstGeneric(name, inner) => {
            assert_eq!(name, "B");
            assert_eq!(**inner, Ty::Bool);
        }
        _ => panic!("Expected Ty::ConstGeneric"),
    }
}

#[test]
fn union_ty_constructs_with_fields() {
    let ty = Ty::Union(
        "MyUnion".to_string(),
        vec![
            ("i".to_string(), Ty::Int(IntTy::I32)),
            ("f".to_string(), Ty::Uint(UintTy::U32)),
        ],
    );
    match &ty {
        Ty::Union(name, fields) => {
            assert_eq!(name, "MyUnion");
            assert_eq!(fields.len(), 2);
            assert_eq!(fields[0].0, "i");
            assert_eq!(fields[1].0, "f");
        }
        _ => panic!("Expected Ty::Union"),
    }
}

#[test]
fn vc_kind_union_access_exists() {
    let _kind = VcKind::UnionAccess;
}

#[test]
fn vc_kind_drop_order_exists() {
    let _kind = VcKind::DropOrder;
}

#[test]
fn vc_kind_pin_safety_exists() {
    let _kind = VcKind::PinSafety;
}

#[test]
fn encode_sort_const_generic_usize_returns_int() {
    use rust_fv_analysis::encode_sort::encode_type;
    use rust_fv_smtlib::sort::Sort;

    let ty = Ty::ConstGeneric("N".to_string(), Box::new(Ty::Uint(UintTy::Usize)));
    let sort = encode_type(&ty);
    // Const generic integer parameters are encoded as Int (unbounded) for SMT reasoning
    assert_eq!(sort, Sort::Int);
}

#[test]
fn encode_sort_const_generic_bool_returns_bool() {
    use rust_fv_analysis::encode_sort::encode_type;
    use rust_fv_smtlib::sort::Sort;

    let ty = Ty::ConstGeneric("B".to_string(), Box::new(Ty::Bool));
    let sort = encode_type(&ty);
    assert_eq!(sort, Sort::Bool);
}

#[test]
fn encode_sort_union_returns_bitvec() {
    use rust_fv_analysis::encode_sort::encode_type;
    use rust_fv_smtlib::sort::Sort;

    // Union with i32 (4 bytes) and u16 (2 bytes) -> BitVec of max(4,2) * 8 = 32
    let ty = Ty::Union(
        "U".to_string(),
        vec![
            ("a".to_string(), Ty::Int(IntTy::I32)),
            ("b".to_string(), Ty::Uint(UintTy::U16)),
        ],
    );
    let sort = encode_type(&ty);
    assert_eq!(sort, Sort::BitVec(32));
}

#[test]
fn generic_param_has_is_const_field() {
    let param = GenericParam {
        name: "N".to_string(),
        trait_bounds: vec![],
        is_const: true,
        const_ty: Some(Ty::Uint(UintTy::Usize)),
    };
    assert!(param.is_const);
    assert_eq!(param.const_ty, Some(Ty::Uint(UintTy::Usize)));
}

#[test]
fn generic_param_default_is_not_const() {
    let param = GenericParam {
        name: "T".to_string(),
        trait_bounds: vec!["Ord".to_string()],
        is_const: false,
        const_ty: None,
    };
    assert!(!param.is_const);
    assert_eq!(param.const_ty, None);
}

#[test]
fn function_has_new_ghost_state_fields() {
    let func = make_test_function();
    assert!(func.union_ghost_states.is_empty());
    assert!(func.pin_ghost_states.is_empty());
    assert!(func.drop_locals.is_empty());
}

#[test]
fn union_ghost_state_constructs() {
    let ugs = UnionGhostState {
        local_name: "_1".to_string(),
        union_name: "MyUnion".to_string(),
        fields: vec![
            ("i".to_string(), Ty::Int(IntTy::I32)),
            ("f".to_string(), Ty::Uint(UintTy::U32)),
        ],
    };
    assert_eq!(ugs.local_name, "_1");
    assert_eq!(ugs.union_name, "MyUnion");
    assert_eq!(ugs.fields.len(), 2);
}

#[test]
fn pin_ghost_state_constructs() {
    let pgs = PinGhostState {
        local_name: "_2".to_string(),
        inner_ty: Ty::Int(IntTy::I32),
    };
    assert_eq!(pgs.local_name, "_2");
    assert_eq!(pgs.inner_ty, Ty::Int(IntTy::I32));
}

#[test]
fn drop_local_info_constructs() {
    let dli = DropLocalInfo {
        local_name: "_3".to_string(),
        ty: Ty::Struct("Foo".to_string(), vec![]),
        has_drop: true,
        drop_order: 0,
    };
    assert_eq!(dli.local_name, "_3");
    assert!(dli.has_drop);
    assert_eq!(dli.drop_order, 0);
}

// === Task 2: Monomorphization, spec parser, VCGen wiring ===

#[test]
fn monomorphize_substitutes_const_generic() {
    use rust_fv_analysis::monomorphize::{TypeInstantiation, substitute_generics};
    use std::collections::HashMap;

    let mut func = make_test_function();
    func.name = "buffer_init".to_string();
    func.generic_params = vec![GenericParam {
        name: "N".to_string(),
        trait_bounds: vec![],
        is_const: true,
        const_ty: Some(Ty::Uint(UintTy::Usize)),
    }];
    // Parameter with const generic type
    func.params = vec![Local {
        name: "_1".to_string(),
        ty: Ty::ConstGeneric("N".to_string(), Box::new(Ty::Uint(UintTy::Usize))),
        is_ghost: false,
    }];

    let mut subs = HashMap::new();
    subs.insert("N".to_string(), Ty::Uint(UintTy::Usize));
    let inst = TypeInstantiation::new(subs, "::<5>".to_string());

    let result = substitute_generics(&func, &inst);
    // After monomorphization, the ConstGeneric type is substituted
    assert_eq!(result.params[0].ty, Ty::Uint(UintTy::Usize));
}

#[test]
fn spec_parser_resolves_const_generic_name() {
    use rust_fv_analysis::spec_parser::parse_spec_expr;

    let mut func = make_test_function();
    func.generic_params = vec![GenericParam {
        name: "N".to_string(),
        trait_bounds: vec![],
        is_const: true,
        const_ty: Some(Ty::Uint(UintTy::Usize)),
    }];

    // The spec expression "N > 0" should resolve N as an SMT constant
    let term = parse_spec_expr("N > 0", &func);
    assert!(
        term.is_some(),
        "Spec parser should resolve const generic parameter N in expression"
    );
}

#[test]
fn vcgen_emits_const_generic_declarations() {
    use rust_fv_analysis::ir::{Constant, Operand, Place, Rvalue, SpecExpr, Statement};
    use rust_fv_analysis::vcgen;

    let mut func = make_test_function();
    func.name = "first".to_string();
    func.generic_params = vec![GenericParam {
        name: "N".to_string(),
        trait_bounds: vec![],
        is_const: true,
        const_ty: Some(Ty::Uint(UintTy::Usize)),
    }];
    func.params = vec![Local {
        name: "_1".to_string(),
        ty: Ty::Array(Box::new(Ty::Int(IntTy::I32)), 0),
        is_ghost: false,
    }];
    func.return_local = Local {
        name: "_0".to_string(),
        ty: Ty::Int(IntTy::I32),
        is_ghost: false,
    };
    // Add both requires and ensures to generate VCs
    func.contracts.requires = vec![SpecExpr {
        raw: "N > 0".to_string(),
    }];
    func.contracts.ensures = vec![SpecExpr {
        raw: "true".to_string(),
    }];

    // Simple body: _0 = 42; return
    func.basic_blocks = vec![BasicBlock {
        statements: vec![Statement::Assign(
            Place {
                local: "_0".to_string(),
                projections: vec![],
            },
            Rvalue::Use(Operand::Constant(Constant::Int(42, IntTy::I32))),
        )],
        terminator: Terminator::Return,
    }];

    let vcs = vcgen::generate_vcs(&func, None);
    // Should generate at least one VC (postcondition)
    assert!(
        !vcs.conditions.is_empty(),
        "VCGen should generate VCs for function with const generic + ensures clause"
    );

    // Check that at least one VC script contains the const generic parameter N
    let has_n_ref = vcs.conditions.iter().any(|vc| {
        let script = vc.script.to_string();
        script.contains(" N ")
    });
    assert!(
        has_n_ref,
        "VCGen should emit SMT constant declaration for const generic parameter N"
    );
}

#[test]
fn const_generic_with_requires_and_ensures_generates_vc() {
    use rust_fv_analysis::ir::{Constant, Operand, Place, Rvalue, SpecExpr, Statement};
    use rust_fv_analysis::vcgen;

    let mut func = make_test_function();
    func.name = "sized_buffer".to_string();
    func.generic_params = vec![GenericParam {
        name: "N".to_string(),
        trait_bounds: vec![],
        is_const: true,
        const_ty: Some(Ty::Uint(UintTy::Usize)),
    }];
    func.contracts.requires = vec![SpecExpr {
        raw: "N > 0".to_string(),
    }];
    func.contracts.ensures = vec![SpecExpr {
        raw: "result == true".to_string(),
    }];
    func.return_local = Local {
        name: "_0".to_string(),
        ty: Ty::Bool,
        is_ghost: false,
    };
    func.basic_blocks = vec![BasicBlock {
        statements: vec![Statement::Assign(
            Place {
                local: "_0".to_string(),
                projections: vec![],
            },
            Rvalue::Use(Operand::Constant(Constant::Bool(true))),
        )],
        terminator: Terminator::Return,
    }];

    let vcs = vcgen::generate_vcs(&func, None);
    // Should generate postcondition VCs
    assert!(
        !vcs.conditions.is_empty(),
        "Should generate VCs for function with const generic requires + ensures"
    );

    // The requires clause N > 0 should appear as an assumption in postcondition VCs
    let has_requires_in_script = vcs.conditions.iter().any(|vc| {
        let script = vc.script.to_string();
        // The requires clause should be encoded as an assertion/assumption containing N
        script.contains(" N ")
    });
    assert!(
        has_requires_in_script,
        "Postcondition VC script should contain const generic parameter N from requires clause"
    );
}

// Helper to construct a test function with all new fields
fn make_test_function() -> Function {
    Function {
        name: "test_fn".to_string(),
        params: vec![],
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Unit,
            is_ghost: false,
        },
        locals: vec![],
        basic_blocks: vec![BasicBlock {
            statements: vec![],
            terminator: Terminator::Return,
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
        coroutine_info: None,
        refcell_ghost_states: vec![],
        maybeuninit_ghost_states: vec![],
        union_ghost_states: vec![],
        pin_ghost_states: vec![],
        drop_locals: vec![],
        hrtb_bounds: vec![],
    }
}
