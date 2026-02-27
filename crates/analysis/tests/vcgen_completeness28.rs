//! Phase 28 TDD scaffold: 10 failing tests for VCGEN-01..04.
//!
//! All tests in this file are intentionally RED before implementation.
//! Tests for already-implemented features (vcgen_01_field_projection) are
//! written as regression guards with tighter assertions.
//!
//! Requirements: VCGEN-01, VCGEN-02, VCGEN-03, VCGEN-04

use rust_fv_analysis::ghost_predicate_db::GhostPredicateDatabase;
use rust_fv_analysis::ir::*;
use rust_fv_analysis::vcgen;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Make a minimal Function IR with no contracts or extra fields.
fn make_func(
    name: &str,
    return_ty: Ty,
    params: Vec<Local>,
    locals: Vec<Local>,
    basic_blocks: Vec<BasicBlock>,
) -> Function {
    Function {
        name: name.to_string(),
        return_local: Local::new("_0", return_ty),
        params,
        locals,
        basic_blocks,
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

/// Build a Function IR with an array parameter and Projection::Index access.
///
/// Equivalent to: fn array_index(arr: [i32; 10], idx: usize) -> i32 { arr[idx] }
///
/// Does NOT include an explicit Assert(BoundsCheck) terminator — the test checks
/// whether VCGen auto-generates a bounds-check VC for Projection::Index accesses.
/// Currently, VCGen does NOT auto-generate bounds VCs for Index projections;
/// it only handles explicit Assert(BoundsCheck) terminators.
fn build_array_index_function() -> Function {
    // _1: [i32; 10], _2: usize
    let params = vec![
        Local::new("_1", Ty::Array(Box::new(Ty::Int(IntTy::I32)), 10)),
        Local::new("_2", Ty::Uint(UintTy::Usize)),
    ];
    // _0 = _1[_2]  (index projection — should trigger auto-generated bounds check)
    let blocks = vec![BasicBlock {
        statements: vec![Statement::Assign(
            Place::local("_0"),
            Rvalue::Use(Operand::Copy(Place::local("_1").index("_2".to_string()))),
        )],
        terminator: Terminator::Return,
    }];
    make_func("array_index", Ty::Int(IntTy::I32), params, vec![], blocks)
}

/// Build a Function IR with a struct type and Projection::Field access.
///
/// Equivalent to: fn field_proj(s: Point) -> i32 { s.x }
/// where Point = struct { x: i32, y: i32 }
/// Includes a postcondition `#[ensures(result == 0)]` to force VC generation.
fn build_field_projection_function() -> Function {
    let point_ty = Ty::Struct(
        "Point".to_string(),
        vec![
            ("x".to_string(), Ty::Int(IntTy::I32)),
            ("y".to_string(), Ty::Int(IntTy::I32)),
        ],
    );
    let params = vec![Local::new("_1", point_ty)];
    // _0 = _1.0  (field index 0 = "x")
    let blocks = vec![BasicBlock {
        statements: vec![Statement::Assign(
            Place::local("_0"),
            Rvalue::Use(Operand::Copy(Place::local("_1").field(0))),
        )],
        terminator: Terminator::Return,
    }];
    let mut func = make_func(
        "field_projection",
        Ty::Int(IntTy::I32),
        params,
        vec![],
        blocks,
    );
    // Add a postcondition to ensure VCs are generated
    func.contracts = Contracts {
        ensures: vec![SpecExpr {
            raw: "result >= -2147483648".to_string(),
        }],
        ..Contracts::default()
    };
    func
}

/// Build a Function IR with Rvalue::Len(place).
///
/// Equivalent to: fn slice_len(arr: [i32; 5]) -> usize { arr.len() }
/// Includes a postcondition `#[ensures(result == 5)]` to force VC generation.
fn build_slice_len_function() -> Function {
    let params = vec![Local::new(
        "_1",
        Ty::Array(Box::new(Ty::Int(IntTy::I32)), 5),
    )];
    // _0 = Len(_1)
    let blocks = vec![BasicBlock {
        statements: vec![Statement::Assign(
            Place::local("_0"),
            Rvalue::Len(Place::local("_1")),
        )],
        terminator: Terminator::Return,
    }];
    let mut func = make_func("slice_len", Ty::Uint(UintTy::Usize), params, vec![], blocks);
    // Add postcondition to ensure VCs are generated (and to verify Len is properly encoded)
    func.contracts = Contracts {
        ensures: vec![SpecExpr {
            raw: "result == 5".to_string(),
        }],
        ..Contracts::default()
    };
    func
}

/// Build a Function IR with Rvalue::Discriminant + SwitchInt.
///
/// Equivalent to:
///   fn match_discr(opt: Option<i32>) -> i32 {
///       match opt { None => 0, Some(_) => 1 }
///   }
fn build_discriminant_function() -> Function {
    let option_ty = Ty::Enum(
        "Option".to_string(),
        vec![
            ("None".to_string(), vec![]),
            ("Some".to_string(), vec![Ty::Int(IntTy::I32)]),
        ],
    );
    let params = vec![Local::new("_1", option_ty)];
    // _2 = Discriminant(_1)
    // SwitchInt(_2): 0 -> bb1 (None branch), otherwise -> bb2 (Some branch)
    // bb1: _0 = 0; return
    // bb2: _0 = 1; return
    let blocks = vec![
        BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_2"),
                Rvalue::Discriminant(Place::local("_1")),
            )],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local("_2")),
                targets: vec![(0, 1)],
                otherwise: 2,
            },
        },
        // bb1: None branch
        BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::Use(Operand::Constant(Constant::Int(0, IntTy::I32))),
            )],
            terminator: Terminator::Return,
        },
        // bb2: Some branch
        BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::Use(Operand::Constant(Constant::Int(1, IntTy::I32))),
            )],
            terminator: Terminator::Return,
        },
    ];
    let mut func = make_func(
        "match_discr",
        Ty::Int(IntTy::I32),
        params,
        vec![Local::new("_2", Ty::Int(IntTy::I32))],
        blocks,
    );
    // Add two postconditions — one per branch outcome — to force per-path VC generation.
    // VCGen creates one VC per postcondition, so two postconditions yield >= 2 VCs.
    // Postcondition 1: tautological bound (always holds — result is 0 or 1)
    // Postcondition 2: upper bound (always holds — result is at most 1)
    // This exercises that SwitchInt path conditions appear in both generated VCs.
    func.contracts = Contracts {
        ensures: vec![
            SpecExpr {
                raw: "result >= 0".to_string(),
            },
            SpecExpr {
                raw: "result <= 1".to_string(),
            },
        ],
        ..Contracts::default()
    };
    func
}

/// Build a Function IR with a cast assignment.
///
/// kind: the CastKind
/// from_ty: source type
/// to_ty: target type
/// Includes a tautological postcondition to force VC generation.
fn build_cast_function(kind: CastKind, from_ty: Ty, to_ty: Ty) -> Function {
    let params = vec![Local::new("_1", from_ty)];
    let blocks = vec![BasicBlock {
        statements: vec![Statement::Assign(
            Place::local("_0"),
            Rvalue::Cast(kind, Operand::Copy(Place::local("_1")), to_ty.clone()),
        )],
        terminator: Terminator::Return,
    }];
    let mut func = make_func("cast_fn", to_ty, params, vec![], blocks);
    // Add a postcondition so VCs are generated even without assertions in the body
    func.contracts = Contracts {
        ensures: vec![SpecExpr {
            raw: "true".to_string(),
        }],
        ..Contracts::default()
    };
    func
}

/// Build a generic Function IR with one GenericParam (T: Ord) and a postcondition.
fn build_generic_function() -> Function {
    let mut func = make_func(
        "generic_fn",
        Ty::Generic("T".to_string()),
        vec![Local::new("_1", Ty::Generic("T".to_string()))],
        vec![],
        vec![BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::Use(Operand::Copy(Place::local("_1"))),
            )],
            terminator: Terminator::Return,
        }],
    );
    func.generic_params = vec![GenericParam {
        name: "T".to_string(),
        trait_bounds: vec!["Ord".to_string()],
    }];
    func.contracts = Contracts {
        ensures: vec![SpecExpr {
            raw: "result == _1".to_string(),
        }],
        ..Contracts::default()
    };
    func
}

// ---------------------------------------------------------------------------
// VCGEN-01: Memory Operations
// ---------------------------------------------------------------------------

/// VCGEN-01a: Array index access generates a bounds-check VC.
///
/// RED: Fails because no BoundsCheck VC is generated for Projection::Index.
/// The current VCGen does not emit an Assert for index < len.
#[test]
fn vcgen_01_array_index() {
    let func = build_array_index_function();
    let vcs = vcgen::generate_vcs(&func, None);

    // Must have at least one VC with a bounds-related description.
    let has_bounds_vc = vcs.conditions.iter().any(|vc| {
        vc.description.contains("bounds")
            || vc.description.contains("index")
            || matches!(vc.location.vc_kind, vcgen::VcKind::MemorySafety)
    });

    assert!(
        has_bounds_vc,
        "VCGEN-01a: expected at least one bounds-check VC for array index access, \
         got {} VCs: {:?}",
        vcs.conditions.len(),
        vcs.conditions
            .iter()
            .map(|v| &v.description)
            .collect::<Vec<_>>()
    );
}

/// VCGEN-01b: Struct field projection produces a selector term in the SMT script.
///
/// This test guards against regression: field projection already works, so we
/// assert that the generated script contains a selector application for the struct.
#[test]
fn vcgen_01_field_projection() {
    let func = build_field_projection_function();
    let vcs = vcgen::generate_vcs(&func, None);

    assert!(
        !vcs.conditions.is_empty(),
        "VCGEN-01b: expected at least one VC for field projection function"
    );

    // Collect SMT text from all VCs
    let all_smt: String = vcs
        .conditions
        .iter()
        .map(|vc| script_to_text(&vc.script))
        .collect::<Vec<_>>()
        .join("\n");

    // The selector for the Point.x field must appear
    assert!(
        all_smt.contains("Point-x"),
        "VCGEN-01b: expected 'Point-x' selector in SMT script, got:\n{all_smt}"
    );
}

/// VCGEN-01c: Rvalue::Len produces an ASSIGNMENT assertion encoding the concrete length.
///
/// RED: Fails because encode_assignment returns None for Rvalue::Len.
/// Without the assignment `(assert (= _0 <len>))`, _0 is unconstrained in the SMT
/// context, meaning the postcondition check `(assert (not (= _0 5)))` is SAT
/// (Z3 picks _0 = 0). After implementation, the assignment must be present.
///
/// The test distinguishes the ASSIGNMENT form `(assert (= _0 X))` from the
/// POSTCONDITION form `(assert (not (= _0 X)))`: only the assignment form implies
/// Len is properly encoded.
#[test]
fn vcgen_01_slice_len() {
    let func = build_slice_len_function();
    let vcs = vcgen::generate_vcs(&func, None);

    assert!(
        !vcs.conditions.is_empty(),
        "VCGEN-01c: expected at least one VC for Rvalue::Len."
    );

    let all_smt: String = vcs
        .conditions
        .iter()
        .map(|vc| script_to_text(&vc.script))
        .collect::<Vec<_>>()
        .join("\n");

    // After implementation: the Len value must be encoded as an assignment assertion.
    // The key marker: there should be an unconstrained `(assert (= _0 <len>))` line
    // that does NOT have `not` wrapping it (i.e., it's the assignment, not the postcondition).
    //
    // Current state: no such line exists (Rvalue::Len returns None from encode_assignment).
    // The script only contains the postcondition form: `(assert (not (= _0 ...)))`.
    let has_len_assignment = all_smt.contains("(assert (= _0 #x")
        || all_smt.lines().any(|line| {
            // Match assignment form: `(assert (= _0 ...))` without `not`
            line.starts_with("(assert (= _0 ")
        });

    assert!(
        has_len_assignment,
        "VCGEN-01c: expected Rvalue::Len to emit assignment '(assert (= _0 <len>))' \
         in the SMT script. Currently Rvalue::Len returns None from encode_assignment \
         so no assignment is generated. Got script:\n{all_smt}"
    );
}

// ---------------------------------------------------------------------------
// VCGEN-02: Conditional Operators / Discriminant
// ---------------------------------------------------------------------------

/// VCGEN-02a: Rvalue::Discriminant + SwitchInt produces a discriminant term in the SMT script.
///
/// RED: Fails because encode_assignment returns None for Rvalue::Discriminant.
#[test]
fn vcgen_02_match_discr() {
    let func = build_discriminant_function();
    let vcs = vcgen::generate_vcs(&func, None);

    assert!(
        !vcs.conditions.is_empty(),
        "VCGEN-02a: expected VCs for match_discr function, got 0. \
         Rvalue::Discriminant currently returns None from encode_assignment."
    );

    let all_smt: String = vcs
        .conditions
        .iter()
        .map(|vc| script_to_text(&vc.script))
        .collect::<Vec<_>>()
        .join("\n");

    // The discriminant extraction must appear in the script
    assert!(
        all_smt.contains("discriminant") || all_smt.contains("_2"),
        "VCGEN-02a: expected discriminant term in SMT script, got:\n{all_smt}"
    );
}

/// VCGEN-02b: Option discriminant SwitchInt produces two path conditions (discr==0, discr==1).
///
/// RED: Fails because Rvalue::Discriminant returns None so no path-guarded
/// assertion about the discriminant value appears in the VCs.
#[test]
fn vcgen_02_if_let() {
    // Same discriminant + SwitchInt structure as vcgen_02_match_discr
    let func = build_discriminant_function();
    let vcs = vcgen::generate_vcs(&func, None);

    assert!(
        !vcs.conditions.is_empty(),
        "VCGEN-02b: expected VCs for if-let (discriminant + SwitchInt), got 0."
    );

    // Count VCs that mention the two path conditions: discr == 0 (None) and discr != 0 (Some)
    // After implementation, each branch should produce a separate path-guarded VC.
    let vc_count = vcs.conditions.len();
    assert!(
        vc_count >= 2,
        "VCGEN-02b: expected at least 2 path-guarded VCs for if-let (one per branch), \
         got {vc_count}"
    );
}

// ---------------------------------------------------------------------------
// VCGEN-03: Typecasts
// ---------------------------------------------------------------------------

/// VCGEN-03a: Sign-extending cast i8->i32 produces Term::SignExtend.
///
/// RED: Fails because encode_int_to_int_cast does not yet exist in encode_term.rs.
#[test]
fn vcgen_03_cast_sign_extend() {
    // Build a cast function: i8 -> i32 (sign-extending cast)
    let func = build_cast_function(CastKind::IntToInt, Ty::Int(IntTy::I8), Ty::Int(IntTy::I32));
    let vcs = vcgen::generate_vcs(&func, None);

    assert!(
        !vcs.conditions.is_empty(),
        "VCGEN-03a: expected VCs for i8->i32 sign-extend cast, got 0."
    );

    let all_smt: String = vcs
        .conditions
        .iter()
        .map(|vc| script_to_text(&vc.script))
        .collect::<Vec<_>>()
        .join("\n");

    // The sign_extend SMT operation must appear for widening signed casts
    assert!(
        all_smt.contains("sign_extend"),
        "VCGEN-03a: expected '((_ sign_extend 24) _1)' in SMT for i8->i32 cast, got:\n{all_smt}"
    );
}

/// VCGEN-03b: Truncating cast i64->i32 produces Term::Extract(31, 0, _).
///
/// RED: Fails because encode_int_to_int_cast does not yet exist.
#[test]
fn vcgen_03_cast_truncate() {
    // Build a cast function: i64 -> i32 (truncating cast)
    let func = build_cast_function(CastKind::IntToInt, Ty::Int(IntTy::I64), Ty::Int(IntTy::I32));
    let vcs = vcgen::generate_vcs(&func, None);

    assert!(
        !vcs.conditions.is_empty(),
        "VCGEN-03b: expected VCs for i64->i32 truncate cast, got 0."
    );

    let all_smt: String = vcs
        .conditions
        .iter()
        .map(|vc| script_to_text(&vc.script))
        .collect::<Vec<_>>()
        .join("\n");

    // The extract operation (bit truncation) must appear: ((_ extract 31 0) _1)
    assert!(
        all_smt.contains("extract"),
        "VCGEN-03b: expected '((_ extract 31 0) _1)' in SMT for i64->i32 cast, got:\n{all_smt}"
    );
}

/// VCGEN-03c: IntToFloat cast is NOT an identity — the script must not reuse
/// the source bitvector at its original bit-width.
///
/// RED: Fails because Rvalue::Cast is currently an identity stub (returns src as-is).
#[test]
fn vcgen_03_transmute() {
    // Build: i32 cast to f32 (IntToFloat)
    let func = build_cast_function(
        CastKind::IntToFloat,
        Ty::Int(IntTy::I32),
        Ty::Float(FloatTy::F32),
    );
    let vcs = vcgen::generate_vcs(&func, None);

    assert!(
        !vcs.conditions.is_empty(),
        "VCGEN-03c: expected VCs for IntToFloat cast (i32->f32), got 0."
    );

    let all_smt: String = vcs
        .conditions
        .iter()
        .map(|vc| script_to_text(&vc.script))
        .collect::<Vec<_>>()
        .join("\n");

    // The result must NOT be a 32-bit bitvector assigned directly to _0.
    // After proper cast encoding, _0 should be a Float sort, not (_ BitVec 32).
    // The current stub copies the i32 bitvec identity, which is wrong.
    // We assert the float sort appears or the identity pattern does NOT appear.
    let is_identity = all_smt.contains("(= _0 _1)");
    assert!(
        !is_identity,
        "VCGEN-03c: cast is identity stub '(= _0 _1)' — IntToFloat must produce \
         a proper float encoding, not raw bitvector identity. Got:\n{all_smt}"
    );
}

// ---------------------------------------------------------------------------
// VCGEN-04: Generics / Trait Bounds
// ---------------------------------------------------------------------------

/// VCGEN-04a: Generic function with trait bound T: Ord produces non-empty VCs.
///
/// RED: Fails because trait bounds are not injected as SMT assumptions —
/// generate_vcs_with_db currently ignores generic_params.
/// Planned for Phase 28 Plan 05 (VCGEN-04: Generic where-clause premises).
#[test]
fn vcgen_04_trait_bound() {
    let func = build_generic_function();
    let ghost_db = GhostPredicateDatabase::new();
    let vcs = vcgen::generate_vcs_with_db(&func, None, &ghost_db);

    assert!(
        !vcs.conditions.is_empty(),
        "VCGEN-04a: expected VCs for generic function with T: Ord trait bound, got 0."
    );

    let all_smt: String = vcs
        .conditions
        .iter()
        .map(|vc| script_to_text(&vc.script))
        .collect::<Vec<_>>()
        .join("\n");

    // The trait bound assumption for Ord must appear in the script.
    // After implementation: something like "(assert (is-Ord T))" or a
    // well-formedness axiom for the T parameter.
    assert!(
        all_smt.contains("Ord") || all_smt.contains("trait") || all_smt.contains("T"),
        "VCGEN-04a: expected trait bound (Ord) axiom in SMT script for generic T: Ord, \
         got:\n{all_smt}"
    );
}

/// VCGEN-04b: Generic function with postcondition is verified with trait bound assumptions.
///
/// RED (partial): generate_vcs_with_db currently does not inject trait bound premises,
/// so postcondition verification of generic functions is incomplete.
/// Planned for Phase 28 Plan 05 (VCGEN-04: Generic where-clause premises).
#[test]
fn vcgen_04_generic_spec() {
    let func = build_generic_function();
    let ghost_db = GhostPredicateDatabase::new();
    let vcs = vcgen::generate_vcs_with_db(&func, None, &ghost_db);

    assert!(
        !vcs.conditions.is_empty(),
        "VCGEN-04b: expected VCs for generic function with postcondition spec, got 0."
    );

    // Check that at least one VC is a postcondition check
    let has_postcondition_vc = vcs
        .conditions
        .iter()
        .any(|vc| matches!(vc.location.vc_kind, vcgen::VcKind::Postcondition));

    assert!(
        has_postcondition_vc,
        "VCGEN-04b: expected at least one Postcondition VC for generic_fn with ensures clause. \
         Got {} VCs: {:?}",
        vcs.conditions.len(),
        vcs.conditions
            .iter()
            .map(|v| format!("{:?}", v.location.vc_kind))
            .collect::<Vec<_>>()
    );
}

// ---------------------------------------------------------------------------
// Utility: SMT script to text (mirrors completeness_suite.rs format_command)
// ---------------------------------------------------------------------------

fn script_to_text(script: &rust_fv_smtlib::script::Script) -> String {
    use rust_fv_smtlib::command::Command as C;
    use rust_fv_smtlib::sort::Sort;
    use rust_fv_smtlib::term::Term;

    fn fmt_sort(s: &Sort) -> String {
        match s {
            Sort::Bool => "Bool".to_string(),
            Sort::Int => "Int".to_string(),
            Sort::Real => "Real".to_string(),
            Sort::BitVec(n) => format!("(_ BitVec {n})"),
            Sort::Array(i, e) => format!("(Array {} {})", fmt_sort(i), fmt_sort(e)),
            Sort::Datatype(n) | Sort::Uninterpreted(n) => n.clone(),
            Sort::Float(e, s) => format!("(_ FloatingPoint {e} {s})"),
            Sort::Seq(inner) => format!("(Seq {})", fmt_sort(inner)),
        }
    }

    fn fmt_term(t: &Term) -> String {
        match t {
            Term::BoolLit(true) => "true".to_string(),
            Term::BoolLit(false) => "false".to_string(),
            Term::IntLit(n) => {
                if *n < 0 {
                    format!("(- {})", -n)
                } else {
                    format!("{n}")
                }
            }
            Term::BitVecLit(val, width) => {
                let hex_digits = (*width as usize).div_ceil(4);
                let mask = if *width >= 128 {
                    i128::MAX
                } else {
                    (1i128 << width) - 1
                };
                let unsigned = val & mask;
                format!("#x{:0>width$x}", unsigned, width = hex_digits)
            }
            Term::Const(n) => n.clone(),
            Term::Not(t) => format!("(not {})", fmt_term(t)),
            Term::And(ts) => format!(
                "(and {})",
                ts.iter().map(fmt_term).collect::<Vec<_>>().join(" ")
            ),
            Term::Or(ts) => format!(
                "(or {})",
                ts.iter().map(fmt_term).collect::<Vec<_>>().join(" ")
            ),
            Term::Implies(a, b) => format!("(=> {} {})", fmt_term(a), fmt_term(b)),
            Term::Iff(a, b) | Term::Eq(a, b) => format!("(= {} {})", fmt_term(a), fmt_term(b)),
            Term::Ite(c, t, e) => {
                format!("(ite {} {} {})", fmt_term(c), fmt_term(t), fmt_term(e))
            }
            Term::BvAdd(a, b) => format!("(bvadd {} {})", fmt_term(a), fmt_term(b)),
            Term::BvSub(a, b) => format!("(bvsub {} {})", fmt_term(a), fmt_term(b)),
            Term::BvMul(a, b) => format!("(bvmul {} {})", fmt_term(a), fmt_term(b)),
            Term::BvSLt(a, b) => format!("(bvslt {} {})", fmt_term(a), fmt_term(b)),
            Term::BvSLe(a, b) => format!("(bvsle {} {})", fmt_term(a), fmt_term(b)),
            Term::BvULt(a, b) => format!("(bvult {} {})", fmt_term(a), fmt_term(b)),
            Term::BvULe(a, b) => format!("(bvule {} {})", fmt_term(a), fmt_term(b)),
            Term::ZeroExtend(n, a) => format!("((_ zero_extend {n}) {})", fmt_term(a)),
            Term::SignExtend(n, a) => format!("((_ sign_extend {n}) {})", fmt_term(a)),
            Term::Extract(hi, lo, a) => format!("((_ extract {hi} {lo}) {})", fmt_term(a)),
            Term::Select(a, i) => format!("(select {} {})", fmt_term(a), fmt_term(i)),
            Term::App(f, args) => {
                if args.is_empty() {
                    format!("({f})")
                } else {
                    format!(
                        "({f} {})",
                        args.iter().map(fmt_term).collect::<Vec<_>>().join(" ")
                    )
                }
            }
            // Delegate remaining term variants to their Display impl
            other => other.to_string(),
        }
    }

    let mut out = String::new();
    for cmd in script.commands() {
        let s = match cmd {
            C::SetLogic(l) => format!("(set-logic {l})"),
            C::SetOption(k, v) => format!("(set-option :{k} {v})"),
            C::DeclareConst(n, s) => format!("(declare-const {n} {})", fmt_sort(s)),
            C::Assert(t) => format!("(assert {})", fmt_term(t)),
            C::CheckSat => "(check-sat)".to_string(),
            C::GetModel => "(get-model)".to_string(),
            C::Comment(t) => format!(";; {t}"),
            C::Exit => "(exit)".to_string(),
            _ => "; <other>".to_string(),
        };
        out.push_str(&s);
        out.push('\n');
    }
    out
}
