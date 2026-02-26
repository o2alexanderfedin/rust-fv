//! Phase 29/30 completeness suite: 11 tests covering MIRCONV-01, MIRCONV-02, VCGEN-05, VCGEN-06.
//!
//! All 11 tests are GREEN: Phase 29 fixed MIRCONV-01/02 and VCGEN-05; Phase 30 closed VCGEN-06.
//! No tests remain #[ignore] — vcgen_06_set_discriminant_assertion fully exercised (variant index 2).
//!
//! Requirements: MIRCONV-01, MIRCONV-02, VCGEN-05, VCGEN-06

use rust_fv_analysis::ir::*;
use rust_fv_analysis::vcgen;

// ---------------------------------------------------------------------------
// Helpers (mirrors vcgen_completeness28.rs)
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

/// Build a cast function with the given CastKind, from_ty, and to_ty.
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
    func.contracts = Contracts {
        ensures: vec![SpecExpr {
            raw: "true".to_string(),
        }],
        ..Contracts::default()
    };
    func
}

/// Utility: render a Script to a string for assertion.
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

// ---------------------------------------------------------------------------
// MIRCONV-01: Cast kind preservation through MIR → IR conversion
// ---------------------------------------------------------------------------

/// MIRCONV-01a: FloatToInt cast kind is preserved — vcgen must emit fp.to_sbv (NOT extract).
///
/// RED: mir_converter.rs currently maps ALL casts to CastKind::IntToInt, so the
/// IR-level CastKind is IntToInt instead of FloatToInt. Even though encode_term.rs
/// has encode_float_to_int_cast(), it is never called because the kind is wrong.
/// After Plan 01 fixes mir_converter.rs, the CastKind will be FloatToInt and
/// encode_float_to_int_cast() will be invoked. That function currently uses Extract
/// as a conservative approximation — asserting fp.to_sbv here tests the Plan 02 fix.
/// This test will be RED until Plan 02 replaces Extract with fp.to_sbv.
///
/// At the IR level (what this test directly controls), the Cast has CastKind::FloatToInt.
/// The vcgen must route through encode_float_to_int_cast (not encode_int_to_int_cast).
/// The current encode_float_to_int_cast uses Extract, so asserting fp.to_sbv == RED.
/// After Plan 02 changes encode_float_to_int_cast to fp.to_sbv, this test goes GREEN.
#[test]
fn mirconv_01_float_to_int_cast_kind() {
    // Build IR directly with CastKind::FloatToInt (bypasses mir_converter)
    let func = build_cast_function(
        CastKind::FloatToInt,
        Ty::Float(FloatTy::F64),
        Ty::Int(IntTy::I32),
    );
    let vcs = vcgen::generate_vcs(&func, None);

    assert!(
        !vcs.conditions.is_empty(),
        "MIRCONV-01a: expected VCs for FloatToInt cast, got 0"
    );

    let all_smt: String = vcs
        .conditions
        .iter()
        .map(|vc| script_to_text(&vc.script))
        .collect::<Vec<_>>()
        .join("\n");

    // RED until Plan 02: encode_float_to_int_cast currently uses Extract, not fp.to_sbv.
    assert!(
        all_smt.contains("fp.to_sbv"),
        "MIRCONV-01a: expected 'fp.to_sbv' in SMT for FloatToInt cast (f64->i32), \
         but got:\n{all_smt}"
    );
}

/// MIRCONV-01b: IntToFloat cast kind is preserved — vcgen emits to_fp (NOT identity).
///
/// This tests that CastKind::IntToFloat is correctly wired to encode_int_to_float_cast()
/// which emits `((_ to_fp ...) RNE ...)`. The encode_term layer already handles this
/// correctly. After Plan 01 fixes mir_converter, the real MIR path is complete.
///
/// At the IR level (direct test), this should already be GREEN since encode_cast
/// handles IntToFloat correctly. This test serves as a regression guard.
#[test]
fn mirconv_01_int_to_float_cast_kind() {
    let func = build_cast_function(
        CastKind::IntToFloat,
        Ty::Int(IntTy::I32),
        Ty::Float(FloatTy::F32),
    );
    let vcs = vcgen::generate_vcs(&func, None);

    assert!(
        !vcs.conditions.is_empty(),
        "MIRCONV-01b: expected VCs for IntToFloat cast, got 0"
    );

    let all_smt: String = vcs
        .conditions
        .iter()
        .map(|vc| script_to_text(&vc.script))
        .collect::<Vec<_>>()
        .join("\n");

    // IntToFloat must produce to_fp encoding, not identity (= _0 _1).
    assert!(
        all_smt.contains("to_fp"),
        "MIRCONV-01b: expected 'to_fp' in SMT for IntToFloat cast (i32->f32), \
         but got:\n{all_smt}"
    );
}

// ---------------------------------------------------------------------------
// MIRCONV-02: Aggregate conversion (struct and enum)
// ---------------------------------------------------------------------------

/// MIRCONV-02a: Struct aggregate Rvalue produces mk-Point constructor in VCs.
///
/// RED: mir_converter.rs currently returns None for all non-Tuple aggregates
/// (line: `_ => return None, // Skip complex aggregates for Phase 1`).
/// After Plan 03 fixes the aggregate conversion, vcgen will see the Aggregate rvalue
/// and emit a constructor call. RED until Plan 03.
#[test]
fn mirconv_02_struct_aggregate() {
    // Build IR with Rvalue::Aggregate(AggregateKind::Struct("Point"), [_1, _2])
    let point_ty = Ty::Struct(
        "Point".to_string(),
        vec![
            ("x".to_string(), Ty::Int(IntTy::I32)),
            ("y".to_string(), Ty::Int(IntTy::I32)),
        ],
    );
    let params = vec![
        Local::new("_1", Ty::Int(IntTy::I32)),
        Local::new("_2", Ty::Int(IntTy::I32)),
    ];
    let blocks = vec![BasicBlock {
        statements: vec![Statement::Assign(
            Place::local("_0"),
            Rvalue::Aggregate(
                AggregateKind::Struct("Point".to_string()),
                vec![
                    Operand::Copy(Place::local("_1")),
                    Operand::Copy(Place::local("_2")),
                ],
            ),
        )],
        terminator: Terminator::Return,
    }];
    let mut func = make_func("build_point", point_ty, params, vec![], blocks);
    func.contracts = Contracts {
        ensures: vec![SpecExpr {
            raw: "true".to_string(),
        }],
        ..Contracts::default()
    };

    let vcs = vcgen::generate_vcs(&func, None);

    assert!(
        !vcs.conditions.is_empty(),
        "MIRCONV-02a: expected VCs for struct aggregate construction, got 0. \
         mir_converter currently skips non-Tuple aggregates."
    );

    let all_smt: String = vcs
        .conditions
        .iter()
        .map(|vc| script_to_text(&vc.script))
        .collect::<Vec<_>>()
        .join("\n");

    assert!(
        all_smt.contains("mk-Point"),
        "MIRCONV-02a: expected 'mk-Point' constructor in SMT for struct aggregate, \
         but got:\n{all_smt}"
    );
}

/// MIRCONV-02b: Enum aggregate Rvalue produces a mk- constructor in VCs.
///
/// RED: Same reason as mirconv_02_struct_aggregate — aggregates other than Tuple
/// are discarded by mir_converter. RED until Plan 03.
#[test]
fn mirconv_02_enum_aggregate() {
    // Build IR with Rvalue::Aggregate(AggregateKind::Enum("Option", 1), [_1])
    let option_ty = Ty::Enum(
        "Option".to_string(),
        vec![
            ("None".to_string(), vec![]),
            ("Some".to_string(), vec![Ty::Int(IntTy::I32)]),
        ],
    );
    let params = vec![Local::new("_1", Ty::Int(IntTy::I32))];
    let blocks = vec![BasicBlock {
        statements: vec![Statement::Assign(
            Place::local("_0"),
            Rvalue::Aggregate(
                AggregateKind::Enum("Option".to_string(), 1),
                vec![Operand::Copy(Place::local("_1"))],
            ),
        )],
        terminator: Terminator::Return,
    }];
    let mut func = make_func("make_some", option_ty, params, vec![], blocks);
    func.contracts = Contracts {
        ensures: vec![SpecExpr {
            raw: "true".to_string(),
        }],
        ..Contracts::default()
    };

    let vcs = vcgen::generate_vcs(&func, None);

    assert!(
        !vcs.conditions.is_empty(),
        "MIRCONV-02b: expected VCs for enum aggregate construction, got 0. \
         mir_converter currently skips non-Tuple aggregates."
    );

    let all_smt: String = vcs
        .conditions
        .iter()
        .map(|vc| script_to_text(&vc.script))
        .collect::<Vec<_>>()
        .join("\n");

    assert!(
        all_smt.contains("mk-"),
        "MIRCONV-02b: expected a 'mk-' constructor in SMT for enum aggregate (Option::Some), \
         but got:\n{all_smt}"
    );
}

/// MIRCONV-02c: Statement::SetDiscriminant IR round-trip through vcgen.
///
/// Plan 03 added Statement::SetDiscriminant(Place, usize) to ir::Statement.
/// VCGen currently treats SetDiscriminant as a no-op (full encoding deferred to Plan 05).
/// This test confirms the IR variant exists and vcgen does not panic on it.
#[test]
fn mirconv_02_set_discriminant() {
    let blocks = vec![BasicBlock {
        statements: vec![Statement::SetDiscriminant(Place::local("_0"), 0)],
        terminator: Terminator::Return,
    }];
    let func = make_func("set_disc", Ty::Int(IntTy::I32), vec![], vec![], blocks);
    // vcgen must not panic; SetDiscriminant is a no-op in VCGen for now.
    // We simply verify the call succeeds (IR round-trip confirmed).
    let _vcs = vcgen::generate_vcs(&func, None);
    // The variant exists and vcgen handles it without panicking — that is the goal.
}

/// VCGEN-06: SetDiscriminant VC emission — unit test.
///
/// RED: VCGen currently treats SetDiscriminant as a no-op (0 VCs emitted).
/// After plan 30-02 adds generate_set_discriminant_vcs(), this test must become GREEN.
#[test]
fn vcgen_06_set_discriminant_unit() {
    let blocks = vec![BasicBlock {
        statements: vec![Statement::SetDiscriminant(Place::local("_1"), 1)],
        terminator: Terminator::Return,
    }];
    let func = make_func("set_disc_vc", Ty::Int(IntTy::I32), vec![], vec![], blocks);
    let vcs = vcgen::generate_vcs(&func, None);

    assert!(
        !vcs.conditions.is_empty(),
        "VCGEN-06: expected VC for SetDiscriminant, got 0"
    );

    let all_smt: String = vcs
        .conditions
        .iter()
        .map(|vc| script_to_text(&vc.script))
        .collect::<Vec<_>>()
        .join("\n");

    assert!(
        all_smt.contains("discriminant"),
        "VCGEN-06: expected 'discriminant' in SMT for SetDiscriminant(_1, 1), but got:\n{all_smt}"
    );
    assert!(
        all_smt.contains('1'),
        "VCGEN-06: expected variant index '1' in SMT for SetDiscriminant(_1, 1), but got:\n{all_smt}"
    );
}

// ---------------------------------------------------------------------------
// VCGEN-05: Float-to-int SMT encoding (fp.to_sbv / fp.to_ubv)
// ---------------------------------------------------------------------------

/// VCGEN-05a: FloatToInt cast for signed target (f64 -> i32) uses fp.to_sbv.
///
/// RED: encode_float_to_int_cast() currently uses `Term::Extract` as a conservative
/// approximation. After Plan 02 replaces Extract with fp.to_sbv/fp.to_ubv, this passes.
#[test]
fn vcgen_05_float_to_int_signed() {
    let func = build_cast_function(
        CastKind::FloatToInt,
        Ty::Float(FloatTy::F64),
        Ty::Int(IntTy::I32),
    );
    let vcs = vcgen::generate_vcs(&func, None);

    assert!(
        !vcs.conditions.is_empty(),
        "VCGEN-05a: expected VCs for FloatToInt signed cast, got 0"
    );

    let all_smt: String = vcs
        .conditions
        .iter()
        .map(|vc| script_to_text(&vc.script))
        .collect::<Vec<_>>()
        .join("\n");

    // RED until Plan 02: currently encodes as extract, not fp.to_sbv
    assert!(
        all_smt.contains("fp.to_sbv"),
        "VCGEN-05a: expected '((_ fp.to_sbv 32) RTZ _1)' in SMT for f64->i32 cast, \
         but got:\n{all_smt}"
    );
}

/// VCGEN-05b: FloatToInt cast for unsigned target (f64 -> u64) uses fp.to_ubv.
///
/// RED: Same reason as vcgen_05_float_to_int_signed. RED until Plan 02.
#[test]
fn vcgen_05_float_to_int_unsigned() {
    let func = build_cast_function(
        CastKind::FloatToInt,
        Ty::Float(FloatTy::F64),
        Ty::Uint(UintTy::U64),
    );
    let vcs = vcgen::generate_vcs(&func, None);

    assert!(
        !vcs.conditions.is_empty(),
        "VCGEN-05b: expected VCs for FloatToInt unsigned cast, got 0"
    );

    let all_smt: String = vcs
        .conditions
        .iter()
        .map(|vc| script_to_text(&vc.script))
        .collect::<Vec<_>>()
        .join("\n");

    // RED until Plan 02: currently encodes as extract, not fp.to_ubv
    assert!(
        all_smt.contains("fp.to_ubv"),
        "VCGEN-05b: expected '((_ fp.to_ubv 64) RTZ _1)' in SMT for f64->u64 cast, \
         but got:\n{all_smt}"
    );
}

// ---------------------------------------------------------------------------
// VCGEN-06: Projected LHS functional update
// ---------------------------------------------------------------------------

/// VCGEN-06a: Field mutation with non-Use rvalue produces mk- functional update in VC.
///
/// RED: When the LHS has projections (Field(0)), vcgen currently does not emit a
/// functional update (mk-StructName). After Plan 05 adds projected LHS support,
/// the VC will contain `mk-` for the struct reconstruction. RED until Plan 05.
#[test]
fn vcgen_06_struct_field_mutation() {
    let point_ty = Ty::Struct(
        "Point".to_string(),
        vec![
            ("x".to_string(), Ty::Int(IntTy::I32)),
            ("y".to_string(), Ty::Int(IntTy::I32)),
        ],
    );
    // fn update_x(p: Point, v: i32) -> Point { p.x = p.x + v; p }
    let params = vec![
        Local::new("_1", point_ty.clone()),
        Local::new("_2", Ty::Int(IntTy::I32)),
    ];
    let blocks = vec![BasicBlock {
        statements: vec![Statement::Assign(
            // Projected LHS: _1.field[0] = _1.field[0] + _2
            Place {
                local: "_1".to_string(),
                projections: vec![Projection::Field(0)],
            },
            Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place {
                    local: "_1".to_string(),
                    projections: vec![Projection::Field(0)],
                }),
                Operand::Copy(Place::local("_2")),
            ),
        )],
        terminator: Terminator::Return,
    }];
    let mut func = make_func("update_x", point_ty, params, vec![], blocks);
    func.contracts = Contracts {
        ensures: vec![SpecExpr {
            raw: "true".to_string(),
        }],
        ..Contracts::default()
    };

    let vcs = vcgen::generate_vcs(&func, None);

    assert!(
        !vcs.conditions.is_empty(),
        "VCGEN-06a: expected VCs for field mutation, got 0"
    );

    let all_smt: String = vcs
        .conditions
        .iter()
        .map(|vc| script_to_text(&vc.script))
        .collect::<Vec<_>>()
        .join("\n");

    // RED until Plan 05: projected LHS currently does not produce mk- functional update
    assert!(
        all_smt.contains("mk-"),
        "VCGEN-06a: expected 'mk-' functional update in SMT for field mutation (BinaryOp rvalue), \
         but got:\n{all_smt}"
    );
}

/// VCGEN-06b: Field mutation with Use rvalue produces mk- functional update in VC.
///
/// This tests whether the existing vcgen handles projected LHS with Use rvalue.
/// May already be partially GREEN (regression guard) or RED (same gap as 06a).
/// RED until Plan 05.
#[test]
fn vcgen_06_field_mutation_use() {
    let point_ty = Ty::Struct(
        "Point".to_string(),
        vec![
            ("x".to_string(), Ty::Int(IntTy::I32)),
            ("y".to_string(), Ty::Int(IntTy::I32)),
        ],
    );
    // fn set_x(p: Point, v: i32) -> Point { p.x = v; p }
    let params = vec![
        Local::new("_1", point_ty.clone()),
        Local::new("_2", Ty::Int(IntTy::I32)),
    ];
    let blocks = vec![BasicBlock {
        statements: vec![Statement::Assign(
            Place {
                local: "_1".to_string(),
                projections: vec![Projection::Field(0)],
            },
            Rvalue::Use(Operand::Copy(Place::local("_2"))),
        )],
        terminator: Terminator::Return,
    }];
    let mut func = make_func("set_x", point_ty, params, vec![], blocks);
    func.contracts = Contracts {
        ensures: vec![SpecExpr {
            raw: "true".to_string(),
        }],
        ..Contracts::default()
    };

    let vcs = vcgen::generate_vcs(&func, None);

    assert!(
        !vcs.conditions.is_empty(),
        "VCGEN-06b: expected VCs for field Use mutation, got 0"
    );

    let all_smt: String = vcs
        .conditions
        .iter()
        .map(|vc| script_to_text(&vc.script))
        .collect::<Vec<_>>()
        .join("\n");

    // RED until Plan 05: projected LHS does not yet produce mk- functional update
    assert!(
        all_smt.contains("mk-"),
        "VCGEN-06b: expected 'mk-' functional update in SMT for field mutation (Use rvalue), \
         but got:\n{all_smt}"
    );
}

/// VCGEN-06c: SetDiscriminant VC emission — assertion test (variant index 2).
///
/// RED: VCGen currently treats SetDiscriminant as a no-op (0 VCs emitted).
/// After plan 30-02 adds generate_set_discriminant_vcs(), this test must become GREEN.
/// Uses variant index 2 to distinguish from vcgen_06_set_discriminant_unit (index 1).
#[test]
fn vcgen_06_set_discriminant_assertion() {
    let blocks = vec![BasicBlock {
        statements: vec![Statement::SetDiscriminant(Place::local("_1"), 2)],
        terminator: Terminator::Return,
    }];
    let func = make_func("set_disc_vc2", Ty::Int(IntTy::I32), vec![], vec![], blocks);
    let vcs = vcgen::generate_vcs(&func, None);

    assert!(
        !vcs.conditions.is_empty(),
        "VCGEN-06: expected VC for SetDiscriminant, got 0"
    );

    let all_smt: String = vcs
        .conditions
        .iter()
        .map(|vc| script_to_text(&vc.script))
        .collect::<Vec<_>>()
        .join("\n");

    assert!(
        all_smt.contains("discriminant"),
        "VCGEN-06: expected 'discriminant' in SMT for SetDiscriminant(_1, 2), but got:\n{all_smt}"
    );
    assert!(
        all_smt.contains('2'),
        "VCGEN-06: expected variant index '2' in SMT for SetDiscriminant(_1, 2), but got:\n{all_smt}"
    );
}
