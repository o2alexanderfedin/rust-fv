//! Phase 45 regression validation suite: 4 tests confirming COMPL-19..22 remain GREEN.
//!
//! These tests consolidate the key assertions from phases 29.1, 30, and 31 into a
//! dedicated Phase 45 validation suite that confirms all four COMPL items are fixed
//! and remain regression-safe.
//!
//! Requirements: COMPL-19, COMPL-20, COMPL-21, COMPL-22

use rust_fv_analysis::for_loop_vcgen::generate_for_loop_vcs;
use rust_fv_analysis::ghost_predicate_db::GhostPredicateDatabase;
use rust_fv_analysis::ir::*;
use rust_fv_analysis::vcgen;

// ---------------------------------------------------------------------------
// Helpers (mirrors vcgen_completeness29.rs)
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
        refcell_ghost_states: vec![],
        maybeuninit_ghost_states: vec![],
        union_ghost_states: vec![],
        pin_ghost_states: vec![],
        drop_locals: vec![],
        hrtb_bounds: vec![],
    }
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

/// Helper: Build a function with a for-loop using the given IteratorKind.
fn make_for_loop_func(iterator_kind: IteratorKind, loop_var: Option<String>) -> Function {
    let params = vec![Local::new("_1", Ty::Int(IntTy::I32))];
    let blocks = vec![
        BasicBlock {
            statements: vec![],
            terminator: Terminator::Goto(1),
        },
        BasicBlock {
            statements: vec![],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local("_2")),
                targets: vec![(1, 2)],
                otherwise: 3,
            },
        },
        BasicBlock {
            statements: vec![],
            terminator: Terminator::Goto(1),
        },
        BasicBlock {
            statements: vec![],
            terminator: Terminator::Return,
        },
    ];

    let mut func = make_func(
        "for_loop_fn",
        Ty::Unit,
        params,
        vec![Local::new("_2", Ty::Bool)],
        blocks,
    );
    func.loops = vec![LoopInfo {
        header_block: 1,
        back_edge_blocks: vec![2],
        invariants: vec![],
        iterator_kind: Some(iterator_kind),
        loop_var,
    }];
    func
}

// ===========================================================================
// COMPL-19: For-loop VCGen produces VCs (smoke test consolidating 29.1 suite)
// ===========================================================================

/// COMPL-19 regression: For-loop VCGen with Range iterator produces non-empty AUFLIA VCs.
///
/// Consolidates the key assertion from the 9 tests in vcgen_completeness29_1.rs:
/// generate_for_loop_vcs with a Range iterator kind produces non-empty VCs with
/// AUFLIA logic containing forall quantifiers.
#[test]
fn compl19_for_loop_vcs_green() {
    let func = make_for_loop_func(
        IteratorKind::Range {
            start: RangeBound::Literal(0),
            end: RangeBound::Local("n".to_string()),
        },
        Some("_3".to_string()),
    );
    let db = GhostPredicateDatabase::default();
    let vcs = generate_for_loop_vcs(&func, &db);

    assert!(
        !vcs.is_empty(),
        "COMPL-19: For-loop VCGen must produce non-empty VCs for Range iterator"
    );

    let any_auflia = vcs.iter().any(|vc| {
        let text = script_to_text(&vc.script);
        text.contains("AUFLIA")
    });
    assert!(
        any_auflia,
        "COMPL-19: For-loop VCGen with Range must produce at least one AUFLIA VC"
    );
}

// ===========================================================================
// COMPL-20: SetDiscriminant produces VCs (not silent no-op)
// ===========================================================================

/// COMPL-20 regression: SetDiscriminant in generate_vcs produces non-empty VCs
/// containing "discriminant" in the SMT output.
#[test]
fn compl20_set_discriminant_produces_vcs() {
    let blocks = vec![BasicBlock {
        statements: vec![Statement::SetDiscriminant(Place::local("_1"), 1)],
        terminator: Terminator::Return,
    }];
    let func = make_func(
        "set_disc_compl20",
        Ty::Int(IntTy::I32),
        vec![],
        vec![],
        blocks,
    );
    let vcs = vcgen::generate_vcs(&func, None);

    assert!(
        !vcs.conditions.is_empty(),
        "COMPL-20: SetDiscriminant must produce non-empty VCs, got 0"
    );

    let all_smt: String = vcs
        .conditions
        .iter()
        .map(|vc| script_to_text(&vc.script))
        .collect::<Vec<_>>()
        .join("\n");

    assert!(
        all_smt.contains("discriminant"),
        "COMPL-20: SetDiscriminant VCs must contain 'discriminant' in SMT, but got:\n{all_smt}"
    );
}

// ===========================================================================
// COMPL-21: Ghost local assignments do not leak into SMT VCs
// ===========================================================================

/// COMPL-21 regression: Ghost local with is_ghost=true does NOT appear in SMT output.
#[test]
fn compl21_ghost_local_filtered() {
    let func = Function {
        name: "ghost_filter_compl21".to_string(),
        return_local: Local::new("_0", Ty::Int(IntTy::I32)),
        params: vec![],
        locals: vec![Local {
            name: "__ghost_x".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: true,
        }],
        basic_blocks: vec![BasicBlock {
            statements: vec![
                Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Constant(Constant::Int(42, IntTy::I32))),
                ),
                Statement::Assign(
                    Place::local("__ghost_x"),
                    Rvalue::Use(Operand::Constant(Constant::Int(0, IntTy::I32))),
                ),
            ],
            terminator: Terminator::Return,
        }],
        contracts: Contracts {
            ensures: vec![SpecExpr {
                raw: "true".to_string(),
            }],
            ..Default::default()
        },
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
    };

    let vcs = vcgen::generate_vcs(&func, None);

    assert!(
        !vcs.conditions.is_empty(),
        "COMPL-21: Expected VCs from tautological postcondition, got 0"
    );

    let all_smt: String = vcs
        .conditions
        .iter()
        .map(|vc| script_to_text(&vc.script))
        .collect::<Vec<_>>()
        .join("\n");

    assert!(
        !all_smt.contains("__ghost_x"),
        "COMPL-21: Ghost local '__ghost_x' must NOT appear in SMT VCs, but it leaked into:\n{all_smt}"
    );
}

// ===========================================================================
// COMPL-22: Spec expressions with 'as int' route through ALL logic (not QF_BV)
// ===========================================================================

/// COMPL-22 regression: When ensures contains "(result as int) > 0" on I32 params,
/// the SMT must use (set-logic ALL) not QF_BV.
#[test]
fn compl22_spec_int_routes_to_all_logic() {
    let func = Function {
        name: "spec_int_compl22".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        },
        params: vec![Local {
            name: "_1".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        }],
        locals: vec![],
        basic_blocks: vec![BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::Use(Operand::Copy(Place::local("_1"))),
            )],
            terminator: Terminator::Return,
        }],
        contracts: Contracts {
            ensures: vec![SpecExpr {
                raw: "(result as int) > 0".to_string(),
            }],
            ..Default::default()
        },
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
    };

    let vcs = vcgen::generate_vcs(&func, None);

    assert!(
        !vcs.conditions.is_empty(),
        "COMPL-22: Expected VCs for function with 'as int' in ensures, got 0"
    );

    let all_smt: String = vcs
        .conditions
        .iter()
        .map(|vc| script_to_text(&vc.script))
        .collect::<Vec<_>>()
        .join("\n");

    assert!(
        all_smt.contains("(set-logic ALL)"),
        "COMPL-22: Expected '(set-logic ALL)' in SMT when ensures contains 'as int', but got:\n{all_smt}"
    );
}
