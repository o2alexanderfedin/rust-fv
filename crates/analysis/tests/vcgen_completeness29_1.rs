//! Phase 29.1 TDD scaffold: 8 failing tests covering for-loop VCGen with iterator range classification.
//!
//! All tests are intentionally RED before Phase 29.1 Plan 02 creates the `for_loop_vcgen` module.
//! Tests fail to compile because `rust_fv_analysis::for_loop_vcgen` does not yet exist.
//!
//! Requirements: VCGEN-01-FORLOOP

use rust_fv_analysis::for_loop_vcgen::generate_for_loop_vcs;
use rust_fv_analysis::ghost_predicate_db::GhostPredicateDatabase;
use rust_fv_analysis::ir::*;
use rust_fv_analysis::vcgen::VcKind;

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

// ---------------------------------------------------------------------------
// Helper: Build a function with a for-loop using the given IteratorKind
// ---------------------------------------------------------------------------

fn make_for_loop_func(iterator_kind: IteratorKind, loop_var: Option<String>) -> Function {
    let params = vec![Local::new("_1", Ty::Int(IntTy::I32))];
    let blocks = vec![
        // bb0: goto bb1
        BasicBlock {
            statements: vec![],
            terminator: Terminator::Goto(1),
        },
        // bb1: loop header — switchInt to bb2 (body) or bb3 (exit)
        BasicBlock {
            statements: vec![],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local("_2")),
                targets: vec![(1, 2)],
                otherwise: 3,
            },
        },
        // bb2: loop body — goto bb1
        BasicBlock {
            statements: vec![],
            terminator: Terminator::Goto(1),
        },
        // bb3: exit — return
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

// ---------------------------------------------------------------------------
// Test 1: Half-open range with runtime end bound
// ---------------------------------------------------------------------------

/// vcgen_for_01_range_half_open: For-loop over `0..n` produces AUFLIA quantified VC.
///
/// RED: `generate_for_loop_vcs` does not exist until Plan 02.
#[test]
fn vcgen_for_01_range_half_open() {
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
        "Expected at least one VC for half-open range"
    );

    let any_auflia = vcs.iter().any(|vc| {
        let text = script_to_text(&vc.script);
        text.contains("AUFLIA") && text.contains("forall")
    });
    assert!(
        any_auflia,
        "Expected at least one VC with AUFLIA logic and forall quantifier"
    );
}

// ---------------------------------------------------------------------------
// Test 2: Inclusive range uses <= for end bound
// ---------------------------------------------------------------------------

/// vcgen_for_02_range_inclusive: For-loop over `0..=n` uses IntLe (<=) for end bound.
///
/// RED: `generate_for_loop_vcs` does not exist until Plan 02.
#[test]
fn vcgen_for_02_range_inclusive() {
    let func = make_for_loop_func(
        IteratorKind::RangeInclusive {
            start: RangeBound::Literal(0),
            end: RangeBound::Local("n".to_string()),
        },
        Some("_3".to_string()),
    );
    let db = GhostPredicateDatabase::default();
    let vcs = generate_for_loop_vcs(&func, &db);

    assert!(
        !vcs.is_empty(),
        "Expected at least one VC for inclusive range"
    );

    let any_auflia = vcs.iter().any(|vc| {
        let text = script_to_text(&vc.script);
        text.contains("AUFLIA") && text.contains("forall")
    });
    assert!(
        any_auflia,
        "Expected at least one VC with AUFLIA logic and forall"
    );

    // Inclusive range end bound must use <= not <
    let has_le = vcs.iter().any(|vc| {
        let text = script_to_text(&vc.script);
        text.contains("<=")
    });
    assert!(has_le, "Inclusive range must use <= for end bound check");

    let has_strict_lt_on_n = vcs.iter().any(|vc| {
        let text = script_to_text(&vc.script);
        text.contains("(< i n)")
    });
    assert!(
        !has_strict_lt_on_n,
        "Inclusive range must NOT use strict (< i n) for end bound"
    );
}

// ---------------------------------------------------------------------------
// Test 3: Literal range end — no DeclareConst for bound variable
// ---------------------------------------------------------------------------

/// vcgen_for_03_range_literal: For-loop over `0..5` embeds literal inline, no bound DeclareConst.
///
/// RED: `generate_for_loop_vcs` does not exist until Plan 02.
#[test]
fn vcgen_for_03_range_literal() {
    let func = make_for_loop_func(
        IteratorKind::Range {
            start: RangeBound::Literal(0),
            end: RangeBound::Literal(5),
        },
        Some("_3".to_string()),
    );
    let db = GhostPredicateDatabase::default();
    let vcs = generate_for_loop_vcs(&func, &db);

    assert!(
        !vcs.is_empty(),
        "Expected at least one VC for literal range"
    );

    // With a literal end bound, we should NOT see a DeclareConst for the bound
    let has_declare_for_bound = vcs.iter().any(|vc| {
        let text = script_to_text(&vc.script);
        // A runtime-bound variable would produce something like "(declare-const n Int)"
        text.contains("(declare-const n ")
    });
    assert!(
        !has_declare_for_bound,
        "Literal range end should not produce a DeclareConst for bound variable"
    );
}

// ---------------------------------------------------------------------------
// Test 4: Bounded unrolling VC uses QF_LIA
// ---------------------------------------------------------------------------

/// vcgen_for_04_bounded_unrolling: Half-open range produces both AUFLIA and QF_LIA VCs.
///
/// RED: `generate_for_loop_vcs` does not exist until Plan 02.
#[test]
fn vcgen_for_04_bounded_unrolling() {
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
        vcs.len() >= 2,
        "Expected at least 2 VCs for range loop (quantified + bounded unrolling), got {}",
        vcs.len()
    );

    let has_qf_lia = vcs.iter().any(|vc| {
        let text = script_to_text(&vc.script);
        text.contains("QF_LIA")
    });
    assert!(
        has_qf_lia,
        "Expected at least one QF_LIA VC for bounded unrolling"
    );
}

// ---------------------------------------------------------------------------
// Test 5: Slice iteration references arr_len
// ---------------------------------------------------------------------------

/// vcgen_for_05_slice_iter: For-loop over slice uses `arr_len` naming (Phase 28 convention).
///
/// RED: `generate_for_loop_vcs` does not exist until Plan 02.
#[test]
fn vcgen_for_05_slice_iter() {
    let func = make_for_loop_func(
        IteratorKind::SliceIter {
            collection_local: "arr".to_string(),
        },
        Some("_3".to_string()),
    );
    let db = GhostPredicateDatabase::default();
    let vcs = generate_for_loop_vcs(&func, &db);

    assert!(!vcs.is_empty(), "Expected at least one VC for slice iter");

    let has_arr_len = vcs.iter().any(|vc| {
        let text = script_to_text(&vc.script);
        text.contains("arr_len")
    });
    assert!(
        has_arr_len,
        "Slice iter VC must use 'arr_len' naming (Phase 28 {{arr}}_len convention)"
    );
}

// ---------------------------------------------------------------------------
// Test 6: Enumerate iterator declares both index_ and elem_ constants
// ---------------------------------------------------------------------------

/// vcgen_for_06_enumerate: Enumerate over slice declares both `index_` and `elem_` SMT constants.
///
/// RED: `generate_for_loop_vcs` does not exist until Plan 02.
#[test]
fn vcgen_for_06_enumerate() {
    let func = make_for_loop_func(
        IteratorKind::Enumerate {
            inner: Box::new(IteratorKind::SliceIter {
                collection_local: "arr".to_string(),
            }),
        },
        Some("_3".to_string()),
    );
    let db = GhostPredicateDatabase::default();
    let vcs = generate_for_loop_vcs(&func, &db);

    assert!(
        !vcs.is_empty(),
        "Expected at least one VC for enumerate iter"
    );

    let combined_text: String = vcs
        .iter()
        .map(|vc| script_to_text(&vc.script))
        .collect::<Vec<_>>()
        .join("\n");

    assert!(
        combined_text.contains("index_"),
        "Enumerate VC must declare an 'index_' SMT constant"
    );
    assert!(
        combined_text.contains("elem_"),
        "Enumerate VC must declare an 'elem_' SMT constant"
    );
}

// ---------------------------------------------------------------------------
// Test 7: Unknown iterator produces single conservative BoolLit(true) VC
// ---------------------------------------------------------------------------

/// vcgen_for_07_unknown_iterator: Unknown iterator kind produces exactly one true VC.
///
/// RED: `generate_for_loop_vcs` does not exist until Plan 02.
#[test]
fn vcgen_for_07_unknown_iterator() {
    let func = make_for_loop_func(
        IteratorKind::Unknown {
            description: "CustomIter".to_string(),
        },
        None,
    );
    let db = GhostPredicateDatabase::default();
    let vcs = generate_for_loop_vcs(&func, &db);

    assert_eq!(
        vcs.len(),
        1,
        "Unknown iterator must produce exactly one conservative VC"
    );

    let text = script_to_text(&vcs[0].script);
    assert!(
        text.contains("true"),
        "Unknown iterator conservative VC must assert 'true'"
    );
}

// ---------------------------------------------------------------------------
// Test 8: Slice element bounds check produces MemorySafety VC
// ---------------------------------------------------------------------------

/// vcgen_for_08_element_bounds_check: Slice iter with loop_var produces MemorySafety VC.
///
/// RED: `generate_for_loop_vcs` does not exist until Plan 02.
#[test]
fn vcgen_for_08_element_bounds_check() {
    let func = make_for_loop_func(
        IteratorKind::SliceIter {
            collection_local: "data".to_string(),
        },
        Some("_5".to_string()),
    );
    let db = GhostPredicateDatabase::default();
    let vcs = generate_for_loop_vcs(&func, &db);

    assert!(
        !vcs.is_empty(),
        "Expected at least one VC for slice bounds check"
    );

    let has_memory_safety = vcs
        .iter()
        .any(|vc| vc.location.vc_kind == VcKind::MemorySafety);
    assert!(
        has_memory_safety,
        "Slice iter with loop_var must produce at least one MemorySafety VC"
    );
}
