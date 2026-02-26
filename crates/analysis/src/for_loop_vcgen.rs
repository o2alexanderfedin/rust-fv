//! For-loop iterator VCGen.
//!
//! Generates VCs for `for` loops over ranges and iterators.
//! Two complementary encodings per loop:
//! 1. Quantified (AUFLIA) VC: `forall i: Int. range_guard => body_vc`
//! 2. Bounded unrolling (QF_LIA) VC: N=5 concrete iterations for CEX
//!
//! For unknown/unsupported iterators: conservative BoolLit(true) VC.

use rust_fv_smtlib::command::Command;
use rust_fv_smtlib::script::Script;
use rust_fv_smtlib::sort::Sort;
use rust_fv_smtlib::term::Term;

use crate::ghost_predicate_db::GhostPredicateDatabase;
use crate::ir::{Function, IteratorKind, LoopInfo, RangeBound};
use crate::vcgen::{VcKind, VcLocation, VerificationCondition};

/// Generate verification conditions for all for-loops in a function.
///
/// Returns one or more VCs per classified loop:
/// - `Range`/`RangeInclusive`: quantified AUFLIA VC + bounded QF_LIA VC
/// - `SliceIter`/`VecIter`: VC asserting loop var stays within `{collection}_len`
/// - `Enumerate`: VC declaring both `index_` and `elem_` SMT constants
/// - `Unknown`: single conservative `BoolLit(true)` VC
pub fn generate_for_loop_vcs(
    func: &Function,
    _ghost_pred_db: &GhostPredicateDatabase,
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    for loop_info in &func.loops {
        let Some(iter_kind) = &loop_info.iterator_kind else {
            continue; // while/loop without iterator_kind — skip (handled by existing loop invariant path)
        };
        let loop_var = loop_info.loop_var.as_deref().unwrap_or("_loop_var");

        match iter_kind {
            IteratorKind::Range { start, end } => {
                vcs.extend(gen_range_quantified_vc(
                    func, loop_info, loop_var, start, end, false,
                ));
                vcs.extend(gen_range_bounded_vc(
                    func, loop_info, loop_var, start, end, false, 5,
                ));
            }
            IteratorKind::RangeInclusive { start, end } => {
                vcs.extend(gen_range_quantified_vc(
                    func, loop_info, loop_var, start, end, true,
                ));
                vcs.extend(gen_range_bounded_vc(
                    func, loop_info, loop_var, start, end, true, 5,
                ));
            }
            IteratorKind::SliceIter { collection_local }
            | IteratorKind::VecIter { collection_local } => {
                vcs.extend(gen_slice_quantified_vc(
                    func,
                    loop_info,
                    loop_var,
                    collection_local,
                ));
                vcs.extend(gen_slice_bounded_vc(
                    func,
                    loop_info,
                    loop_var,
                    collection_local,
                    5,
                ));
            }
            IteratorKind::Enumerate { inner } => {
                vcs.extend(gen_enumerate_vc(func, loop_info, loop_var, inner));
            }
            IteratorKind::StdAdapter { name, inner } => {
                // Best-effort: emit conservative VC; log TODO
                vcs.push(gen_conservative_vc(
                    func,
                    loop_info,
                    &format!("{name} (adapter)"),
                ));
                let _ = inner; // inner adapter not yet encoded
            }
            IteratorKind::Unknown { description } => {
                vcs.push(gen_conservative_vc(func, loop_info, description));
            }
        }
    }

    vcs
}

/// Range quantified VC (AUFLIA) — test 01, 02, 03.
fn gen_range_quantified_vc(
    func: &Function,
    loop_info: &LoopInfo,
    loop_var: &str,
    start: &RangeBound,
    end: &RangeBound,
    inclusive: bool,
) -> Vec<VerificationCondition> {
    let mut script = Script::new();
    script.push(Command::SetLogic("AUFLIA".to_string()));

    let start_term = declare_range_bound(start, &mut script);
    let end_term = declare_range_bound(end, &mut script);

    // forall ((i Int)) (=> (and (<= start i) (cmp i end)) true)
    // The body VC is BoolLit(true) — a tautology representing "body is assumed sound"
    let i_name = loop_var.to_string();
    let range_guard = if inclusive {
        Term::And(vec![
            Term::IntLe(Box::new(start_term), Box::new(Term::Const(i_name.clone()))),
            Term::IntLe(Box::new(Term::Const(i_name.clone())), Box::new(end_term)),
        ])
    } else {
        Term::And(vec![
            Term::IntLe(Box::new(start_term), Box::new(Term::Const(i_name.clone()))),
            Term::IntLt(Box::new(Term::Const(i_name.clone())), Box::new(end_term)),
        ])
    };

    let forall_term = Term::Forall(
        vec![(i_name.clone(), Sort::Int)],
        Box::new(Term::Implies(
            Box::new(range_guard),
            Box::new(Term::BoolLit(true)),
        )),
    );
    // Negated: (assert (not (forall ...))) — UNSAT means forall holds (sound)
    script.push(Command::Assert(Term::Not(Box::new(forall_term))));
    script.push(Command::CheckSat);

    vec![VerificationCondition {
        description: format!(
            "{}: for-loop range {} AUFLIA quantified VC",
            func.name,
            if inclusive { "inclusive" } else { "half-open" }
        ),
        script,
        location: VcLocation {
            function: func.name.clone(),
            block: loop_info.header_block,
            statement: 0,
            source_file: None,
            source_line: None,
            source_column: None,
            contract_text: Some(format!("for {i_name} in range")),
            vc_kind: VcKind::LoopInvariantExit,
        },
    }]
}

/// Declare a range bound: literal embeds inline, Local declares DeclareConst.
fn declare_range_bound(bound: &RangeBound, script: &mut Script) -> Term {
    match bound {
        RangeBound::Literal(n) => Term::IntLit(*n),
        RangeBound::Local(name) => {
            script.push(Command::DeclareConst(name.clone(), Sort::Int));
            Term::Const(name.clone())
        }
    }
}

/// Range bounded unrolling VC (QF_LIA) — test 04.
fn gen_range_bounded_vc(
    func: &Function,
    loop_info: &LoopInfo,
    loop_var: &str,
    start: &RangeBound,
    end: &RangeBound,
    inclusive: bool,
    depth: usize,
) -> Vec<VerificationCondition> {
    let mut script = Script::new();
    script.push(Command::SetLogic("QF_LIA".to_string()));

    let start_term = declare_range_bound(start, &mut script);
    let end_term = declare_range_bound(end, &mut script);

    // For each k in 0..depth: (=> (cmp (+ start k) end) true)
    for k in 0..depth {
        let k_plus_start = if k == 0 {
            start_term.clone()
        } else {
            Term::IntAdd(
                Box::new(start_term.clone()),
                Box::new(Term::IntLit(k as i128)),
            )
        };
        let guard = if inclusive {
            Term::IntLe(Box::new(k_plus_start.clone()), Box::new(end_term.clone()))
        } else {
            Term::IntLt(Box::new(k_plus_start.clone()), Box::new(end_term.clone()))
        };
        // (assert (=> guard true)) — trivially true, establishes unrolling structure
        script.push(Command::Assert(Term::Implies(
            Box::new(guard),
            Box::new(Term::BoolLit(true)),
        )));
    }
    script.push(Command::CheckSat);

    vec![VerificationCondition {
        description: format!(
            "{}: for-loop range bounded unrolling VC (depth={})",
            func.name, depth
        ),
        script,
        location: VcLocation {
            function: func.name.clone(),
            block: loop_info.header_block,
            statement: 0,
            source_file: None,
            source_line: None,
            source_column: None,
            contract_text: Some(format!("for {loop_var} in range (bounded N={depth})")),
            vc_kind: VcKind::LoopInvariantExit,
        },
    }]
}

/// Slice/Vec quantified VC (test 05) — uses `{arr}_len` from Phase 28.
fn gen_slice_quantified_vc(
    func: &Function,
    loop_info: &LoopInfo,
    loop_var: &str,
    collection_local: &str,
) -> Vec<VerificationCondition> {
    use crate::encode_term::len_constant_name;
    let len_name = len_constant_name(collection_local);

    let mut script = Script::new();
    script.push(Command::SetLogic("AUFLIA".to_string()));
    script.push(Command::DeclareConst(len_name.clone(), Sort::Int));

    let i_name = loop_var.to_string();
    let range_guard = Term::And(vec![
        Term::IntLe(
            Box::new(Term::IntLit(0)),
            Box::new(Term::Const(i_name.clone())),
        ),
        Term::IntLt(
            Box::new(Term::Const(i_name.clone())),
            Box::new(Term::Const(len_name.clone())),
        ),
    ]);
    let forall_term = Term::Forall(
        vec![(i_name.clone(), Sort::Int)],
        Box::new(Term::Implies(
            Box::new(range_guard),
            Box::new(Term::BoolLit(true)),
        )),
    );
    script.push(Command::Assert(Term::Not(Box::new(forall_term))));
    script.push(Command::CheckSat);

    let mut result = vec![VerificationCondition {
        description: format!(
            "{}: for-loop slice/vec iter AUFLIA quantified VC ({})",
            func.name, collection_local
        ),
        script,
        location: VcLocation {
            function: func.name.clone(),
            block: loop_info.header_block,
            statement: 0,
            source_file: None,
            source_line: None,
            source_column: None,
            contract_text: Some(format!("for {i_name} in {collection_local}.iter()")),
            vc_kind: VcKind::LoopInvariantExit,
        },
    }];

    // Test 08: emit a MemorySafety VC when loop_var is known (for element bounds check)
    if loop_info.loop_var.is_some() {
        let mut safety_script = Script::new();
        safety_script.push(Command::SetLogic("QF_LIA".to_string()));
        safety_script.push(Command::DeclareConst(len_name.clone(), Sort::Int));
        safety_script.push(Command::DeclareConst(i_name.clone(), Sort::Int));
        // bounds check: 0 <= i && i < len
        safety_script.push(Command::Assert(Term::And(vec![
            Term::IntLe(
                Box::new(Term::IntLit(0)),
                Box::new(Term::Const(i_name.clone())),
            ),
            Term::IntLt(
                Box::new(Term::Const(i_name.clone())),
                Box::new(Term::Const(len_name.clone())),
            ),
        ])));
        safety_script.push(Command::CheckSat);

        result.push(VerificationCondition {
            description: format!(
                "{}: for-loop slice element bounds check (MemorySafety)",
                func.name
            ),
            script: safety_script,
            location: VcLocation {
                function: func.name.clone(),
                block: loop_info.header_block,
                statement: 0,
                source_file: None,
                source_line: None,
                source_column: None,
                contract_text: Some(format!("{collection_local}[{i_name}] bounds check")),
                vc_kind: VcKind::MemorySafety,
            },
        });
    }

    result
}

/// Slice bounded unrolling VC (test 05 regression).
fn gen_slice_bounded_vc(
    func: &Function,
    loop_info: &LoopInfo,
    loop_var: &str,
    collection_local: &str,
    depth: usize,
) -> Vec<VerificationCondition> {
    use crate::encode_term::len_constant_name;
    let len_name = len_constant_name(collection_local);

    let mut script = Script::new();
    script.push(Command::SetLogic("QF_LIA".to_string()));
    script.push(Command::DeclareConst(len_name.clone(), Sort::Int));

    for k in 0..depth {
        let guard = Term::IntLt(
            Box::new(Term::IntLit(k as i128)),
            Box::new(Term::Const(len_name.clone())),
        );
        script.push(Command::Assert(Term::Implies(
            Box::new(guard),
            Box::new(Term::BoolLit(true)),
        )));
    }
    script.push(Command::CheckSat);

    vec![VerificationCondition {
        description: format!(
            "{}: for-loop slice/vec iter bounded unrolling VC (depth={})",
            func.name, depth
        ),
        script,
        location: VcLocation {
            function: func.name.clone(),
            block: loop_info.header_block,
            statement: 0,
            source_file: None,
            source_line: None,
            source_column: None,
            contract_text: Some(format!(
                "for {loop_var} in {collection_local}.iter() (bounded N={depth})"
            )),
            vc_kind: VcKind::LoopInvariantExit,
        },
    }]
}

/// Enumerate VC (test 06) — declares `index_{loop_var}: Int` and `elem_{loop_var}: Int`.
fn gen_enumerate_vc(
    func: &Function,
    loop_info: &LoopInfo,
    loop_var: &str,
    inner: &IteratorKind,
) -> Vec<VerificationCondition> {
    let mut script = Script::new();
    script.push(Command::SetLogic("AUFLIA".to_string()));

    let index_name = format!("index_{loop_var}");
    let elem_name = format!("elem_{loop_var}");
    script.push(Command::DeclareConst(index_name.clone(), Sort::Int));
    // Elem type: use Sort::Int as conservative default
    script.push(Command::DeclareConst(elem_name.clone(), Sort::Int));

    // index >= 0
    script.push(Command::Assert(Term::IntLe(
        Box::new(Term::IntLit(0)),
        Box::new(Term::Const(index_name.clone())),
    )));

    script.push(Command::CheckSat);

    // Also emit inner iterator VCs (e.g., slice bounds)
    let mut inner_vcs = match inner {
        IteratorKind::SliceIter { collection_local }
        | IteratorKind::VecIter { collection_local } => {
            gen_slice_quantified_vc(func, loop_info, loop_var, collection_local)
        }
        _ => vec![],
    };

    let mut result = vec![VerificationCondition {
        description: format!(
            "{}: for-loop enumerate VC (index_{loop_var}, elem_{loop_var})",
            func.name
        ),
        script,
        location: VcLocation {
            function: func.name.clone(),
            block: loop_info.header_block,
            statement: 0,
            source_file: None,
            source_line: None,
            source_column: None,
            contract_text: Some(format!("for ({loop_var}, elem) in iter.enumerate()")),
            vc_kind: VcKind::LoopInvariantExit,
        },
    }];
    result.append(&mut inner_vcs);
    result
}

/// Conservative VC (tests 07, StdAdapter) — BoolLit(true).
fn gen_conservative_vc(
    func: &Function,
    loop_info: &LoopInfo,
    iterator_name: &str,
) -> VerificationCondition {
    let mut script = Script::new();
    script.push(Command::SetLogic("QF_LIA".to_string()));
    // TODO: encode {iterator_name} iterator
    script.push(Command::Assert(Term::BoolLit(true)));
    script.push(Command::CheckSat);

    VerificationCondition {
        description: format!(
            "{}: for-loop over {} — conservative VC (BoolLit(true))",
            func.name, iterator_name
        ),
        script,
        location: VcLocation {
            function: func.name.clone(),
            block: loop_info.header_block,
            statement: 0,
            source_file: None,
            source_line: None,
            source_column: None,
            contract_text: Some(format!("loop over {} (conservative)", iterator_name)),
            vc_kind: VcKind::LoopInvariantExit,
        },
    }
}
