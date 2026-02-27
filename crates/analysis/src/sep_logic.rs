/// Separation logic heap domain and pts_to predicate encoding.
///
/// This module provides:
/// - `declare_sep_heap()`: SMT declarations for the heap and permission arrays.
/// - `declare_heapval_accessor()`: Declaration of the bitvector accessor for HeapVal.
/// - `encode_pts_to()`: Encodes `pts_to(ptr, val)` as a compound SMT term.
/// - `sep_logic_smt_logic()`: Returns the SMT-LIB logic string appropriate for separation logic VCs.
/// - `extract_pts_to_footprint()`: Walks an encoded term and extracts the footprint of pts_to applications.
///
/// ## Heap model
///
/// The separation heap is represented as two uninterpreted SMT arrays:
/// - `sep_heap : (Array (_ BitVec 64) HeapVal)` — maps addresses to heap values
/// - `perm : (Array (_ BitVec 64) Bool)` — maps addresses to ownership permissions
///
/// `HeapVal` is an uninterpreted sort; `heapval_as_bvN` coerces it to a bitvector.
///
/// ## pts_to encoding
///
/// `pts_to(p, v)` is encoded as:
/// ```smt2
/// (and (select perm p)
///      (= (heapval_as_bvN (select sep_heap p)) v))
/// ```
use rust_fv_smtlib::command::Command;
use rust_fv_smtlib::sort::Sort;
use rust_fv_smtlib::term::Term;

/// Emit SMT declarations required for the separation heap domain.
///
/// Returns 3 commands:
/// 1. `(declare-sort HeapVal 0)`
/// 2. `(declare-fun sep_heap () (Array (_ BitVec 64) HeapVal))`
/// 3. `(declare-fun perm () (Array (_ BitVec 64) Bool))`
pub fn declare_sep_heap() -> Vec<Command> {
    vec![
        // Uninterpreted sort for heap values
        Command::DeclareSort("HeapVal".to_string(), 0),
        // sep_heap : Array Addr HeapVal
        Command::DeclareFun(
            "sep_heap".to_string(),
            vec![],
            Sort::Array(
                Box::new(Sort::BitVec(64)),
                Box::new(Sort::Uninterpreted("HeapVal".to_string())),
            ),
        ),
        // perm : Array Addr Bool
        Command::DeclareFun(
            "perm".to_string(),
            vec![],
            Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::Bool)),
        ),
    ]
}

/// Emit the declaration of a HeapVal-to-bitvector accessor function.
///
/// `(declare-fun heapval_as_bvN (HeapVal) (_ BitVec N))`
///
/// The name of the function is `heapval_as_bv{pointee_bits}` (e.g., `heapval_as_bv32`).
pub fn declare_heapval_accessor(pointee_bits: u32) -> Command {
    let name = format!("heapval_as_bv{pointee_bits}");
    Command::DeclareFun(
        name,
        vec![Sort::Uninterpreted("HeapVal".to_string())],
        Sort::BitVec(pointee_bits),
    )
}

/// Encode `pts_to(ptr, val)` as:
/// ```smt2
/// (and (select perm ptr)
///      (= (heapval_as_bvN (select sep_heap ptr)) val))
/// ```
///
/// where N = `pointee_bits`.
pub fn encode_pts_to(ptr: Term, val: Term, pointee_bits: u32) -> Term {
    // (select perm ptr)
    let perm_check = Term::Select(
        Box::new(Term::Const("perm".to_string())),
        Box::new(ptr.clone()),
    );

    // (select sep_heap ptr)
    let heap_select = Term::Select(Box::new(Term::Const("sep_heap".to_string())), Box::new(ptr));

    // (heapval_as_bvN (select sep_heap ptr))
    let accessor_name = format!("heapval_as_bv{pointee_bits}");
    let heap_val_typed = Term::App(accessor_name, vec![heap_select]);

    // (= (heapval_as_bvN ...) val)
    let val_eq = Term::Eq(Box::new(heap_val_typed), Box::new(val));

    // (and perm_check val_eq)
    Term::And(vec![perm_check, val_eq])
}

/// Return the SMT-LIB logic string for separation logic verification conditions.
///
/// - `has_frame_forall = false` → `"QF_AUFBV"` (quantifier-free arrays + bitvectors)
/// - `has_frame_forall = true`  → `"AUFBV"` (arrays + bitvectors + quantifiers for frame rule)
pub fn sep_logic_smt_logic(has_frame_forall: bool) -> &'static str {
    if has_frame_forall {
        "AUFBV"
    } else {
        "QF_AUFBV"
    }
}

/// Walk an encoded separation-logic term and collect all footprint pointers.
///
/// A `pts_to(ptr, val)` is represented as `Term::And([Select(perm, ptr), Eq(...)])`.
/// This function identifies every such pattern and returns the `ptr` argument.
///
/// Used by the frame rule (Plan 03) to compute the write-set of a callee spec.
pub fn extract_pts_to_footprint(spec_term: &Term) -> Vec<Term> {
    let mut footprint = Vec::new();
    collect_footprint(spec_term, &mut footprint);
    footprint
}

/// Recursive helper for `extract_pts_to_footprint`.
fn collect_footprint(term: &Term, acc: &mut Vec<Term>) {
    match term {
        Term::And(arms) => {
            // Detect pts_to pattern: And([Select(perm, ptr), ...])
            if let Some(first) = arms.first()
                && let Term::Select(arr, idx) = first
                && let Term::Const(arr_name) = arr.as_ref()
                && arr_name == "perm"
            {
                acc.push(*idx.clone());
                // Don't recurse into arms — this whole And IS the pts_to encoding.
                return;
            }
            // Not a pts_to pattern — recurse into all arms.
            for arm in arms {
                collect_footprint(arm, acc);
            }
        }
        Term::Or(arms) => {
            for arm in arms {
                collect_footprint(arm, acc);
            }
        }
        Term::Not(inner) => collect_footprint(inner, acc),
        Term::Implies(lhs, rhs) => {
            collect_footprint(lhs, acc);
            collect_footprint(rhs, acc);
        }
        Term::Forall(_, body) | Term::Exists(_, body) => collect_footprint(body, acc),
        Term::Let(_, body) => collect_footprint(body, acc),
        Term::Ite(cond, then_, else_) => {
            collect_footprint(cond, acc);
            collect_footprint(then_, acc);
            collect_footprint(else_, acc);
        }
        Term::Annotated(inner, _) => collect_footprint(inner, acc),
        _ => {}
    }
}

/// Build the frame axiom asserting that sep_heap is unchanged for all addresses
/// outside the given footprint after a function call.
///
/// Emits:
///   (forall ((_sep_frame_addr (_ BitVec 64)))
///     (! (=> (not (or (= _sep_frame_addr p1) ...))
///            (= (select sep_heap _sep_frame_addr) (select sep_heap_pre _sep_frame_addr)))
///        :pattern ((select sep_heap _sep_frame_addr))))
///
/// The `:pattern` trigger tells Z3's E-matching to only instantiate this forall
/// when a sep_heap select term is present, avoiding quantifier looping.
pub fn build_frame_axiom(footprint_ptrs: &[Term]) -> Term {
    let addr_var = "_sep_frame_addr".to_string();

    // not_in_fp: addr is not one of the footprint pointers
    let not_in_fp: Term = if footprint_ptrs.is_empty() {
        Term::BoolLit(true)
    } else {
        let in_fp: Vec<Term> = footprint_ptrs
            .iter()
            .map(|p| Term::Eq(Box::new(Term::Const(addr_var.clone())), Box::new(p.clone())))
            .collect();
        Term::Not(Box::new(if in_fp.len() == 1 {
            in_fp.into_iter().next().unwrap()
        } else {
            Term::Or(in_fp)
        }))
    };

    // sep_heap unchanged: (= (select sep_heap addr) (select sep_heap_pre addr))
    let post_select = Term::Select(
        Box::new(Term::Const("sep_heap".to_string())),
        Box::new(Term::Const(addr_var.clone())),
    );
    let pre_select = Term::Select(
        Box::new(Term::Const("sep_heap_pre".to_string())),
        Box::new(Term::Const(addr_var.clone())),
    );
    let heap_unchanged = Term::Eq(Box::new(post_select.clone()), Box::new(pre_select));

    let body = Term::Implies(Box::new(not_in_fp), Box::new(heap_unchanged));

    // Trigger: :pattern ((select sep_heap addr)) for E-matching efficiency
    let trigger = post_select; // reuse the post-call select term as the pattern
    let annotated = Term::Annotated(Box::new(body), vec![("pattern".to_string(), vec![trigger])]);

    Term::Forall(vec![(addr_var, Sort::BitVec(64))], Box::new(annotated))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_declare_sep_heap_commands() {
        let cmds = declare_sep_heap();
        assert_eq!(
            cmds.len(),
            3,
            "declare_sep_heap() must return exactly 3 commands"
        );
        assert!(
            matches!(cmds[0], Command::DeclareSort(ref name, 0) if name == "HeapVal"),
            "First command must be DeclareSort(HeapVal, 0), got {:?}",
            cmds[0]
        );
        assert!(
            matches!(cmds[1], Command::DeclareFun(ref name, _, _) if name == "sep_heap"),
            "Second command must declare sep_heap, got {:?}",
            cmds[1]
        );
        assert!(
            matches!(cmds[2], Command::DeclareFun(ref name, _, _) if name == "perm"),
            "Third command must declare perm, got {:?}",
            cmds[2]
        );
    }

    #[test]
    fn test_encode_pts_to_structure() {
        let ptr = Term::Const("p".to_string());
        let val = Term::Const("v".to_string());
        let result = encode_pts_to(ptr, val, 32);

        // Must be Term::And with exactly 2 arms
        if let Term::And(arms) = &result {
            assert_eq!(arms.len(), 2, "pts_to must encode as And with 2 arms");

            // First arm must be Select(perm, ptr)
            match &arms[0] {
                Term::Select(arr, _idx) => {
                    assert_eq!(
                        *arr.as_ref(),
                        Term::Const("perm".to_string()),
                        "First arm of pts_to must select from 'perm'"
                    );
                }
                other => panic!("Expected Select(perm, ...) as first arm, got {other:?}"),
            }
        } else {
            panic!("encode_pts_to must produce Term::And, got {result:?}");
        }
    }

    #[test]
    fn test_sep_logic_smt_logic() {
        assert_eq!(sep_logic_smt_logic(false), "QF_AUFBV");
        assert_eq!(sep_logic_smt_logic(true), "AUFBV");
    }

    #[test]
    fn test_build_frame_axiom_empty_footprint() {
        // With an empty footprint, frame axiom is a universal "heap unchanged"
        let axiom = build_frame_axiom(&[]);
        assert!(
            matches!(axiom, Term::Forall(_, _)),
            "build_frame_axiom must produce Term::Forall, got {axiom:?}"
        );
        if let Term::Forall(vars, _body) = &axiom {
            assert_eq!(vars.len(), 1, "frame axiom must bind exactly one variable");
            assert_eq!(
                vars[0].0, "_sep_frame_addr",
                "bound variable must be _sep_frame_addr"
            );
            assert!(
                matches!(vars[0].1, Sort::BitVec(64)),
                "bound variable sort must be BitVec(64)"
            );
        }
    }

    #[test]
    fn test_build_frame_axiom_single_ptr() {
        let ptr = Term::Const("p".to_string());
        let axiom = build_frame_axiom(&[ptr]);
        assert!(
            matches!(axiom, Term::Forall(_, _)),
            "build_frame_axiom with one pointer must produce Term::Forall"
        );
    }

    #[test]
    fn test_build_frame_axiom_multiple_ptrs() {
        let ptrs = vec![Term::Const("p".to_string()), Term::Const("q".to_string())];
        let axiom = build_frame_axiom(&ptrs);
        assert!(
            matches!(axiom, Term::Forall(_, _)),
            "build_frame_axiom with multiple pointers must produce Term::Forall"
        );
    }
}
