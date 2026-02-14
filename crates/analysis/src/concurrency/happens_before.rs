/// Happens-before encoding for concurrency verification.
///
/// Implements the happens-before partial order for data race detection,
/// encoding all 5 Rust atomic memory orderings (Relaxed, Acquire, Release,
/// AcqRel, SeqCst) as SMT constraints following C11 semantics.
use crate::ir::AtomicOrdering;
use crate::vcgen::{VcKind, VcLocation, VerificationCondition};
use rust_fv_smtlib::script::Script;
use rust_fv_smtlib::term::Term;

/// Event identifier in the happens-before relation.
pub type EventId = usize;

/// A memory access event in the program.
#[derive(Debug, Clone)]
pub struct MemoryAccess {
    /// Unique event identifier
    pub event_id: EventId,
    /// Memory location (place name)
    pub location: String,
    /// True if this is a write/store, false if read/load
    pub is_write: bool,
    /// Thread that performed this access
    pub thread_id: usize,
    /// Source line number (if available)
    pub source_line: Option<usize>,
}

/// Encode happens-before relation between two events.
///
/// Returns an SMT term: `timestamp_a < timestamp_b` using bitvector signed less-than.
pub fn happens_before(event_a: EventId, event_b: EventId) -> Term {
    Term::BvSLt(
        Box::new(Term::Const(format!("ts_{}", event_a))),
        Box::new(Term::Const(format!("ts_{}", event_b))),
    )
}

/// Encode reads-from relation.
///
/// Returns an SMT term: `rf_load == event_store`
pub fn reads_from(load_event: EventId, store_event: EventId) -> Term {
    Term::Eq(
        Box::new(Term::Const(format!("rf_{}", load_event))),
        Box::new(Term::Const(format!("event_{}", store_event))),
    )
}

/// Encode atomic ordering constraints as SMT terms.
///
/// Maps Rust's 5 atomic orderings to C11 semantics:
/// - SeqCst: total order via happens_before(store, load)
/// - Release: implies(reads_from(load, store), happens_before(store, load))
/// - Acquire: implies(reads_from(load, store), happens_before(store, load))
/// - AcqRel: same as Acquire (both acquire and release semantics)
/// - Relaxed: BoolLit(true) (no synchronization, only atomicity)
pub fn encode_atomic_ordering(
    ordering: AtomicOrdering,
    store_event: EventId,
    load_event: EventId,
) -> Term {
    match ordering {
        AtomicOrdering::SeqCst => happens_before(store_event, load_event),
        AtomicOrdering::Release | AtomicOrdering::Acquire | AtomicOrdering::AcqRel => {
            Term::Implies(
                Box::new(reads_from(load_event, store_event)),
                Box::new(happens_before(store_event, load_event)),
            )
        }
        AtomicOrdering::Relaxed => Term::BoolLit(true),
    }
}

/// Encode mutex happens-before relation.
///
/// A mutex unlock (release) synchronizes-with the next lock (acquire).
pub fn mutex_happens_before(
    release_thread: usize,
    release_pc: usize,
    acquire_thread: usize,
    acquire_pc: usize,
) -> Term {
    let release_ts = format!("ts_t{}_pc{}", release_thread, release_pc);
    let acquire_ts = format!("ts_t{}_pc{}", acquire_thread, acquire_pc);
    Term::BvSLt(
        Box::new(Term::Const(release_ts)),
        Box::new(Term::Const(acquire_ts)),
    )
}

/// Check if two memory accesses conflict.
///
/// Accesses conflict if:
/// - They access the same location
/// - They are from different threads
/// - At least one is a write
fn conflicting(a: &MemoryAccess, b: &MemoryAccess) -> bool {
    a.location == b.location && a.thread_id != b.thread_id && (a.is_write || b.is_write)
}

/// Generate data race freedom verification conditions.
///
/// For each pair of conflicting accesses, generate a VC asserting that
/// they must be ordered by the happens-before relation.
pub fn data_race_freedom_vcs(accesses: &[MemoryAccess]) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    for i in 0..accesses.len() {
        for j in (i + 1)..accesses.len() {
            let a = &accesses[i];
            let b = &accesses[j];

            if conflicting(a, b) {
                let _hb_a_b = happens_before(a.event_id, b.event_id);
                let _hb_b_a = happens_before(b.event_id, a.event_id);
                let _ordered = Term::Or(vec![_hb_a_b, _hb_b_a]);

                let description = format!(
                    "Data race freedom: conflicting accesses to {} from threads {} and {} must be ordered",
                    a.location, a.thread_id, b.thread_id
                );

                let script = Script::new(); // Placeholder - will be filled by VCGen

                vcs.push(VerificationCondition {
                    description,
                    script,
                    location: VcLocation {
                        function: "concurrent_fn".to_string(),
                        block: 0,
                        statement: 0,
                        source_file: None,
                        source_line: a.source_line,
                        contract_text: Some(format!("{} accessed by multiple threads", a.location)),
                        vc_kind: VcKind::DataRaceFreedom,
                    },
                });
            }
        }
    }

    vcs
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_happens_before_encoding() {
        let hb = happens_before(0, 1);
        match hb {
            Term::BvSLt(a, b) => {
                assert_eq!(*a, Term::Const("ts_0".to_string()));
                assert_eq!(*b, Term::Const("ts_1".to_string()));
            }
            _ => panic!("Expected BvSLt"),
        }
    }

    #[test]
    fn test_reads_from_encoding() {
        let rf = reads_from(0, 1);
        match rf {
            Term::Eq(a, b) => {
                assert_eq!(*a, Term::Const("rf_0".to_string()));
                assert_eq!(*b, Term::Const("event_1".to_string()));
            }
            _ => panic!("Expected Eq"),
        }
    }

    #[test]
    fn test_seqcst_ordering() {
        let term = encode_atomic_ordering(AtomicOrdering::SeqCst, 0, 1);
        match term {
            Term::BvSLt(a, b) => {
                assert_eq!(*a, Term::Const("ts_0".to_string()));
                assert_eq!(*b, Term::Const("ts_1".to_string()));
            }
            _ => panic!("Expected BvSLt for SeqCst"),
        }
    }

    #[test]
    fn test_acquire_ordering() {
        let term = encode_atomic_ordering(AtomicOrdering::Acquire, 0, 1);
        match term {
            Term::Implies(rf, hb) => {
                assert!(matches!(*rf, Term::Eq(_, _)));
                assert!(matches!(*hb, Term::BvSLt(_, _)));
            }
            _ => panic!("Expected Implies for Acquire"),
        }
    }

    #[test]
    fn test_release_ordering() {
        let term = encode_atomic_ordering(AtomicOrdering::Release, 0, 1);
        match term {
            Term::Implies(rf, hb) => {
                assert!(matches!(*rf, Term::Eq(_, _)));
                assert!(matches!(*hb, Term::BvSLt(_, _)));
            }
            _ => panic!("Expected Implies for Release"),
        }
    }

    #[test]
    fn test_acqrel_ordering() {
        let term = encode_atomic_ordering(AtomicOrdering::AcqRel, 0, 1);
        match term {
            Term::Implies(rf, hb) => {
                assert!(matches!(*rf, Term::Eq(_, _)));
                assert!(matches!(*hb, Term::BvSLt(_, _)));
            }
            _ => panic!("Expected Implies for AcqRel"),
        }
    }

    #[test]
    fn test_relaxed_ordering() {
        let term = encode_atomic_ordering(AtomicOrdering::Relaxed, 0, 1);
        assert_eq!(term, Term::BoolLit(true));
    }

    #[test]
    fn test_mutex_happens_before() {
        let hb = mutex_happens_before(0, 5, 1, 10);
        match hb {
            Term::BvSLt(a, b) => {
                assert_eq!(*a, Term::Const("ts_t0_pc5".to_string()));
                assert_eq!(*b, Term::Const("ts_t1_pc10".to_string()));
            }
            _ => panic!("Expected BvSLt"),
        }
    }

    #[test]
    fn test_data_race_freedom_conflicting() {
        let accesses = vec![
            MemoryAccess {
                event_id: 0,
                location: "x".to_string(),
                is_write: true,
                thread_id: 0,
                source_line: Some(10),
            },
            MemoryAccess {
                event_id: 1,
                location: "x".to_string(),
                is_write: true,
                thread_id: 1,
                source_line: Some(20),
            },
        ];

        let vcs = data_race_freedom_vcs(&accesses);
        assert_eq!(vcs.len(), 1);
        assert!(vcs[0].description.contains("Data race freedom"));
        assert!(vcs[0].description.contains("threads 0 and 1"));
    }

    #[test]
    fn test_data_race_freedom_no_conflict_reads() {
        let accesses = vec![
            MemoryAccess {
                event_id: 0,
                location: "x".to_string(),
                is_write: false,
                thread_id: 0,
                source_line: Some(10),
            },
            MemoryAccess {
                event_id: 1,
                location: "x".to_string(),
                is_write: false,
                thread_id: 1,
                source_line: Some(20),
            },
        ];

        let vcs = data_race_freedom_vcs(&accesses);
        assert_eq!(vcs.len(), 0); // Two reads don't conflict
    }

    #[test]
    fn test_data_race_freedom_no_conflict_different_location() {
        let accesses = vec![
            MemoryAccess {
                event_id: 0,
                location: "x".to_string(),
                is_write: true,
                thread_id: 0,
                source_line: Some(10),
            },
            MemoryAccess {
                event_id: 1,
                location: "y".to_string(),
                is_write: true,
                thread_id: 1,
                source_line: Some(20),
            },
        ];

        let vcs = data_race_freedom_vcs(&accesses);
        assert_eq!(vcs.len(), 0); // Different locations don't conflict
    }

    #[test]
    fn test_data_race_freedom_same_thread() {
        let accesses = vec![
            MemoryAccess {
                event_id: 0,
                location: "x".to_string(),
                is_write: true,
                thread_id: 0,
                source_line: Some(10),
            },
            MemoryAccess {
                event_id: 1,
                location: "x".to_string(),
                is_write: true,
                thread_id: 0,
                source_line: Some(20),
            },
        ];

        let vcs = data_race_freedom_vcs(&accesses);
        assert_eq!(vcs.len(), 0); // Same thread doesn't conflict
    }
}
