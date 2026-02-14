/// Lock invariant verification.
///
/// Implements lock invariant encoding: invariants are assumed at acquire
/// (added to path condition) and asserted at release (generate VC).
use crate::vcgen::{VcLocation, VerificationCondition};
use rust_fv_smtlib::script::Script;

/// Lock operation type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LockOp {
    /// Lock acquisition (assume invariant)
    Acquire,
    /// Lock release (assert invariant)
    Release,
}

/// Generate lock invariant verification conditions.
///
/// For each lock operation:
/// - At Acquire: return None (invariant assumed, no VC generated)
/// - At Release: generate VcKind::LockInvariant VC asserting invariant holds
pub fn lock_invariant_vcs(
    mutex_local: &str,
    invariant_expr: &str,
    locations: &[(VcLocation, LockOp)],
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    for (location, op) in locations {
        match op {
            LockOp::Acquire => {
                // No VC generated - invariant is assumed and added to path condition
                continue;
            }
            LockOp::Release => {
                let description = format!(
                    "Lock invariant for {} must hold at release: {}",
                    mutex_local, invariant_expr
                );

                // Placeholder script - will be filled by VCGen
                let script = Script::new();

                vcs.push(VerificationCondition {
                    description,
                    script,
                    location: location.clone(),
                });
            }
        }
    }

    vcs
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vcgen::VcKind;

    fn test_location(block: usize, op: LockOp) -> (VcLocation, LockOp) {
        (
            VcLocation {
                function: "test_fn".to_string(),
                block,
                statement: 0,
                source_file: None,
                source_line: None,
                contract_text: None,
                vc_kind: VcKind::LockInvariant,
            },
            op,
        )
    }

    #[test]
    fn test_lock_invariant_at_acquire() {
        let locations = vec![test_location(0, LockOp::Acquire)];
        let vcs = lock_invariant_vcs("mutex", "x > 0", &locations);
        assert_eq!(vcs.len(), 0); // No VC for acquire
    }

    #[test]
    fn test_lock_invariant_at_release() {
        let locations = vec![test_location(1, LockOp::Release)];
        let vcs = lock_invariant_vcs("mutex", "x > 0", &locations);
        assert_eq!(vcs.len(), 1);
        assert_eq!(vcs[0].location.vc_kind, VcKind::LockInvariant);
        assert!(vcs[0].description.contains("Lock invariant"));
        assert!(vcs[0].description.contains("mutex"));
        assert!(vcs[0].description.contains("x > 0"));
    }

    #[test]
    fn test_lock_invariant_description() {
        let locations = vec![test_location(1, LockOp::Release)];
        let vcs = lock_invariant_vcs("my_mutex", "balance >= 0", &locations);
        assert_eq!(vcs.len(), 1);
        assert!(vcs[0].description.contains("my_mutex"));
        assert!(vcs[0].description.contains("balance >= 0"));
        assert!(vcs[0].description.contains("release"));
    }

    #[test]
    fn test_lock_invariant_multiple_releases() {
        let locations = vec![
            test_location(1, LockOp::Acquire),
            test_location(2, LockOp::Release),
            test_location(3, LockOp::Release),
        ];
        let vcs = lock_invariant_vcs("mutex", "x > 0", &locations);
        assert_eq!(vcs.len(), 2); // One VC per release
        assert_eq!(vcs[0].location.block, 2);
        assert_eq!(vcs[1].location.block, 3);
    }
}
