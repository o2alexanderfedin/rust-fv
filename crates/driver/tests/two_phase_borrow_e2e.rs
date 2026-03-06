/// End-to-end two-phase borrow tests (COMPL-13).
///
/// Tests that the MIR converter populates BorrowPhase::Reserved for two-phase borrows
/// and that detect_borrow_conflicts produces no false positives for the
/// vec.push(vec.len()) pattern.
use std::collections::HashMap;

use rust_fv_analysis::borrow_conflict::{detect_borrow_conflicts, generate_conflict_vcs};
use rust_fv_analysis::ir::{BorrowInfo, BorrowPhase};
use rust_fv_analysis::lifetime_analysis::LifetimeContext;

/// Test: Reserved mutable borrow + Active shared borrow with overlapping live ranges
/// produces NO conflicts (the two-phase borrow skip logic).
/// Then, when both are Active, a conflict IS detected (control case).
#[test]
fn test_two_phase_borrow_e2e_no_false_positive() {
    // Simulates vec.push(vec.len()) pattern:
    // _2 = &mut vec  (Reserved, for push receiver)
    // _3 = &vec      (Active shared, for len)
    // call push(_2, _3) -- _2 activates here

    let mut context = LifetimeContext::new();

    // Shared borrow for vec.len()
    context.register_borrow(BorrowInfo {
        local_name: "_3".to_string(),
        region: "'_0".to_string(),
        is_mutable: false,
        deref_level: 0,
        source_local: None,
        phase: BorrowPhase::Active,
    });

    // Mutable borrow in Reserved phase for push receiver
    context.register_borrow(BorrowInfo {
        local_name: "_2".to_string(),
        region: "'_1".to_string(),
        is_mutable: true,
        deref_level: 0,
        source_local: None,
        phase: BorrowPhase::Reserved,
    });

    // Both live in blocks 0-2 (overlapping)
    let mut live_ranges = HashMap::new();
    live_ranges.insert("_3".to_string(), vec![0, 1, 2]);
    live_ranges.insert("_2".to_string(), vec![0, 1, 2]);

    let conflicts = detect_borrow_conflicts(&context, &live_ranges, None);
    assert!(
        conflicts.is_empty(),
        "Expected NO conflict for Reserved mutable borrow overlapping shared borrow \
         (two-phase pattern), but got {} conflict(s)",
        conflicts.len()
    );

    // No VCs generated
    let vcs = generate_conflict_vcs(&conflicts, "push_len_fn");
    assert!(
        vcs.is_empty(),
        "Expected no conflict VCs for Reserved borrow"
    );
}

/// Control case: when both borrows are Active, conflict IS detected.
#[test]
fn test_two_phase_borrow_e2e_active_does_conflict() {
    let mut context = LifetimeContext::new();

    // Shared borrow (Active)
    context.register_borrow(BorrowInfo {
        local_name: "_3".to_string(),
        region: "'_0".to_string(),
        is_mutable: false,
        deref_level: 0,
        source_local: None,
        phase: BorrowPhase::Active,
    });

    // Mutable borrow also Active (NOT Reserved)
    context.register_borrow(BorrowInfo {
        local_name: "_2".to_string(),
        region: "'_1".to_string(),
        is_mutable: true,
        deref_level: 0,
        source_local: None,
        phase: BorrowPhase::Active,
    });

    // Same overlapping live ranges
    let mut live_ranges = HashMap::new();
    live_ranges.insert("_3".to_string(), vec![0, 1, 2]);
    live_ranges.insert("_2".to_string(), vec![0, 1, 2]);

    let conflicts = detect_borrow_conflicts(&context, &live_ranges, None);
    assert_eq!(
        conflicts.len(),
        1,
        "Expected exactly 1 conflict when mutable borrow is Active (not Reserved)"
    );

    // Verify VCs are generated
    let vcs = generate_conflict_vcs(&conflicts, "push_len_fn");
    assert_eq!(vcs.len(), 1, "Expected 1 conflict VC for Active borrow");
}

/// Activated borrows also produce conflicts (reservation consumed at call site).
#[test]
fn test_two_phase_borrow_e2e_activated_conflicts() {
    let mut context = LifetimeContext::new();

    context.register_borrow(BorrowInfo {
        local_name: "_3".to_string(),
        region: "'_0".to_string(),
        is_mutable: false,
        deref_level: 0,
        source_local: None,
        phase: BorrowPhase::Active,
    });

    // Mutable borrow Activated (post-reservation)
    context.register_borrow(BorrowInfo {
        local_name: "_2".to_string(),
        region: "'_1".to_string(),
        is_mutable: true,
        deref_level: 0,
        source_local: None,
        phase: BorrowPhase::Activated,
    });

    let mut live_ranges = HashMap::new();
    live_ranges.insert("_3".to_string(), vec![0, 1, 2]);
    live_ranges.insert("_2".to_string(), vec![1, 2, 3]);

    let conflicts = detect_borrow_conflicts(&context, &live_ranges, None);
    assert_eq!(
        conflicts.len(),
        1,
        "Expected 1 conflict for Activated mutable borrow overlapping shared borrow"
    );
}
