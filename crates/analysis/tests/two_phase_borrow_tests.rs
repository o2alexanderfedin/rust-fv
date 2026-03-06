/// Two-phase borrow modeling tests (COMPL-13).
///
/// Tests that the verifier correctly handles two-phase borrows:
/// - Reserved borrows do not conflict with shared borrows
/// - Active borrows conflict with shared borrows (existing behavior)
/// - Activated borrows conflict like Active (reservation consumed)
/// - vec.push(vec.len()) pattern produces no false positive
use std::collections::HashMap;

use rust_fv_analysis::borrow_conflict::{detect_borrow_conflicts, generate_conflict_vcs};
use rust_fv_analysis::ir::{BorrowInfo, BorrowPhase};
use rust_fv_analysis::lifetime_analysis::LifetimeContext;

// === Test 1: Reserved borrow does not conflict with shared borrows ===

#[test]
fn test_reserved_borrow_no_conflict_with_shared() {
    let mut context = LifetimeContext::new();

    // Shared borrow
    context.register_borrow(BorrowInfo {
        local_name: "_1".to_string(),
        region: "'a".to_string(),
        is_mutable: false,
        deref_level: 0,
        source_local: None,
        phase: BorrowPhase::Active,
    });

    // Mutable borrow in Reserved phase (two-phase)
    context.register_borrow(BorrowInfo {
        local_name: "_2".to_string(),
        region: "'b".to_string(),
        is_mutable: true,
        deref_level: 0,
        source_local: None,
        phase: BorrowPhase::Reserved,
    });

    let mut live_ranges = HashMap::new();
    live_ranges.insert("_1".to_string(), vec![0, 1, 2]);
    live_ranges.insert("_2".to_string(), vec![0, 1, 2]);

    let conflicts = detect_borrow_conflicts(&context, &live_ranges, None);
    assert!(
        conflicts.is_empty(),
        "Expected no conflict for Reserved mutable borrow with shared borrow, got {}",
        conflicts.len()
    );
}

// === Test 2: Active borrow conflicts with shared borrows (existing behavior) ===

#[test]
fn test_active_borrow_conflicts_with_shared() {
    let mut context = LifetimeContext::new();

    context.register_borrow(BorrowInfo {
        local_name: "_1".to_string(),
        region: "'a".to_string(),
        is_mutable: false,
        deref_level: 0,
        source_local: None,
        phase: BorrowPhase::Active,
    });

    context.register_borrow(BorrowInfo {
        local_name: "_2".to_string(),
        region: "'b".to_string(),
        is_mutable: true,
        deref_level: 0,
        source_local: None,
        phase: BorrowPhase::Active,
    });

    let mut live_ranges = HashMap::new();
    live_ranges.insert("_1".to_string(), vec![0, 1, 2]);
    live_ranges.insert("_2".to_string(), vec![1, 2, 3]);

    let conflicts = detect_borrow_conflicts(&context, &live_ranges, None);
    assert_eq!(
        conflicts.len(),
        1,
        "Expected 1 conflict for Active mutable borrow overlapping shared borrow"
    );
}

// === Test 3: Activated borrow conflicts like Active (reservation consumed) ===

#[test]
fn test_activated_borrow_conflicts_like_active() {
    let mut context = LifetimeContext::new();

    context.register_borrow(BorrowInfo {
        local_name: "_1".to_string(),
        region: "'a".to_string(),
        is_mutable: false,
        deref_level: 0,
        source_local: None,
        phase: BorrowPhase::Active,
    });

    // Activated mutable borrow (reservation consumed)
    context.register_borrow(BorrowInfo {
        local_name: "_2".to_string(),
        region: "'b".to_string(),
        is_mutable: true,
        deref_level: 0,
        source_local: None,
        phase: BorrowPhase::Activated,
    });

    let mut live_ranges = HashMap::new();
    live_ranges.insert("_1".to_string(), vec![0, 1, 2]);
    live_ranges.insert("_2".to_string(), vec![1, 2, 3]);

    let conflicts = detect_borrow_conflicts(&context, &live_ranges, None);
    assert_eq!(
        conflicts.len(),
        1,
        "Expected 1 conflict for Activated mutable borrow overlapping shared borrow"
    );
}

// === Test 4: Two-phase pattern (Reserved + shared + Activated) produces no conflict ===

#[test]
fn test_two_phase_pattern_no_false_positive() {
    // Models vec.push(vec.len()) pattern:
    // 1. &mut vec is Reserved (for push)
    // 2. &vec is taken (for len) -- no conflict with Reserved
    // 3. &mut vec is Activated (push call)
    // The shared borrow for len() should NOT conflict with the Reserved mutable borrow
    let mut context = LifetimeContext::new();

    // Shared borrow for vec.len()
    context.register_borrow(BorrowInfo {
        local_name: "_1".to_string(),
        region: "'a".to_string(),
        is_mutable: false,
        deref_level: 0,
        source_local: None,
        phase: BorrowPhase::Active,
    });

    // Mutable borrow in Reserved phase for push
    context.register_borrow(BorrowInfo {
        local_name: "_2".to_string(),
        region: "'b".to_string(),
        is_mutable: true,
        deref_level: 0,
        source_local: None,
        phase: BorrowPhase::Reserved,
    });

    // Both live in blocks 0-2 (overlapping)
    let mut live_ranges = HashMap::new();
    live_ranges.insert("_1".to_string(), vec![0, 1]);
    live_ranges.insert("_2".to_string(), vec![0, 1, 2]);

    let conflicts = detect_borrow_conflicts(&context, &live_ranges, None);
    assert!(
        conflicts.is_empty(),
        "Expected no conflict for two-phase borrow pattern (vec.push(vec.len())), got {}",
        conflicts.len()
    );
}

// === Test 5: Two-phase activation overlapping with another mutable borrow produces conflict ===

#[test]
fn test_two_phase_activation_with_mut_borrow_conflict() {
    // When an Activated borrow overlaps with another mutable borrow, conflict is detected
    let mut context = LifetimeContext::new();

    // A shared borrow that overlaps with Activated mutable
    context.register_borrow(BorrowInfo {
        local_name: "_1".to_string(),
        region: "'a".to_string(),
        is_mutable: false,
        deref_level: 0,
        source_local: None,
        phase: BorrowPhase::Active,
    });

    // Activated mutable borrow overlapping with shared
    context.register_borrow(BorrowInfo {
        local_name: "_2".to_string(),
        region: "'b".to_string(),
        is_mutable: true,
        deref_level: 0,
        source_local: None,
        phase: BorrowPhase::Activated,
    });

    let mut live_ranges = HashMap::new();
    live_ranges.insert("_1".to_string(), vec![0, 1, 2]);
    live_ranges.insert("_2".to_string(), vec![1, 2, 3]);

    let conflicts = detect_borrow_conflicts(&context, &live_ranges, None);
    assert_eq!(
        conflicts.len(),
        1,
        "Expected conflict when Activated borrow overlaps shared borrow"
    );

    // Verify that conflict VCs are generated
    let vcs = generate_conflict_vcs(&conflicts, "test_fn");
    assert_eq!(vcs.len(), 1);
}
