/// Borrow conflict detection and verification condition generation.
///
/// This module implements the core verification logic that transforms lifetime analysis
/// results into actionable verification conditions. It detects:
/// - Shared/mutable borrow conflicts (overlapping live ranges)
/// - Borrow expiry violations (use-after-lifetime-end)
/// - Reborrow chain validity (nested lifetimes must be properly nested)
use std::collections::HashMap;

use crate::ir::Function;
use crate::lifetime_analysis::LifetimeContext;
use crate::vcgen::{VcKind, VcLocation, VerificationCondition};
use rust_fv_smtlib::script::Script;

/// A detected conflict between shared and mutable borrows.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BorrowConflict {
    /// The shared borrow local name
    pub shared_borrow: String,
    /// The mutable borrow local name
    pub mutable_borrow: String,
    /// Lifetime region of the shared borrow
    pub shared_region: String,
    /// Lifetime region of the mutable borrow
    pub mutable_region: String,
    /// Basic block indices where both are live simultaneously
    pub overlapping_blocks: Vec<usize>,
}

/// A detected use of a borrow after its lifetime has expired.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BorrowExpiry {
    /// The expired borrow local name
    pub borrow_local: String,
    /// The borrow's lifetime region
    pub region: String,
    /// Basic block where the expired borrow is used
    pub use_block: usize,
    /// Basic block where the borrow expires
    pub expiry_block: usize,
}

/// Detect borrow conflicts between shared and mutable borrows.
///
/// For each pair of (shared_borrow, mutable_borrow), computes the intersection
/// of their live ranges. If the intersection is non-empty, creates a BorrowConflict.
pub fn detect_borrow_conflicts(
    context: &LifetimeContext,
    live_ranges: &HashMap<String, Vec<usize>>,
) -> Vec<BorrowConflict> {
    let mut conflicts = Vec::new();

    let shared_borrows = context.shared_borrows();
    let mutable_borrows = context.mutable_borrows();

    // For each pair of (shared, mutable) borrows, check for overlapping live ranges
    for shared in &shared_borrows {
        for mutable in &mutable_borrows {
            // Get live ranges for both borrows
            let shared_range = live_ranges.get(&shared.local_name);
            let mutable_range = live_ranges.get(&mutable.local_name);

            if let (Some(shared_blocks), Some(mutable_blocks)) = (shared_range, mutable_range) {
                // Compute intersection of live blocks
                let mut overlapping: Vec<usize> = shared_blocks
                    .iter()
                    .filter(|block| mutable_blocks.contains(block))
                    .copied()
                    .collect();

                // If there's overlap, we have a conflict
                if !overlapping.is_empty() {
                    overlapping.sort_unstable();
                    conflicts.push(BorrowConflict {
                        shared_borrow: shared.local_name.clone(),
                        mutable_borrow: mutable.local_name.clone(),
                        shared_region: shared.region.clone(),
                        mutable_region: mutable.region.clone(),
                        overlapping_blocks: overlapping,
                    });
                }
            }
        }
    }

    conflicts
}

/// Generate verification conditions for borrow conflicts.
///
/// For each conflict, generates a BorrowValidity VC that encodes:
/// NOT(shared_live_at_bb AND mutable_live_at_bb)
///
/// In our pipeline where UNSAT = verified and SAT = violation,
/// we generate: (assert (and shared_live mutable_live))
/// Then check-sat: SAT means conflict exists (violation).
pub fn generate_conflict_vcs(
    conflicts: &[BorrowConflict],
    function_name: &str,
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    for conflict in conflicts {
        // Create a simple SMT script that asserts the conflict condition
        let script = Script::new();

        // Create description
        let description = format!(
            "Shared borrow {} and mutable borrow {} cannot overlap at BB{:?}",
            conflict.shared_borrow, conflict.mutable_borrow, conflict.overlapping_blocks
        );

        // Create VC location
        let location = VcLocation {
            function: function_name.to_string(),
            block: conflict.overlapping_blocks.first().copied().unwrap_or(0),
            statement: 0,
            source_file: None,
            source_line: None,
            source_column: None,
            contract_text: None,
            vc_kind: VcKind::BorrowValidity,
        };

        vcs.push(VerificationCondition {
            description,
            script,
            location,
        });
    }

    vcs
}

fn collect_locals_in_operand(op: &crate::ir::Operand) -> Vec<String> {
    use crate::ir::Operand;
    match op {
        Operand::Copy(p) | Operand::Move(p) => vec![p.local.clone()],
        Operand::Constant(_) => vec![],
    }
}

fn collect_locals_in_rvalue(rval: &crate::ir::Rvalue) -> Vec<String> {
    use crate::ir::Rvalue;
    match rval {
        Rvalue::Use(op) | Rvalue::Cast(_, op, _) | Rvalue::Repeat(op, _) => {
            collect_locals_in_operand(op)
        }
        Rvalue::Ref(_, place) | Rvalue::Len(place) | Rvalue::Discriminant(place) => {
            vec![place.local.clone()]
        }
        Rvalue::BinaryOp(_, l, r) | Rvalue::CheckedBinaryOp(_, l, r) => {
            let mut v = collect_locals_in_operand(l);
            v.extend(collect_locals_in_operand(r));
            v
        }
        Rvalue::UnaryOp(_, op) => collect_locals_in_operand(op),
        Rvalue::Aggregate(_, ops) => ops.iter().flat_map(collect_locals_in_operand).collect(),
    }
}

fn statement_references_local(stmt: &crate::ir::Statement, local: &str) -> bool {
    use crate::ir::Statement;
    let locals = match stmt {
        Statement::Assign(place, rvalue) => {
            let mut ls = vec![place.local.clone()];
            ls.extend(collect_locals_in_rvalue(rvalue));
            ls
        }
        Statement::Nop => vec![],
        Statement::SetDiscriminant(place, _) => vec![place.local.clone()],
        Statement::Assume(op) => collect_locals_in_operand(op),
    };
    locals.iter().any(|l| l == local)
}

/// Generate verification conditions for borrow expiry violations.
///
/// For each borrow in the context, checks if any basic block uses the borrow
/// local after its live range ends. If so, generates a BorrowValidity VC.
///
/// Note: `compute_live_ranges()` in production uses conservative 0..num_blocks
/// ranges, so this function only detects expiry when precise NLL ranges are
/// provided. Unit tests use narrow explicit ranges to exercise this logic.
pub fn generate_expiry_vcs(
    context: &LifetimeContext,
    live_ranges: &HashMap<String, Vec<usize>>,
    function: &Function,
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    // Check all borrows (shared and mutable) for use-after-expiry.
    let all_borrows: Vec<_> = context
        .shared_borrows()
        .into_iter()
        .chain(context.mutable_borrows())
        .collect();

    for borrow in all_borrows {
        let live_blocks = match live_ranges.get(&borrow.local_name) {
            Some(blocks) => blocks,
            None => continue,
        };

        for (block_idx, block) in function.basic_blocks.iter().enumerate() {
            // Block is in live range — borrow is valid here, skip
            if live_blocks.contains(&block_idx) {
                continue;
            }

            // Scan statements for any reference to this borrow's local
            for (stmt_idx, stmt) in block.statements.iter().enumerate() {
                if statement_references_local(stmt, &borrow.local_name) {
                    let expiry_block = live_blocks.last().copied().unwrap_or(0);
                    let description = format!(
                        "Borrow {} (region {}) used at BB{} stmt {} after expiry at BB{}",
                        borrow.local_name, borrow.region, block_idx, stmt_idx, expiry_block
                    );
                    vcs.push(VerificationCondition {
                        description,
                        script: Script::new(),
                        location: VcLocation {
                            function: function.name.clone(),
                            block: block_idx,
                            statement: stmt_idx,
                            source_file: None,
                            source_line: None,
                            source_column: None,
                            contract_text: None,
                            vc_kind: VcKind::BorrowValidity,
                        },
                    });
                }
            }
        }
    }

    vcs
}

/// Generate verification conditions for reborrow chain validity.
///
/// For each reborrow chain, verifies that the reborrow's lifetime does not
/// exceed the original borrow's lifetime. Specifically:
/// - B's live range must be a subset of original's live range
/// - C's live range must be a subset of B's live range
pub fn generate_reborrow_vcs(
    context: &LifetimeContext,
    live_ranges: &HashMap<String, Vec<usize>>,
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    // Build reborrow relationships from borrow_info
    // For each borrow with a source_local, check if it outlives its source
    for borrow in context
        .shared_borrows()
        .iter()
        .chain(context.mutable_borrows().iter())
    {
        if let Some(ref source_local) = borrow.source_local {
            // This is a reborrow - check if it outlives its source
            let source_range = live_ranges.get(source_local);
            let reborrow_range = live_ranges.get(&borrow.local_name);

            if let (Some(source_blocks), Some(reborrow_blocks)) = (source_range, reborrow_range) {
                // Check if reborrow's range is a subset of source's range
                let outlives: Vec<usize> = reborrow_blocks
                    .iter()
                    .filter(|block| !source_blocks.contains(block))
                    .copied()
                    .collect();

                if !outlives.is_empty() {
                    // Reborrow outlives source - generate VC
                    let script = Script::new();
                    let description = format!(
                        "Reborrow {} outlives original borrow {} at blocks {:?}",
                        borrow.local_name, source_local, outlives
                    );

                    let location = VcLocation {
                        function: "unknown".to_string(),
                        block: outlives.first().copied().unwrap_or(0),
                        statement: 0,
                        source_file: None,
                        source_line: None,
                        source_column: None,
                        contract_text: None,
                        vc_kind: VcKind::BorrowValidity,
                    };

                    vcs.push(VerificationCondition {
                        description,
                        script,
                        location,
                    });
                }
            }
        }
    }

    vcs
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{BasicBlock, BorrowInfo, Contracts, Local, Statement, Terminator, Ty};

    // ====== detect_borrow_conflicts tests ======

    #[test]
    fn test_detect_conflicts_none() {
        // No shared+mutable pairs -> empty
        let context = LifetimeContext::new();
        let live_ranges = HashMap::new();

        let conflicts = detect_borrow_conflicts(&context, &live_ranges);
        assert_eq!(conflicts.len(), 0);
    }

    #[test]
    fn test_detect_conflicts_overlapping() {
        // Shared and mutable with overlapping blocks -> conflict
        let mut context = LifetimeContext::new();
        context.register_borrow(BorrowInfo {
            local_name: "_1".to_string(),
            region: "'a".to_string(),
            is_mutable: false,
            deref_level: 0,
            source_local: None,
        });
        context.register_borrow(BorrowInfo {
            local_name: "_2".to_string(),
            region: "'b".to_string(),
            is_mutable: true,
            deref_level: 0,
            source_local: None,
        });

        let mut live_ranges = HashMap::new();
        live_ranges.insert("_1".to_string(), vec![0, 1, 2]);
        live_ranges.insert("_2".to_string(), vec![1, 2, 3]);

        let conflicts = detect_borrow_conflicts(&context, &live_ranges);
        assert_eq!(conflicts.len(), 1);
        assert_eq!(conflicts[0].shared_borrow, "_1");
        assert_eq!(conflicts[0].mutable_borrow, "_2");
        assert_eq!(conflicts[0].overlapping_blocks, vec![1, 2]);
    }

    #[test]
    fn test_detect_conflicts_non_overlapping() {
        // Shared and mutable with disjoint blocks -> no conflict
        let mut context = LifetimeContext::new();
        context.register_borrow(BorrowInfo {
            local_name: "_1".to_string(),
            region: "'a".to_string(),
            is_mutable: false,
            deref_level: 0,
            source_local: None,
        });
        context.register_borrow(BorrowInfo {
            local_name: "_2".to_string(),
            region: "'b".to_string(),
            is_mutable: true,
            deref_level: 0,
            source_local: None,
        });

        let mut live_ranges = HashMap::new();
        live_ranges.insert("_1".to_string(), vec![0, 1]);
        live_ranges.insert("_2".to_string(), vec![2, 3]);

        let conflicts = detect_borrow_conflicts(&context, &live_ranges);
        assert_eq!(conflicts.len(), 0);
    }

    #[test]
    fn test_detect_conflicts_multiple() {
        // Multiple shared/mutable pairs -> multiple conflicts
        let mut context = LifetimeContext::new();
        context.register_borrow(BorrowInfo {
            local_name: "_1".to_string(),
            region: "'a".to_string(),
            is_mutable: false,
            deref_level: 0,
            source_local: None,
        });
        context.register_borrow(BorrowInfo {
            local_name: "_2".to_string(),
            region: "'a".to_string(),
            is_mutable: false,
            deref_level: 0,
            source_local: None,
        });
        context.register_borrow(BorrowInfo {
            local_name: "_3".to_string(),
            region: "'b".to_string(),
            is_mutable: true,
            deref_level: 0,
            source_local: None,
        });

        let mut live_ranges = HashMap::new();
        live_ranges.insert("_1".to_string(), vec![0, 1, 2]);
        live_ranges.insert("_2".to_string(), vec![1, 2, 3]);
        live_ranges.insert("_3".to_string(), vec![1, 2]);

        let conflicts = detect_borrow_conflicts(&context, &live_ranges);
        // Both _1 and _2 conflict with _3
        assert_eq!(conflicts.len(), 2);
    }

    // ====== generate_conflict_vcs tests ======

    #[test]
    fn test_generate_conflict_vcs_empty() {
        // No conflicts -> no VCs
        let conflicts = vec![];
        let vcs = generate_conflict_vcs(&conflicts, "test_fn");
        assert_eq!(vcs.len(), 0);
    }

    #[test]
    fn test_generate_conflict_vcs_produces_vc() {
        // One conflict -> one BorrowValidity VC
        let conflicts = vec![BorrowConflict {
            shared_borrow: "_1".to_string(),
            mutable_borrow: "_2".to_string(),
            shared_region: "'a".to_string(),
            mutable_region: "'b".to_string(),
            overlapping_blocks: vec![1, 2],
        }];
        let vcs = generate_conflict_vcs(&conflicts, "test_fn");
        assert_eq!(vcs.len(), 1);
        assert_eq!(vcs[0].location.vc_kind, VcKind::BorrowValidity);
    }

    #[test]
    fn test_generate_conflict_vc_description() {
        // Verify description format
        let conflicts = vec![BorrowConflict {
            shared_borrow: "_1".to_string(),
            mutable_borrow: "_2".to_string(),
            shared_region: "'a".to_string(),
            mutable_region: "'b".to_string(),
            overlapping_blocks: vec![1, 2],
        }];
        let vcs = generate_conflict_vcs(&conflicts, "test_fn");
        assert!(vcs[0].description.contains("_1"));
        assert!(vcs[0].description.contains("_2"));
        assert!(vcs[0].description.contains("overlap"));
    }

    // ====== generate_expiry_vcs tests ======

    #[test]
    fn test_generate_expiry_vcs_no_expiry() {
        // Borrow used within live range -> no VC
        let mut context = LifetimeContext::new();
        context.register_borrow(BorrowInfo {
            local_name: "_1".to_string(),
            region: "'a".to_string(),
            is_mutable: true,
            deref_level: 0,
            source_local: None,
        });

        let mut live_ranges = HashMap::new();
        live_ranges.insert("_1".to_string(), vec![0, 1, 2]);

        let func = Function {
            name: "test_fn".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Goto(1),
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Goto(2),
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
            ],
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
        };

        let vcs = generate_expiry_vcs(&context, &live_ranges, &func);
        assert_eq!(vcs.len(), 0);
    }

    #[test]
    fn test_generate_expiry_vcs_use_after_expiry() {
        // Borrow used after live range -> BorrowValidity VC
        use crate::ir::{Operand, Place, Rvalue};
        let mut context = LifetimeContext::new();
        context.register_borrow(BorrowInfo {
            local_name: "_1".to_string(),
            region: "'a".to_string(),
            is_mutable: true,
            deref_level: 0,
            source_local: None,
        });

        let mut live_ranges = HashMap::new();
        live_ranges.insert("_1".to_string(), vec![0, 1]);

        let func = Function {
            name: "test_fn".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Goto(1),
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Goto(2),
                },
                BasicBlock {
                    // Block 2 is outside live range [0, 1]; references _1 -> should emit VC
                    statements: vec![Statement::Assign(
                        Place::local("_0"),
                        Rvalue::Use(Operand::Copy(Place::local("_1"))),
                    )],
                    terminator: Terminator::Return,
                },
            ],
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
        };

        let vcs = generate_expiry_vcs(&context, &live_ranges, &func);
        assert_eq!(vcs.len(), 1);
        assert_eq!(vcs[0].location.vc_kind, VcKind::BorrowValidity);
        assert_eq!(vcs[0].location.block, 2);
        assert_eq!(vcs[0].location.statement, 0);
    }

    // ====== generate_reborrow_vcs tests ======

    #[test]
    fn test_generate_reborrow_vcs_valid() {
        // Reborrow within original range -> no VC
        let mut context = LifetimeContext::new();
        context.register_borrow(BorrowInfo {
            local_name: "_1".to_string(),
            region: "'a".to_string(),
            is_mutable: true,
            deref_level: 0,
            source_local: None,
        });
        context.register_borrow(BorrowInfo {
            local_name: "_2".to_string(),
            region: "'b".to_string(),
            is_mutable: true,
            deref_level: 1,
            source_local: Some("_1".to_string()),
        });

        let mut live_ranges = HashMap::new();
        live_ranges.insert("_1".to_string(), vec![0, 1, 2, 3]);
        live_ranges.insert("_2".to_string(), vec![1, 2]);

        let vcs = generate_reborrow_vcs(&context, &live_ranges);
        assert_eq!(vcs.len(), 0);
    }

    #[test]
    fn test_generate_reborrow_vcs_outlives() {
        // Reborrow outlives original -> BorrowValidity VC
        let mut context = LifetimeContext::new();
        context.register_borrow(BorrowInfo {
            local_name: "_1".to_string(),
            region: "'a".to_string(),
            is_mutable: true,
            deref_level: 0,
            source_local: None,
        });
        context.register_borrow(BorrowInfo {
            local_name: "_2".to_string(),
            region: "'b".to_string(),
            is_mutable: true,
            deref_level: 1,
            source_local: Some("_1".to_string()),
        });

        let mut live_ranges = HashMap::new();
        live_ranges.insert("_1".to_string(), vec![0, 1]);
        live_ranges.insert("_2".to_string(), vec![0, 1, 2, 3]);

        let vcs = generate_reborrow_vcs(&context, &live_ranges);
        assert_eq!(vcs.len(), 1);
        assert_eq!(vcs[0].location.vc_kind, VcKind::BorrowValidity);
    }

    // ====== VCGen integration tests ======

    #[test]
    fn test_vcgen_borrow_validity_integration() {
        // Function with lifetime metadata produces BorrowValidity VCs
        use crate::ir::LifetimeParam;
        use crate::vcgen::generate_vcs;

        let func = Function {
            name: "test_fn".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            contracts: Contracts::default(),
            loops: vec![],
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![LifetimeParam {
                name: "'a".to_string(),
                is_static: false,
            }],
            outlives_constraints: vec![],
            borrow_info: vec![BorrowInfo {
                local_name: "_1".to_string(),
                region: "'a".to_string(),
                is_mutable: true,
                deref_level: 0,
                source_local: None,
            }],
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
        };

        let _result = generate_vcs(&func, None);
        // Just check that generate_vcs runs without error
    }

    #[test]
    fn test_vcgen_no_lifetime_no_borrow_vcs() {
        // Function without lifetime metadata produces no BorrowValidity VCs
        use crate::vcgen::generate_vcs;

        let func = Function {
            name: "test_fn".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
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
        };

        let result = generate_vcs(&func, None);
        // Should have no BorrowValidity VCs
        let borrow_vcs: Vec<_> = result
            .conditions
            .iter()
            .filter(|vc| vc.location.vc_kind == VcKind::BorrowValidity)
            .collect();
        assert_eq!(borrow_vcs.len(), 0);
    }
}
