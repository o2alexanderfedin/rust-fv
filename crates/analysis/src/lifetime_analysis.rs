/// Lifetime analysis for borrow checking verification.
///
/// This module implements lifetime parameter extraction, outlives constraint resolution,
/// reborrow chain detection, and live range computation for NLL-based lifetime reasoning.
use std::collections::HashMap;

use crate::ir::{BorrowInfo, Function, LifetimeParam, OutlivesConstraint, ReborrowChain};

/// Context for lifetime analysis within a function.
///
/// Stores all lifetime parameters, outlives constraints, borrow information,
/// and reborrow chains for a single function.
#[derive(Debug, Clone)]
pub struct LifetimeContext {
    /// Lifetime name -> param info
    lifetimes: HashMap<String, LifetimeParam>,
    /// All outlives constraints
    outlives: Vec<OutlivesConstraint>,
    /// Local name -> borrow info
    borrow_map: HashMap<String, BorrowInfo>,
    /// All reborrow chains
    reborrow_chains: Vec<ReborrowChain>,
}

impl LifetimeContext {
    /// Create a new empty lifetime context.
    pub fn new() -> Self {
        Self {
            lifetimes: HashMap::new(),
            outlives: Vec::new(),
            borrow_map: HashMap::new(),
            reborrow_chains: Vec::new(),
        }
    }

    /// Add a lifetime parameter to the context.
    pub fn add_lifetime(&mut self, param: LifetimeParam) {
        self.lifetimes.insert(param.name.clone(), param);
    }

    /// Add an outlives constraint to the context.
    pub fn add_outlives(&mut self, constraint: OutlivesConstraint) {
        self.outlives.push(constraint);
    }

    /// Register a borrow in the context.
    pub fn register_borrow(&mut self, info: BorrowInfo) {
        self.borrow_map.insert(info.local_name.clone(), info);
    }

    /// Get borrow information for a local.
    pub fn get_borrow(&self, local_name: &str) -> Option<&BorrowInfo> {
        self.borrow_map.get(local_name)
    }

    /// Get lifetime parameter by name.
    pub fn get_lifetime(&self, name: &str) -> Option<&LifetimeParam> {
        self.lifetimes.get(name)
    }

    /// Get all outlives constraints.
    pub fn outlives_constraints(&self) -> &[OutlivesConstraint] {
        &self.outlives
    }

    /// Get all borrows associated with a specific region.
    pub fn borrows_in_region(&self, region: &str) -> Vec<&BorrowInfo> {
        self.borrow_map
            .values()
            .filter(|b| b.region == region)
            .collect()
    }

    /// Get all mutable borrows.
    pub fn mutable_borrows(&self) -> Vec<&BorrowInfo> {
        self.borrow_map.values().filter(|b| b.is_mutable).collect()
    }

    /// Get all shared borrows.
    pub fn shared_borrows(&self) -> Vec<&BorrowInfo> {
        self.borrow_map.values().filter(|b| !b.is_mutable).collect()
    }

    /// Get all reborrow chains.
    pub fn reborrow_chains(&self) -> &[ReborrowChain] {
        &self.reborrow_chains
    }
}

impl Default for LifetimeContext {
    fn default() -> Self {
        Self::new()
    }
}

/// Extract lifetime parameters from a function.
///
/// For now, returns the function's lifetime_params field directly.
/// In future MIR integration, this will extract from HIR/MIR.
pub fn extract_lifetime_params(func: &Function) -> Vec<LifetimeParam> {
    func.lifetime_params.clone()
}

/// Resolve outlives constraints with transitive closure.
///
/// Given constraints like 'a: 'b and 'b: 'c, adds the transitive constraint 'a: 'c.
/// Iterates until no new constraints are added (fixpoint).
pub fn resolve_outlives(func: &Function) -> Vec<OutlivesConstraint> {
    let mut constraints = func.outlives_constraints.clone();
    let mut changed = true;

    while changed {
        let current_len = constraints.len();

        // Find transitive constraints: if 'a: 'b and 'b: 'c, then 'a: 'c
        let mut new_constraints = Vec::new();
        for c1 in &constraints {
            for c2 in &constraints {
                if c1.shorter == c2.longer {
                    let transitive = OutlivesConstraint {
                        longer: c1.longer.clone(),
                        shorter: c2.shorter.clone(),
                    };
                    // Check if this constraint already exists
                    if !constraints.contains(&transitive) && !new_constraints.contains(&transitive)
                    {
                        new_constraints.push(transitive);
                    }
                }
            }
        }

        constraints.extend(new_constraints);
        changed = constraints.len() > current_len;
    }

    constraints
}

/// Detect reborrow chains from borrow information.
///
/// Scans borrow_info for entries with source_local set and groups them into chains.
/// Returns one ReborrowChain per chain root.
pub fn detect_reborrow_chains(func: &Function) -> Vec<ReborrowChain> {
    let mut chains = Vec::new();
    let mut processed = std::collections::HashSet::new();

    // Build a map of source -> reborrows
    let mut reborrow_map: HashMap<String, Vec<String>> = HashMap::new();
    for borrow in &func.borrow_info {
        if let Some(ref source) = borrow.source_local {
            reborrow_map
                .entry(source.clone())
                .or_default()
                .push(borrow.local_name.clone());
        }
    }

    // For each borrow, if it has reborrows, trace the full chain
    for borrow in &func.borrow_info {
        if reborrow_map.contains_key(&borrow.local_name) && !processed.contains(&borrow.local_name)
        {
            // This is a chain root (has reborrows and hasn't been processed)
            let mut chain = Vec::new();
            let mut current = borrow.local_name.clone();

            // Trace the chain
            while let Some(reborrows) = reborrow_map.get(&current) {
                chain.extend(reborrows.clone());
                processed.insert(current.clone());
                // For simplicity, follow the first reborrow if multiple exist
                current = reborrows[0].clone();
            }

            if !chain.is_empty() {
                chains.push(ReborrowChain {
                    original: borrow.local_name.clone(),
                    reborrows: chain,
                });
            }
        }
    }

    chains
}

/// Build a complete lifetime context from a function.
///
/// Orchestrates extraction, resolution, and detection of all lifetime information.
pub fn build_lifetime_context(func: &Function) -> LifetimeContext {
    let mut context = LifetimeContext::new();

    // Extract and add lifetime parameters
    for param in extract_lifetime_params(func) {
        context.add_lifetime(param);
    }

    // Resolve and add outlives constraints
    for constraint in resolve_outlives(func) {
        context.add_outlives(constraint);
    }

    // Register all borrows
    for borrow in &func.borrow_info {
        context.register_borrow(borrow.clone());
    }

    // Detect and store reborrow chains
    context.reborrow_chains = detect_reborrow_chains(func);

    context
}

/// Check if a borrow's region is 'static or outlives 'static.
///
/// Returns true if the borrow is valid for the entire program lifetime.
pub fn check_static_validity(borrow: &BorrowInfo, context: &LifetimeContext) -> bool {
    // Direct 'static check
    if borrow.region == "'static" {
        return true;
    }

    // Check if region outlives 'static via constraints
    for constraint in &context.outlives {
        if constraint.longer == borrow.region && constraint.shorter == "'static" {
            return true;
        }
    }

    false
}

/// Compute live ranges for all borrows in the function.
///
/// Returns a map from borrow local name to the set of basic block indices where it's live.
///
/// This is a simplified conservative approximation:
/// - A borrow is live from its creation block through all blocks that reference it
/// - The driver will provide precise MIR-based live ranges in future integration
pub fn compute_live_ranges(func: &Function) -> HashMap<String, Vec<usize>> {
    let mut live_ranges: HashMap<String, Vec<usize>> = HashMap::new();

    for borrow in &func.borrow_info {
        // Simple heuristic: assume borrow is live from block 0 to the end
        // In a real implementation, we'd trace MIR statements to find actual usage
        let range: Vec<usize> = (0..func.basic_blocks.len()).collect();
        live_ranges.insert(borrow.local_name.clone(), range);
    }

    live_ranges
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{BasicBlock, Contracts, Local, Terminator, Ty};

    // ====== LifetimeContext tests ======

    #[test]
    fn test_lifetime_context_new() {
        let context = LifetimeContext::new();
        assert_eq!(context.lifetimes.len(), 0);
        assert_eq!(context.outlives.len(), 0);
        assert_eq!(context.borrow_map.len(), 0);
        assert_eq!(context.reborrow_chains.len(), 0);
    }

    #[test]
    fn test_lifetime_context_add_lifetime() {
        let mut context = LifetimeContext::new();
        let lifetime = LifetimeParam {
            name: "'a".to_string(),
            is_static: false,
        };
        context.add_lifetime(lifetime.clone());
        assert_eq!(context.get_lifetime("'a"), Some(&lifetime));
    }

    #[test]
    fn test_lifetime_context_add_outlives() {
        let mut context = LifetimeContext::new();
        let constraint = OutlivesConstraint {
            longer: "'a".to_string(),
            shorter: "'b".to_string(),
        };
        context.add_outlives(constraint.clone());
        assert_eq!(context.outlives_constraints().len(), 1);
        assert_eq!(context.outlives_constraints()[0], constraint);
    }

    #[test]
    fn test_lifetime_context_register_borrow() {
        let mut context = LifetimeContext::new();
        let borrow = BorrowInfo {
            local_name: "_1".to_string(),
            region: "'a".to_string(),
            is_mutable: false,
            deref_level: 0,
            source_local: None,
        };
        context.register_borrow(borrow.clone());
        assert_eq!(context.get_borrow("_1"), Some(&borrow));
    }

    #[test]
    fn test_lifetime_context_borrows_in_region() {
        let mut context = LifetimeContext::new();
        let borrow1 = BorrowInfo {
            local_name: "_1".to_string(),
            region: "'a".to_string(),
            is_mutable: false,
            deref_level: 0,
            source_local: None,
        };
        let borrow2 = BorrowInfo {
            local_name: "_2".to_string(),
            region: "'a".to_string(),
            is_mutable: true,
            deref_level: 0,
            source_local: None,
        };
        let borrow3 = BorrowInfo {
            local_name: "_3".to_string(),
            region: "'b".to_string(),
            is_mutable: false,
            deref_level: 0,
            source_local: None,
        };
        context.register_borrow(borrow1);
        context.register_borrow(borrow2);
        context.register_borrow(borrow3);

        let in_a = context.borrows_in_region("'a");
        assert_eq!(in_a.len(), 2);

        let in_b = context.borrows_in_region("'b");
        assert_eq!(in_b.len(), 1);
    }

    #[test]
    fn test_lifetime_context_mutable_borrows() {
        let mut context = LifetimeContext::new();
        let borrow1 = BorrowInfo {
            local_name: "_1".to_string(),
            region: "'a".to_string(),
            is_mutable: false,
            deref_level: 0,
            source_local: None,
        };
        let borrow2 = BorrowInfo {
            local_name: "_2".to_string(),
            region: "'a".to_string(),
            is_mutable: true,
            deref_level: 0,
            source_local: None,
        };
        context.register_borrow(borrow1);
        context.register_borrow(borrow2);

        let mut_borrows = context.mutable_borrows();
        assert_eq!(mut_borrows.len(), 1);
        assert_eq!(mut_borrows[0].local_name, "_2");
    }

    #[test]
    fn test_lifetime_context_shared_borrows() {
        let mut context = LifetimeContext::new();
        let borrow1 = BorrowInfo {
            local_name: "_1".to_string(),
            region: "'a".to_string(),
            is_mutable: false,
            deref_level: 0,
            source_local: None,
        };
        let borrow2 = BorrowInfo {
            local_name: "_2".to_string(),
            region: "'a".to_string(),
            is_mutable: true,
            deref_level: 0,
            source_local: None,
        };
        context.register_borrow(borrow1);
        context.register_borrow(borrow2);

        let shared_borrows = context.shared_borrows();
        assert_eq!(shared_borrows.len(), 1);
        assert_eq!(shared_borrows[0].local_name, "_1");
    }

    // ====== extract_lifetime_params tests ======

    #[test]
    fn test_extract_lifetime_params() {
        let func = Function {
            name: "test_fn".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            loops: vec![],
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![LifetimeParam {
                name: "'a".to_string(),
                is_static: false,
            }],
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
        };
        let params = extract_lifetime_params(&func);
        assert_eq!(params.len(), 1);
        assert_eq!(params[0].name, "'a");
    }

    #[test]
    fn test_extract_lifetime_params_empty() {
        let func = Function {
            name: "test_fn".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![],
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
        };
        let params = extract_lifetime_params(&func);
        assert_eq!(params.len(), 0);
    }

    // ====== resolve_outlives tests ======

    #[test]
    fn test_resolve_outlives_simple() {
        let func = Function {
            name: "test_fn".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            loops: vec![],
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![OutlivesConstraint {
                longer: "'a".to_string(),
                shorter: "'b".to_string(),
            }],
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
        };
        let resolved = resolve_outlives(&func);
        assert_eq!(resolved.len(), 1);
        assert_eq!(resolved[0].longer, "'a");
        assert_eq!(resolved[0].shorter, "'b");
    }

    #[test]
    fn test_resolve_outlives_transitive() {
        let func = Function {
            name: "test_fn".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            loops: vec![],
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![
                OutlivesConstraint {
                    longer: "'a".to_string(),
                    shorter: "'b".to_string(),
                },
                OutlivesConstraint {
                    longer: "'b".to_string(),
                    shorter: "'c".to_string(),
                },
            ],
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
        };
        let resolved = resolve_outlives(&func);
        // Should have original 2 plus transitive 'a: 'c
        assert_eq!(resolved.len(), 3);
        assert!(resolved.contains(&OutlivesConstraint {
            longer: "'a".to_string(),
            shorter: "'c".to_string(),
        }));
    }

    #[test]
    fn test_resolve_outlives_no_duplicates() {
        let func = Function {
            name: "test_fn".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            loops: vec![],
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![
                OutlivesConstraint {
                    longer: "'a".to_string(),
                    shorter: "'b".to_string(),
                },
                OutlivesConstraint {
                    longer: "'a".to_string(),
                    shorter: "'b".to_string(),
                }, // duplicate
            ],
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
        };
        let resolved = resolve_outlives(&func);
        // Duplicates should be preserved as-is (no deduplication in this implementation)
        // The transitive closure won't add more duplicates
        assert_eq!(resolved.len(), 2);
    }

    // ====== detect_reborrow_chains tests ======

    #[test]
    fn test_detect_reborrow_chains_none() {
        let func = Function {
            name: "test_fn".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            loops: vec![],
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
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
        };
        let chains = detect_reborrow_chains(&func);
        assert_eq!(chains.len(), 0);
    }

    #[test]
    fn test_detect_reborrow_chains_single() {
        let func = Function {
            name: "test_fn".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            loops: vec![],
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![
                BorrowInfo {
                    local_name: "_1".to_string(),
                    region: "'a".to_string(),
                    is_mutable: true,
                    deref_level: 0,
                    source_local: None,
                },
                BorrowInfo {
                    local_name: "_2".to_string(),
                    region: "'b".to_string(),
                    is_mutable: true,
                    deref_level: 1,
                    source_local: Some("_1".to_string()),
                },
            ],
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
        };
        let chains = detect_reborrow_chains(&func);
        assert_eq!(chains.len(), 1);
        assert_eq!(chains[0].original, "_1");
        assert_eq!(chains[0].reborrows, vec!["_2"]);
    }

    #[test]
    fn test_detect_reborrow_chains_deep() {
        let func = Function {
            name: "test_fn".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            loops: vec![],
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![
                BorrowInfo {
                    local_name: "_1".to_string(),
                    region: "'a".to_string(),
                    is_mutable: true,
                    deref_level: 0,
                    source_local: None,
                },
                BorrowInfo {
                    local_name: "_2".to_string(),
                    region: "'b".to_string(),
                    is_mutable: true,
                    deref_level: 1,
                    source_local: Some("_1".to_string()),
                },
                BorrowInfo {
                    local_name: "_3".to_string(),
                    region: "'c".to_string(),
                    is_mutable: true,
                    deref_level: 2,
                    source_local: Some("_2".to_string()),
                },
            ],
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
        };
        let chains = detect_reborrow_chains(&func);
        assert_eq!(chains.len(), 1);
        assert_eq!(chains[0].original, "_1");
        assert_eq!(chains[0].reborrows, vec!["_2", "_3"]);
    }

    // ====== build_lifetime_context tests ======

    #[test]
    fn test_build_lifetime_context() {
        let func = Function {
            name: "test_fn".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            loops: vec![],
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![LifetimeParam {
                name: "'a".to_string(),
                is_static: false,
            }],
            outlives_constraints: vec![OutlivesConstraint {
                longer: "'a".to_string(),
                shorter: "'b".to_string(),
            }],
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
        };
        let context = build_lifetime_context(&func);
        assert_eq!(context.lifetimes.len(), 1);
        assert_eq!(context.outlives.len(), 1);
        assert_eq!(context.borrow_map.len(), 1);
    }

    // ====== check_static_validity tests ======

    #[test]
    fn test_check_static_validity_is_static() {
        let borrow = BorrowInfo {
            local_name: "_1".to_string(),
            region: "'static".to_string(),
            is_mutable: false,
            deref_level: 0,
            source_local: None,
        };
        let context = LifetimeContext::new();
        assert!(check_static_validity(&borrow, &context));
    }

    #[test]
    fn test_check_static_validity_outlives_static() {
        let borrow = BorrowInfo {
            local_name: "_1".to_string(),
            region: "'a".to_string(),
            is_mutable: false,
            deref_level: 0,
            source_local: None,
        };
        let mut context = LifetimeContext::new();
        context.add_outlives(OutlivesConstraint {
            longer: "'a".to_string(),
            shorter: "'static".to_string(),
        });
        assert!(check_static_validity(&borrow, &context));
    }

    #[test]
    fn test_check_static_validity_not_static() {
        let borrow = BorrowInfo {
            local_name: "_1".to_string(),
            region: "'a".to_string(),
            is_mutable: false,
            deref_level: 0,
            source_local: None,
        };
        let context = LifetimeContext::new();
        assert!(!check_static_validity(&borrow, &context));
    }

    // ====== compute_live_ranges tests ======

    #[test]
    fn test_compute_live_ranges_basic() {
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
                    terminator: Terminator::Return,
                },
            ],
            contracts: Contracts::default(),
            loops: vec![],
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
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
        };
        let ranges = compute_live_ranges(&func);
        assert_eq!(ranges.get("_1").unwrap(), &vec![0, 1]);
    }
}
