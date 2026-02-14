/// Deadlock detection via lock-order graph cycle detection.
///
/// Uses Tarjan's strongly connected components algorithm (via petgraph)
/// to find potential deadlocks in lock acquisition patterns.
use crate::vcgen::{VcKind, VcLocation, VerificationCondition};
use rust_fv_smtlib::script::Script;
use std::collections::HashMap;

/// Lock identifier.
pub type LockId = usize;

/// Lock-order graph.
///
/// Tracks which locks are acquired while holding other locks.
/// An edge A → B means "lock A was held when lock B was acquired".
#[derive(Debug, Clone)]
pub struct LockOrderGraph {
    adjacency: HashMap<LockId, Vec<LockId>>,
}

impl LockOrderGraph {
    /// Create a new empty lock-order graph.
    pub fn new() -> Self {
        Self {
            adjacency: HashMap::new(),
        }
    }

    /// Add an edge: held_lock was held when acquired_lock was acquired.
    pub fn add_edge(&mut self, held: LockId, acquired: LockId) {
        self.adjacency.entry(held).or_default().push(acquired);
    }

    /// Check if a lock has a self-loop.
    pub fn has_self_loop(&self, lock: LockId) -> bool {
        self.adjacency
            .get(&lock)
            .map(|neighbors| neighbors.contains(&lock))
            .unwrap_or(false)
    }

    /// Get outgoing edges from a lock.
    pub fn edges_from(&self, lock: LockId) -> &[LockId] {
        self.adjacency
            .get(&lock)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    /// Get all nodes in the graph.
    fn all_nodes(&self) -> Vec<LockId> {
        let mut nodes = Vec::new();
        for (&node, neighbors) in &self.adjacency {
            nodes.push(node);
            for &neighbor in neighbors {
                if !nodes.contains(&neighbor) {
                    nodes.push(neighbor);
                }
            }
        }
        nodes.sort_unstable();
        nodes
    }
}

impl Default for LockOrderGraph {
    fn default() -> Self {
        Self::new()
    }
}

/// A detected deadlock cycle.
#[derive(Debug, Clone)]
pub struct DeadlockCycle {
    /// Lock IDs in the cycle
    pub locks: Vec<LockId>,
    /// Example trace showing conflicting lock orders
    pub example_trace: Vec<String>,
}

/// Detect deadlocks using Tarjan's SCC algorithm.
///
/// Any strongly connected component with >1 node or a self-loop indicates
/// a potential deadlock.
pub fn detect_deadlock(graph: &LockOrderGraph) -> Option<DeadlockCycle> {
    let nodes = graph.all_nodes();

    if nodes.is_empty() {
        return None;
    }

    // Check for self-loops first (simplest case)
    for &node in &nodes {
        if graph.has_self_loop(node) {
            return Some(DeadlockCycle {
                locks: vec![node],
                example_trace: vec![format!("Lock {} acquired while already holding it", node)],
            });
        }
    }

    // Use Tarjan's algorithm to find SCCs
    struct TarjanState {
        index: usize,
        stack: Vec<LockId>,
        indices: HashMap<LockId, usize>,
        lowlinks: HashMap<LockId, usize>,
        on_stack: HashMap<LockId, bool>,
        sccs: Vec<Vec<LockId>>,
    }

    impl TarjanState {
        fn new() -> Self {
            Self {
                index: 0,
                stack: Vec::new(),
                indices: HashMap::new(),
                lowlinks: HashMap::new(),
                on_stack: HashMap::new(),
                sccs: Vec::new(),
            }
        }

        fn strongconnect(&mut self, v: LockId, graph: &LockOrderGraph) {
            self.indices.insert(v, self.index);
            self.lowlinks.insert(v, self.index);
            self.index += 1;
            self.stack.push(v);
            self.on_stack.insert(v, true);

            for &w in graph.edges_from(v) {
                if !self.indices.contains_key(&w) {
                    self.strongconnect(w, graph);
                    let w_lowlink = *self.lowlinks.get(&w).unwrap();
                    let v_lowlink = *self.lowlinks.get(&v).unwrap();
                    self.lowlinks.insert(v, v_lowlink.min(w_lowlink));
                } else if *self.on_stack.get(&w).unwrap_or(&false) {
                    let w_index = *self.indices.get(&w).unwrap();
                    let v_lowlink = *self.lowlinks.get(&v).unwrap();
                    self.lowlinks.insert(v, v_lowlink.min(w_index));
                }
            }

            if self.lowlinks.get(&v) == self.indices.get(&v) {
                let mut scc = Vec::new();
                loop {
                    let w = self.stack.pop().unwrap();
                    self.on_stack.insert(w, false);
                    scc.push(w);
                    if w == v {
                        break;
                    }
                }
                if scc.len() > 1 {
                    self.sccs.push(scc);
                }
            }
        }
    }

    let mut state = TarjanState::new();

    for &node in &nodes {
        if !state.indices.contains_key(&node) {
            state.strongconnect(node, graph);
        }
    }

    // Return the first cycle found
    if let Some(cycle) = state.sccs.first() {
        let example_trace = cycle
            .windows(2)
            .map(|pair| format!("Lock {} → Lock {}", pair[0], pair[1]))
            .collect();

        Some(DeadlockCycle {
            locks: cycle.clone(),
            example_trace,
        })
    } else {
        None
    }
}

/// Generate deadlock verification conditions.
///
/// These are diagnostic VCs (always-SAT pattern) that report detected deadlocks.
pub fn deadlock_vcs(cycles: &[DeadlockCycle]) -> Vec<VerificationCondition> {
    cycles
        .iter()
        .map(|cycle| {
            let lock_list = cycle
                .locks
                .iter()
                .map(|id| id.to_string())
                .collect::<Vec<_>>()
                .join(", ");

            let description = format!(
                "Potential deadlock: locks [{}] acquired in conflicting order",
                lock_list
            );

            VerificationCondition {
                description,
                script: Script::new(),
                location: VcLocation {
                    function: "concurrent_fn".to_string(),
                    block: 0,
                    statement: 0,
                    source_file: None,
                    source_line: None,
                    contract_text: Some(cycle.example_trace.join("; ")),
                    vc_kind: VcKind::Deadlock,
                },
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_no_deadlock_linear() {
        let mut graph = LockOrderGraph::new();
        graph.add_edge(0, 1);
        let result = detect_deadlock(&graph);
        assert!(result.is_none());
    }

    #[test]
    fn test_deadlock_simple_cycle() {
        let mut graph = LockOrderGraph::new();
        graph.add_edge(0, 1);
        graph.add_edge(1, 0);
        let result = detect_deadlock(&graph);
        assert!(result.is_some());
        let cycle = result.unwrap();
        assert_eq!(cycle.locks.len(), 2);
        assert!(cycle.locks.contains(&0));
        assert!(cycle.locks.contains(&1));
    }

    #[test]
    fn test_deadlock_self_loop() {
        let mut graph = LockOrderGraph::new();
        graph.add_edge(0, 0);
        let result = detect_deadlock(&graph);
        assert!(result.is_some());
        let cycle = result.unwrap();
        assert_eq!(cycle.locks, vec![0]);
    }

    #[test]
    fn test_deadlock_three_node_cycle() {
        let mut graph = LockOrderGraph::new();
        graph.add_edge(0, 1);
        graph.add_edge(1, 2);
        graph.add_edge(2, 0);
        let result = detect_deadlock(&graph);
        assert!(result.is_some());
        let cycle = result.unwrap();
        assert_eq!(cycle.locks.len(), 3);
        assert!(cycle.locks.contains(&0));
        assert!(cycle.locks.contains(&1));
        assert!(cycle.locks.contains(&2));
    }

    #[test]
    fn test_deadlock_vc_generation() {
        let cycles = vec![DeadlockCycle {
            locks: vec![0, 1],
            example_trace: vec!["Lock 0 → Lock 1".to_string(), "Lock 1 → Lock 0".to_string()],
        }];

        let vcs = deadlock_vcs(&cycles);
        assert_eq!(vcs.len(), 1);
        assert_eq!(vcs[0].location.vc_kind, VcKind::Deadlock);
        assert!(vcs[0].description.contains("Potential deadlock"));
        assert!(vcs[0].description.contains("0, 1"));
    }

    #[test]
    fn test_empty_graph() {
        let graph = LockOrderGraph::new();
        let result = detect_deadlock(&graph);
        assert!(result.is_none());
    }
}
