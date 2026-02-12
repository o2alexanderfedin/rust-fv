//! Call graph extraction and topological sorting for verification order.
//!
//! Builds a call graph from IR functions and produces a topological ordering
//! where leaf functions (callees) are verified before their callers.
//!
//! This ensures that function summaries are available when verifying callers,
//! enabling modular verification.

use std::collections::{HashMap, HashSet, VecDeque};

use crate::ir::{Function, Terminator};

/// Call graph representation.
pub struct CallGraph {
    /// Edges: caller -> list of callees
    edges: HashMap<String, Vec<String>>,
    /// All function names in the graph
    all_functions: HashSet<String>,
}

impl CallGraph {
    /// Build a call graph from a list of functions.
    ///
    /// Scans each function's basic blocks for `Terminator::Call` to extract call edges.
    pub fn from_functions(functions: &[(String, &Function)]) -> Self {
        let mut edges: HashMap<String, Vec<String>> = HashMap::new();
        let mut all_functions: HashSet<String> = HashSet::new();

        for (name, func) in functions {
            all_functions.insert(name.clone());

            // Scan basic blocks for calls
            let mut callees = Vec::new();
            for bb in &func.basic_blocks {
                if let Terminator::Call {
                    func: func_name, ..
                } = &bb.terminator
                {
                    // Normalize callee name (strip "const ", take last segment)
                    let normalized = normalize_func_name(func_name);
                    callees.push(normalized);
                }
            }

            if !callees.is_empty() {
                edges.insert(name.clone(), callees);
            }
        }

        Self {
            edges,
            all_functions,
        }
    }

    /// Compute topological ordering of functions.
    ///
    /// Returns a list of function names where leaf functions (callees with no outgoing edges
    /// to other verified functions) come first, and callers come after their callees.
    ///
    /// Uses Kahn's algorithm (BFS-based topological sort). If cycles are detected,
    /// breaks them arbitrarily and emits a warning.
    pub fn topological_order(&self) -> Vec<String> {
        // Build reverse edges (callee -> list of callers)
        let mut in_degree: HashMap<String, usize> = HashMap::new();
        let mut reverse_edges: HashMap<String, Vec<String>> = HashMap::new();

        for func in &self.all_functions {
            in_degree.insert(func.clone(), 0);
        }

        for (caller, callees) in &self.edges {
            for callee in callees {
                // Only count edges to functions in our verification set
                if self.all_functions.contains(callee) {
                    *in_degree.entry(callee.clone()).or_insert(0) += 1;
                    reverse_edges
                        .entry(callee.clone())
                        .or_default()
                        .push(caller.clone());
                }
            }
        }

        // Kahn's algorithm: process nodes with in-degree 0
        let mut queue: VecDeque<String> = in_degree
            .iter()
            .filter(|(_, deg)| **deg == 0)
            .map(|(name, _)| name.clone())
            .collect();

        let mut result = Vec::new();

        while let Some(node) = queue.pop_front() {
            result.push(node.clone());

            // Decrease in-degree of callers
            if let Some(callers) = reverse_edges.get(&node) {
                for caller in callers {
                    if let Some(deg) = in_degree.get_mut(caller) {
                        *deg -= 1;
                        if *deg == 0 {
                            queue.push_back(caller.clone());
                        }
                    }
                }
            }
        }

        // Check for cycles
        if result.len() != self.all_functions.len() {
            let remaining: Vec<_> = self
                .all_functions
                .iter()
                .filter(|f| !result.contains(f))
                .cloned()
                .collect();
            tracing::warn!(
                "Call graph cycle detected involving: {:?}. Breaking arbitrarily.",
                remaining
            );
            // Add remaining nodes in arbitrary order
            result.extend(remaining);
        }

        result
    }
}

/// Normalize function name for call graph matching.
///
/// Strips "const " prefix and takes the last `::` segment.
fn normalize_func_name(name: &str) -> String {
    let trimmed = name.trim();
    let without_const = trimmed.strip_prefix("const ").unwrap_or(trimmed);
    without_const
        .split("::")
        .last()
        .unwrap_or(without_const)
        .to_string()
}
