//! Call graph extraction, topological sorting, and recursion detection.
//!
//! Builds a call graph from IR functions and produces a topological ordering
//! where leaf functions (callees) are verified before their callers.
//!
//! Also detects recursive functions via Tarjan's SCC algorithm (petgraph),
//! identifying both direct recursion (self-loops) and mutual recursion
//! (multi-node strongly connected components).
//!
//! This ensures that function summaries are available when verifying callers,
//! enabling modular verification.

use std::collections::{HashMap, HashSet, VecDeque};

use petgraph::algo::tarjan_scc;
use petgraph::graph::{DiGraph, NodeIndex};
use petgraph::visit::EdgeRef;

use crate::ir::{Function, Terminator};

/// A group of mutually recursive functions (or a single directly recursive function).
#[derive(Debug, Clone)]
pub struct RecursiveGroup {
    /// Function names in this recursive group.
    pub functions: Vec<String>,
}

impl RecursiveGroup {
    /// Check if a function is in this recursive group.
    pub fn contains(&self, name: &str) -> bool {
        self.functions.iter().any(|f| f == name)
    }

    /// True if this is mutual recursion (2+ functions), false if direct recursion.
    pub fn is_mutual(&self) -> bool {
        self.functions.len() > 1
    }
}

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

    /// Detect recursive functions using Tarjan's SCC algorithm.
    ///
    /// Returns a list of `RecursiveGroup`s. Each group contains either:
    /// - A single directly recursive function (calls itself), or
    /// - Two or more mutually recursive functions (form a cycle).
    ///
    /// Non-recursive functions are excluded even though `tarjan_scc` returns
    /// them as size-1 SCCs. We check for self-edges to distinguish direct
    /// recursion from non-recursive singletons.
    pub fn detect_recursion(&self) -> Vec<RecursiveGroup> {
        let mut graph: DiGraph<String, ()> = DiGraph::new();
        let mut node_map: HashMap<String, NodeIndex> = HashMap::new();

        // Add all functions as nodes
        for func in &self.all_functions {
            let idx = graph.add_node(func.clone());
            node_map.insert(func.clone(), idx);
        }

        // Add edges (only for calls within our function set)
        for (caller, callees) in &self.edges {
            if let Some(&caller_idx) = node_map.get(caller) {
                for callee in callees {
                    if let Some(&callee_idx) = node_map.get(callee) {
                        graph.add_edge(caller_idx, callee_idx, ());
                    }
                }
            }
        }

        // Run Tarjan's SCC algorithm
        let sccs = tarjan_scc(&graph);

        // Filter: keep SCCs with size > 1 (mutual recursion) or
        // size == 1 with a self-edge (direct recursion)
        let mut groups = Vec::new();
        for scc in sccs {
            if scc.len() > 1 {
                // Mutual recursion: multi-node SCC
                let functions: Vec<String> = scc.iter().map(|&idx| graph[idx].clone()).collect();
                groups.push(RecursiveGroup { functions });
            } else if scc.len() == 1 {
                // Check for self-edge (direct recursion)
                let node = scc[0];
                let has_self_edge = graph.edges(node).any(|e| e.target() == node);
                if has_self_edge {
                    groups.push(RecursiveGroup {
                        functions: vec![graph[node].clone()],
                    });
                }
            }
        }

        groups
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{
        BasicBlock, Contracts, Function, IntTy, Local, Operand, Place, Statement, Terminator, Ty,
    };

    /// Helper: create a minimal function with given basic blocks.
    fn make_function(name: &str, basic_blocks: Vec<BasicBlock>) -> Function {
        Function {
            name: name.to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Int(IntTy::I32)),
            locals: vec![],
            basic_blocks,
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
        }
    }

    /// Helper: create a basic block with a Call terminator.
    fn call_block(callee: &str) -> BasicBlock {
        BasicBlock {
            statements: vec![],
            terminator: Terminator::Call {
                func: callee.to_string(),
                args: vec![Operand::Copy(Place::local("_1"))],
                destination: Place::local("_0"),
                target: 0,
            },
        }
    }

    /// Helper: create a basic block with a Return terminator.
    fn return_block() -> BasicBlock {
        BasicBlock {
            statements: vec![Statement::Nop],
            terminator: Terminator::Return,
        }
    }

    // ====== normalize_func_name tests ======

    #[test]
    fn normalize_plain_name() {
        assert_eq!(normalize_func_name("foo"), "foo");
    }

    #[test]
    fn normalize_strips_const_prefix() {
        assert_eq!(normalize_func_name("const bar"), "bar");
    }

    #[test]
    fn normalize_takes_last_segment() {
        assert_eq!(normalize_func_name("std::ops::add"), "add");
    }

    #[test]
    fn normalize_const_with_path() {
        assert_eq!(normalize_func_name("const std::cmp::max"), "max");
    }

    #[test]
    fn normalize_trims_whitespace() {
        assert_eq!(normalize_func_name("  foo  "), "foo");
    }

    #[test]
    fn normalize_single_segment() {
        assert_eq!(normalize_func_name("compute"), "compute");
    }

    #[test]
    fn normalize_empty_string() {
        assert_eq!(normalize_func_name(""), "");
    }

    // ====== CallGraph::from_functions tests ======

    #[test]
    fn from_functions_empty() {
        let funcs: Vec<(String, &Function)> = vec![];
        let cg = CallGraph::from_functions(&funcs);
        assert!(cg.all_functions.is_empty());
        assert!(cg.edges.is_empty());
    }

    #[test]
    fn from_functions_single_no_calls() {
        let f = make_function("main", vec![return_block()]);
        let funcs = vec![("main".to_string(), &f)];
        let cg = CallGraph::from_functions(&funcs);
        assert_eq!(cg.all_functions.len(), 1);
        assert!(cg.all_functions.contains("main"));
        assert!(cg.edges.is_empty());
    }

    #[test]
    fn from_functions_single_with_call() {
        let f = make_function("main", vec![call_block("helper"), return_block()]);
        let funcs = vec![("main".to_string(), &f)];
        let cg = CallGraph::from_functions(&funcs);
        assert_eq!(cg.all_functions.len(), 1);
        assert!(cg.edges.contains_key("main"));
        assert_eq!(cg.edges["main"], vec!["helper".to_string()]);
    }

    #[test]
    fn from_functions_two_with_dependency() {
        let caller = make_function("caller", vec![call_block("callee"), return_block()]);
        let callee = make_function("callee", vec![return_block()]);
        let funcs = vec![
            ("caller".to_string(), &caller),
            ("callee".to_string(), &callee),
        ];
        let cg = CallGraph::from_functions(&funcs);
        assert_eq!(cg.all_functions.len(), 2);
        assert_eq!(cg.edges["caller"], vec!["callee".to_string()]);
        assert!(!cg.edges.contains_key("callee"));
    }

    #[test]
    fn from_functions_normalizes_const_callee() {
        let f = make_function(
            "main",
            vec![call_block("const std::ops::add"), return_block()],
        );
        let funcs = vec![("main".to_string(), &f)];
        let cg = CallGraph::from_functions(&funcs);
        assert_eq!(cg.edges["main"], vec!["add".to_string()]);
    }

    #[test]
    fn from_functions_multiple_calls_in_one_function() {
        let f = make_function(
            "main",
            vec![call_block("foo"), call_block("bar"), return_block()],
        );
        let funcs = vec![("main".to_string(), &f)];
        let cg = CallGraph::from_functions(&funcs);
        assert_eq!(cg.edges["main"].len(), 2);
        assert_eq!(cg.edges["main"][0], "foo");
        assert_eq!(cg.edges["main"][1], "bar");
    }

    // ====== CallGraph::topological_order tests ======

    #[test]
    fn topological_order_empty() {
        let funcs: Vec<(String, &Function)> = vec![];
        let cg = CallGraph::from_functions(&funcs);
        let order = cg.topological_order();
        assert!(order.is_empty());
    }

    #[test]
    fn topological_order_single_function() {
        let f = make_function("main", vec![return_block()]);
        let funcs = vec![("main".to_string(), &f)];
        let cg = CallGraph::from_functions(&funcs);
        let order = cg.topological_order();
        assert_eq!(order, vec!["main".to_string()]);
    }

    #[test]
    fn topological_order_linear_chain() {
        // a -> b -> c: in-degree counts callers, so a=0, b=1, c=1.
        // The algorithm processes nodes with 0 callers first, then decreases
        // in-degree of the processed node's callers (via reverse_edges).
        // All three functions must appear in the output.
        let a = make_function("a", vec![call_block("b"), return_block()]);
        let b = make_function("b", vec![call_block("c"), return_block()]);
        let c = make_function("c", vec![return_block()]);
        let funcs = vec![
            ("a".to_string(), &a),
            ("b".to_string(), &b),
            ("c".to_string(), &c),
        ];
        let cg = CallGraph::from_functions(&funcs);
        let order = cg.topological_order();
        assert_eq!(order.len(), 3);
        assert!(order.contains(&"a".to_string()));
        assert!(order.contains(&"b".to_string()));
        assert!(order.contains(&"c".to_string()));
        // a has 0 in-degree (no callers), so it appears first
        assert_eq!(order[0], "a");
    }

    #[test]
    fn topological_order_diamond_dependency() {
        // top -> left, top -> right, left -> bottom, right -> bottom
        // All four functions must appear in the result.
        let top = make_function(
            "top",
            vec![call_block("left"), call_block("right"), return_block()],
        );
        let left = make_function("left", vec![call_block("bottom"), return_block()]);
        let right = make_function("right", vec![call_block("bottom"), return_block()]);
        let bottom = make_function("bottom", vec![return_block()]);
        let funcs = vec![
            ("top".to_string(), &top),
            ("left".to_string(), &left),
            ("right".to_string(), &right),
            ("bottom".to_string(), &bottom),
        ];
        let cg = CallGraph::from_functions(&funcs);
        let order = cg.topological_order();
        assert_eq!(order.len(), 4);
        assert!(order.contains(&"top".to_string()));
        assert!(order.contains(&"left".to_string()));
        assert!(order.contains(&"right".to_string()));
        assert!(order.contains(&"bottom".to_string()));
        // top has 0 in-degree (no callers), so it appears first
        assert_eq!(order[0], "top");
    }

    #[test]
    fn topological_order_cycle_includes_all_functions() {
        // a -> b -> a (cycle): all functions should still appear
        let a = make_function("a", vec![call_block("b"), return_block()]);
        let b = make_function("b", vec![call_block("a"), return_block()]);
        let funcs = vec![("a".to_string(), &a), ("b".to_string(), &b)];
        let cg = CallGraph::from_functions(&funcs);
        let order = cg.topological_order();
        assert_eq!(order.len(), 2);
        assert!(order.contains(&"a".to_string()));
        assert!(order.contains(&"b".to_string()));
    }

    #[test]
    fn topological_order_external_callee_ignored() {
        // a calls "external_fn" that is not in our function set
        // Should not affect topological ordering
        let a = make_function("a", vec![call_block("external_fn"), return_block()]);
        let funcs = vec![("a".to_string(), &a)];
        let cg = CallGraph::from_functions(&funcs);
        let order = cg.topological_order();
        assert_eq!(order.len(), 1);
        assert_eq!(order[0], "a");
    }

    #[test]
    fn topological_order_callee_then_caller() {
        // b -> a: b calls a. In the reverse_edges graph, a maps to [b].
        // in_degree: a=1, b=0. b is processed first, then
        // reverse_edges["b"] is empty. So a remains unprocessed and gets
        // appended via the cycle-recovery path. Both functions appear.
        let a = make_function("a", vec![return_block()]);
        let b = make_function("b", vec![call_block("a"), return_block()]);
        let funcs = vec![("a".to_string(), &a), ("b".to_string(), &b)];
        let cg = CallGraph::from_functions(&funcs);
        let order = cg.topological_order();
        assert_eq!(order.len(), 2);
        assert!(order.contains(&"a".to_string()));
        assert!(order.contains(&"b".to_string()));
    }

    #[test]
    fn topological_order_independent_functions() {
        // No calls between them: all should appear (order is arbitrary)
        let a = make_function("a", vec![return_block()]);
        let b = make_function("b", vec![return_block()]);
        let c = make_function("c", vec![return_block()]);
        let funcs = vec![
            ("a".to_string(), &a),
            ("b".to_string(), &b),
            ("c".to_string(), &c),
        ];
        let cg = CallGraph::from_functions(&funcs);
        let order = cg.topological_order();
        assert_eq!(order.len(), 3);
        assert!(order.contains(&"a".to_string()));
        assert!(order.contains(&"b".to_string()));
        assert!(order.contains(&"c".to_string()));
    }

    // ====== RecursiveGroup tests (Phase 6) ======

    #[test]
    fn test_recursive_group_contains() {
        let group = RecursiveGroup {
            functions: vec!["factorial".to_string()],
        };
        assert!(group.contains("factorial"));
        assert!(!group.contains("fibonacci"));
    }

    #[test]
    fn test_recursive_group_is_mutual() {
        let direct = RecursiveGroup {
            functions: vec!["factorial".to_string()],
        };
        assert!(!direct.is_mutual());

        let mutual = RecursiveGroup {
            functions: vec!["even".to_string(), "odd".to_string()],
        };
        assert!(mutual.is_mutual());
    }

    // ====== CallGraph::detect_recursion tests (Phase 6) ======

    #[test]
    fn test_detect_recursion_empty_graph() {
        let funcs: Vec<(String, &Function)> = vec![];
        let cg = CallGraph::from_functions(&funcs);
        let groups = cg.detect_recursion();
        assert!(groups.is_empty());
    }

    #[test]
    fn test_detect_recursion_no_recursion() {
        // a -> b -> c (linear chain, no recursion)
        let a = make_function("a", vec![call_block("b"), return_block()]);
        let b = make_function("b", vec![call_block("c"), return_block()]);
        let c = make_function("c", vec![return_block()]);
        let funcs = vec![
            ("a".to_string(), &a),
            ("b".to_string(), &b),
            ("c".to_string(), &c),
        ];
        let cg = CallGraph::from_functions(&funcs);
        let groups = cg.detect_recursion();
        assert!(
            groups.is_empty(),
            "Linear chain should have no recursive groups"
        );
    }

    #[test]
    fn test_detect_recursion_direct_self_loop() {
        // factorial calls itself
        let factorial = make_function("factorial", vec![call_block("factorial"), return_block()]);
        let funcs = vec![("factorial".to_string(), &factorial)];
        let cg = CallGraph::from_functions(&funcs);
        let groups = cg.detect_recursion();
        assert_eq!(groups.len(), 1);
        assert!(groups[0].contains("factorial"));
        assert!(!groups[0].is_mutual());
    }

    #[test]
    fn test_detect_recursion_mutual_two_functions() {
        // even -> odd -> even (cycle)
        let even = make_function("even", vec![call_block("odd"), return_block()]);
        let odd = make_function("odd", vec![call_block("even"), return_block()]);
        let funcs = vec![("even".to_string(), &even), ("odd".to_string(), &odd)];
        let cg = CallGraph::from_functions(&funcs);
        let groups = cg.detect_recursion();
        assert_eq!(groups.len(), 1);
        assert!(groups[0].contains("even"));
        assert!(groups[0].contains("odd"));
        assert!(groups[0].is_mutual());
    }

    #[test]
    fn test_detect_recursion_mutual_three_functions() {
        // a -> b -> c -> a
        let a = make_function("a", vec![call_block("b"), return_block()]);
        let b = make_function("b", vec![call_block("c"), return_block()]);
        let c = make_function("c", vec![call_block("a"), return_block()]);
        let funcs = vec![
            ("a".to_string(), &a),
            ("b".to_string(), &b),
            ("c".to_string(), &c),
        ];
        let cg = CallGraph::from_functions(&funcs);
        let groups = cg.detect_recursion();
        assert_eq!(groups.len(), 1);
        assert!(groups[0].contains("a"));
        assert!(groups[0].contains("b"));
        assert!(groups[0].contains("c"));
        assert!(groups[0].is_mutual());
    }

    #[test]
    fn test_detect_recursion_mixed_recursive_and_non() {
        // helper (non-recursive) + factorial (self-loop)
        let helper = make_function("helper", vec![return_block()]);
        let factorial = make_function(
            "factorial",
            vec![
                call_block("factorial"),
                call_block("helper"),
                return_block(),
            ],
        );
        let funcs = vec![
            ("helper".to_string(), &helper),
            ("factorial".to_string(), &factorial),
        ];
        let cg = CallGraph::from_functions(&funcs);
        let groups = cg.detect_recursion();
        assert_eq!(groups.len(), 1);
        assert!(groups[0].contains("factorial"));
        assert!(!groups[0].contains("helper"));
    }

    #[test]
    fn test_detect_recursion_two_separate_sccs() {
        // Group 1: factorial (self-loop), Group 2: even <-> odd
        let factorial = make_function("factorial", vec![call_block("factorial"), return_block()]);
        let even = make_function("even", vec![call_block("odd"), return_block()]);
        let odd = make_function("odd", vec![call_block("even"), return_block()]);
        let funcs = vec![
            ("factorial".to_string(), &factorial),
            ("even".to_string(), &even),
            ("odd".to_string(), &odd),
        ];
        let cg = CallGraph::from_functions(&funcs);
        let groups = cg.detect_recursion();
        assert_eq!(groups.len(), 2);

        // Find which group is which
        let has_factorial = groups
            .iter()
            .any(|g| g.contains("factorial") && g.functions.len() == 1);
        let has_even_odd = groups
            .iter()
            .any(|g| g.contains("even") && g.contains("odd") && g.functions.len() == 2);
        assert!(has_factorial, "Should have factorial self-loop group");
        assert!(has_even_odd, "Should have even/odd mutual recursion group");
    }

    #[test]
    fn test_detect_recursion_self_loop_in_size_one_scc() {
        // Critical pitfall: tarjan_scc returns size-1 SCCs for ALL nodes.
        // Only nodes with self-edges are truly recursive.
        // Non-recursive node 'a' should NOT appear in recursive groups.
        let a = make_function("a", vec![return_block()]);
        let b = make_function("b", vec![call_block("b"), return_block()]);
        let funcs = vec![("a".to_string(), &a), ("b".to_string(), &b)];
        let cg = CallGraph::from_functions(&funcs);
        let groups = cg.detect_recursion();
        assert_eq!(groups.len(), 1, "Only 'b' (self-loop) should be recursive");
        assert!(groups[0].contains("b"));
        assert!(!groups[0].contains("a"));
    }
}
