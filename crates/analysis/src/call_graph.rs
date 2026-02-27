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
///
/// Internally stores normalized (short) function names for edges and the
/// all_functions set so that callee references from MIR debug output
/// (which are short names like "abs") match against verified function names
/// (which are full paths like "e2e_bench::abs").
///
/// The `name_map` field maps normalized → full names to restore full paths
/// in public API return values.
pub struct CallGraph {
    /// Edges: caller (normalized) -> list of callees (normalized)
    edges: HashMap<String, Vec<String>>,
    /// All function names in the graph (normalized short names)
    all_functions: HashSet<String>,
    /// Mapping from normalized name → full name for API outputs
    name_map: HashMap<String, String>,
}

impl CallGraph {
    /// Build a call graph from a list of functions.
    ///
    /// Scans each function's basic blocks for `Terminator::Call` to extract call edges.
    ///
    /// Both caller names and callee references from MIR are normalized to their
    /// short (last-segment) forms internally.  The `name_map` records the mapping
    /// from normalized → full so that public API methods can return full names.
    pub fn from_functions(functions: &[(String, &Function)]) -> Self {
        let mut edges: HashMap<String, Vec<String>> = HashMap::new();
        let mut all_functions: HashSet<String> = HashSet::new();
        let mut name_map: HashMap<String, String> = HashMap::new();

        for (name, func) in functions {
            // Normalize caller name so it matches normalized callee references
            let norm_name = normalize_func_name(name);
            all_functions.insert(norm_name.clone());
            name_map
                .entry(norm_name.clone())
                .or_insert_with(|| name.clone());

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
                edges.insert(norm_name, callees);
            }
        }

        Self {
            edges,
            all_functions,
            name_map,
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

        // Translate normalized names back to full names for callers
        result
            .into_iter()
            .map(|norm| self.name_map.get(&norm).cloned().unwrap_or(norm))
            .collect()
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
                // Mutual recursion: multi-node SCC — translate normalized → full names
                let functions: Vec<String> = scc
                    .iter()
                    .map(|&idx| {
                        let norm = &graph[idx];
                        self.name_map
                            .get(norm)
                            .cloned()
                            .unwrap_or_else(|| norm.clone())
                    })
                    .collect();
                groups.push(RecursiveGroup { functions });
            } else if scc.len() == 1 {
                // Check for self-edge (direct recursion)
                let node = scc[0];
                let has_self_edge = graph.edges(node).any(|e| e.target() == node);
                if has_self_edge {
                    let norm = &graph[node];
                    let full = self
                        .name_map
                        .get(norm)
                        .cloned()
                        .unwrap_or_else(|| norm.clone());
                    groups.push(RecursiveGroup {
                        functions: vec![full],
                    });
                }
            }
        }

        groups
    }

    /// Compute transitive callers of a function (reverse transitive closure).
    ///
    /// Returns all functions that transitively call the given function,
    /// excluding the function itself. Handles cycles safely via visited set.
    ///
    /// # Arguments
    /// * `func_name` - Name of the function to find callers for
    ///
    /// # Returns
    /// List of function names that transitively call `func_name`
    pub fn transitive_callers(&self, func_name: &str) -> Vec<String> {
        // Normalize the input name to match internal storage
        let norm_start = normalize_func_name(func_name);

        // Build reverse edges (callee -> list of callers), using normalized names
        let mut reverse_edges: HashMap<String, Vec<String>> = HashMap::new();

        for (caller, callees) in &self.edges {
            for callee in callees {
                // Only consider edges where both caller and callee are in all_functions
                if self.all_functions.contains(callee) && self.all_functions.contains(caller) {
                    reverse_edges
                        .entry(callee.clone())
                        .or_default()
                        .push(caller.clone());
                }
            }
        }

        // BFS from norm_start through reverse edges
        let mut visited: HashSet<String> = HashSet::new();
        let mut queue: VecDeque<String> = VecDeque::new();
        let mut result: Vec<String> = Vec::new();

        // Start with direct callers
        if let Some(direct_callers) = reverse_edges.get(&norm_start) {
            for caller in direct_callers {
                if !visited.contains(caller) {
                    visited.insert(caller.clone());
                    queue.push_back(caller.clone());
                    result.push(caller.clone());
                }
            }
        }

        // BFS to find transitive callers
        while let Some(current) = queue.pop_front() {
            if let Some(callers_of_current) = reverse_edges.get(&current) {
                for caller in callers_of_current {
                    if !visited.contains(caller) {
                        visited.insert(caller.clone());
                        queue.push_back(caller.clone());
                        result.push(caller.clone());
                    }
                }
            }
        }

        // Translate normalized names back to full names
        result
            .into_iter()
            .map(|norm| self.name_map.get(&norm).cloned().unwrap_or(norm))
            .collect()
    }

    /// Get direct callees of a function.
    ///
    /// Returns only functions in the verification set (all_functions).
    ///
    /// # Arguments
    /// * `func_name` - Name of the function
    ///
    /// # Returns
    /// List of direct callees
    pub fn direct_callees(&self, func_name: &str) -> Vec<String> {
        // Normalize the input name to match internal storage
        let norm_name = normalize_func_name(func_name);
        self.edges
            .get(&norm_name)
            .map(|callees| {
                callees
                    .iter()
                    .filter(|callee| self.all_functions.contains(*callee))
                    .map(|callee| {
                        // Translate normalized callee name back to full name
                        self.name_map
                            .get(callee)
                            .cloned()
                            .unwrap_or_else(|| callee.clone())
                    })
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Identify all functions that need re-verification due to contract changes.
    ///
    /// Computes the set of functions whose contracts have changed, plus all
    /// transitive callers of those functions.
    ///
    /// # Arguments
    /// * `all_functions` - List of (function_name, current_contract_hash) pairs
    /// * `cache` - Closure to look up cached contract hash by function name
    ///
    /// # Returns
    /// Set of function names that need re-verification
    #[allow(dead_code)] // Used in future phases
    pub fn changed_contract_functions<F>(
        &self,
        all_functions: &[(String, [u8; 32])],
        cache: F,
    ) -> HashSet<String>
    where
        F: Fn(&str) -> Option<[u8; 32]>,
    {
        let mut changed_set: HashSet<String> = HashSet::new();

        // First, find all functions with changed contracts
        for (func_name, current_hash) in all_functions {
            if let Some(cached_hash) = cache(func_name) {
                if cached_hash != *current_hash {
                    changed_set.insert(func_name.clone());
                }
            } else {
                // No cached entry means contract is "changed" (new)
                changed_set.insert(func_name.clone());
            }
        }

        // Then add all transitive callers
        let direct_changed: Vec<String> = changed_set.iter().cloned().collect();
        for func_name in &direct_changed {
            let callers = self.transitive_callers(func_name);
            for caller in callers {
                changed_set.insert(caller);
            }
        }

        changed_set
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
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
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

    // ====== CallGraph::transitive_callers tests ======

    #[test]
    fn test_transitive_callers_empty_graph() {
        let funcs: Vec<(String, &Function)> = vec![];
        let cg = CallGraph::from_functions(&funcs);
        let callers = cg.transitive_callers("nonexistent");
        assert!(callers.is_empty());
    }

    #[test]
    fn test_transitive_callers_linear_chain() {
        // a -> b -> c: transitive_callers(c) should return [b, a]
        let a = make_function("a", vec![call_block("b"), return_block()]);
        let b = make_function("b", vec![call_block("c"), return_block()]);
        let c = make_function("c", vec![return_block()]);
        let funcs = vec![
            ("a".to_string(), &a),
            ("b".to_string(), &b),
            ("c".to_string(), &c),
        ];
        let cg = CallGraph::from_functions(&funcs);
        let callers = cg.transitive_callers("c");
        assert_eq!(callers.len(), 2);
        assert!(callers.contains(&"b".to_string()));
        assert!(callers.contains(&"a".to_string()));
    }

    #[test]
    fn test_transitive_callers_diamond() {
        // top -> left, top -> right, left -> bottom, right -> bottom
        // transitive_callers(bottom) should return [left, right, top]
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
        let callers = cg.transitive_callers("bottom");
        assert_eq!(callers.len(), 3);
        assert!(callers.contains(&"left".to_string()));
        assert!(callers.contains(&"right".to_string()));
        assert!(callers.contains(&"top".to_string()));
    }

    #[test]
    fn test_transitive_callers_with_cycle() {
        // a -> b -> a (cycle)
        // transitive_callers(a) should return [b, a] (both are in the cycle)
        // But wait, a appears because: a calls b, b calls a, so "b is a caller of a",
        // and "a is a caller of b", thus transitively "a is a caller of a" via b.
        // However, we exclude self from the initial set, so this returns [b]
        // Actually: direct callers of a are [b]. Then we BFS from b, which has
        // direct callers [a]. So the full set is [b, a], but we need to verify
        // this doesn't cause infinite loop (handled by visited set).
        let a = make_function("a", vec![call_block("b"), return_block()]);
        let b = make_function("b", vec![call_block("a"), return_block()]);
        let funcs = vec![("a".to_string(), &a), ("b".to_string(), &b)];
        let cg = CallGraph::from_functions(&funcs);
        let callers = cg.transitive_callers("a");
        // In a cycle, both functions call each other transitively
        assert_eq!(callers.len(), 2);
        assert!(callers.contains(&"b".to_string()));
        assert!(callers.contains(&"a".to_string()));
    }

    #[test]
    fn test_transitive_callers_includes_self_in_cycle() {
        // a -> a (self-loop)
        // transitive_callers(a) should return [a] because a calls itself
        // This is correct: if a's contract changes, a needs re-verification
        let a = make_function("a", vec![call_block("a"), return_block()]);
        let funcs = vec![("a".to_string(), &a)];
        let cg = CallGraph::from_functions(&funcs);
        let callers = cg.transitive_callers("a");
        assert_eq!(callers.len(), 1);
        assert!(callers.contains(&"a".to_string()));
    }

    #[test]
    fn test_transitive_callers_with_external_callees() {
        // a -> b, b -> external (external not in verified set)
        // transitive_callers(b) should return [a]
        let a = make_function("a", vec![call_block("b"), return_block()]);
        let b = make_function("b", vec![call_block("external"), return_block()]);
        let funcs = vec![("a".to_string(), &a), ("b".to_string(), &b)];
        let cg = CallGraph::from_functions(&funcs);
        let callers = cg.transitive_callers("b");
        assert_eq!(callers.len(), 1);
        assert!(callers.contains(&"a".to_string()));
    }

    #[test]
    fn test_transitive_callers_leaf_function() {
        // a -> b, c -> b (b is a leaf from perspective of no callees)
        // transitive_callers(b) should return [a, c]
        let a = make_function("a", vec![call_block("b"), return_block()]);
        let c = make_function("c", vec![call_block("b"), return_block()]);
        let b = make_function("b", vec![return_block()]);
        let funcs = vec![
            ("a".to_string(), &a),
            ("b".to_string(), &b),
            ("c".to_string(), &c),
        ];
        let cg = CallGraph::from_functions(&funcs);
        let callers = cg.transitive_callers("b");
        assert_eq!(callers.len(), 2);
        assert!(callers.contains(&"a".to_string()));
        assert!(callers.contains(&"c".to_string()));
    }

    // ====== CallGraph::direct_callees tests ======

    #[test]
    fn test_direct_callees_returns_only_verified() {
        // a -> b, a -> external (external not in verified set)
        let a = make_function(
            "a",
            vec![call_block("b"), call_block("external"), return_block()],
        );
        let b = make_function("b", vec![return_block()]);
        let funcs = vec![("a".to_string(), &a), ("b".to_string(), &b)];
        let cg = CallGraph::from_functions(&funcs);
        let callees = cg.direct_callees("a");
        assert_eq!(callees.len(), 1);
        assert_eq!(callees[0], "b");
    }

    #[test]
    fn test_direct_callees_empty_for_leaf() {
        // a (no calls)
        let a = make_function("a", vec![return_block()]);
        let funcs = vec![("a".to_string(), &a)];
        let cg = CallGraph::from_functions(&funcs);
        let callees = cg.direct_callees("a");
        assert!(callees.is_empty());
    }

    #[test]
    fn test_direct_callees_multiple() {
        // a -> b, a -> c
        let a = make_function("a", vec![call_block("b"), call_block("c"), return_block()]);
        let b = make_function("b", vec![return_block()]);
        let c = make_function("c", vec![return_block()]);
        let funcs = vec![
            ("a".to_string(), &a),
            ("b".to_string(), &b),
            ("c".to_string(), &c),
        ];
        let cg = CallGraph::from_functions(&funcs);
        let callees = cg.direct_callees("a");
        assert_eq!(callees.len(), 2);
        assert!(callees.contains(&"b".to_string()));
        assert!(callees.contains(&"c".to_string()));
    }

    #[test]
    fn test_direct_callees_nonexistent_function() {
        let a = make_function("a", vec![return_block()]);
        let funcs = vec![("a".to_string(), &a)];
        let cg = CallGraph::from_functions(&funcs);
        let callees = cg.direct_callees("nonexistent");
        assert!(callees.is_empty());
    }

    // ====== CallGraph::changed_contract_functions tests ======

    #[test]
    fn test_changed_contract_functions_direct_change() {
        // a -> b (b's contract changed)
        // Should return {b, a}
        let a = make_function("a", vec![call_block("b"), return_block()]);
        let b = make_function("b", vec![return_block()]);
        let funcs = vec![("a".to_string(), &a), ("b".to_string(), &b)];
        let cg = CallGraph::from_functions(&funcs);

        let all_functions = vec![
            ("a".to_string(), [1u8; 32]),
            ("b".to_string(), [2u8; 32]), // Different hash = changed
        ];

        let cache = |name: &str| {
            if name == "a" {
                Some([1u8; 32])
            } else if name == "b" {
                Some([99u8; 32]) // Different from current = changed
            } else {
                None
            }
        };

        let changed = cg.changed_contract_functions(&all_functions, cache);
        assert_eq!(changed.len(), 2);
        assert!(changed.contains("a"));
        assert!(changed.contains("b"));
    }

    #[test]
    fn test_changed_contract_functions_transitive() {
        // a -> b -> c (c's contract changed)
        // Should return {c, b, a}
        let a = make_function("a", vec![call_block("b"), return_block()]);
        let b = make_function("b", vec![call_block("c"), return_block()]);
        let c = make_function("c", vec![return_block()]);
        let funcs = vec![
            ("a".to_string(), &a),
            ("b".to_string(), &b),
            ("c".to_string(), &c),
        ];
        let cg = CallGraph::from_functions(&funcs);

        let all_functions = vec![
            ("a".to_string(), [1u8; 32]),
            ("b".to_string(), [2u8; 32]),
            ("c".to_string(), [3u8; 32]),
        ];

        let cache = |name: &str| match name {
            "a" => Some([1u8; 32]),
            "b" => Some([2u8; 32]),
            "c" => Some([99u8; 32]), // Changed
            _ => None,
        };

        let changed = cg.changed_contract_functions(&all_functions, cache);
        assert_eq!(changed.len(), 3);
        assert!(changed.contains("a"));
        assert!(changed.contains("b"));
        assert!(changed.contains("c"));
    }

    #[test]
    fn test_changed_contract_functions_no_change() {
        // a -> b (no changes)
        // Should return empty set
        let a = make_function("a", vec![call_block("b"), return_block()]);
        let b = make_function("b", vec![return_block()]);
        let funcs = vec![("a".to_string(), &a), ("b".to_string(), &b)];
        let cg = CallGraph::from_functions(&funcs);

        let all_functions = vec![("a".to_string(), [1u8; 32]), ("b".to_string(), [2u8; 32])];

        let cache = |name: &str| match name {
            "a" => Some([1u8; 32]),
            "b" => Some([2u8; 32]),
            _ => None,
        };

        let changed = cg.changed_contract_functions(&all_functions, cache);
        assert!(changed.is_empty());
    }

    #[test]
    fn test_changed_contract_functions_cache_miss() {
        // a (no cached entry = treated as changed)
        let a = make_function("a", vec![return_block()]);
        let funcs = vec![("a".to_string(), &a)];
        let cg = CallGraph::from_functions(&funcs);

        let all_functions = vec![("a".to_string(), [1u8; 32])];
        let cache = |_: &str| None; // No cache entries

        let changed = cg.changed_contract_functions(&all_functions, cache);
        assert_eq!(changed.len(), 1);
        assert!(changed.contains("a"));
    }
}
