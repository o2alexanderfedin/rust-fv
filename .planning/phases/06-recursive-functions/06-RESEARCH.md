# Phase 6: Recursive Functions - Research

**Researched:** 2026-02-11
**Domain:** Recursive function verification via uninterpreted function encoding and termination analysis
**Confidence:** HIGH

## Summary

Recursive function verification requires three core components: (1) detecting recursion via call graph SCC analysis, (2) encoding recursive functions as uninterpreted SMT functions with axioms for base/recursive cases, and (3) proving termination via mandatory `#[decreases(expr)]` annotations that specify a well-founded measure.

The standard approach, proven in Dafny, F*, and Verus, uses uninterpreted functions to avoid infinite SMT unrolling while preserving soundness. Z3's `define-fun-rec` provides native support, but the more flexible axiom-based encoding allows finer control over unrolling depth. Termination checking converts `decreases` clauses into VCs that verify the measure strictly decreases at each recursive call site.

rust-fv already has the necessary infrastructure: ContractDatabase for function summaries, call graph extraction in `call_graph.rs`, MIR-based function call detection, and Z3 integration. Phase 6 extends this with petgraph for SCC analysis (mutual recursion), termination measure VCs, and diagnostic improvements.

**Primary recommendation:** Use axiom-based uninterpreted function encoding (not Z3's define-fun-rec) to maintain full control over verification depth and error reporting. Require `#[decreases(expr)]` for all recursive functions (detected via SCC analysis), generate termination VCs comparing measure at call site vs. entry, and provide clear diagnostics when termination proofs fail.

## Standard Stack

### Core
| Library | Version | Purpose | Why Standard |
|---------|---------|---------|--------------|
| petgraph | 0.8.3 | Call graph SCC analysis | Industry standard for graph algorithms in Rust; used by cargo, rustc ecosystem tools |
| Z3 (existing) | 0.19 | SMT solving with uninterpreted functions | Already integrated; supports quantified axioms for recursive encoding |
| rustc_middle (existing) | nightly | MIR function call detection | Already used; Terminator::Call provides call graph edges |

### Supporting
| Library | Version | Purpose | When to Use |
|---------|---------|---------|-------------|
| tracing (existing) | 0.1 | Diagnostics for recursion depth | Debugging SCC detection, termination failures |

### Alternatives Considered
| Instead of | Could Use | Tradeoff |
|------------|-----------|----------|
| petgraph | Hand-rolled Tarjan | petgraph is battle-tested; no reason to reimplement |
| Axiom encoding | Z3 define-fun-rec | define-fun-rec automates unrolling but loses control over depth limits and error reporting |
| Mandatory decreases | Auto-infer measures | Termination undecidable; unsound to assume without proof |

**Installation:**
```bash
# Add to crates/analysis/Cargo.toml
petgraph = "0.8.3"
```

## Architecture Patterns

### Recommended Project Structure
```
crates/analysis/src/
├── recursion.rs              # NEW: Recursion detection, termination VCs
├── call_graph.rs             # EXTEND: Add SCC detection via petgraph
├── vcgen.rs                  # EXTEND: Generate termination VCs, handle recursive calls
└── contract_db.rs            # EXTEND: Mark recursive functions in summaries
```

### Pattern 1: SCC-Based Recursion Detection
**What:** Build call graph from IR functions, run petgraph's tarjan_scc to find strongly connected components (SCCs with size > 1 = mutual recursion, self-loops = direct recursion)
**When to use:** Phase 6 initialization, before VCGen
**Example:**
```rust
// Source: petgraph official docs + rust-fv call_graph.rs patterns
use petgraph::graph::DiGraph;
use petgraph::algo::tarjan_scc;

pub fn detect_recursive_functions(functions: &[Function]) -> Vec<RecursiveGroup> {
    let mut graph = DiGraph::<String, ()>::new();
    let mut node_map = HashMap::new();

    // Build call graph
    for func in functions {
        let idx = graph.add_node(func.name.clone());
        node_map.insert(func.name.clone(), idx);
    }

    for func in functions {
        let caller_idx = node_map[&func.name];
        for bb in &func.basic_blocks {
            if let Terminator::Call { func: callee, .. } = &bb.terminator {
                let callee_name = normalize_callee_name(callee);
                if let Some(&callee_idx) = node_map.get(&callee_name) {
                    graph.add_edge(caller_idx, callee_idx, ());
                }
            }
        }
    }

    // Find SCCs (strongly connected components)
    let sccs = tarjan_scc(&graph);

    // Extract recursive groups
    sccs.into_iter()
        .filter(|scc| scc.len() > 1 || has_self_loop(&graph, scc[0]))
        .map(|scc| RecursiveGroup {
            functions: scc.iter().map(|&idx| graph[idx].clone()).collect(),
        })
        .collect()
}
```

### Pattern 2: Uninterpreted Function Encoding with Axioms
**What:** For recursive function `f`, declare uninterpreted SMT function `f_uninterp`, add axioms for base/recursive cases guarded by condition predicates
**When to use:** VCGen for recursive functions identified by SCC analysis
**Example:**
```rust
// Source: F* SMT encoding patterns + Z3 design_recfuns.md
fn encode_recursive_function(func: &Function, script: &mut Script) {
    // Declare uninterpreted function: (declare-fun fact_uninterp (Int) Int)
    let params_sort: Vec<Sort> = func.params.iter()
        .map(|p| encode_type(&p.ty))
        .collect();
    let return_sort = encode_type(&func.return_local.ty);

    script.add(Command::DeclareFun {
        name: format!("{}_uninterp", func.name),
        param_sorts: params_sort,
        return_sort: return_sort.clone(),
    });

    // Axiom for base case: (assert (=> (< n 1) (= (fact_uninterp n) 1)))
    // Axiom for recursive case: (assert (=> (>= n 1)
    //   (= (fact_uninterp n) (* n (fact_uninterp (- n 1))))))
    // Generated from MIR basic blocks with conditional logic
}
```

### Pattern 3: Termination VC Generation
**What:** For each recursive call site, generate VC proving `decreases(args_at_call) < decreases(args_at_entry)` under path conditions
**When to use:** VCGen for functions with `#[decreases(expr)]` annotation
**Example:**
```rust
// Source: Dafny/Verus termination checking patterns
fn generate_termination_vcs(
    func: &Function,
    call_sites: &[CallSiteInfo],
    decreases_expr: &SpecExpr,
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    // Parse decreases expression to get measure at function entry
    let entry_measure = parse_spec_expr(&decreases_expr.raw);

    for call_site in call_sites {
        // Substitute actual arguments into decreases expression
        let call_measure = substitute_args(&entry_measure, &call_site.args);

        // VC: measure at call strictly less than measure at entry
        // (assert (not (< call_measure entry_measure)))  ; negated for UNSAT = valid
        let vc = build_termination_vc(
            entry_measure.clone(),
            call_measure,
            &call_site.path_condition,
            &call_site.prior_assignments,
        );

        vcs.push(VerificationCondition {
            description: format!(
                "Termination: decreases measure at call to {} must be less than at entry",
                func.name
            ),
            script: vc,
            location: VcLocation {
                function: func.name.clone(),
                block: call_site.block_idx,
                vc_kind: VcKind::Termination,
                contract_text: Some(decreases_expr.raw.clone()),
                ..Default::default()
            },
        });
    }

    vcs
}
```

### Anti-Patterns to Avoid
- **Inlining recursive calls:** Leads to infinite unrolling, solver non-termination
- **Omitting termination checks:** Unsound; non-terminating recursion breaks postcondition reasoning
- **Using Z3's define-fun-rec without depth limits:** Can hang solver on deep recursion
- **Auto-inferring termination measures:** Undecidable problem; explicit annotation required

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| SCC detection | Custom Tarjan's algorithm | petgraph::algo::tarjan_scc | Proven correct, optimized, used by rustc ecosystem |
| Well-founded ordering | Custom ordering proofs | Natural numbers (n decreases to 0) + tuple lexicographic | Z3 built-in Int theory handles < natively |
| Recursive call depth limiting | Custom fuel mechanism | Axiom-based encoding with explicit measure VCs | Clearer error messages, no heuristic depth tuning |
| Mutual recursion handling | Separate per-function analysis | SCC-based grouping | Mutual recursion = single SCC; analyze together |

**Key insight:** Recursion verification has been solved by Dafny/F*/Verus; don't reinvent encodings. The complexity is in sound axiomatization and termination proofs, not in graph algorithms or SMT syntax.

## Common Pitfalls

### Pitfall 1: Missing Termination Annotation on Recursive Functions
**What goes wrong:** Developer writes recursive function without `#[decreases(expr)]`, verifier accepts it (unsound) or silently fails
**Why it happens:** Termination undecidable; can't auto-infer in general
**How to avoid:** Detect recursion via SCC analysis, emit error if `#[decreases]` missing: "recursive function `factorial` requires #[decreases(n)] annotation"
**Warning signs:** Verification succeeds on non-terminating function (e.g., `fn loop_forever(n: i32) { loop_forever(n) }`)

### Pitfall 2: Decreases Measure Not Actually Decreasing
**What goes wrong:** Developer annotates `#[decreases(n)]` but calls recursively with `n` or `n+1` instead of `n-1`
**Why it happens:** Typo, off-by-one error, misunderstanding of measure
**How to avoid:** Generate termination VC comparing `measure(args_at_call)` vs. `measure(params_at_entry)`, provide counterexample when SAT
**Warning signs:** Termination VC returns SAT with model showing `n_call >= n_entry`

### Pitfall 3: Forgetting Self-Loops in SCC Detection
**What goes wrong:** Function calls itself directly but SCC has size 1, not flagged as recursive
**Why it happens:** Tarjan's SCC treats single-node with self-loop as size-1 SCC
**How to avoid:** Check `has_self_loop()` for size-1 SCCs: `graph.edges(node).any(|edge| edge.target() == node)`
**Warning signs:** Direct recursion not detected, missing termination checks

### Pitfall 4: Structural Measure on Non-Structural Recursion
**What goes wrong:** Developer uses `#[decreases(tree.size())]` but recursion doesn't follow tree structure
**Why it happens:** Confusion between structural recursion (automatic) and general recursion (needs proof)
**How to avoid:** Document that decreases works on any integer expression, not just structural measures; provide examples
**Warning signs:** Termination VC fails on valid structural recursion patterns

### Pitfall 5: Mutual Recursion with Inconsistent Measures
**What goes wrong:** `even(n)` has `#[decreases(n)]`, `odd(n)` has `#[decreases(n-1)]`, verification fails
**Why it happens:** Mutual recursion requires all functions in SCC share same measure sequence
**How to avoid:** Detect SCC size > 1, validate all functions have compatible decreases clauses (e.g., all use `n`)
**Warning signs:** Mutual recursion termination VCs fail despite each function individually decreasing

### Pitfall 6: Infinite Axiom Instantiation
**What goes wrong:** Axioms for recursive function cause Z3 to instantiate infinitely, solver hangs
**Why it happens:** Quantified axioms without proper triggers or depth limits
**How to avoid:** Use fuel-based encoding (F* pattern) or explicit depth parameter in uninterpreted function, limit instantiation depth
**Warning signs:** Z3 timeout on simple recursive functions with base case

## Code Examples

Verified patterns from research and existing rust-fv codebase:

### Example 1: Factorial with Decreases Annotation
```rust
// Source: Dafny termination examples
#[requires(n >= 0)]
#[ensures(result > 0)]
#[decreases(n)]
pub fn factorial(n: i32) -> i32 {
    if n <= 1 {
        1
    } else {
        n * factorial(n - 1)  // Termination VC: (n-1) < n under path condition n > 1
    }
}
```

### Example 2: Mutual Recursion (Even/Odd)
```rust
// Source: Dafny mutual recursion guide
#[decreases(n)]
pub fn even(n: i32) -> bool {
    if n == 0 { true } else { odd(n - 1) }
}

#[decreases(n)]
pub fn odd(n: i32) -> bool {
    if n == 0 { false } else { even(n - 1) }
}

// SCC analysis detects: {even, odd} form a strongly connected component
// Termination VCs:
// - In even: (n-1) < n when n != 0
// - In odd: (n-1) < n when n != 0
```

### Example 3: Tree Traversal with Structural Measure
```rust
// Source: Structural recursion patterns
pub struct Tree {
    value: i32,
    left: Option<Box<Tree>>,
    right: Option<Box<Tree>>,
}

impl Tree {
    #[spec]
    pub fn size(&self) -> i32 {
        1 + self.left.as_ref().map_or(0, |t| t.size())
          + self.right.as_ref().map_or(0, |t| t.size())
    }
}

#[decreases(tree.size())]
pub fn sum(tree: &Tree) -> i32 {
    tree.value
        + tree.left.as_ref().map_or(0, |t| sum(t))
        + tree.right.as_ref().map_or(0, |t| sum(t))
    // Termination VCs:
    // - left.size() < tree.size() (follows from definition)
    // - right.size() < tree.size()
}
```

### Example 4: Call Graph SCC Detection (Petgraph Integration)
```rust
// Source: petgraph docs + rust-fv call_graph.rs
use petgraph::graph::DiGraph;
use petgraph::algo::tarjan_scc;
use std::collections::HashMap;

pub fn detect_recursion(functions: &[Function]) -> Vec<Vec<String>> {
    let mut graph = DiGraph::<String, ()>::new();
    let mut indices = HashMap::new();

    // Add nodes
    for func in functions {
        let idx = graph.add_node(func.name.clone());
        indices.insert(func.name.clone(), idx);
    }

    // Add edges
    for func in functions {
        let caller = indices[&func.name];
        for bb in &func.basic_blocks {
            if let Terminator::Call { func: callee, .. } = &bb.terminator {
                if let Some(&callee_idx) = indices.get(callee) {
                    graph.add_edge(caller, callee_idx, ());
                }
            }
        }
    }

    // Find SCCs
    let sccs = tarjan_scc(&graph);

    // Filter to recursive groups (size > 1 or self-loop)
    sccs.into_iter()
        .filter(|scc| {
            scc.len() > 1 ||
            graph.edges(scc[0]).any(|e| e.target() == scc[0])
        })
        .map(|scc| scc.iter().map(|&idx| graph[idx].clone()).collect())
        .collect()
}
```

### Example 5: Fibonacci with Missing Decreases (Error Diagnostic)
```rust
// Source: Phase requirements REC-05
pub fn fibonacci(n: i32) -> i32 {
    if n <= 1 {
        n
    } else {
        fibonacci(n - 1) + fibonacci(n - 2)
    }
}

// Expected diagnostic:
// error: recursive function `fibonacci` missing termination measure
//   |
// 1 | pub fn fibonacci(n: i32) -> i32 {
//   |        ^^^^^^^^^ recursive function detected in call graph SCC
//   |
//   = help: add #[decreases(n)] annotation to prove termination
```

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| Inline recursion (Hoare logic) | Uninterpreted functions with axioms | ~2008 (Dafny) | Enables modular verification of recursion |
| Manual termination proofs | Automated decreases clause checking | ~2010 (Dafny) | Developer writes measure, tool checks |
| Hand-rolled SCC | petgraph tarjan_scc | 2015+ (Rust ecosystem) | Correct, optimized, maintained |
| Z3 define-fun-rec (auto-unroll) | Axiom-based (controlled) | 2016 (F*/Verus) | Better error messages, depth control |

**Deprecated/outdated:**
- **Fuel-based encoding (F* style):** Clever but opaque; axiom-based with explicit termination VCs clearer for Rust developers
- **Auto-inferred termination measures:** Prusti tried, marked as future work; consensus is explicit annotation required
- **Bounded unrolling without termination proof:** Unsound; Prusti warns against this

## Open Questions

1. **How to handle higher-order recursion (functions passed as arguments)?**
   - What we know: MIR doesn't fully resolve closures to DefIds at call sites in all cases
   - What's unclear: Whether Phase 6 scope includes recursive closures or defers to Phase 7
   - Recommendation: Detect and reject for now; Phase 7 (Closures) will handle. Conservative but sound.

2. **Should we support multi-variant decreases (tuples)?**
   - What we know: Dafny/Verus support `decreases (n, m)` for lexicographic ordering
   - What's unclear: Necessary for Phase 6 success criteria? Requirements show single-expr examples
   - Recommendation: Phase 6 supports single expr; tuple support in Phase 6.1 if needed

3. **How to provide counterexamples for termination failures?**
   - What we know: Z3 model shows values where `measure_call >= measure_entry`
   - What's unclear: Best UX for presenting this (e.g., "when n = 5, recursive call uses n = 5, not decreasing")
   - Recommendation: Extract model, show concrete values in diagnostic: "counterexample: n = 5 at entry, n = 5 at recursive call"

## Sources

### Primary (HIGH confidence)
- [Dafny Termination Documentation](https://dafny.org/latest/OnlineTutorial/Termination) - Comprehensive guide on decreases clauses, well-founded orderings, and termination checking
- [F* SMT Encoding Guide](https://fstar-lang.org/tutorial/book/under_the_hood/uth_smt.html) - Detailed explanation of uninterpreted function encoding with fuel-instrumented axioms
- [Z3 Recursive Functions Design](https://github.com/Z3Prover/z3/blob/master/doc/design_recfuns.md) - Official Z3 documentation on define-fun-rec and case-based axiom compilation
- [petgraph tarjan_scc API](https://docs.rs/petgraph/latest/petgraph/algo/fn.tarjan_scc.html) - Official Rust documentation for Tarjan's SCC algorithm
- [Model Finding for Recursive Functions in SMT](https://www.cs.vu.nl/~jbe248/frf_conf.pdf) - Research paper on uninterpreted function encoding for recursive functions
- rust-fv codebase: `crates/analysis/src/call_graph.rs`, `crates/analysis/src/contract_db.rs`, `crates/analysis/src/vcgen.rs` (lines 588-607 for call site handling)

### Secondary (MEDIUM confidence)
- [Verus Decreases Clause Reference](https://verus-lang.github.io/verus/guide/reference-decreases.html) - Syntax and semantics for decreases with when/via clauses
- [Prusti Recursive Function Handling](https://link.springer.com/chapter/10.1007/978-3-031-06773-0_5) - Notes that termination checking is future work, uses bounded unrolling
- [Graphs in Rust with Petgraph](https://depth-first.com/articles/2020/02/03/graphs-in-rust-an-introduction-to-petgraph/) - Tutorial on DiGraph, add_node, add_edge API
- [Structural Recursion and Termination](https://www.cs.mcgill.ca/~dthibo1/papers/termination.pdf) - Comparison of structural recursion vs. sized types for termination
- [Rustc MIR Call Detection](https://rustc-dev-guide.rust-lang.org/mir/index.html) - MIR structure with Terminator::Call for call graph extraction

### Tertiary (LOW confidence)
- WebSearch results on "recursive function verification pitfalls" - General programming guidance, not verification-specific
- WebSearch results on "SMT-LIB define-fun-rec" - GitHub issues and discussions, not authoritative docs

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH - petgraph is proven (used by cargo/rustc tooling), Z3 already integrated
- Architecture: HIGH - Uninterpreted function + axiom encoding is standard across Dafny/F*/Verus
- Termination VCs: HIGH - Decreases clause → measure comparison is well-established pattern
- SCC detection: HIGH - Tarjan's algorithm is textbook, petgraph implementation battle-tested
- Pitfalls: MEDIUM - Derived from tool documentation and research papers, not rust-fv-specific experience
- Mutual recursion: MEDIUM - SCC approach is standard, but tuple decreases support unclear from requirements

**Research date:** 2026-02-11
**Valid until:** 2026-03-13 (30 days - stable domain, unlikely to change)
