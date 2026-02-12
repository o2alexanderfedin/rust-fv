# Phase 5: Performance and Polish - Research

**Researched:** 2026-02-11
**Domain:** Performance optimization, caching, parallelism, error reporting
**Confidence:** HIGH

## Summary

Phase 5 optimizes verification for interactive development (sub-1s simple, sub-5s complex) through four independent performance strategies: (1) VC caching with hash-based invalidation to skip unchanged functions, (2) per-function parallelism via process-based solver instances, (3) formula simplification using Z3's built-in tactics, and (4) rustc-style error messages with counterexamples. The project already has Criterion benchmarks, colored output, counterexample extraction, and SolverBackend abstraction—this phase builds on existing infrastructure rather than adding new verification capabilities.

**Primary recommendation:** Use Rayon for parallel function verification, FxHashMap for cache key storage, ariadne for rustc-style diagnostics, Z3's simplify() API for formula simplification, and extend existing Criterion benchmarks with A/B comparison for simplification impact.

## User Constraints

<user_constraints>
### Locked Decisions (from CONTEXT.md)

#### Benchmark strategy
- Both existing E2E test programs (as regression baselines) AND synthetic stress tests (for scalability limits)
- Latency targets: sub-1s for single-function verification, sub-5s for loops + inter-procedural calls
- Formula simplification measured via A/B comparison: run each benchmark with and without simplification, report % reduction in solver time
- Benchmarks are developer-only, not CI-gated (consistent with existing 01-03 decision)

#### Caching behavior
- Per-function cache granularity: if function body + contracts unchanged, skip re-verification
- Cache stored in target/rust-fv-cache/ directory (cleaned by cargo clean, standard Rust convention)
- Conservative invalidation: hash of all contracts + all function bodies — any change re-verifies everything
- Add --fresh flag to cargo verify to force re-verification (useful for debugging or after solver upgrades)

#### Parallelism model
- Per-function parallelism: verify multiple functions simultaneously, each function's VCs run sequentially
- Process-based parallelism via subprocess solver instances (supports multi-solver future: Z3, CVC5, etc.)
- Default to cores/2 parallel instances, configurable via --jobs N flag (like cargo build -j N)
- Topological verification order: build call graph, verify leaf functions first (ensures callee contracts are checked before use)

#### Error message design
- Rustc-style error format: source file + line number, colored arrows pointing to failing spec, counterexample below
- Suggest fixes for common patterns when obvious: "add overflow check", "strengthen precondition", "add loop invariant"
- Add --output-format json flag for structured JSON output (enables IDE/rust-analyzer integration)

### Claude's Discretion
- Counterexample display format (variable assignments vs execution trace — pick based on implementation feasibility)
- Exact formula simplification passes (constant folding, dead code elimination, CSE — pick based on measured impact)
- Thread management for process pool (tokio, std::thread, or simple subprocess spawning)
- JSON output schema design

### Deferred Ideas (OUT OF SCOPE)
None — discussion stayed within phase scope
</user_constraints>

## Standard Stack

### Core Performance Libraries
| Library | Version | Purpose | Why Standard |
|---------|---------|---------|--------------|
| rayon | 1.10+ | Data parallelism | Rust's de-facto standard for CPU parallelism, work-stealing scheduler, zero-cost abstraction over thread pools |
| rustc-hash (FxHashMap) | 2.1+ | Fast non-cryptographic hashing | Used by rustc compiler, 2-6% faster than alternatives for caching keys, low-quality but extremely fast |
| ariadne | 0.4+ | Compiler-style diagnostics | Rustc-inspired error reporting, multi-line labels, color generation, explicit codespan focus |
| serde_json | 1.0+ | JSON serialization | Industry standard for structured output, zero-copy deserialization |
| criterion | 0.5+ | Benchmarking | Already in use, statistical analysis, baseline comparison built-in |

### Supporting Libraries
| Library | Version | Purpose | When to Use |
|---------|---------|---------|-------------|
| schemars | 0.8+ | JSON Schema generation | For --output-format json schema documentation |
| topo_sort | 0.4+ | Topological sorting | For call graph ordering (verify leaf functions first) |
| sha2 | 0.10+ | Hashing for cache keys | For conservative cache invalidation (hash function bodies + contracts) |

### Alternatives Considered
| Instead of | Could Use | Tradeoff |
|------------|-----------|----------|
| rayon | tokio::spawn_blocking | Tokio adds async complexity unnecessary for CPU-bound tasks; rayon's work-stealing is optimal for parallel verification |
| ariadne | miette | Miette has more features (unicode, screen-reader friendly) but heavier dependencies; ariadne is lighter and rustc-focused |
| FxHashMap | std::HashMap | Std uses SipHash (cryptographic, slower); FxHash is 2-6% faster for cache lookups with acceptable collision rates |

**Installation:**
```bash
# Already has criterion, colored
cargo add rayon rustc-hash ariadne serde_json schemars topo_sort sha2
```

## Architecture Patterns

### Recommended Project Structure
```
crates/driver/src/
├── cache.rs              # VC cache with hash-based invalidation
├── parallel_verify.rs    # Rayon-based parallel verification
├── diagnostics.rs        # Ariadne error formatting
└── json_output.rs        # Structured JSON output

crates/analysis/src/
├── simplify.rs           # Z3 formula simplification wrapper
└── call_graph.rs         # Topological sorting for verification order

crates/analysis/benches/
├── vcgen_bench.rs        # Existing (extend with A/B simplification)
└── stress_bench.rs       # New: synthetic stress tests
```

### Pattern 1: Hash-Based Cache Invalidation
**What:** Compute SHA-256 hash of (function body MIR + all contracts), use as cache key. On cache hit, skip VCGen and solver entirely.
**When to use:** Every verification run (unless --fresh flag present)
**Example:**
```rust
use sha2::{Sha256, Digest};
use rustc_hash::FxHashMap;

struct VCCache {
    /// Map: function_hash -> cached SolverResult
    cache: FxHashMap<[u8; 32], SolverResult>,
    cache_dir: PathBuf, // target/rust-fv-cache/
}

impl VCCache {
    fn compute_hash(mir: &Body<'_>, contracts: &Contracts) -> [u8; 32] {
        let mut hasher = Sha256::new();
        // Hash MIR statements and terminators
        for bb in mir.basic_blocks.iter() {
            hasher.update(format!("{:?}", bb)); // Conservative: hash debug repr
        }
        // Hash contracts
        for req in &contracts.requires {
            hasher.update(req.raw.as_bytes());
        }
        for ens in &contracts.ensures {
            hasher.update(ens.raw.as_bytes());
        }
        hasher.finalize().into()
    }

    fn get(&self, hash: &[u8; 32]) -> Option<&SolverResult> {
        self.cache.get(hash)
    }

    fn insert(&mut self, hash: [u8; 32], result: SolverResult) {
        self.cache.insert(hash, result);
        // Persist to disk: target/rust-fv-cache/<hex_hash>.json
        let file = self.cache_dir.join(format!("{}.json", hex::encode(hash)));
        let json = serde_json::to_string(&result).unwrap();
        std::fs::write(file, json).ok();
    }

    fn load_from_disk(&mut self) {
        // Read all .json files from cache_dir
        for entry in std::fs::read_dir(&self.cache_dir).unwrap() {
            let path = entry.unwrap().path();
            if path.extension() == Some(OsStr::new("json")) {
                let hash_str = path.file_stem().unwrap().to_str().unwrap();
                let hash: [u8; 32] = hex::decode(hash_str).unwrap().try_into().unwrap();
                let json = std::fs::read_to_string(path).unwrap();
                let result: SolverResult = serde_json::from_str(&json).unwrap();
                self.cache.insert(hash, result);
            }
        }
    }
}
```

### Pattern 2: Rayon Parallel Verification
**What:** Use rayon's par_iter() to verify multiple functions in parallel. Each function's VCs run sequentially (no nested parallelism).
**When to use:** When verifying crate with 2+ annotated functions
**Example:**
```rust
use rayon::prelude::*;

fn verify_all_functions(
    functions: Vec<Function>,
    solver_config: SolverConfig,
    jobs: usize,
) -> Vec<FunctionResult> {
    // Configure Rayon thread pool
    rayon::ThreadPoolBuilder::new()
        .num_threads(jobs)
        .build()
        .unwrap()
        .install(|| {
            functions.par_iter()
                .map(|func| verify_single_function(func, &solver_config))
                .collect()
        })
}

fn verify_single_function(func: &Function, config: &SolverConfig) -> FunctionResult {
    // Each worker creates its own subprocess solver instance
    let solver = Z3Solver::new(config.clone());
    let vcs = generate_vcs(func, None);

    let mut verified_count = 0;
    for vc in &vcs.conditions {
        let result = solver.check_sat(&vc.script);
        if result.is_unsat() {
            verified_count += 1;
        }
    }

    FunctionResult {
        name: func.name.clone(),
        status: if verified_count == vcs.conditions.len() {
            VerificationStatus::Ok
        } else {
            VerificationStatus::Fail
        },
        vc_count: vcs.conditions.len(),
        verified_count,
        message: None,
    }
}
```

### Pattern 3: Topological Verification Order
**What:** Build call graph, topologically sort to verify leaf functions (no callees) first, then their callers.
**When to use:** Always, for inter-procedural verification soundness
**Example:**
```rust
use topo_sort::TopoSort;

fn topological_order(functions: &[Function], contract_db: &ContractDatabase) -> Vec<usize> {
    let mut topo = TopoSort::new();

    // Add all functions as nodes
    for (idx, func) in functions.iter().enumerate() {
        topo.insert(idx);
    }

    // Add edges: if func A calls func B, add edge B -> A (B must be verified first)
    for (caller_idx, caller) in functions.iter().enumerate() {
        for callee_name in extract_call_targets(caller) {
            if let Some(callee_idx) = functions.iter().position(|f| f.name == callee_name) {
                topo.add_dependency(caller_idx, callee_idx);
            }
        }
    }

    // Return topologically sorted indices
    topo.into_vec().unwrap()
}

fn extract_call_targets(func: &Function) -> Vec<String> {
    // Scan MIR for Terminator::Call, extract function names
    func.basic_blocks.iter()
        .filter_map(|bb| match &bb.terminator {
            Terminator::Call { func_name, .. } => Some(func_name.clone()),
            _ => None,
        })
        .collect()
}
```

### Pattern 4: Ariadne Diagnostics
**What:** Use ariadne to format verification failures like rustc errors: source location, colored arrows, counterexample.
**When to use:** For all verification failures (unless --output-format json)
**Example:**
```rust
use ariadne::{Report, ReportKind, Label, Color, Source};

fn report_verification_failure(
    func_name: &str,
    contract: &str,
    source_file: &str,
    line: usize,
    counterexample: &Model,
) {
    let source = Source::from(std::fs::read_to_string(source_file).unwrap());

    Report::build(ReportKind::Error, source_file, line)
        .with_message(format!("verification failed: {}", func_name))
        .with_label(
            Label::new((source_file, line..line+1))
                .with_message(format!("postcondition `{}` does not hold", contract))
                .with_color(Color::Red)
        )
        .with_note(format_counterexample(counterexample))
        .finish()
        .eprint((source_file, source))
        .unwrap();
}

fn format_counterexample(model: &Model) -> String {
    let mut lines = vec!["Counterexample:".to_string()];
    for (var, val) in &model.assignments {
        lines.push(format!("  {} = {}", var, val));
    }
    lines.join("\n")
}
```

### Pattern 5: Z3 Formula Simplification
**What:** Call Z3's simplify() API before check_sat() to apply constant folding, dead code elimination, etc.
**When to use:** Always, measure impact via Criterion A/B benchmarks
**Example:**
```rust
// In Z3NativeSolver (crates/solver/src/z3_native.rs)
fn check_sat_simplified(&self, script: &Script) -> Result<SolverResult, SolverError> {
    let ctx = z3::Context::new(&self.config);

    // Convert SMT-LIB script to Z3 AST
    let formula = self.script_to_z3_ast(&ctx, script)?;

    // Apply Z3's built-in simplification
    let simplified = formula.simplify();

    // Solve simplified formula
    let solver = z3::Solver::new(&ctx);
    solver.assert(&simplified);

    match solver.check() {
        z3::SatResult::Sat => {
            let model = solver.get_model().unwrap();
            Ok(SolverResult::Sat(Some(self.extract_model(&model))))
        }
        z3::SatResult::Unsat => Ok(SolverResult::Unsat),
        z3::SatResult::Unknown => Ok(SolverResult::Unknown("unknown".to_string())),
    }
}
```

### Anti-Patterns to Avoid
- **Nested parallelism:** Don't parallelize individual VCs within a function (overhead exceeds benefit for typical 1-5 VCs per function)
- **Tokio for CPU work:** Tokio's async is for I/O concurrency; solver calls are CPU-bound (use rayon or std::thread instead)
- **Cryptographic hashing:** Don't use SipHash/BLAKE3 for cache keys (slower than necessary; SHA-256 is sufficient and widely available)
- **JSON parsing errors:** Don't return JSON to stdout/stderr mixed with text (breaks cargo's output parsing; use --output-format json exclusively)

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Thread pool management | Custom thread spawning logic | rayon::par_iter() | Rayon handles work-stealing, CPU pinning, panic recovery; custom pools suffer deadlocks, unbalanced load |
| Topological sorting | DFS-based cycle detection | topo_sort crate | Handles cycles gracefully, Kahn's algorithm tested, edge cases (self-loops, disconnected graphs) solved |
| Compiler diagnostics | Custom ANSI color codes + formatting | ariadne crate | Multi-line spans, label positioning, color generation, unicode handling all solved; custom formatters miss edge cases |
| JSON schema validation | Hand-written schema docs | schemars derive macro | Auto-generates schema from Rust types, keeps docs in sync with code, avoids drift |
| Hash-based caching | Custom serialization + file I/O | serde_json + std::fs | Handles versioning, errors, partial writes; custom serialization is bug-prone and breaks on type changes |

**Key insight:** These problems look simple but have hidden complexity. Rayon's work-stealing prevents starvation that naive thread pools suffer. Ariadne handles terminal width, color detection, and unicode graphemes correctly. Topo_sort detects cycles and handles disconnected components. Rolling your own means rediscovering these edge cases through production bugs.

## Common Pitfalls

### Pitfall 1: Cache Invalidation Too Narrow
**What goes wrong:** Caching only function body hash, not contracts, causes stale results when precondition changes.
**Why it happens:** Easy to forget contracts are part of verification input (not just function body).
**How to avoid:** Hash formula: `SHA256(function_body_mir + requires + ensures + invariants)`. If any contract changes, hash changes.
**Warning signs:** Verification passes after strengthening precondition (should fail or re-verify).

### Pitfall 2: Rayon Thread Count = CPU Count
**What goes wrong:** Setting rayon threads = CPU count causes 100% CPU usage, system unresponsiveness, thermal throttling on laptops.
**Why it happens:** Each verification spawns Z3 subprocess, which also uses CPU (double-counted cores).
**How to avoid:** Default to `cores/2` parallel jobs. User can override with --jobs N.
**Warning signs:** Fan noise, system lag during verification, battery drain.

### Pitfall 3: Blocking I/O in Rayon Workers
**What goes wrong:** Calling std::fs::read() or waiting on subprocess in rayon worker blocks the thread, starves work-stealing.
**Why it happens:** Rayon workers are CPU-bound by design; blocking I/O breaks assumption.
**How to avoid:** Pre-load all files before rayon::par_iter(). Use spawn_blocking for subprocess waits (or keep sequential per-function).
**Warning signs:** Rayon thread pool hangs, uneven load distribution, single worker at 100% while others idle.

### Pitfall 4: Counterexample Parsing Errors Silent
**What goes wrong:** Z3 model parsing fails (malformed output), but error is swallowed, user sees "verification failed" with no counterexample.
**Why it happens:** Solver output parsing is fragile, easy to silently ignore parse failures.
**How to avoid:** Log parse failures to stderr. Return `SolverResult::Sat(None)` with warning, not silent failure.
**Warning signs:** Counterexamples missing for obvious failures (e.g., `ensures(false)`).

### Pitfall 5: JSON Output Mixed with Text
**What goes wrong:** Writing both JSON and progress messages to stdout breaks --output-format json (invalid JSON).
**Why it happens:** Debugging prints or status messages leak to stdout instead of stderr.
**How to avoid:** Strict separation: JSON to stdout, all diagnostics/progress to stderr. Test with `cargo verify --output-format json | jq`.
**Warning signs:** `jq` parse errors, IDE integration broken, JSON contains text fragments.

## Code Examples

Verified patterns from official sources:

### Rayon Parallel Iterator (Official Docs)
```rust
// Source: https://docs.rs/rayon/latest/rayon/
use rayon::prelude::*;

// Convert sequential to parallel verification
let results: Vec<FunctionResult> = functions
    .par_iter()  // Change .iter() to .par_iter()
    .map(|func| verify_single_function(func, &solver))
    .collect();

// Configure thread pool size
let pool = rayon::ThreadPoolBuilder::new()
    .num_threads(num_cpus::get() / 2)  // cores/2 for subprocess workloads
    .build()
    .unwrap();

pool.install(|| {
    functions.par_iter().map(verify_single_function).collect()
});
```

### Ariadne Error Reporting (Official Example)
```rust
// Source: https://github.com/zesterer/ariadne
use ariadne::{Report, ReportKind, Label, Color};

Report::build(ReportKind::Error, "example.rs", 12)
    .with_message("verification failed")
    .with_label(
        Label::new(("example.rs", 12..13))
            .with_message("postcondition does not hold")
            .with_color(Color::Red)
    )
    .with_note("Counterexample:\n  x = 5\n  y = -1")
    .finish()
    .eprint(("example.rs", source))
    .unwrap();
```

### FxHashMap Usage (rustc-hash)
```rust
// Source: https://docs.rs/rustc-hash/
use rustc_hash::FxHashMap;

// 2-6% faster than std::HashMap for cache keys
let mut cache: FxHashMap<[u8; 32], SolverResult> = FxHashMap::default();
cache.insert(hash, result);

// Warning: Not cryptographically secure (don't use for security-sensitive data)
```

### Criterion A/B Benchmark (Official Guide)
```rust
// Source: https://bheisler.github.io/criterion.rs/book/
use criterion::{Criterion, criterion_group, criterion_main};

fn bench_simplification_impact(c: &mut Criterion) {
    let func = make_complex_function();
    let solver = Z3Solver::with_default_config().unwrap();

    let mut group = c.benchmark_group("simplification");

    // Baseline: no simplification
    group.bench_function("without_simplify", |b| {
        b.iter(|| {
            let vcs = generate_vcs(&func, None);
            for vc in &vcs.conditions {
                solver.check_sat(&vc.script);
            }
        });
    });

    // Treatment: with simplification
    group.bench_function("with_simplify", |b| {
        b.iter(|| {
            let vcs = generate_vcs(&func, None);
            for vc in &vcs.conditions {
                solver.check_sat_simplified(&vc.script);
            }
        });
    });

    group.finish();
}
```

### Topological Sort (topo_sort crate)
```rust
// Source: https://docs.rs/topo_sort/
use topo_sort::TopoSort;

let mut topo = TopoSort::new();

// Add nodes and dependencies
topo.insert("main");
topo.insert("helper");
topo.add_dependency("main", "helper"); // main depends on helper

// Get sorted order (helper, then main)
let sorted = topo.into_vec_nodes();
assert_eq!(sorted, vec!["helper", "main"]);
```

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| std::HashMap | FxHashMap (rustc-hash) | 2018 (rustc adopted) | 2-6% faster lookups, compiler-grade performance for cache keys |
| fnv hash | fxhash (FxHasher) | 2018 | Rustc benchmarks show 6% speedup; low-quality but extremely fast for non-crypto use |
| Tokio for CPU tasks | Rayon for data parallelism | 2015 (rayon release) | Work-stealing beats async for CPU-bound tasks; tokio is for I/O concurrency |
| codespan-reporting | ariadne | 2021 (ariadne release) | Ariadne is lighter-weight, rustc-focused; codespan-reporting is more general but heavier |

**Deprecated/outdated:**
- `crossbeam::thread::scope`: Use rayon instead (higher-level, work-stealing built-in)
- `colored` crate for diagnostics: Use ariadne (handles positioning, multi-line spans, not just colors)
- Manual Z3 tactic chaining: Use `z3::Ast::simplify()` (Z3's built-in simplification is well-tuned)

## Open Questions

1. **Z3 native API simplify() vs subprocess with tactics**
   - What we know: Z3 native API has `.simplify()` method, subprocess can run `(simplify ...)` command
   - What's unclear: Which approach is faster? Does native API preserve all optimizations?
   - Recommendation: Benchmark both; if native API simplify() is sufficient, use it (less complexity); if subprocess tactics are faster, add tactic chaining

2. **Cache persistence format: JSON vs bincode**
   - What we know: JSON is human-readable, debuggable; bincode is faster, smaller
   - What's unclear: Does cache I/O time matter? (likely dwarfed by solver time)
   - Recommendation: Start with JSON (debuggability wins early), switch to bincode if profiling shows I/O bottleneck

3. **Counterexample format: variable assignments vs execution trace**
   - What we know: Z3 model gives variable assignments; execution trace requires instrumenting MIR
   - What's unclear: Do users prefer "x=5, y=-1" or "block 0 -> block 2 -> return"?
   - Recommendation: Start with variable assignments (already extractable from Z3 model), add execution trace if user feedback requests it

## Sources

### Primary (HIGH confidence)
- Rayon official docs: [GitHub - rayon-rs/rayon](https://github.com/rayon-rs/rayon), [Rust Cookbook - Data Parallelism](https://rust-lang-nursery.github.io/rust-cookbook/concurrency/parallel.html)
- Ariadne GitHub: [zesterer/ariadne](https://github.com/zesterer/ariadne), [lib.rs](https://lib.rs/crates/ariadne)
- Criterion.rs docs: [bheisler/criterion.rs](https://github.com/bheisler/criterion.rs), [Official FAQ](https://bheisler.github.io/criterion.rs/book/faq.html)
- Z3 simplification: [Online Z3 Guide - Formula Simplification](https://microsoft.github.io/z3guide/programming/Example%20Programs/Formula%20Simplification/), [Tactics Summary](https://microsoft.github.io/z3guide/docs/strategies/summary/)
- Topological sort: [topo_sort crate](https://docs.rs/topo_sort), [Rust Algorithms - Topological Sort](https://github.com/TheAlgorithms/Rust/blob/master/src/graph/topological_sort.rs)

### Secondary (MEDIUM confidence)
- Rust Performance Book - Hashing: [nnethercote.github.io/perf-book](https://nnethercote.github.io/perf-book/hashing.html)
- Tokio spawning docs: [tokio.rs/tutorial/spawning](https://tokio.rs/tokio/tutorial/spawning)
- Serde JSON: [docs.rs/serde_json](https://docs.rs/serde_json), [serde.rs error handling](https://serde.rs/error-handling.html)

### Tertiary (LOW confidence - general compiler optimization theory)
- Common subexpression elimination: [Wikipedia](https://en.wikipedia.org/wiki/Common_subexpression_elimination)
- Constant folding: [ScienceDirect Topics](https://www.sciencedirect.com/topics/computer-science/constant-folding)
- Dead code elimination: [ScienceDirect Topics](https://www.sciencedirect.com/topics/computer-science/dead-code-elimination)

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH - Rayon, rustc-hash, ariadne, criterion all verified via official docs and codebase usage
- Architecture: HIGH - Patterns verified via official examples (rayon par_iter, ariadne reports, criterion A/B)
- Pitfalls: MEDIUM - Derived from Rust best practices and rayon docs; cache invalidation and thread count are well-documented, others inferred
- Formula simplification: MEDIUM - Z3 docs confirm simplify() API exists, but impact on verification time requires measurement

**Research date:** 2026-02-11
**Valid until:** ~60 days (stable Rust ecosystem; rayon/criterion APIs rarely change)
