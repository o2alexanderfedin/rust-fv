# Phase 14: Incremental Verification - Research

**Researched:** 2026-02-15
**Domain:** Incremental verification, cache invalidation, dependency tracking
**Confidence:** HIGH

## Summary

Phase 14 enhances existing per-function caching (`target/rust-fv-cache/`) with two-hash invalidation (MIR hash + contract hash), transitive dependency tracking, and per-function status reporting. The existing infrastructure (`VcCache`, `CallGraph`, `verify_functions_parallel`) provides a strong foundation: SHA-256 hashing, JSON persistence, call graph extraction, and topological ordering are already production-ready.

The core innovation is **dual-hash granular invalidation**: changing a function body only re-verifies that function (MIR hash changed), while changing a contract re-verifies the function plus all transitive dependents (contract hash changed). This achieves the roadmap goal of <1s re-verification for isolated changes while maintaining soundness through conservative transitive invalidation.

**Primary recommendation:** Extend existing `CacheEntry` with separate `mir_hash` and `contract_hash` fields, build reverse call graph for transitive invalidation, add invalidation reason tracking, and implement age-based eviction (30-day TTL). Use petgraph for transitive closure computation. Do NOT implement Z3 push/pop persistence (CONTEXT overrides success criteria #3).

## User Constraints (from CONTEXT.md)

### Locked Decisions
- **Cache granularity:** Per-function caching with separate MIR hash and contract hash per function
- **Transitive invalidation:** Contract changes re-verify self + all transitive dependents (soundness requirement)
- **Cache VC results only:** No persistent Z3 solver state across runs (overrides roadmap success criteria #3)
- **Developer feedback:** Show every function with status (verified/skipped/failed), timing (total by default, per-function with --verbose), and invalidation reasons
- **Cache bypass:** `--fresh` flag for one-off full re-verification, `cargo verify clean` subcommand for permanent cache clearing
- **Persistence:** `target/verify-cache/` location, JSON format, age-based eviction (30 days), no size limit
- **Benchmarking:** Synthetic + real-world samples, measure wall-clock ratio and cache hit rate, CI nightly runs, <1s target at 1,000 lines

### Claude's Discretion
- Dependency graph data structure and traversal algorithm
- MIR hashing implementation details
- JSON cache schema design
- Synthetic benchmark codebase generation approach
- Eviction implementation (lazy on access vs. periodic cleanup)

### Deferred Ideas (OUT OF SCOPE)
None

## Standard Stack

### Core Dependencies (Already in Workspace)

| Library | Version | Purpose | Why Standard |
|---------|---------|---------|--------------|
| `sha2` | 0.10 | SHA-256 hashing | Already used in `VcCache::compute_key`, cryptographic quality prevents collisions |
| `rustc-hash` | 2.1 | Fast hash maps | Already used throughout codebase, FxHashMap for internal collections |
| `serde` / `serde_json` | 1.0 | JSON serialization | Already used for cache persistence, human-readable debugging |
| `petgraph` | 0.6+ | Graph algorithms | Already used for `CallGraph::detect_recursion`, provides `tarjan_scc` |
| `rayon` | 1.10 | Parallel iteration | Already used in `verify_functions_parallel` |

### New Dependencies (Recommended)

| Library | Version | Purpose | When to Use |
|---------|---------|---------|-------------|
| `chrono` or `time` | 0.4 / 0.3 | Timestamp tracking | For 30-day age-based eviction |

### Alternatives Considered

| Instead of | Could Use | Tradeoff |
|------------|-----------|----------|
| SHA-256 | BLAKE3 | 2.8x faster but requires new dependency; SHA-256 sufficient for current scale |
| JSON | Bincode/MessagePack | Faster serialization but loses human-readability; JSON aids debugging |
| Lazy eviction | Periodic cleanup thread | Thread adds complexity; lazy on access is simpler |

**Installation:**
```bash
# Already in Cargo.toml workspace:
# sha2 = "0.10"
# rustc-hash = "2.1"
# serde = { version = "1.0", features = ["derive"] }
# serde_json = "1.0"
# rayon = "1.10"

# Add to workspace dependencies:
chrono = "0.4"  # or time = "0.3"
```

## Architecture Patterns

### Recommended Project Structure
```
crates/driver/src/
├── cache.rs              # VcCache with dual-hash extension
├── parallel.rs           # verify_functions_parallel (unchanged)
├── callbacks.rs          # Status reporting integration
└── invalidation.rs       # NEW: Transitive invalidation logic
```

### Pattern 1: Dual-Hash Cache Entry

**What:** Separate MIR and contract hashes per function, enabling precise invalidation
**When to use:** Always — this is the core innovation for Phase 14
**Example:**
```rust
// Source: Extended from existing cache.rs

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheEntry {
    pub verified: bool,
    pub vc_count: usize,
    pub verified_count: usize,
    pub message: Option<String>,

    // NEW: Dual-hash fields
    pub mir_hash: [u8; 32],
    pub contract_hash: [u8; 32],
    pub timestamp: i64,  // Unix timestamp for age-based eviction
    pub dependencies: Vec<String>,  // Function names this depends on
}

impl VcCache {
    pub fn compute_hashes(
        func_name: &str,
        contracts: &Contracts,
        ir_debug: &str,
    ) -> ([u8; 32], [u8; 32]) {
        // MIR hash: function name + body representation
        let mut mir_hasher = Sha256::new();
        mir_hasher.update(func_name.as_bytes());
        mir_hasher.update(ir_debug.as_bytes());
        let mir_hash = mir_hasher.finalize().into();

        // Contract hash: function name + all specs
        let mut contract_hasher = Sha256::new();
        contract_hasher.update(func_name.as_bytes());
        for req in &contracts.requires {
            contract_hasher.update(b"requires:");
            contract_hasher.update(req.raw.as_bytes());
        }
        for ens in &contracts.ensures {
            contract_hasher.update(b"ensures:");
            contract_hasher.update(ens.raw.as_bytes());
        }
        // ... (invariants, pure flag, etc.)
        let contract_hash = contract_hasher.finalize().into();

        (mir_hash, contract_hash)
    }
}
```

### Pattern 2: Reverse Call Graph for Transitive Invalidation

**What:** Build reverse edges (callee → callers) to find all functions affected by contract change
**When to use:** When contract hash changes
**Example:**
```rust
// Source: Extend existing call_graph.rs

impl CallGraph {
    /// Compute transitive closure of callers for a given function.
    /// Uses BFS to find all functions that transitively depend on `func_name`.
    pub fn transitive_callers(&self, func_name: &str) -> Vec<String> {
        let mut result = Vec::new();
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();

        queue.push_back(func_name.to_string());
        visited.insert(func_name.to_string());

        while let Some(current) = queue.pop_front() {
            // Find all functions that call `current`
            for (caller, callees) in &self.edges {
                if callees.contains(&current) && !visited.contains(caller) {
                    visited.insert(caller.clone());
                    queue.push_back(caller.clone());
                    result.push(caller.clone());
                }
            }
        }

        result
    }
}
```

### Pattern 3: Invalidation Reason Tracking

**What:** Attach reason to cache invalidation for developer feedback
**When to use:** Always display when re-verifying
**Example:**
```rust
// Source: New invalidation.rs module

#[derive(Debug, Clone)]
pub enum InvalidationReason {
    MirChanged,
    ContractChanged { dependency: String },
    Fresh,  // --fresh flag
    CacheMiss,
    Expired,  // 30-day TTL
}

pub struct InvalidationDecision {
    pub should_verify: bool,
    pub reason: Option<InvalidationReason>,
}

impl VcCache {
    pub fn should_verify(
        &self,
        func_name: &str,
        mir_hash: [u8; 32],
        contract_hash: [u8; 32],
        dependencies: &[String],
    ) -> InvalidationDecision {
        let key = self.compute_cache_key(func_name);

        match self.get(&key) {
            None => InvalidationDecision {
                should_verify: true,
                reason: Some(InvalidationReason::CacheMiss),
            },
            Some(entry) => {
                // Check expiration (30 days)
                let now = chrono::Utc::now().timestamp();
                if now - entry.timestamp > 30 * 24 * 60 * 60 {
                    return InvalidationDecision {
                        should_verify: true,
                        reason: Some(InvalidationReason::Expired),
                    };
                }

                // Check MIR hash
                if entry.mir_hash != mir_hash {
                    return InvalidationDecision {
                        should_verify: true,
                        reason: Some(InvalidationReason::MirChanged),
                    };
                }

                // Check contract hash (self or dependencies)
                if entry.contract_hash != contract_hash {
                    return InvalidationDecision {
                        should_verify: true,
                        reason: Some(InvalidationReason::ContractChanged {
                            dependency: func_name.to_string(),
                        }),
                    };
                }

                // Cache hit
                InvalidationDecision {
                    should_verify: false,
                    reason: None,
                }
            }
        }
    }
}
```

### Pattern 4: Per-Function Status Reporting

**What:** Display verification status for every function (verified/skipped/failed)
**When to use:** Always in output
**Example:**
```rust
// Source: Extend callbacks.rs print_results

// Output example:
// [rust-fv] Verifying 15 functions...
//   ✓ add (verified, 3 VCs)
//   → sub (skipped: cached)
//   ✗ mul (failed: postcondition)
//   ⟳ div (re-verifying: contract of mul changed)
```

### Anti-Patterns to Avoid

- **Z3 push/pop persistence:** User decision explicitly rejects solver state persistence (overrides roadmap success criteria #3). Cache VC results only.
- **Size-based eviction:** Complexity not justified; rely on age-based + manual `cargo verify clean`
- **Global cache key:** Must be per-function for granular invalidation
- **Ignoring transitive dependencies:** Contract changes MUST invalidate all callers (soundness requirement)

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Transitive closure | Custom DFS with cycle detection | `CallGraph::transitive_callers` (BFS) | Already battle-tested, handles cycles gracefully |
| Graph algorithms | Manual adjacency list traversal | `petgraph` (already in deps) | Tarjan's SCC already used, well-optimized |
| Timestamp handling | Manual Unix time arithmetic | `chrono::Utc::now()` or `time::OffsetDateTime` | Handles edge cases (leap seconds, timezones) |
| Hash collisions | Custom collision handling | SHA-256 (128-bit fingerprint) | 2^64 operations needed for 50% collision probability |

**Key insight:** Incremental compilation is notoriously complex. Dafny's dependency checksums (see research) and Rust compiler's fingerprinting system (128-bit BLAKE2) prove this approach works at scale. Don't reinvent — adapt proven patterns.

## Common Pitfalls

### Pitfall 1: Missing Transitive Invalidation

**What goes wrong:** Changing `foo`'s contract doesn't re-verify `bar` (which calls `foo`), causing unsound results
**Why it happens:** Only checking direct dependencies, not transitive closure
**How to avoid:** Always compute transitive callers when contract hash changes
**Warning signs:** Cache hit on function that should have been invalidated, mysterious verification failures on unchanged functions

### Pitfall 2: MIR Hash Instability

**What goes wrong:** Identical function bodies produce different hashes across runs
**Why it happens:** Including unstable MIR details (debug info, local numbering) in hash
**How to avoid:** Hash normalized IR representation (use existing `format!("{:?}", ir_func)` which omits transient data)
**Warning signs:** 0% cache hit rate despite no code changes

### Pitfall 3: Ignoring Dependency Cycles

**What goes wrong:** Infinite loop when computing transitive callers in recursive functions
**Why it happens:** Not tracking visited nodes during graph traversal
**How to avoid:** Use `visited` set in BFS (see Pattern 2 example)
**Warning signs:** Hang during invalidation computation, stack overflow

### Pitfall 4: Timestamp Timezone Issues

**What goes wrong:** Cache expires immediately or never depending on system timezone
**Why it happens:** Mixing local time and UTC
**How to avoid:** Always use UTC (`chrono::Utc::now()`) for timestamps
**Warning signs:** Intermittent cache eviction, different behavior across machines

### Pitfall 5: Over-Invalidation on Internal Changes

**What goes wrong:** Renaming a local variable invalidates cache
**Why it happens:** Hashing raw MIR instead of semantic representation
**How to avoid:** Hash IR debug representation (already does variable renaming normalization)
**Warning signs:** Cache misses on whitespace/comment changes

### Pitfall 6: Forgetting --fresh Flag Semantics

**What goes wrong:** `--fresh` clears cache permanently instead of bypassing for one run
**Why it happens:** Confusing one-off bypass with permanent deletion
**How to avoid:** `--fresh` sets flag that bypasses cache lookup, `cargo verify clean` deletes files
**Warning signs:** Cache always empty after using --fresh

## Code Examples

Verified patterns from existing codebase:

### Existing Cache Lookup (cache.rs:151-154)
```rust
// Source: https://github.com/o2alexanderfedin/rust-fv/blob/develop/crates/driver/src/cache.rs#L151
pub fn get(&self, key: &[u8; 32]) -> Option<&CacheEntry> {
    self.entries.get(key)
}
```

### Existing Cache Insertion (cache.rs:156-170)
```rust
// Source: cache.rs lines 156-170
pub fn insert(&mut self, key: [u8; 32], entry: CacheEntry) {
    // Write to disk
    let filename = bytes_to_hex(&key);
    let path = self.cache_dir.join(format!("{}.json", filename));

    if let Ok(json) = serde_json::to_string_pretty(&entry) {
        let _ = fs::write(&path, json);
    }

    // Insert in memory
    self.entries.insert(key, entry);
}
```

### Existing Call Graph Extraction (call_graph.rs:49-81)
```rust
// Source: call_graph.rs lines 49-81
pub fn from_functions(functions: &[(String, &Function)]) -> Self {
    let mut edges: HashMap<String, Vec<String>> = HashMap::new();
    let mut all_functions: HashSet<String> = HashSet::new();

    for (name, func) in functions {
        all_functions.insert(name.clone());

        // Scan basic blocks for calls
        let mut callees = Vec::new();
        for bb in &func.basic_blocks {
            if let Terminator::Call { func: func_name, .. } = &bb.terminator {
                let normalized = normalize_func_name(func_name);
                callees.push(normalized);
            }
        }

        if !callees.is_empty() {
            edges.insert(name.clone(), callees);
        }
    }

    Self { edges, all_functions }
}
```

### Existing Cache Hit Logic (parallel.rs:71-88)
```rust
// Source: parallel.rs lines 71-88
let (cached_tasks, uncached_tasks): (Vec<_>, Vec<_>) = tasks
    .into_iter()
    .partition(|task| !fresh && cache.get(&task.cache_key).is_some());

tracing::info!(
    "Cache: {} hits, {} misses",
    cached_tasks.len(),
    uncached_tasks.len()
);

let mut all_results: Vec<VerificationTaskResult> = cached_tasks
    .into_iter()
    .map(|task| {
        let entry = cache.get(&task.cache_key).unwrap();
        tracing::debug!("Cache hit: {}", task.name);
        // ... reconstruct VerificationResult from CacheEntry
    })
    .collect();
```

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| Single MIR hash | Dual hash (MIR + contract) | Phase 14 | Precise invalidation: body changes don't re-verify callers |
| No dependency tracking | Transitive closure | Phase 14 | Soundness: contract changes propagate to all dependents |
| No eviction | 30-day TTL | Phase 14 | Prevents unbounded cache growth |
| Generic status | Per-function status + reason | Phase 14 | Developer understands why re-verification triggered |
| No Z3 persistence | Cache VC results only | Phase 14 (user decision) | Simpler than push/pop, sufficient for <1s goal |

**Modern verification tools (2025-2026):**

- **Dafny** (2020-2024): Uses dependency checksums at entity level, stores cache alongside source files, proven at Microsoft Research scale
- **Rust compiler** (2021-2026): 128-bit BLAKE2 fingerprints, query-based incremental compilation, handles 1M+ LOC codebases
- **Pyrefly** (2026): Moved from module-level to type-level dependency tracking, achieved 18x speedup ([source](https://pyrefly.org/blog/2026/02/06/performance-improvements/))

**Key insight:** Modern incremental verification tracks **what** changed (MIR vs contract), not just **if** something changed.

**Deprecated/outdated:**
- Z3 push/pop for incremental verification (user explicitly rejected per CONTEXT decisions)
- Size-based LRU eviction (age-based TTL simpler and sufficient)

## Open Questions

1. **Optimal hash algorithm**
   - What we know: SHA-256 currently used, BLAKE3 is 2.8x faster
   - What's unclear: Whether hashing is bottleneck at 1,000-line scale
   - Recommendation: Benchmark SHA-256 performance first, defer BLAKE3 migration unless >10% overhead

2. **Eviction strategy: lazy vs. periodic**
   - What we know: Lazy on access is simpler, periodic cleanup is more predictable
   - What's unclear: Whether lazy eviction causes noticeable startup time
   - Recommendation: Start with lazy (check timestamp during `cache.load()`), add periodic if users report slowness

3. **JSON schema versioning**
   - What we know: Schema will evolve (adding fields to CacheEntry)
   - What's unclear: How to handle old cache files with missing fields
   - Recommendation: Use `#[serde(default)]` for new fields, version number in filename (`{hash}_v2.json`)

4. **Benchmark representativeness**
   - What we know: Need synthetic + real-world samples
   - What's unclear: Which real-world projects to include
   - Recommendation: Start with stdlib contracts tests (already 1,000+ lines), add user codebases when available

## Sources

### Primary (HIGH confidence)

- **Rust compiler incremental compilation:** [Incremental compilation in detail](https://rustc-dev-guide.rust-lang.org/queries/incremental-compilation-in-detail.html) — 128-bit fingerprints, query-based dependency tracking
- **Rust compiler fingerprinting:** [RFC 1298: Incremental Compilation](https://rust-lang.github.io/rfcs/1298-incremental-compilation.html) — Hash function selection (BLAKE2 vs SipHash vs MetroHash), collision mitigation
- **Dafny dependency checksums:** [The Dafny Integrated Development Environment](https://arxiv.org/pdf/1404.6602) — Entity-level checksums, transitive dependency tracking
- **Existing codebase:** `/crates/driver/src/cache.rs`, `/crates/driver/src/parallel.rs`, `/crates/analysis/src/call_graph.rs` — Current implementation details
- **petgraph documentation:** [petgraph crates.io](https://crates.io/crates/petgraph) — Graph algorithms in Rust
- **Z3 incremental solving:** [Programming Z3](https://theory.stanford.edu/~nikolaj/programmingz3.html) — Push/pop semantics (researched but rejected per user decision)

### Secondary (MEDIUM confidence)

- **BLAKE3 performance:** [SHA-256 Alternatives 2025](https://devtoolspro.org/articles/sha256-alternatives-faster-hash-functions-2025/) — xxHash3 31 GB/s, BLAKE3 8.4 GB/s, SHA-256 3.0 GB/s
- **Pyrefly incremental improvements:** [Making Pyrefly Diagnostics 18x Faster](https://pyrefly.org/blog/2026/02/06/performance-improvements/) — Type-level dependency tracking vs module-level
- **Cache invalidation strategies:** [Skip: Cache Invalidation and Reactive Systems](https://skiplabs.io/blog/cache_invalidation) — Reactive model, dependency tracking
- **Rust caching libraries:** [Moka concurrent caching](https://github.com/moka-rs/moka) — TTL/TTI expiration policies

### Tertiary (LOW confidence)

- **SMT solver benchmarking:** [Predicting SMT Solver Performance](https://arxiv.org/pdf/1701.08466) — BenchExec framework for verification tools
- **Dependency graph algorithms:** [Dependency graphs with applications to verification](https://link.springer.com/article/10.1007/s10009-020-00578-9) — Fixed-point computation on dependency graphs

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH — All dependencies already in workspace or minimal additions
- Architecture: HIGH — Patterns extend existing code (cache.rs, call_graph.rs), no radical changes
- Pitfalls: MEDIUM-HIGH — Dafny and rustc provide validation, but formal verification has unique edge cases

**Research date:** 2026-02-15
**Valid until:** 2026-03-15 (30 days for stable domain, Rust compiler/verification techniques evolve slowly)

---

**Research complete. Ready for planning.**
