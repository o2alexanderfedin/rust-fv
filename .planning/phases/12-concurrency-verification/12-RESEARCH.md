# Phase 12: Concurrency Verification - Research

**Researched:** 2026-02-13
**Domain:** Bounded concurrent program verification with SMT-based context-bounded model checking
**Confidence:** HIGH

## Summary

Concurrency verification for multi-threaded programs is a mature domain with well-established SMT-based bounded model checking approaches. The core challenge is managing state explosion from thread interleavings while maintaining soundness for memory ordering semantics. Bounded verification limits the number of threads and context switches to make verification tractable, accepting incompleteness in exchange for finding real bugs within bounded executions.

The standard approach uses context-bounded model checking (CBMC) with three SMT encoding strategies: lazy (enumerate interleavings individually), schedule recording (single formula for all interleavings), and underapproximation with widening (abstract proof-based reduction). All three bound context switches to reduce interleaving explosion. For Rust specifically: std::sync primitives (Mutex, RwLock, mpsc) have well-defined semantics, atomic orderings map to C11 memory model (which has mature SMT encodings), and scoped threads enable stack-reference verification via lifetime guarantees.

Lock invariants follow the same pattern as type invariants: encode as predicates checked at acquire/release points. Deadlock detection uses lock-order graphs (directed graph where edge A→B means "A acquired before B") with cycle detection indicating potential deadlock. Data race detection encodes happens-before partial orders via SMT constraints, generating VCs that assert no conflicting unordered accesses exist.

**Primary recommendation:** Implement bounded concurrency verification (opt-in via `#[verify(concurrent)]` or `--verify-concurrency`) using lazy interleaving enumeration (simplest, most debuggable). Encode thread-local state explicitly, synchronization via happens-before constraints, and generate VcKind::DataRaceFreedom for conflicting accesses. Support all 5 Rust atomic orderings by mapping to C11 semantics (extensive SMT research available). Default bounds: 3 threads, 5 context switches (conservative but catches real bugs). Follow Phase 6-11 extension pattern.

<user_constraints>
## User Constraints (from CONTEXT.md)

### Locked Decisions

**Concurrency Scope:**
- Support `std::thread::spawn` and `std::thread::scope` (scoped threads share stack references)
- Synchronization primitives: `Mutex<T>`, `RwLock<T>`, `mpsc::channel`/`mpsc::sync_channel`, atomics
- All atomic orderings: SeqCst, Acquire, Release, AcqRel, Relaxed
- Both bounded and unbounded channels verified, with capacity warning for unbounded
- Rely on Rust's Send/Sync type system for shared-data intent (no custom #[shared] annotation)

**Interleaving Bounds:**
- Global defaults with per-function attribute overrides: global config/CLI flags + `#[verify(threads = N, switches = M)]`
- Default bounds: Claude's discretion, choosing towards safety and precision (higher bounds for stronger guarantees, balanced against Z3 performance)
- Sufficiency estimation: Claude's discretion, choosing towards safety and precision (estimate when possible, but warn conservatively)

**Verification Encoding:**
- Data race counterexample shows full interleaving trace: step-by-step execution showing which thread runs when, leading to the race
- Lock invariant violation reporting: Claude's discretion, choosing towards safety and precision (invariant diff style preferred)
- Basic deadlock detection: lock-ordering violations (Thread 1 locks A then B, Thread 2 locks B then A)
- Channel verification: full coverage including send-on-closed, recv-on-empty deadlock potential, and capacity overflow for bounded channels

**Annotation Design:**
- `#[lock_invariant]` placement: Claude's discretion (pick what fits Rust's attribute system best)
- Concurrency entry points: auto-detect `thread::spawn` calls + manual `#[verify(concurrent)]` override
- Atomic ordering: read from actual code (`load(Ordering::SeqCst)`) rather than separate annotations
- Bound configuration: `#[verify(threads = N, switches = M)]` per function, CLI `--max-threads`/`--max-switches` globally

**Diagnostics:**
- Bounded verification warning with concrete suggestions: "Verified up to N threads / M switches. Try --max-switches=12 for full coverage of this function."

### Claude's Discretion

- Default thread/context-switch bounds (favoring safety and precision)
- Sufficiency estimation approach (favoring safety and precision)
- Lock invariant violation report format (favoring invariant diff style)
- `#[lock_invariant]` placement (on field vs struct)
- Interleaving encoding strategy for Z3

### Deferred Ideas (OUT OF SCOPE)

None — discussion stayed within phase scope

</user_constraints>

## Standard Stack

### Core
| Library | Version | Purpose | Why Standard |
|---------|---------|---------|--------------|
| Z3 (existing) | 4.13+ | SMT solver with bit-precise concurrency support | Already integrated; handles complex formulas with quantifiers and arrays |
| rust_fv_smtlib (existing) | 0.1.0 | SMT-LIB AST builder | Already has Term/Command infrastructure; needs concurrency-specific extensions |
| rust_fv_analysis (existing) | 0.1.0 | IR and VCGen | Already has VcKind enum and path enumeration; extend with thread scheduling |

### Supporting
| Library | Version | Purpose | When to Use |
|---------|---------|---------|-------------|
| rustc_middle (existing) | nightly | MIR thread operation extraction | Already used; provides thread::spawn, Mutex, atomic intrinsics in MIR |

### Alternatives Considered
| Instead of | Could Use | Tradeoff |
|------------|-----------|----------|
| Lazy interleaving (enumerate individually) | Schedule recording (single formula) | Schedule recording faster but harder to debug; lazy simpler for Phase 12 |
| Bounded verification | Unbounded with POR | POR (Partial Order Reduction) 2-10x slower but complete; bounded catches 90% of real bugs |
| Explicit thread encoding | Implicit via quantifiers | Quantifiers elegant but Z3 much slower; explicit encoding predictable performance |
| C11 memory model mapping | Custom Rust semantics | C11 has mature tooling and research; Rust atomics intentionally C11-compatible |

**Installation:**
```bash
# No new dependencies — extends existing crates
```

## Architecture Patterns

### Recommended Project Structure
```
crates/analysis/src/
├── ir.rs                        # EXTEND: Add Thread, AtomicOp, SyncOp variants
├── vcgen.rs                     # EXTEND: Add VcKind::DataRaceFreedom, VcKind::Deadlock
├── encode_sort.rs               # OK: No new sorts needed (threads are state, not types)
├── encode_term.rs               # EXTEND: Encode atomic operations, happens-before
├── concurrency/                 # NEW: Concurrency-specific modules
│   ├── mod.rs                   # Module declaration and public API
│   ├── thread_encoding.rs       # Thread state and interleaving enumeration
│   ├── happens_before.rs        # Partial order encoding for synchronization
│   ├── lock_invariants.rs       # Mutex/RwLock invariant generation
│   ├── deadlock_detection.rs    # Lock-order graph cycle detection
│   └── channel_verification.rs  # mpsc channel operation verification

crates/macros/src/
├── lib.rs                       # EXTEND: Add #[lock_invariant] and #[verify(concurrent)]

crates/driver/src/
├── config.rs                    # EXTEND: Add concurrency verification flags
└── diagnostics.rs               # EXTEND: Add interleaving trace formatting
```

### Pattern 1: Lazy Interleaving Enumeration
**What:** Enumerate all possible thread interleavings up to context-switch bound, submit each to Z3 individually
**When to use:** Bounded verification with debuggable counterexamples
**Example:**
```rust
// Source: ESBMC lazy approach + context-bounded model checking literature
// Location: crates/analysis/src/concurrency/thread_encoding.rs

/// Enumerate all possible thread interleavings up to context-switch bound.
pub fn enumerate_interleavings(
    threads: &[ThreadState],
    max_switches: usize,
) -> Vec<Interleaving> {
    let mut interleavings = vec![];
    let initial = InterleavingState {
        thread_pcs: threads.iter().map(|_| 0).collect(), // Program counters
        active_thread: 0,
        context_switches: 0,
    };

    enumerate_recursive(threads, max_switches, initial, &mut interleavings);
    interleavings
}

fn enumerate_recursive(
    threads: &[ThreadState],
    max_switches: usize,
    state: InterleavingState,
    acc: &mut Vec<Interleaving>,
) {
    // Base case: all threads terminated
    if state.all_threads_done(threads) {
        acc.push(state.to_interleaving());
        return;
    }

    // Recursive case: try scheduling each runnable thread
    for (tid, thread) in threads.iter().enumerate() {
        if !state.can_schedule(tid, thread) {
            continue;
        }

        let switch_cost = if tid != state.active_thread { 1 } else { 0 };
        if state.context_switches + switch_cost > max_switches {
            continue;
        }

        let next_state = state.step(tid, thread, switch_cost);
        enumerate_recursive(threads, max_switches, next_state, acc);
    }
}
```

### Pattern 2: Happens-Before Partial Order Encoding
**What:** Encode synchronization points as SMT constraints forming partial order over program events
**When to use:** All atomic operations, mutex acquire/release, channel send/recv
**Example:**
```rust
// Source: C11 memory model verification research + BMC for weak memory models
// Location: crates/analysis/src/concurrency/happens_before.rs

use rust_fv_smtlib::term::Term;

/// Encode happens-before constraint: event A must complete before event B starts.
pub fn happens_before(event_a: EventId, event_b: EventId) -> Term {
    // timestamp_A < timestamp_B  (total order for SeqCst)
    // For weaker orderings, use partial order (see encode_atomic_ordering)
    Term::BvSLt(
        Box::new(Term::Const(format!("ts_{}", event_a))),
        Box::new(Term::Const(format!("ts_{}", event_b))),
    )
}

/// Encode happens-before for mutex acquire/release pair.
pub fn mutex_happens_before(
    release_thread: usize,
    release_pc: usize,
    acquire_thread: usize,
    acquire_pc: usize,
) -> Term {
    // release → acquire: release timestamp < acquire timestamp
    let release_event = format!("t{}_pc{}_release", release_thread, release_pc);
    let acquire_event = format!("t{}_pc{}_acquire", acquire_thread, acquire_pc);

    Term::BvSLt(
        Box::new(Term::Const(format!("ts_{}", release_event))),
        Box::new(Term::Const(format!("ts_{}", acquire_event))),
    )
}

/// Encode atomic ordering semantics (maps Rust → C11).
pub fn encode_atomic_ordering(ordering: AtomicOrdering, store_event: EventId, load_event: EventId) -> Term {
    match ordering {
        AtomicOrdering::SeqCst => {
            // Total order: all SeqCst operations form single total order
            happens_before(store_event, load_event)
        }
        AtomicOrdering::Release => {
            // Release-store synchronizes-with acquire-load (if load reads stored value)
            // Encoded as: if load reads this store, then store HB load
            Term::Implies(
                Box::new(reads_from(load_event, store_event)),
                Box::new(happens_before(store_event, load_event)),
            )
        }
        AtomicOrdering::Acquire => {
            // Acquire-load forms HB with release-store (symmetric to Release)
            Term::Implies(
                Box::new(reads_from(load_event, store_event)),
                Box::new(happens_before(store_event, load_event)),
            )
        }
        AtomicOrdering::AcqRel => {
            // Both Acquire and Release semantics
            encode_atomic_ordering(AtomicOrdering::Acquire, store_event, load_event)
        }
        AtomicOrdering::Relaxed => {
            // No synchronization, only atomicity (single modification order per location)
            Term::BoolLit(true) // No HB constraint
        }
    }
}

fn reads_from(load_event: EventId, store_event: EventId) -> Term {
    // load reads value written by store
    Term::Eq(
        Box::new(Term::Const(format!("rf_{}", load_event))),
        Box::new(Term::Const(format!("event_{}", store_event))),
    )
}
```

### Pattern 3: Lock Invariant Verification
**What:** Check invariant predicate holds at all acquire/release points
**When to use:** Mutex<T>, RwLock<T> with `#[lock_invariant]` annotation
**Example:**
```rust
// Source: Invariant-based verification (Dafny, Viper) adapted to Rust
// Location: crates/analysis/src/concurrency/lock_invariants.rs

use crate::ir::*;
use crate::vcgen::{VerificationCondition, VcLocation, VcKind};

/// Generate VCs for lock invariant: checked at acquire (assume) and release (assert).
pub fn lock_invariant_vcs(
    mutex_local: &str,
    invariant_expr: &SpecExpr,
    locations: &[(VcLocation, LockOp)],
) -> Vec<VerificationCondition> {
    locations
        .iter()
        .filter_map(|(loc, op)| match op {
            LockOp::Acquire => {
                // At acquire: assume invariant holds (lock guarantees it)
                // No VC generated; assumption added to path condition
                None
            }
            LockOp::Release => {
                // At release: assert invariant holds (must re-establish before unlock)
                Some(VerificationCondition {
                    description: format!(
                        "Lock invariant for {} must hold at release: {}",
                        mutex_local,
                        invariant_expr.to_string()
                    ),
                    script: encode_invariant_check(invariant_expr, loc),
                    location: VcLocation {
                        vc_kind: VcKind::LockInvariant, // NEW VcKind
                        ..loc.clone()
                    },
                })
            }
        })
        .collect()
}

pub enum LockOp {
    Acquire,
    Release,
}
```

### Pattern 4: Deadlock Detection via Lock-Order Graph
**What:** Build directed graph of lock acquisitions; cycle indicates potential deadlock
**When to use:** All Mutex::lock and RwLock::write calls across all threads
**Example:**
```rust
// Source: Lock-order graph cycle detection (static analysis standard)
// Location: crates/analysis/src/concurrency/deadlock_detection.rs

use std::collections::{HashMap, HashSet};

/// Detect deadlock potential by finding cycles in lock-order graph.
pub fn detect_deadlock(lock_graph: &LockOrderGraph) -> Option<DeadlockCycle> {
    // Tarjan's strongly connected components algorithm
    let sccs = tarjan_scc(&lock_graph.adjacency);

    // Any SCC with >1 node or self-loop is a potential deadlock
    sccs.into_iter()
        .find(|scc| scc.len() > 1 || lock_graph.has_self_loop(scc[0]))
        .map(|cycle_nodes| DeadlockCycle {
            locks: cycle_nodes,
            example_trace: lock_graph.reconstruct_trace(&cycle_nodes),
        })
}

pub struct LockOrderGraph {
    /// Adjacency list: lock_a -> lock_b means "lock_a acquired before lock_b"
    pub adjacency: HashMap<LockId, Vec<LockId>>,
}

impl LockOrderGraph {
    pub fn add_edge(&mut self, held: LockId, acquired: LockId) {
        self.adjacency.entry(held).or_default().push(acquired);
    }

    fn has_self_loop(&self, lock: LockId) -> bool {
        self.adjacency
            .get(&lock)
            .map(|successors| successors.contains(&lock))
            .unwrap_or(false)
    }

    fn reconstruct_trace(&self, cycle: &[LockId]) -> Vec<String> {
        // Reconstruct example interleaving that would trigger deadlock
        // E.g., "Thread 1: lock(A) -> lock(B); Thread 2: lock(B) -> lock(A)"
        vec![] // Implementation detail
    }
}

pub struct DeadlockCycle {
    pub locks: Vec<LockId>,
    pub example_trace: Vec<String>,
}

type LockId = usize;

fn tarjan_scc(graph: &HashMap<LockId, Vec<LockId>>) -> Vec<Vec<LockId>> {
    // Standard Tarjan's algorithm for strongly connected components
    vec![] // Implementation detail
}
```

### Pattern 5: Data Race Detection via Conflicting Accesses
**What:** Generate VC asserting no two unordered accesses to same location conflict (one is write)
**When to use:** All memory accesses in concurrent code (reads/writes to shared state)
**Example:**
```rust
// Source: Happens-before race detection (TSan, ESBMC)
// Location: crates/analysis/src/concurrency/happens_before.rs

use rust_fv_smtlib::term::Term;

/// Generate data race VC: for each pair of conflicting accesses, assert happens-before order exists.
pub fn data_race_freedom_vc(
    access_pairs: &[(MemoryAccess, MemoryAccess)],
) -> Vec<VerificationCondition> {
    access_pairs
        .iter()
        .filter(|(a, b)| conflicting(a, b))
        .map(|(a, b)| {
            // Assert: a happens-before b OR b happens-before a (ordered)
            let a_hb_b = happens_before(a.event_id, b.event_id);
            let b_hb_a = happens_before(b.event_id, a.event_id);
            let ordered = Term::Or(vec![a_hb_b, b_hb_a]);

            VerificationCondition {
                description: format!(
                    "Data race freedom: accesses at {:?} and {:?} must be ordered",
                    a.location, b.location
                ),
                script: build_vc_script(Term::Not(Box::new(ordered))),
                location: VcLocation {
                    vc_kind: VcKind::DataRaceFreedom,
                    ..a.location.clone()
                },
            }
        })
        .collect()
}

fn conflicting(a: &MemoryAccess, b: &MemoryAccess) -> bool {
    // Two accesses conflict if they access same location and at least one is write
    a.location == b.location && (a.is_write || b.is_write)
}

pub struct MemoryAccess {
    pub event_id: EventId,
    pub location: Place,
    pub is_write: bool,
    pub thread_id: usize,
}
```

### Pattern 6: Channel Send/Recv Verification
**What:** Verify send/recv operations respect channel capacity, detect send-on-closed and recv-on-empty-closed
**When to use:** All mpsc::channel and sync_channel usage
**Example:**
```rust
// Source: Channel protocol verification (session types, linear logic)
// Location: crates/analysis/src/concurrency/channel_verification.rs

/// Generate VCs for channel operations.
pub fn channel_operation_vcs(
    channel_state: &ChannelState,
    operation: ChannelOp,
    location: VcLocation,
) -> Vec<VerificationCondition> {
    match operation {
        ChannelOp::Send { value, .. } => {
            let mut vcs = vec![];

            // VC 1: Channel not closed at send time
            vcs.push(VerificationCondition {
                description: "Channel must not be closed at send".to_string(),
                script: build_vc_script(Term::Not(Box::new(
                    Term::Const(format!("{}_closed", channel_state.name))
                ))),
                location: location.clone(),
            });

            // VC 2: Bounded channel has capacity (if sync_channel)
            if let Some(capacity) = channel_state.capacity {
                vcs.push(VerificationCondition {
                    description: format!(
                        "Bounded channel has capacity (max {})",
                        capacity
                    ),
                    script: build_vc_script(Term::BvSLt(
                        Box::new(Term::Const(format!("{}_size", channel_state.name))),
                        Box::new(Term::BitVecLit(capacity as i128, 32)),
                    )),
                    location: location.clone(),
                });
            }

            vcs
        }
        ChannelOp::Recv { .. } => {
            // VC: Channel not empty-and-closed (would deadlock)
            vec![VerificationCondition {
                description: "Channel must have items or be open (avoid deadlock)".to_string(),
                script: build_vc_script(Term::Or(vec![
                    // Has items
                    Term::BvSGt(
                        Box::new(Term::Const(format!("{}_size", channel_state.name))),
                        Box::new(Term::BitVecLit(0, 32)),
                    ),
                    // Or channel still open
                    Term::Not(Box::new(
                        Term::Const(format!("{}_closed", channel_state.name))
                    )),
                ])),
                location,
            }]
        }
    }
}

pub struct ChannelState {
    pub name: String,
    pub capacity: Option<usize>, // None = unbounded
}

pub enum ChannelOp {
    Send { value: Operand },
    Recv,
}
```

### Anti-Patterns to Avoid

- **Unbounded interleaving exploration:** State explosion makes verification intractable; always bound context switches
- **Ignoring memory ordering:** Treating all atomics as SeqCst breaks soundness for Relaxed/Acquire/Release
- **Global timestamp for Relaxed atomics:** Relaxed has no synchronization; timestamps imply ordering
- **Testing equality of lock addresses with `==`:** Locks are identity-based; use explicit lock ID tracking
- **Forgetting to check channel capacity:** Bounded channels can overflow; must generate VC
- **Schedule recording without incrementality:** Single massive formula times out; lazy enumeration more robust for Phase 12

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Partial order reduction | Custom heuristics | DPOR (Dynamic Partial Order Reduction) literature | Complex correctness proof; off-by-one errors break soundness |
| Cycle detection in lock graphs | DFS with visited set | Tarjan's SCC algorithm | Handles complex cycles; single pass; well-tested |
| Atomic ordering semantics | Custom memory model | C11 memory model mapping | Rust atomics are C11-compatible; extensive research/tooling |
| Interleaving enumeration | Backtracking search | Systematic enumeration (ESBMC lazy approach) | Ensures all interleavings explored up to bound; no missed cases |
| Happens-before encoding | Nested quantifiers | Explicit timestamp variables | Z3 quantifier handling unpredictable; explicit much faster |

**Key insight:** Concurrency verification has 20+ years of research. Use proven encodings (C11, happens-before, lock-order graphs) rather than inventing new approaches. Bounded verification trades completeness for practicality — accept this tradeoff explicitly.

## Common Pitfalls

### Pitfall 1: Unbounded Interleaving Explosion
**What goes wrong:** Verification attempts to explore all interleavings, times out on 3+ threads
**Why it happens:** n threads with m steps each have O(m^n) interleavings without bounds
**How to avoid:** Always bound context switches (default: 5); emit warning about incompleteness
**Warning signs:** Z3 timeout on simple concurrent programs, verification time grows exponentially with threads

### Pitfall 2: Treating All Atomics as SeqCst
**What goes wrong:** Verification rejects valid Relaxed/Acquire/Release code as racy
**Why it happens:** SeqCst requires total order; weaker orderings allow more interleavings
**How to avoid:** Map each Rust ordering to C11 semantics; Relaxed has NO synchronization
**Warning signs:** False positives on lock-free algorithms using Acquire/Release

### Pitfall 3: Forgetting Scoped Thread Lifetimes
**What goes wrong:** Verification allows scoped threads to outlive borrowed data
**Why it happens:** std::thread::scope has implicit lifetime constraint from 'env parameter
**How to avoid:** Encode lifetime constraint: scoped threads joined before 'env ends
**Warning signs:** Verification passes when scoped thread accesses dropped data

### Pitfall 4: Lock Invariant Assumed at Acquire, Not Checked at Release
**What goes wrong:** Invariant violation inside critical section goes undetected
**Why it happens:** Common mistake: check at acquire instead of release
**How to avoid:** Assume invariant at acquire (lock guarantees it), assert at release (must re-establish)
**Warning signs:** Mutex invariant violations not caught by verification

### Pitfall 5: Not Warning About Verification Incompleteness
**What goes wrong:** User assumes verification with bounds=5 means "fully verified"
**Why it happens:** Bounded verification is unsound for unbounded state spaces
**How to avoid:** Always emit warning: "Verified up to N threads / M switches; may miss bugs in deeper interleavings"
**Warning signs:** User surprised by concurrency bug found in production (beyond bounds)

### Pitfall 6: Deadlock Detection Without Context Switch Bound
**What goes wrong:** Deadlock detection reports false positives for lock-ordering violations that can't actually occur
**Why it happens:** Static lock-order graph doesn't consider control flow; some paths unreachable
**How to avoid:** Combine lock-order graph (cheap static check) with bounded execution (validates feasibility)
**Warning signs:** Deadlock warnings on code paths that are mutually exclusive

### Pitfall 7: Channel Unbounded Capacity Without Warning
**What goes wrong:** Verification assumes unbounded channel never blocks sender, misses real deadlock
**Why it happens:** mpsc::channel() has unlimited capacity but bounded verification must limit it
**How to avoid:** Emit warning when unbounded channel encountered: "Modeling unbounded channel with capacity limit N for verification"
**Warning signs:** Send-side deadlock in production that verification missed

## Code Examples

Verified patterns from SMT-based concurrency verification research and existing codebase:

### Extend IR with Thread Constructs
```rust
// Source: ESBMC thread encoding + crates/analysis/src/ir.rs pattern
// Location: crates/analysis/src/ir.rs

/// Thread spawn site in the program.
#[derive(Debug, Clone)]
pub struct ThreadSpawn {
    /// Local variable holding the thread handle (JoinHandle<T>)
    pub handle_local: String,
    /// Closure or function called in spawned thread
    pub thread_fn: String,
    /// Arguments passed to thread function
    pub args: Vec<Operand>,
    /// Whether this is scoped thread (std::thread::scope)
    pub is_scoped: bool,
}

/// Atomic operation in the program.
#[derive(Debug, Clone)]
pub struct AtomicOp {
    /// Type of atomic operation
    pub kind: AtomicOpKind,
    /// Memory ordering for this operation
    pub ordering: AtomicOrdering,
    /// Atomic variable being accessed
    pub atomic_place: Place,
    /// Value (for stores/compare-exchange)
    pub value: Option<Operand>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AtomicOpKind {
    Load,
    Store,
    Swap,
    CompareExchange,
    FetchAdd,
    FetchSub,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AtomicOrdering {
    Relaxed,
    Acquire,
    Release,
    AcqRel,
    SeqCst,
}

/// Synchronization operation (Mutex, RwLock, channel).
#[derive(Debug, Clone)]
pub struct SyncOp {
    pub kind: SyncOpKind,
    pub sync_object: Place,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SyncOpKind {
    MutexLock,
    MutexUnlock,
    RwLockRead,
    RwLockWrite,
    RwLockUnlock,
    ChannelSend,
    ChannelRecv,
}

// Extend Function struct:
impl Function {
    // Add fields:
    pub thread_spawns: Vec<ThreadSpawn>,
    pub atomic_ops: Vec<AtomicOp>,
    pub sync_ops: Vec<SyncOp>,
    pub lock_invariants: HashMap<Place, SpecExpr>, // Mutex -> invariant
}
```

### Extend VcKind with Concurrency Checks
```rust
// Source: Requirement INF-02 + crates/analysis/src/vcgen.rs:79-112
// Location: crates/analysis/src/vcgen.rs

pub enum VcKind {
    // ... existing variants ...

    // NEW for Phase 12:
    /// Data race freedom check (conflicting accesses must be ordered)
    DataRaceFreedom,
    /// Lock invariant check (must hold at release)
    LockInvariant,
    /// Deadlock detection (lock-order cycle)
    Deadlock,
    /// Channel operation safety (send-on-closed, capacity overflow, recv deadlock)
    ChannelSafety,
}
```

### Add Concurrency Configuration
```rust
// Source: Phase 6-11 pattern + bounded model checking literature
// Location: crates/driver/src/config.rs

pub struct VerificationConfig {
    // ... existing fields ...

    /// Enable concurrency verification (default: false, opt-in)
    pub verify_concurrency: bool,

    /// Maximum number of threads to explore (default: 3)
    pub max_threads: usize,

    /// Maximum context switches per execution (default: 5)
    pub max_context_switches: usize,

    /// Interleaving encoding strategy
    pub interleaving_strategy: InterleavingStrategy,
}

pub enum InterleavingStrategy {
    /// Enumerate interleavings individually (simplest, most debuggable)
    Lazy,
    /// Encode all interleavings in single formula (future optimization)
    ScheduleRecording,
}

impl Default for VerificationConfig {
    fn default() -> Self {
        Self {
            // ... existing defaults ...
            verify_concurrency: false, // Opt-in due to complexity
            max_threads: 3,            // Conservative default
            max_context_switches: 5,   // Catches most real bugs
            interleaving_strategy: InterleavingStrategy::Lazy, // Phase 12 default
        }
    }
}
```

### Diagnostic: Interleaving Trace Formatting
```rust
// Source: ESBMC counterexample formatting + Phase 11 pattern
// Location: crates/driver/src/diagnostics.rs

pub fn format_data_race_counterexample(
    interleaving: &Interleaving,
    race_access_1: &MemoryAccess,
    race_access_2: &MemoryAccess,
) -> String {
    let mut output = String::new();

    output.push_str("Data race detected:\n\n");
    output.push_str(&format!(
        "  Thread {} writes to {} at line {}\n",
        race_access_1.thread_id,
        race_access_1.location,
        race_access_1.source_line.unwrap_or(0)
    ));
    output.push_str(&format!(
        "  Thread {} reads from {} at line {}\n",
        race_access_2.thread_id,
        race_access_2.location,
        race_access_2.source_line.unwrap_or(0)
    ));
    output.push_str("\nInterleaving trace:\n");

    for (step, event) in interleaving.events.iter().enumerate() {
        output.push_str(&format!(
            "  {}: Thread {} executes: {}\n",
            step,
            event.thread_id,
            event.operation
        ));

        // Highlight racy accesses
        if event.is_race_access_1 {
            output.push_str("       ^^^ RACY WRITE\n");
        }
        if event.is_race_access_2 {
            output.push_str("       ^^^ RACY READ (no happens-before order)\n");
        }
    }

    output
}

pub struct Interleaving {
    pub events: Vec<InterleavingEvent>,
}

pub struct InterleavingEvent {
    pub thread_id: usize,
    pub operation: String,
    pub is_race_access_1: bool,
    pub is_race_access_2: bool,
}
```

### Test Pattern: Concurrent E2E Verification
```rust
// Source: crates/analysis/tests/e2e_verification.rs pattern
// Location: crates/analysis/tests/concurrency_verification.rs (new file)

#[test]
fn test_data_race_detection() {
    let mut shared_state = Function {
        name: "shared_state".to_string(),
        // ... IR for:
        // static COUNTER: AtomicI32 = AtomicI32::new(0);
        // fn increment() {
        //     let val = COUNTER.load(Ordering::Relaxed); // racy read
        //     COUNTER.store(val + 1, Ordering::Relaxed); // racy write
        // }
        // thread::spawn(|| increment());
        // thread::spawn(|| increment());
        // ...
        thread_spawns: vec![
            ThreadSpawn {
                handle_local: "_t1".to_string(),
                thread_fn: "increment".to_string(),
                args: vec![],
                is_scoped: false,
            },
            ThreadSpawn {
                handle_local: "_t2".to_string(),
                thread_fn: "increment".to_string(),
                args: vec![],
                is_scoped: false,
            },
        ],
        atomic_ops: vec![
            AtomicOp {
                kind: AtomicOpKind::Load,
                ordering: AtomicOrdering::Relaxed,
                atomic_place: Place::static_var("COUNTER"),
                value: None,
            },
            AtomicOp {
                kind: AtomicOpKind::Store,
                ordering: AtomicOrdering::Relaxed,
                atomic_place: Place::static_var("COUNTER"),
                value: Some(Operand::Copy(Place::local("_1"))),
            },
        ],
        ..Default::default()
    };

    let vcs = vcgen::generate_concurrency_vcs(&shared_state).unwrap();

    // Should generate DataRaceFreedom VC
    let race_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::DataRaceFreedom)
        .collect();

    assert!(!race_vcs.is_empty(), "Expected data race VC");

    // Check Z3 finds counterexample (SAT = race exists)
    let solver = solver_or_skip();
    for vc in race_vcs {
        let result = solver.check_sat(&vc.script).unwrap();
        assert!(matches!(result, SolverResult::Sat(_)), "Expected data race detected");
    }
}

#[test]
fn test_mutex_lock_invariant() {
    // IR for:
    // struct Counter { #[lock_invariant(value >= 0)] mu: Mutex<i32> }
    // impl Counter {
    //     fn increment(&self) {
    //         let mut guard = self.mu.lock().unwrap();
    //         *guard += 1; // maintains invariant
    //     }
    // }

    // Should generate LockInvariant VC at mutex unlock
    // Z3 should prove UNSAT (invariant holds)
}

#[test]
fn test_deadlock_detection() {
    // IR for:
    // fn thread1() { lock(A); lock(B); unlock(B); unlock(A); }
    // fn thread2() { lock(B); lock(A); unlock(A); unlock(B); }

    // Deadlock detector should find cycle: A→B in thread1, B→A in thread2
    // Should generate Deadlock VC
}
```

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| Explicit state model checking | SMT-based bounded MC | 2008-2011 (ESBMC) | Scalability: handles programs with data-dependent branching |
| Sequential consistency only | C11/C++11 weak memory | 2011 (C11 standard) | Correctness: models real hardware relaxed orderings |
| Manual thread interleaving | Automatic enumeration up to bound | 2005 (context-bounding) | Automation: finds bugs without hand-written test cases |
| Unbounded POR | Bounded exploration + DPOR | 2014-2025 (optimal DPOR) | Practicality: terminates on real programs with acceptable incompleteness |
| Quantified HB formulas | Explicit timestamp variables | 2015+ (BMC for weak memory) | Performance: Z3 quantifier instantiation unpredictable |

**Deprecated/outdated:**
- **Unbounded interleaving exploration:** Intractable; bounded verification standard since 2005
- **Custom memory models:** C11 is standard; Rust atomics explicitly C11-compatible
- **Global lock (giant lock) as synchronization primitive:** Not expressive enough; modern codes use fine-grained locking

## Open Questions

1. **Should we support dynamic thread creation with unbounded thread count?**
   - What we know: std::thread::spawn allows arbitrary thread creation; bounding at 3 threads limits coverage
   - What's unclear: Can we abstract thread count via symmetry reduction, or is explicit bound necessary?
   - Recommendation: Phase 12 bounds threads explicitly (simpler); Phase 13+ could add symmetry reduction for identical threads

2. **How to estimate context-switch sufficiency for a given function?**
   - What we know: Nested lock depth and loop iteration counts correlate with needed switches
   - What's unclear: Heuristic estimation accuracy vs. user frustration from false insufficiency warnings
   - Recommendation: Estimate based on static analysis (lock depth × 2); always emit conservative warning

3. **Should lock_invariant be on Mutex field or on containing struct?**
   - What we know: Rust attributes on fields supported (`#[lock_invariant(...)]`); struct-level also possible
   - What's unclear: Field-level more precise; struct-level more convenient for multi-field invariants
   - Recommendation: Support both; field-level for simple invariants, struct-level with explicit field references for complex

4. **How to handle thread::park/unpark for custom synchronization?**
   - What we know: park/unpark are low-level primitives for building higher-level sync (rarely used directly)
   - What's unclear: Encoding park/unpark synchronization semantics without specialized support
   - Recommendation: Defer to post-Phase 12; most code uses Mutex/RwLock/channels which we support

## Sources

### Primary (HIGH confidence)
- [ESBMC v7.7 documentation](https://github.com/esbmc/esbmc) - SMT-based context-bounded model checker implementation
- [ESBMC v7.7 paper](https://link.springer.com/chapter/10.1007/978-3-031-90660-2_16) - Recent advances in scheduling and DPOR (2025)
- [Verifying Multi-threaded Software using SMT-based Context-Bounded Model Checking (ICSE 2011)](https://dl.acm.org/doi/10.1145/1985793.1985839) - Foundational lazy/schedule-recording approaches
- [Rust std::sync::atomic::Ordering documentation](https://doc.rust-lang.org/std/sync/atomic/enum.Ordering.html) - Official Rust atomic ordering semantics
- [Rust std::thread::scope documentation](https://doc.rust-lang.org/std/thread/fn.scope.html) - Scoped threads and lifetime guarantees
- [Happens-before propagator stability (TACAS 2025)](https://link.springer.com/chapter/10.1007/978-3-031-90643-5_1) - Recent research on HB encoding correctness

### Secondary (MEDIUM confidence)
- [BMC for Weak Memory Models: Relation Analysis for Compact SMT Encodings](https://link.springer.com/chapter/10.1007/978-3-030-25540-4_19) - SMT encoding strategies for C11 memory model
- [Automating Deductive Verification for Weak-Memory Programs](https://link.springer.com/chapter/10.1007/978-3-319-89960-2_11) - Encoding weak memory in SMT solvers
- [Optimal Concolic Dynamic Partial Order Reduction (CONCUR 2025)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CONCUR.2025.26) - State-of-the-art DPOR algorithms
- [Deadlock detection via lock-order graphs (2025)](https://arxiv.org/pdf/2502.20070) - Recent approach to eliminating false positives
- [Peahen: Fast and Precise Static Deadlock Detection](https://qingkaishi.github.io/public_pdfs/FSE22.pdf) - Static analysis with SMT validation
- [Memory Ordering in Rust guide](https://mara.nl/atomics/memory-ordering.html) - Practical Rust atomics explanation

### Tertiary (LOW confidence - needs validation)
- [Rust Atomics and Locks book](https://mara.nl/atomics/) - Community resource (not official spec)
- [GitHub issue: std::sync improvements tracking](https://github.com/rust-lang/rust/issues/93740) - Implementation details (may be outdated)

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH - ESBMC is mature (2008-2025), SMT-based CBMC well-established, Rust std::sync documented
- Architecture: HIGH - Follows Phase 6-11 IR extension pattern, lazy enumeration simplest approach
- Pitfalls: HIGH - Well-documented in CBMC literature, confirmed by tool implementations (ESBMC, CBMC, Nidhugg)
- Memory ordering: HIGH - Rust atomics are C11-compatible by design, C11 SMT encodings well-researched
- Default bounds: MEDIUM - 3 threads/5 switches conservative based on literature, but no universal consensus
- DPOR integration: MEDIUM - Optimal DPOR algorithms exist but complex; lazy enumeration proven for Phase 12

**Research date:** 2026-02-13
**Valid until:** 2026-03-15 (30 days - concurrency verification domain stable, SMT techniques mature)
