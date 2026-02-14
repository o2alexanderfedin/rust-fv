# Phase 12: Concurrency Verification - Context

**Gathered:** 2026-02-13
**Status:** Ready for planning

<domain>
## Phase Boundary

Bounded concurrent program verification with sequential consistency and full memory ordering support. Developer can verify programs using std::thread (spawn + scoped threads), Mutex, RwLock, mpsc channels, and atomics with all orderings. Verification is bounded by configurable thread count and context-switch limits.

</domain>

<decisions>
## Implementation Decisions

### Concurrency Scope
- Support `std::thread::spawn` and `std::thread::scope` (scoped threads share stack references)
- Synchronization primitives: `Mutex<T>`, `RwLock<T>`, `mpsc::channel`/`mpsc::sync_channel`, atomics
- All atomic orderings: SeqCst, Acquire, Release, AcqRel, Relaxed
- Both bounded and unbounded channels verified, with capacity warning for unbounded
- Rely on Rust's Send/Sync type system for shared-data intent (no custom #[shared] annotation)

### Interleaving Bounds
- Global defaults with per-function attribute overrides: global config/CLI flags + `#[verify(threads = N, switches = M)]`
- Default bounds: Claude's discretion, choosing towards safety and precision (higher bounds for stronger guarantees, balanced against Z3 performance)
- Sufficiency estimation: Claude's discretion, choosing towards safety and precision (estimate when possible, but warn conservatively)

### Verification Encoding
- Data race counterexample shows full interleaving trace: step-by-step execution showing which thread runs when, leading to the race
- Lock invariant violation reporting: Claude's discretion, choosing towards safety and precision (invariant diff style preferred)
- Basic deadlock detection: lock-ordering violations (Thread 1 locks A then B, Thread 2 locks B then A)
- Channel verification: full coverage including send-on-closed, recv-on-empty deadlock potential, and capacity overflow for bounded channels

### Annotation Design
- `#[lock_invariant]` placement: Claude's discretion (pick what fits Rust's attribute system best)
- Concurrency entry points: auto-detect `thread::spawn` calls + manual `#[verify(concurrent)]` override
- Atomic ordering: read from actual code (`load(Ordering::SeqCst)`) rather than separate annotations
- Bound configuration: `#[verify(threads = N, switches = M)]` per function, CLI `--max-threads`/`--max-switches` globally

### Diagnostics
- Bounded verification warning with concrete suggestions: "Verified up to N threads / M switches. Try --max-switches=12 for full coverage of this function."

### Claude's Discretion
- Default thread/context-switch bounds (favoring safety and precision)
- Sufficiency estimation approach (favoring safety and precision)
- Lock invariant violation report format (favoring invariant diff style)
- `#[lock_invariant]` placement (on field vs struct)
- Interleaving encoding strategy for Z3

</decisions>

<specifics>
## Specific Ideas

- Full memory ordering support (all 5 Rust orderings) — not just SeqCst
- Scoped threads important for verifying shared-reference patterns
- Channel verification should catch real bugs: send-on-closed panics, deadlocks from blocking recv on empty unbounded channel
- Deadlock detection via lock-ordering analysis (basic cycle detection in lock graph)
- Counterexamples should show the full interleaving trace, not just conflicting access locations

</specifics>

<deferred>
## Deferred Ideas

None — discussion stayed within phase scope

</deferred>

---

*Phase: 12-concurrency-verification*
*Context gathered: 2026-02-13*
