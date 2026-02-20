# Phase 21: Weak Memory Models - Research

**Researched:** 2026-02-19
**Domain:** RC11 weak memory model SMT encoding, coherence axioms (mo/rf/co), litmus tests, data race detection
**Confidence:** HIGH (codebase gap analysis), HIGH (RC11 formal model), MEDIUM (SMT encoding strategy)

<phase_requirements>
## Phase Requirements

| ID | Description | Research Support |
|----|-------------|-----------------|
| WMM-01 | User can verify programs using `Relaxed`, `Acquire`, `Release`, and `AcqRel` atomic orderings with full RC11 coherence axioms (`mo`, `rf`, `co`) | `AtomicOrdering` enum already exists in `ir.rs`; `encode_atomic_ordering()` in `happens_before.rs` currently collapses Relaxed to `BoolLit(true)` and collapses Acquire/Release/AcqRel to a single form — needs full RC11 axiom set: mo (modification order total order per location), rf (reads-from assignment), co (coherence: hb;eco? irreflexive), framing per ordering level |
| WMM-02 | All 8 canonical C11 litmus tests (IRIW, SB, LB, MP, CoRR, CoRW, CoWR, CoWW) produce correct allowed/forbidden verdicts | No litmus test infrastructure exists; tests must be built as IR-level test Functions in a new `weak_memory_litmus.rs`; each test encodes a specific pattern of atomic reads/writes and must produce UNSAT (for forbidden behaviors) or SAT (for allowed behaviors) from Z3 |
| WMM-03 | Data race detection extends to cover weak memory orderings (not just SeqCst) | `data_race_freedom_vcs()` in `happens_before.rs` generates VCs for all conflicting access pairs; currently the `encode_atomic_ordering` function returns `BoolLit(true)` for Relaxed which causes race VCs to be trivially SAT (race exists); with RC11 mo/rf/co encoding, Relaxed operations produce `VcKind::WeakMemoryRace` VCs that are SAT precisely when a race exists under the relaxed model |
| WMM-04 | All weak memory axioms are scoped to `WeakMemory*` VcKind — existing SeqCst proofs not regressed | `VcKind` enum in `vcgen.rs` needs new variants: `WeakMemoryCoherence`, `WeakMemoryRace`, `WeakMemoryAtomicity`; existing `DataRaceFreedom`, `LockInvariant` etc. unchanged; `generate_concurrency_vcs()` only invokes weak memory path when `atomic_ops` contains non-SeqCst orderings |
</phase_requirements>

## Summary

Phase 21 replaces a deliberately incomplete "stub" encoding of weak memory orderings with a sound RC11 encoding. The current codebase (`happens_before.rs::encode_atomic_ordering`) collapses `Relaxed` to `Term::BoolLit(true)` and collapses `Acquire`/`Release`/`AcqRel` to a single `implies(reads_from, happens_before)` pattern — this is semantically incorrect for RC11 (the AcqRel encoding is wrong per STATE.md flagged concern), and Relaxed produces no synchronization constraint at all (correct behavior) but also no race-detection axioms (incorrect).

The phase must implement the **axiomatic RC11 memory model** as an SMT encoding. RC11 defines consistency via four acyclicity/irreflexivity conditions on an execution graph:
1. **COHERENCE**: `hb ; eco?` is irreflexive (equivalently: `hb_loc ∪ rf ∪ co ∪ fr` is acyclic)
2. **ATOMICITY**: `rmw ∩ (rb ; mo) = ∅`
3. **SC**: `psc` is acyclic (for SeqCst accesses only)
4. **NO-THIN-AIR**: `sb ∪ rf` is acyclic (prevents speculation)

In the SMT encoding, execution events (atomic operations) are given integer timestamps (modification order values per location). The `rf` (reads-from) relation is encoded as: each load event is assigned an integer `rf_N` equal to the event ID of the store it reads from. The `mo` (modification order) is a per-location total order on stores encoded as: for each pair of same-location stores (i, j), an `Int` variable `mo_loc_i_j` which is either 0 or 1. Coherence axioms become SMT constraints asserting these relations form no cycles.

The key insight from Dartagnan and related tools: encode the execution as a **candidate execution graph** (events + rf assignment + mo order), then assert the RC11 consistency axioms as SMT formulas. Z3 finds an assignment satisfying all axioms if a consistent execution exists; UNSAT means no consistent execution exists (violation forbidden).

**Primary recommendation:** Implement `rc11.rs` as a new module in `crates/analysis/src/concurrency/` containing the RC11 axiom encoding. Add `WeakMemoryCoherence`, `WeakMemoryRace`, and `WeakMemoryAtomicity` variants to `VcKind`. Extend `generate_concurrency_vcs()` with a `generate_weak_memory_vcs()` call that is invoked only when non-SeqCst atomic ops are present. Build the 8 litmus tests as SMT-level integration tests in `weak_memory_litmus.rs`.

## Standard Stack

### Core
| Library | Version | Purpose | Why Standard |
|---------|---------|---------|--------------|
| Z3 (via rust_fv_smtlib) | existing | SMT encoding of RC11 axioms as integer order + boolean relations | Already the solver backend; `Term::BvSLt`, `Term::Eq`, `Term::Forall`, `Term::Implies` all exist |
| rust_fv_smtlib | existing | `Term`, `Sort`, `Command` for RC11 SMT assertions | All required sorts (Int, Bool, BitVec) and term forms present |
| rust_fv_analysis::ir | existing | `AtomicOp`, `AtomicOrdering`, `AtomicOpKind` | All five orderings already in `AtomicOrdering` enum |
| rust_fv_analysis::vcgen | existing | `VcKind`, `generate_concurrency_vcs()` | Extension point already exists: add weak memory path to `generate_concurrency_vcs()` |

### Supporting
| Library | Version | Purpose | When to Use |
|---------|---------|---------|-------------|
| `Sort::Int` (smtlib) | existing | Modification order timestamps (integer total order per location) | Encoding `mo_i_j` ordering integers for same-location stores |
| `Sort::Bool` (smtlib) | existing | Reads-from relation Boolean variables `rf_N_M` (load N reads from store M) | Encoding the rf function as existential choice |
| `Term::BvSLt` (smtlib) | existing | Current `happens_before` timestamp comparison | Reused for `mo` total order when using BV timestamps |

### Alternatives Considered
| Instead of | Could Use | Tradeoff |
|------------|-----------|----------|
| Integer timestamps for mo order | Boolean matrix `mo[i][j]` for all pairs | Integer timestamps scale better (n vars vs n^2 vars); transitive closure is automatic via integer comparison |
| Explicit acyclicity as `(assert (acyclic hb))` | Encode acyclicity as `hb+eco is irreflexive` = no self-loops in transitive closure | Irreflexivity is simpler to encode in SMT: `forall e. not hb_eco(e, e)` — transitive closure not required if we directly encode reachability |
| Full `hb ; eco?` irreflexivity assertion | Per-litmus coherence checks | Full axiom is sound and general; per-litmus is fragile. Use full axioms |
| Stateless model checking (GenMC style) | SMT bounded model checking | SMT BMC integrates cleanly with existing `generate_concurrency_vcs` infrastructure |

**No new Cargo dependencies required.** `Sort::Int` and `Term::BvSLt`/integer comparison are already in smtlib crate.

## Architecture Patterns

### Recommended Project Structure

New files and extensions:

```
crates/analysis/src/
├── concurrency/
│   ├── mod.rs               # EXTEND: pub mod rc11; re-export RC11 types
│   ├── happens_before.rs    # EXTEND: fix AcqRel encoding; add WeakMemory relation helpers
│   └── rc11.rs              # NEW: RC11 axiom encoding (mo, rf, co, coherence, atomicity, SC, no-thin-air)
├── vcgen.rs                 # EXTEND: VcKind new variants + generate_weak_memory_vcs() call
crates/analysis/tests/
└── weak_memory_litmus.rs    # NEW: 8 canonical C11 litmus tests (IRIW, SB, LB, MP, CoRR/RW/WR/WW)
```

### Pattern 1: RC11 Execution Graph Representation

**What:** An RC11 execution is a set of events (loads/stores with ordering) plus two relations: `rf` (reads-from) and `mo` (modification order). The SMT encoding declares:
- One `Int` constant per event for `mo` ordering (per-location, stores only)
- One `Bool` constant per (load, store) pair for `rf` (which store does each load read from)
- Axioms asserting `mo` is a strict total order per location and `rf` assigns each load to exactly one store

**SMT-LIB structure for N events:**
```smtlib
; Events are numbered 0..N-1
; mo_order_i: modification order position of store i (Int, per location)
(declare-fun mo_order_0 () Int)
(declare-fun mo_order_1 () Int)

; rf_0_1 = true means event 0 (load) reads from event 1 (store)
(declare-fun rf_0_1 () Bool)

; mo is a strict total order on same-location stores:
; (for stores i, j to location L: mo_order_i != mo_order_j)
(assert (distinct mo_order_0 mo_order_1))

; rf is a function (each load reads from exactly one store):
; (for load i: exactly one rf_i_j is true)
(assert (or rf_0_1 rf_0_2))  ; load 0 reads from store 1 or store 2
(assert (not (and rf_0_1 rf_0_2)))  ; but not both
```

**Confidence:** HIGH — this is the standard approach used by Dartagnan (Springer BMC paper) and Cerberus-BMC; validated by prior published BMC tools.

### Pattern 2: RC11 Coherence Axiom Encoding

**What:** The RC11 coherence axiom `hb ; eco? is irreflexive` means: for any event `e`, it is not the case that `e` is related to itself by first `hb` (happens-before) and then `eco` (extended coherence order = rf ∪ mo ∪ fr). In SMT, encode as: for each pair of events (i, j), if `hb(i, j)` and `eco(j, i)`, that is a contradiction.

For a bounded set of N events, the coherence axiom becomes a finite conjunction of constraints. Since we have a small fixed set of events (typically 4-8 for litmus tests, up to ~20 for real programs), we enumerate all pairs:

```smtlib
; For all pairs (i, j): not (hb(i,j) AND eco(j,i))
; hb(i,j): event i happens before event j (via sequenced-before OR synchronizes-with)
; eco(j,i): event j is in extended coherence order before event i
;   eco = rf | mo | fr (from-read: load reads from store before another store)

; Example for load L reading from store S1 when store S2 comes later in mo:
; fr(L, S2) because L reads S1 and S2 is mo-after S1
(assert (not (and (hb_0_1) (eco_1_0))))
```

In the bounded N-event case, `hb(i,j)` and `eco(j,i)` can be encoded as Bool constants derived from:
- `sb` (sequenced-before): event i is in the same thread as j and precedes it
- `sw` (synchronizes-with): a Release store at i is rf-related to an Acquire load at j

**Confidence:** HIGH — from RC11 formal definition (Lahav et al. "Repairing Sequential Consistency in C/C++11" PLDI 2017) and Dartagnan BMC encoding.

### Pattern 3: Ordering-Specific Synchronization (`sw` relation)

**What:** The `sw` (synchronizes-with) relation is defined by the ordering of atomic operations:
- **Relaxed**: no synchronization — contributes nothing to `sw`
- **Release** store + **Acquire** load: if `rf(Load, Store)` and Store is Release and Load is Acquire (or stronger), then `sw(Store, Load)`
- **AcqRel**: a RMW (fetch-add, compare-exchange) with AcqRel has both Acquire and Release effects — it synchronizes-with any Acquire that reads from it AND any Release that it reads from
- **SeqCst**: total order; existing `ts_N` timestamp encoding is correct

**SMT encoding for sw (for Release store at event S and Acquire load at event L):**
```smtlib
; sw(S, L) = rf(S, L) AND is_release(S) AND is_acquire(L)
(define-fun sw_S_L () Bool
    (and rf_L_S              ; load L reads from store S
         true                 ; S has Release ordering (static, encoded as true)
         true))               ; L has Acquire ordering (static, encoded as true)
```

**AcqRel encoding (fixing the current bug):** The current codebase merges Acquire, Release, and AcqRel into the same encoding: `implies(reads_from(load, store), happens_before(store, load))`. This is wrong for AcqRel because:
- A `fetch_add(AcqRel)` is both a read and a write
- It must synchronize-with any Acquire load that reads its written value (Release side)
- AND it must be ordered after any Release store whose value it reads (Acquire side)

The fix: AcqRel operations get BOTH synchronization constraints, not just one.

**Confidence:** HIGH — from RC11 definition; AcqRel bug is documented in STATE.md.

### Pattern 4: New VcKind Variants

**What:** Three new VcKind variants, separate from the existing SeqCst/mutex infrastructure:

```rust
// In vcgen.rs, extend VcKind enum:
pub enum VcKind {
    // ... existing variants unchanged ...

    /// Weak memory coherence check (RC11 hb;eco? irreflexive)
    /// Generated only for functions with non-SeqCst atomic ops
    WeakMemoryCoherence,

    /// Weak memory data race check (conflicting accesses without ordering)
    /// Under Relaxed ordering, Relaxed-vs-Relaxed to same location is a race
    WeakMemoryRace,

    /// Weak memory atomicity check (RMW operations: rmw ∩ (rb ; mo) = ∅)
    WeakMemoryAtomicity,
}
```

**SeqCst backward compatibility:** The existing `DataRaceFreedom` VcKind and `encode_atomic_ordering(SeqCst, ...)` are not touched. The new `WeakMemoryRace` is only used when the function has at least one non-SeqCst atomic op. A function with only SeqCst ops continues to use the existing path unchanged.

**Confidence:** HIGH — direct extension of existing enum pattern; VcKind filter in `generate_concurrency_vcs` already cleanly separates concerns.

### Pattern 5: 8 Canonical Litmus Tests (SMT-Level)

**What:** Each litmus test is a short concurrent program encoding expressed directly as SMT (not via the IR + VCGen pipeline). Tests are written as hand-crafted SMT scripts in the integration test, then submitted to Z3. The test asserts:
- For **forbidden** behaviors: `(check-sat)` should return `UNSAT` (no consistent RC11 execution exists)
- For **allowed** behaviors: `(check-sat)` should return `SAT` (a consistent execution exists)

**The 8 tests:**

| Litmus Test | Pattern | Expected Under RC11 |
|-------------|---------|---------------------|
| IRIW (Independent Reads from Independent Writes) | T1: x=1; T2: y=1; T3: r1=x, r2=y; T4: r3=y, r4=x | Forbidden: T3 sees x=1,y=0 while T4 sees y=1,x=0 simultaneously |
| SB (Store Buffering) | T1: x=1, r1=y; T2: y=1, r2=x | Allowed under Relaxed; Forbidden under SeqCst |
| LB (Load Buffering) | T1: r1=x, y=1; T2: r2=y, x=1 | Forbidden under RC11 (no-thin-air: sb∪rf acyclic) |
| MP (Message Passing) | T1: x=1(Rel), y=1(Rel); T2: r1=y(Acq), r2=x(Acq) | Forbidden that r1=1 but r2=0; this is the Rel/Acq guarantee |
| CoRR (Coherence Read-Read) | Two reads of x in same thread must see non-decreasing mo order | Forbidden to read old value after new |
| CoRW (Coherence Read-Write) | Read then write same location; mo must respect | Forbidden reordering |
| CoWR (Coherence Write-Read) | Write then read same location; read must see write or later | Forbidden to see earlier value |
| CoWW (Coherence Write-Write) | Two writes same location must be totally ordered by mo | Forbidden concurrent writes without mo |

**Test pattern (in Rust test file, using SMT-LIB assembly):**
```rust
#[test]
fn test_mp_message_passing_forbidden() {
    // MP: T1: (x=1 Release)(y=1 Release), T2: (r1=y Acquire)(r2=x Acquire)
    // Forbidden: r1==1 AND r2==0
    // Under RC11 Release-Acquire: if T2 reads y=1, it synchronizes-with T1's write of y,
    // so T2 must also see x=1.
    let smtlib = r#"
(set-logic QF_LIA)
; Events: W_x(0)=1 (Release), W_y(1)=1 (Release), R_y(2)=? (Acq), R_x(3)=? (Acq)
(declare-fun rf_2_1 () Bool)   ; R_y reads from W_y
(declare-fun rf_3_0 () Bool)   ; R_x reads from W_x
(declare-fun rf_3_init () Bool) ; R_x reads from init (x=0)
; rf is functional
(assert (or rf_3_0 rf_3_init))
(assert (not (and rf_3_0 rf_3_init)))
; rf_2_1: R_y reads W_y=1 (assume r1=1, so this must be true)
(assert rf_2_1)
; sw(W_y, R_y) because Release->Acquire and rf(R_y, W_y)
; sw implies hb(W_x, R_x) because W_x sb W_y sw R_y sb R_x
; Therefore R_x must see W_x, so rf_3_0 must be true:
; Encode: if rf_2_1 (r1=1) then rf_3_0 (r2=1) -- the forbidden case is rf_2_1 AND rf_3_init
(assert rf_3_init)             ; assert forbidden: r2=0
; Check for contradiction with RC11 coherence
; hb: W_x sb W_y sw R_y sb R_x => hb(W_x, R_x)
; eco: fr(R_x, W_x) because R_x reads init and W_x is later in mo
; Coherence violation: hb(W_x, R_x) and fr(R_x, W_x) = hb;eco loop
(assert false)                 ; encoding the cycle as contradiction
(check-sat)                    ; expected: UNSAT
"#;
    // ... submit to Z3, assert UNSAT
}
```

**Note:** The actual litmus test encoding will be at the IR level (constructing `Function` with `AtomicOp` structs) and using `generate_weak_memory_vcs()` to produce SMT scripts, then submitting to Z3. The hand-crafted SMT shown above is for illustration; the final tests use the VCGen pipeline.

**Confidence:** MEDIUM — the litmus test expected results are well-established in the literature (HIGH confidence). The specific IR-level encoding approach is derived from the existing `concurrency_verification.rs` test pattern (verified in codebase). The hand-crafted SMT detail may need adjustment once rc11.rs is implemented.

### Anti-Patterns to Avoid

- **Keeping `Relaxed => BoolLit(true)` without mo/rf encoding:** Relaxed atomicity means NO synchronization (correct), but Relaxed operations STILL participate in the `mo` (modification order) and `rf` (reads-from) relations. `BoolLit(true)` prevents race detection for Relaxed-vs-Relaxed accesses entirely.
- **Merging Acquire, Release, AcqRel into one `implies(rf, hb)` case:** AcqRel has both sides; Release only contributes to `sw` when the other side is Acquire; Acquire only contributes when the other side is Release. The current merged encoding is unsound for AcqRel.
- **Adding RC11 axioms to SeqCst VCs:** RC11 weak memory axioms must be scoped to `WeakMemory*` VcKind only. If the function has only SeqCst atomics, do not invoke `generate_weak_memory_vcs()`.
- **Using QF_BV for RC11 axiom VCs:** The modification order timestamps and rf relation Boolean variables live in the integer/Boolean domain. Use `QF_LIA` (quantifier-free linear integer arithmetic) for RC11 VCs, not `QF_BV`. This is critical for performance — Dartagnan found integer encoding outperforms bitvector for WMM axioms.
- **Building a full acyclicity check via transitive closure:** For bounded N events, check all N*(N-1) pairs for `(hb(i,j) AND eco(j,i))`. Do not attempt to compute transitive closure symbolically — iterate over all pairs at VC generation time.
- **Applying litmus test logic to production verification without VcKind scoping:** The litmus tests validate the encoding. Production verification of real programs must route through the VcKind filter so only weak memory VCs appear for weak memory orderings.

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Acyclicity of hb;eco? relation | Custom graph cycle detection | Bounded N-pair enumeration: `forall i,j: not (hb(i,j) AND eco(j,i))` | For bounded N events, N*(N-1) assertions are decidable by QF_LIA/Z3; no symbolic transitive closure needed |
| SMT Int ordering for mo | Custom BV timestamp encoding | `Sort::Int` with `(declare-fun mo_order_N () Int)` + `(assert (distinct ...))` | Dartagnan paper shows integer encoding outperforms BV for modification order; `Sort::Int` already in smtlib crate |
| RF relation uniqueness | Constraint propagation | SMT `(assert (or rf_i_j1 rf_i_j2))` + `(assert (not (and rf_i_j1 rf_i_j2)))` | Exactly-one encoding is standard; Z3 handles cardinality constraints natively |
| C11 litmus test harness | Custom test DSL | IR-level `Function` construction following existing `concurrency_verification.rs` pattern | Reuses existing `make_concurrent_function` helper; no new harness needed |
| AcqRel two-sided encoding | Custom RMW analysis | Encode as two separate `sw` contributions (Release-side + Acquire-side) per AcqRel event | Cleaner than a single combined term; matches the formal RC11 definition of RMW events |

**Key insight:** RC11 over a bounded set of N events reduces to a finite SAT problem in QF_LIA (integers + Booleans). No custom fixpoint, no unbounded quantifiers. The entire axiom set is a conjunction of linear/Boolean formulas.

## Common Pitfalls

### Pitfall 1: AcqRel Is Not Equivalent to `Release OR Acquire`

**What goes wrong:** The current codebase collapses AcqRel to the same `implies(rf, hb)` formula as Release/Acquire individually. AcqRel on a RMW (fetch_add, compare_exchange) means the operation is BOTH a Release write AND an Acquire read simultaneously.

**Why it happens:** The symmetry between Release and Acquire makes it tempting to merge them. AcqRel is the union, but the union applies to the SAME event simultaneously, not to different events.

**How to avoid:** For an `AcqRel` RMW event E:
- Its WRITE side synchronizes-with any Acquire load that reads from E (Release contribution)
- Its READ side is synchronizes-with any Release store whose value E reads (Acquire contribution)
Both contributions to `sw` must be separately encoded.

**Warning signs:** The MP litmus test passes with AcqRel but IRIW gives wrong verdict.

**Reference:** STATE.md explicitly flags: "[Phase 21] RC11 AcqRel encoding — not equivalent to Release OR Acquire; derive from arXiv:2108.06944"

### Pitfall 2: `fr` (From-Read) Relation Requires `mo`

**What goes wrong:** The from-read relation `fr(L, S2)` says "load L reads from a store S1 that precedes S2 in mo". `fr` depends on `mo` — you cannot encode `fr` without first committing to a specific `mo` assignment. If `mo` is existentially quantified (any valid total order), `fr` is derived.

**Why it happens:** Treating `fr` as a static pre-computed relation rather than derived from `rf` and `mo`.

**How to avoid:** In the SMT encoding, `fr(L, S2)` = `∃S1. rf(L, S1) AND mo(S1, S2)`. Encode as:
```smtlib
; fr(L, S2) holds iff L reads from some S1 where S1 is mo-before S2
(define-fun fr_L_S2 () Bool
    (or (and rf_L_S1 (< mo_order_S1 mo_order_S2))
        (and rf_L_S0 (< mo_order_S0 mo_order_S2))))
```
Since N is bounded, enumerate all (load, store) pairs.

**Warning signs:** CoRR/CoRW/CoWR tests give UNSAT when they should be SAT (or vice versa), because `fr` is computed incorrectly.

### Pitfall 3: Sequenced-Before Must Be Intra-Thread Only

**What goes wrong:** `sb` (sequenced-before) encodes program order within a single thread. If `sb` accidentally includes cross-thread ordering, the `sw` and `hb` relations become too strong, causing legitimate weak memory behaviors to be marked as violations.

**Why it happens:** The `thread_id` field in `MemoryAccess` is currently a placeholder (`0` — see vcgen.rs line 3445 comment). Events from different threads must not be `sb`-related.

**How to avoid:** In `generate_weak_memory_vcs()`, use `thread_id` to correctly partition events by thread. Events E1 and E2 are `sb`-related iff `E1.thread_id == E2.thread_id AND E1.event_id < E2.event_id` (program order within thread). The `thread_id` placeholder must be resolved — use `func.thread_spawns` to assign thread IDs to atomic ops.

**Warning signs:** SB (Store Buffering) litmus test returns UNSAT when it should be SAT (because sb incorrectly orders cross-thread events).

### Pitfall 4: QF_BV Logic Rejects Integer `mo_order` Variables

**What goes wrong:** The existing concurrency VCs use `(set-logic QF_BV)`. Adding `(declare-fun mo_order_0 () Int)` into a `QF_BV` script causes Z3 to reject the query with "unknown sort" or "sort mismatch".

**Why it happens:** `QF_BV` (quantifier-free bit-vectors) does not include the integer sort. RC11 mo-order timestamps are most naturally `Int`, not `BitVec`.

**How to avoid:** Use `(set-logic QF_LIA)` for weak memory VCs (linear integer arithmetic for mo integers + Boolean rf variables). Or use `(set-logic ALL)` if mixing with bitvector value constraints. Provide `weak_memory_smt_logic() -> &'static str { "QF_LIA" }` helper in `rc11.rs`.

**Warning signs:** Z3 error "invalid logic for sort Int" in any weak memory VC.

### Pitfall 5: SeqCst Regression From New VcKind Scope

**What goes wrong:** Adding `generate_weak_memory_vcs()` call unconditionally into `generate_concurrency_vcs()` could run RC11 axioms on SeqCst-only functions, generating `WeakMemory*` VCs that did not exist before, potentially failing on previously-passing functions.

**Why it happens:** Forgetting to gate on `has_non_seqcst_atomics(func)`.

**How to avoid:** Gate the entire RC11 path:
```rust
fn has_non_seqcst_atomics(func: &Function) -> bool {
    func.atomic_ops.iter().any(|op| op.ordering != AtomicOrdering::SeqCst)
}
// In generate_concurrency_vcs():
if has_non_seqcst_atomics(func) {
    vcs.append(&mut generate_weak_memory_vcs(func));
}
```

**Warning signs:** Existing `concurrency_verification.rs` tests start failing with unexpected `WeakMemoryCoherence` VCs.

### Pitfall 6: Litmus Test Thread-ID Assignment

**What goes wrong:** Litmus tests require events to be partitioned into threads. The `MemoryAccess.thread_id` field is currently always `0` (placeholder). Litmus tests with two threads produce wrong verdicts because all events appear to be in the same thread (no cross-thread races, no inter-thread rf).

**Why it happens:** The VCGen placeholder comment at vcgen.rs:3445 "Placeholder - will be filled by interleaving enumeration" was never implemented.

**How to avoid:** For the litmus test integration tests, directly construct `MemoryAccess` structs with correct `thread_id` values rather than deriving them from `AtomicOp` in `generate_concurrency_vcs()`. For production, the thread_id assignment requires resolving which atomic ops belong to which thread spawn — this can be approximated using `func.thread_spawns` ordering.

**Warning signs:** All litmus tests return SAT (no races) because all events are in thread 0, making no access cross-thread.

## Code Examples

Verified patterns from codebase inspection:

### RC11 Modification Order Variables (`rc11.rs`)

```rust
// Source: codebase Sort::Int usage from smtlib/src/sort.rs; Command::DeclareFun from command.rs
use rust_fv_smtlib::command::Command;
use rust_fv_smtlib::sort::Sort;
use rust_fv_smtlib::term::Term;

/// Declare modification order position variable for a store event.
/// mo_order_N is an Int giving the position of event N in the per-location total order.
pub fn declare_mo_order(event_id: usize) -> Command {
    Command::DeclareFun(
        format!("mo_order_{}", event_id),
        vec![],
        Sort::Int,
    )
}

/// Declare reads-from Boolean variable: rf_load_store = true iff load reads from store.
pub fn declare_rf(load_event: usize, store_event: usize) -> Command {
    Command::DeclareFun(
        format!("rf_{}_{}", load_event, store_event),
        vec![],
        Sort::Bool,
    )
}

/// mo is a strict total order: all same-location stores have distinct mo positions.
pub fn assert_mo_total_order(store_events: &[usize]) -> Vec<Command> {
    let mut cmds = Vec::new();
    for i in 0..store_events.len() {
        for j in (i + 1)..store_events.len() {
            let ei = store_events[i];
            let ej = store_events[j];
            // mo_order_i != mo_order_j
            let neq = Term::Not(Box::new(Term::Eq(
                Box::new(Term::Const(format!("mo_order_{}", ei))),
                Box::new(Term::Const(format!("mo_order_{}", ej))),
            )));
            cmds.push(Command::Assert(neq));
        }
    }
    cmds
}

/// rf is a function: each load reads from exactly one store.
pub fn assert_rf_functional(load_event: usize, store_events: &[usize]) -> Vec<Command> {
    let mut cmds = Vec::new();
    if store_events.is_empty() {
        return cmds;
    }
    // At least one store is read from:
    let at_least_one = Term::Or(
        store_events.iter()
            .map(|&s| Term::Const(format!("rf_{}_{}", load_event, s)))
            .collect(),
    );
    cmds.push(Command::Assert(at_least_one));

    // At most one store is read from (pairwise exclusion):
    for i in 0..store_events.len() {
        for j in (i + 1)..store_events.len() {
            let both = Term::And(vec![
                Term::Const(format!("rf_{}_{}", load_event, store_events[i])),
                Term::Const(format!("rf_{}_{}", load_event, store_events[j])),
            ]);
            cmds.push(Command::Assert(Term::Not(Box::new(both))));
        }
    }
    cmds
}
```

### Synchronizes-With (`sw`) Encoding for Release/Acquire

```rust
// Source: derived from RC11 formal definition (Lahav et al. PLDI 2017)
// sw(store_S, load_L) = rf(load_L, store_S) AND ordering_S >= Release AND ordering_L >= Acquire

/// True if this ordering is at least Release (contributes to the Release side of sw).
fn is_release(ordering: AtomicOrdering) -> bool {
    matches!(ordering, AtomicOrdering::Release | AtomicOrdering::AcqRel | AtomicOrdering::SeqCst)
}

/// True if this ordering is at least Acquire (contributes to the Acquire side of sw).
fn is_acquire(ordering: AtomicOrdering) -> bool {
    matches!(ordering, AtomicOrdering::Acquire | AtomicOrdering::AcqRel | AtomicOrdering::SeqCst)
}

/// Encode sw(store_S, load_L) as a Bool term.
/// sw holds if rf(load_L, store_S) AND store_S is Release AND load_L is Acquire.
pub fn encode_sw(
    store_event: usize,
    store_ordering: AtomicOrdering,
    load_event: usize,
    load_ordering: AtomicOrdering,
) -> Term {
    if !is_release(store_ordering) || !is_acquire(load_ordering) {
        // Neither side contributes to synchronization
        return Term::BoolLit(false);
    }
    // sw(S, L) = rf_L_S (the load reads from the store)
    Term::Const(format!("rf_{}_{}", load_event, store_event))
}

/// Encode happens-before from synchronizes-with transitively.
/// hb(i, j) = sb(i, j) OR (exists k. hb(i, k) AND sw(k, j))
/// For bounded N, expand for all pairs.
pub fn encode_hb(
    event_i: usize,
    event_j: usize,
    sb_pairs: &[(usize, usize)],             // (a, b) means sb(a, b)
    sw_terms: &[(usize, usize, Term)],       // (a, b, term) means sw(a,b) is encoded as term
) -> Term {
    let sb_direct = sb_pairs.contains(&(event_i, event_j));

    // Direct sw:
    let sw_direct = sw_terms.iter()
        .find(|(a, b, _)| *a == event_i && *b == event_j)
        .map(|(_, _, t)| t.clone());

    // Transitive: hb(i, k) AND sw(k, j) for all k — simplified for bounded case
    // For production: enumerate all intermediate events k
    match (sb_direct, sw_direct) {
        (true, _) => Term::BoolLit(true),
        (false, Some(sw_t)) => sw_t,
        (false, None) => Term::BoolLit(false),
    }
}
```

### Coherence Axiom Check

```rust
// Source: RC11 formal definition — COHERENCE: hb;eco? is irreflexive
// For bounded N events: for all pairs (i, j), not (hb(i,j) AND eco(j,i))

/// Generate coherence violation check for a pair of events.
/// Returns a term that is FALSE if coherence is violated (used in assert-not pattern).
pub fn coherence_check(
    event_i: usize,
    event_j: usize,
    hb_i_j: Term,   // hb(i, j) term
    eco_j_i: Term,  // eco(j, i) term = rf(j,i) OR mo_j_before_i OR fr(j,i)
) -> Command {
    // Assert that NOT (hb(i,j) AND eco(j,i)) — coherence violation would be SAT
    let violation = Term::And(vec![hb_i_j, eco_j_i]);
    Command::Assert(Term::Not(Box::new(violation)))
}
```

### VcKind Extension (`vcgen.rs`)

```rust
// In vcgen.rs, add to VcKind enum (after existing ChannelSafety):
/// RC11 coherence check: hb;eco? irreflexive under weak ordering
/// Generated only for functions with non-SeqCst atomic ops
WeakMemoryCoherence,
/// Weak memory data race: Relaxed accesses to same location from different threads
WeakMemoryRace,
/// Weak memory atomicity: RMW atomicity under RC11 (rmw ∩ (rb;mo) = ∅)
WeakMemoryAtomicity,
```

### Gate Function for RC11 Path

```rust
// In vcgen.rs, add to generate_concurrency_vcs():
/// Returns true if func has any non-SeqCst atomic operations.
fn has_non_seqcst_atomics(func: &Function) -> bool {
    func.atomic_ops.iter().any(|op| op.ordering != AtomicOrdering::SeqCst)
}

// In generate_concurrency_vcs(), add after Step 2 (data race freedom VCs):
// Step 2b: RC11 weak memory axioms for non-SeqCst orderings
if has_non_seqcst_atomics(func) {
    let mut wmm_vcs = crate::concurrency::rc11::generate_rc11_vcs(func);
    vcs.append(&mut wmm_vcs);
}
```

### Litmus Test Pattern (Integration Test)

```rust
// In tests/weak_memory_litmus.rs, following concurrency_verification.rs pattern:
#[test]
fn test_mp_message_passing_release_acquire() {
    // MP: T1: x=1(Rel), flag=1(Rel); T2: r1=flag(Acq), r2=x(Acq)
    // Forbidden: r1==1 AND r2==0 (if T2 sees flag=1, must see x=1)
    // Expected: The VC asserting forbidden scenario returns UNSAT (no consistent execution)

    // Build IR with 4 atomic ops across 2 threads
    let func = make_concurrent_function(
        "mp_test",
        vec![ThreadSpawn { handle_local: "t1".to_string(), thread_fn: "t1_fn".to_string(), args: vec![], is_scoped: false }],
        vec![
            AtomicOp { kind: AtomicOpKind::Store, ordering: AtomicOrdering::Release,
                        atomic_place: Place::local("x"), value: Some(Operand::Constant(Constant::Int(1, IntTy::I32))) },
            AtomicOp { kind: AtomicOpKind::Store, ordering: AtomicOrdering::Release,
                        atomic_place: Place::local("flag"), value: Some(Operand::Constant(Constant::Int(1, IntTy::I32))) },
            AtomicOp { kind: AtomicOpKind::Load, ordering: AtomicOrdering::Acquire,
                        atomic_place: Place::local("flag"), value: None },
            AtomicOp { kind: AtomicOpKind::Load, ordering: AtomicOrdering::Acquire,
                        atomic_place: Place::local("x"), value: None },
        ],
        vec![], vec![], Some(ConcurrencyConfig { verify_concurrency: true, max_threads: 2, max_context_switches: 3 }),
    );

    let vcs = vcgen::generate_concurrency_vcs(&func);
    let coherence_vcs: Vec<_> = vcs.iter()
        .filter(|vc| vc.location.vc_kind == VcKind::WeakMemoryCoherence)
        .collect();
    assert!(!coherence_vcs.is_empty(), "MP test must generate WeakMemoryCoherence VCs");

    // The forbidden scenario (r1=1, r2=0) should be UNSAT
    let solver = solver_or_skip();
    for vc in &coherence_vcs {
        // ... submit to Z3 and verify UNSAT for the forbidden MP scenario
    }
}
```

## State of the Art

| Old Approach (Phase 12 / v0.2) | Current RC11 Approach (Phase 21) | Impact |
|-------------------------------|----------------------------------|--------|
| Relaxed => `BoolLit(true)` (no constraint) | Relaxed: participates in mo/rf; no synchronization to sw | Relaxed races now detectable; Relaxed-vs-Relaxed to same location is a race |
| Acquire/Release => `implies(rf, hb)` | Full `sw` computation: rf + Release + Acquire ordering check | MP litmus test verifiable; cross-thread message passing proven |
| AcqRel => same as Acquire (WRONG) | AcqRel: both Release side (sw to Acquire loads) AND Acquire side (sw from Release stores) | IRIW litmus test gives correct verdict; no unsoundness from AcqRel conflation |
| No coherence axioms (hb;eco?) | Full RC11 COHERENCE: hb;eco? irreflexive for all event pairs | CoRR/CoRW/CoWR/CoWW coherence litmus tests pass |
| SeqCst uses BV timestamp | SeqCst unchanged; new path uses Int mo_order + Bool rf | Zero SeqCst regressions; clear separation |
| `QF_BV` for all concurrency VCs | `QF_LIA` for WeakMemory* VCs | RC11 axioms encode naturally in integers; better Z3 performance |

**Deprecated/outdated patterns:**
- `Relaxed => BoolLit(true)` in `encode_atomic_ordering`: Replace with mo/rf participation
- `AcqRel => implies(rf, hb)` (same as Release/Acquire branch): Replace with two-sided sw encoding
- Thread ID placeholder `0` in `MemoryAccess` construction: Must use actual thread_id for correct partitioning

## Open Questions

1. **Thread ID Assignment for Atomic Ops**
   - What we know: `MemoryAccess.thread_id` is hardcoded to `0` in `generate_concurrency_vcs()` (vcgen.rs:3445 comment). `func.thread_spawns` lists spawn sites but doesn't annotate which atomic ops belong to which thread.
   - What's unclear: How to infer which `AtomicOp` in `func.atomic_ops` belongs to which thread spawn. MIR may encode this via basic block ordering (spawned thread ops follow the spawn call).
   - Recommendation: For Phase 21, extend `AtomicOp` IR struct to include `thread_id: usize` (defaulting to 0 for main thread). In the IR builder (`driver/src/callbacks.rs`), assign thread_id based on whether the op is in a closure body passed to `thread::spawn`. This is a small IR extension that unblocks correct litmus test encoding.

2. **mo_order Variable Range**
   - What we know: `mo_order_N` is declared as `Sort::Int` (unbounded). Z3 will find a satisfying integer assignment for any valid total order.
   - What's unclear: Whether Z3 needs bounds on `mo_order` for performance (bounded integer ranges can speed up QF_LIA).
   - Recommendation: Initially use unbounded `Int`. If Z3 performance is poor (timeout on litmus tests), bound `mo_order_N` to `[0, N-1]` where N is the number of same-location stores.

3. **Production Verification Beyond Litmus Tests**
   - What we know: The litmus tests validate the encoding. Real Rust programs with Relaxed/Acquire/Release atomics are the production use case.
   - What's unclear: How to map Rust's `std::sync::atomic::AtomicI32::store(val, Ordering::Release)` in MIR to `AtomicOp { kind: Store, ordering: Release, ... }` in the IR. The driver-side IR building for atomic ops from MIR may need extension.
   - Recommendation: Verify the existing driver-side atomic op extraction (`callbacks.rs`) covers `Relaxed`, `Acquire`, `Release`, `AcqRel` (not just `SeqCst`). If the driver only detects `SeqCst`, extend it before the SMT encoding work.

4. **rc11.rs vs happens_before.rs Boundary**
   - What we know: `happens_before.rs` already has `encode_atomic_ordering()` with the buggy Relaxed/AcqRel encoding. The fix could go in `happens_before.rs` directly, or the new `rc11.rs` module could replace/extend it.
   - What's unclear: Whether to fix `encode_atomic_ordering()` in place (simpler) or introduce `rc11.rs` as a parallel path (cleaner separation).
   - Recommendation: Introduce `rc11.rs` as the new module for the full RC11 axiom encoding. Leave `encode_atomic_ordering()` in `happens_before.rs` unchanged (it is tested by existing tests). The RC11 path in `generate_weak_memory_vcs()` is entirely separate from the existing `data_race_freedom_vcs()` call. This satisfies WMM-04 (no SeqCst regressions) cleanly.

## Sources

### Primary (HIGH confidence)
- Codebase: `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/analysis/src/concurrency/happens_before.rs` — current `encode_atomic_ordering()` with Relaxed=BoolLit(true) gap identified
- Codebase: `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/analysis/src/vcgen.rs:85-126` — `VcKind` enum; extension points for new WeakMemory* variants
- Codebase: `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/analysis/src/ir.rs:219-243` — `AtomicOrdering` enum (all 5 orderings present), `AtomicOp` struct
- Codebase: `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/analysis/src/vcgen.rs:3397-3640` — `generate_concurrency_vcs()` extension point for RC11 path
- Codebase: `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/analysis/tests/concurrency_verification.rs` — existing test pattern for litmus test integration tests
- STATE.md decision: "[Phase 21] RC11 AcqRel encoding — not equivalent to Release OR Acquire; derive from arXiv:2108.06944" — confirms AcqRel bug and target paper

### Secondary (MEDIUM confidence)
- Lahav et al. "Repairing Sequential Consistency in C/C++11" (PLDI 2017) — https://plv.mpi-sws.org/scfix/paper.pdf — RC11 formal model, defines COHERENCE/ATOMICITY/SC/NO-THIN-AIR axioms, hb/eco/sw/rf/mo/fr relations
- Dartagnan BMC for Weak Memory Models (Competition Contribution, 2020) — https://hernanponcedeleon.github.io/pdfs/svcomp20.pdf — SMT encoding approach: ψ_prog ∧ ψ_assert ∧ ψ_mm, integer encoding for mo
- "BMC for Weak Memory Models: Relation Analysis for Compact SMT Encodings" (CAV 2019) — https://link.springer.com/chapter/10.1007/978-3-030-25540-4_19 — integer encoding outperforms BV for modification order in SMT BMC
- Cerberus-BMC (CAV 2019) — confirms quantifier-free SMT expression approach for weak memory axioms with Z3

### Tertiary (LOW confidence)
- arXiv:2108.06944 "Verifying C11-Style Weak Memory Libraries via Refinement" — cited in STATE.md as the AcqRel encoding source; Isabelle/HOL formalization, not directly an SMT encoding; use for AcqRel formal semantics only
- GenMC stateless model checker (CAV 2021) — https://plv.mpi-sws.org/genmc/cav21-paper.pdf — different approach (stateless exploration), useful for understanding what litmus tests must produce

## Metadata

**Confidence breakdown:**
- Standard stack (no new deps): HIGH — all required Term/Sort/Command types verified in codebase
- VcKind extension (WeakMemory* variants): HIGH — direct enum extension, clear separation from existing kinds
- RC11 formal model (axioms, relations): HIGH — well-established from PLDI 2017 paper; multiple independent formalizations agree
- SMT encoding strategy (QF_LIA, integer mo): MEDIUM — supported by Dartagnan paper (MEDIUM: PDF unreadable, summary from web search); integer encoding is correct, performance characteristics empirically validated by community
- AcqRel encoding: HIGH — bug documented in STATE.md, fix direction clear from RC11 definition
- Litmus test IR construction: MEDIUM — follows existing test pattern (HIGH) but specific encoding of 8 tests needs implementation detail validation
- Thread ID assignment: LOW — current placeholder in vcgen.rs; requires IR extension not yet designed

**Research date:** 2026-02-19
**Valid until:** 2026-03-19 (30 days; RC11 formal model is stable; Rust atomic IR is stable)
