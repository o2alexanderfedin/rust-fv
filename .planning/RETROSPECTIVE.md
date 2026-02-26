# Project Retrospective — rust-fv

*A living document updated after each milestone. Lessons feed forward into future planning.*

---

## Milestone: v0.5 — SMT Completeness

**Shipped:** 2026-02-24 (UAT validated 2026-02-25)
**Phases:** 2 (Phases 28-29) + 1 UAT phase | **Plans:** 11 total | **Sessions:** ~3

### What Was Built

- Numeric `as`-cast encoding (`encode_cast()`) — sign-extension, zero-extension, truncation, FPA semantics
- Match/if-let/while-let discriminant binding via `Rvalue::Discriminant` uninterpreted selector
- Array bounds VCs + `Rvalue::Len` as named SMT constant; generic `where`-clause premises as `Assert`
- CastKind preservation (exhaustive match), `AggregateKind::Adt/Closure`, `SetDiscriminant/Assume` IR variants
- Float-to-int soundness fix (`fp.to_sbv/fp.to_ubv RTZ`); `TyKind::Param → ir::Ty::Generic`
- Missing rvalue variants: `CopyForDeref`, `RawPtr`, `Repeat`
- Projected LHS struct field mutation via SMT functional record update
- UAT Phase 00: 22-item test suite validating v0.4+v0.5 deliverables end-to-end (all PASS)

### What Worked

- TDD scaffold (Plan 01) as gating mechanism: 10 RED tests defined the exact scope before any implementation — prevented scope creep and gave instant feedback on completion
- Exhaustive match patterns in `mir_converter.rs` — compiler enforces completeness on MIR API changes; far better than wildcard arms
- Post-archive UAT phase: running UAT as a separate Phase 00 after archiving v0.5 provided independent validation without polluting the implementation phases
- `infer_operand_type()` fallback pattern for cast source types — handles opaque operands gracefully without panics

### What Was Inefficient

- Rvalue::Len for `for`/iterator loops deferred to v0.6 — the initial scope estimate was optimistic; VCGEN-01 ended up partial (for loops harder than simple index access)
- `vcgen_06_set_discriminant_assertion` test ignored — SetDiscriminant VCGen encoding deferred after IR variant added (IR side done, VCGen side not)
- Some decisions required multiple sub-plans to fully resolve (e.g., `Cow<Ty>` for Downcast narrowing discovered mid-implementation)

### Patterns Established

- **TDD scaffold as Phase 01**: Always write RED tests as the first plan; GREEN tests on later plans confirm completion — no guesswork about "is this done?"
- **Exhaustive match for external API coverage**: Use exhaustive enum matches on MIR/IR types so compiler enforces coverage when upstream changes
- **Post-archive UAT phase**: Separate UAT validation phase (Phase 00) after milestone archive provides clean end-to-end validation without complicating implementation phases
- **Functional record update pattern**: SMT `mk-StructName` with ALL fields — changed field gets new_val, others get `selector(base)` — correct arity by construction

### Key Lessons

1. **Scope TDD tests precisely**: When writing the scaffold, test the exact behavior (e.g., `vcgen_01_array_index` tests VCGen auto-generation for `Projection::Index`, not `Assert` terminator) — mismatch wastes implementation cycles
2. **Defer vs deferred-but-document**: When deferring (VCGEN-01 partial, SetDiscriminant VCGen), document the exact gap in MILESTONES.md Known Gaps so v0.6 has a clear starting point
3. **UAT scope creep risk**: A 22-item UAT for two milestones (v0.4+v0.5) is the right size — larger would become a project unto itself

### Cost Observations

- Model: sonnet (balanced profile throughout)
- Pattern: Phase research + plan check + executor + verifier subagents per plan
- Notable: TDD scaffold plan was the most value-dense — defined all requirements upfront and made subsequent plans mechanical

---

## Milestone: v0.4 — Full Rust Verification

**Shipped:** 2026-02-23
**Phases:** 9 (Phases 19-27) | **Plans:** 27 | **Sessions:** ~6

### What Was Built

- Typed counterexample generation (CEX-01..04) — Rust values not SSA/hex, ariadne labels, JSON, VSCode wiring
- Separation logic (SEP-01..04) — `pts_to`, separating conjunction, frame rule, recursive ghost predicates
- Weak memory models (WMM-01..04) — full RC11, 8 litmus tests, Relaxed/Acquire/Release data race detection
- Higher-order closures (HOF-01..02) — `fn_spec` entailments via AUFLIA, `FnMut` SSA-versioned environments
- Async/await (ASY-01..02) — sequential polling model, `#[state_invariant]`, poll_iteration/await_side IDE rendering
- Gap closure phases: SEP-04 ghost predicate wiring, CEX v2 IDE integration, WMM-03 race fix, async IDE fidelity

### What Worked

- Separate heap domain for separation logic (not byte-array model) — avoided conflict with `heap_model.rs`
- `Arc<GhostPredicateDb>` threading through `VerificationTask` — compiler enforced thread-safety, clean boundary
- Post-transform MIR detection for async: fallback to SwitchInt discriminant counting (no `Yield` terminators at `after_analysis`)
- "Gap closure phases" pattern: dedicated phases (24-27) to fix integration gaps found during 19-23 — better than trying to get it right the first time

### What Was Inefficient

- Ghost predicate wiring gap (SEP-04) discovered post-implementation — required Phase 24 to fix production path
- VSCode counterexample v2 schema mismatch — required Phase 25 to close IDE gap
- WMM-03 `Assert(BoolLit(true))` fix — WeakMemoryRace VC was trivially satisfied; required Phase 26
- Async counterexample IDE fidelity — poll_iteration/await_side gap required Phase 27

### Patterns Established

- **Gap closure phases**: After a milestone, run dedicated phases to fix integration gaps — more reliable than trying to predict all wiring issues upfront
- **Violation-detection semantics for coherence VCs**: Assert violation condition (SAT = issue found) vs Assert invariant (UNSAT = issue found) — consistent with WeakMemoryRace, WeakMemoryCoherence

### Key Lessons

1. **Integration gaps are predictable**: For features spanning crate boundaries (driver → analysis → IDE), plan a gap-closure phase budget (15-20% of implementation phases)
2. **QF_LIA for ordering relations**: Integer sequences for mo/rf/co are simpler than bitvectors; avoid QF_BV complexity for non-arithmetic ordering constraints

---

## Cross-Milestone Trends

### Process Evolution

| Milestone | Phases | Plans | Key Process Change |
|-----------|--------|-------|-------------------|
| v0.1 | 5 | 17 | Initial pipeline — TDD soundness/completeness test suites from day 1 |
| v0.2 | 7 | 21 | Added gap-tolerance: phases allowed to depend on previous phase's gap closure |
| v0.3 | 6 | 20 | VSCode extension added TypeScript layer; research phases started for complex domains |
| v0.4 | 9 | 27 | Gap closure phases pattern established; post-archive UAT introduced |
| v0.5 | 2+1 | 11 | TDD scaffold as Phase 01 gating mechanism; post-archive UAT phase validated all 22 items |

### Cumulative Quality

| Milestone | Tests (Rust) | Notes |
|-----------|-------------|-------|
| v0.1 | 1,741 | Soundness + completeness suites established |
| v0.2 | 2,264 | +523 tests for advanced verification features |
| v0.3 | 1,613 lib | Recount (lib tests only); TypeScript tests added for VSCode |
| v0.4 | Not counted | Focused on integration correctness over raw test count |
| v0.5 | All 93 plans' tests green; 22/22 UAT items pass | TDD scaffold → all RED tests GREEN |

### Top Lessons (Verified Across Milestones)

1. **TDD scaffold first**: Writing RED tests before implementation consistently produces cleaner, more focused implementations with no ambiguous "is this done?" moments
2. **Gap closure budget**: Budget 15-20% of phases for integration gap closure — consistently needed across v0.4, v0.5
3. **Post-archive UAT**: Separate end-to-end UAT phase after archiving provides clean validation signal — adopted v0.4 onwards
4. **Exhaustive match on external APIs**: Compiler-enforced completeness for MIR/IR types is worth the verbosity — catches API changes automatically
5. **Layer separation for cross-domain features**: Features touching driver→analysis→IDE always have integration gaps; design clear handoff boundaries upfront
