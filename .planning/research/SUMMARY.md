# Project Research Summary

**Project:** rust-fv v0.2 Advanced Verification
**Domain:** Formal verification tool enhancement (SMT-based Rust verifier)
**Researched:** 2026-02-11
**Confidence:** MEDIUM-HIGH

## Executive Summary

This research covers integrating 7 advanced verification features into rust-fv: recursive functions, closures, trait objects, unsafe code verification, lifetime reasoning, floating-point arithmetic, and concurrency. The v0.1 foundation (1,741 tests, 43,621 LOC, 5-crate architecture) is solid and well-positioned for extension. All advanced features are achievable through careful SMT encoding and VCGen extensions—this is primarily an **encoding challenge**, not a dependency challenge.

The recommended approach prioritizes features by impact × feasibility: start with recursive functions and closures (HIGH user value, MEDIUM complexity, build on existing inter-procedural verification), then trait objects and lifetimes (extend existing prophecy variables), defer floating-point and concurrency to later phases due to performance concerns. Critical insight: **NO major new dependencies required**—only petgraph 0.8.3 for call graph analysis. The existing Z3 stack already supports quantifiers, datatypes, floating-point theory, and uninterpreted functions.

Key risks center on **underestimating SMT encoding complexity**: features that seem like "just add support for X" require soundness-critical decisions (termination checking, capture semantics, open vs closed-world vtables, NaN handling). User chose to implement ALL 7 features in v0.2 despite recommendation to defer FP/concurrency—this increases scope from 4-5 table stakes features to full suite, estimated ~14,200 LOC total. Mitigation: phased implementation following dependency order (recursion → closures → traits → lifetimes → unsafe → FP → concurrency), with dedicated phase research for high-complexity areas.

## Key Findings

### Recommended Stack

**No major new dependencies required.** The v0.1 stack (Z3 4.13+, syn 2.0, rustc APIs, 5-crate workspace) already provides necessary theories. One addition: petgraph 0.8.3 for recursive function call graph analysis (Tarjan's SCC algorithm). Optional: polonius 0.3.0 for advanced lifetime reasoning (start without, add if basic rustc borrow checker output insufficient).

**Core capabilities already available:**
- **Z3 quantifiers** (recursive functions via uninterpreted functions + axioms)
- **Z3 datatypes** (closures as struct environments, trait objects as sum types)
- **Z3 FloatingPoint theory** (IEEE 754 via QF_FP/QF_FPBV logics)
- **rustc MIR APIs** (closure capture modes, trait vtables, borrow checker facts)

**Critical stack insight:** Advanced features are **encoding challenges**, not dependency challenges. Work is in VCGen and SMT translation logic, not in acquiring new tools.

### Expected Features

**Table stakes (must have for advanced verifier):**
- **Recursive function verification** — users expect termination checking + correctness proofs (factorial, tree traversal ubiquitous)
- **Simple closures** — Rust uses closures everywhere (iterators, callbacks); must verify closure-using code
- **Basic trait objects** — Box&lt;dyn Trait&gt; common in real code; dynamic dispatch verification expected
- **Basic lifetime reasoning** — lifetimes are Rust's defining feature; must respect lifetime constraints in verification
- **Unsafe code detection** — flag unsafe blocks, warn users, perform basic pointer validity checks

**Differentiators (set apart from other tools):**
- **Advanced recursive verification** — mutual recursion, fuel control, separate proof functions (matches Verus/F*)
- **Higher-order closures** — verify iterator combinators (map, filter, fold) with FnMut/FnOnce semantics
- **Floating-point correctness** — prove numerical properties beyond safety (accuracy bounds, NaN handling)
- **Concurrent separation logic** — verify lock-free algorithms, atomic invariants (Creusot 0.9.0 / VerusSync-style)

**Anti-features (avoid or limit scope):**
- **Verify all unsafe code automatically** — pointer aliasing undecidable; requires manual annotations or defer to Miri
- **Full FP verification by default** — SMT FPA theory slow; most code verifies logic, not numerics
- **Automatic closure contract inference** — requires specification entailments (academic frontier); require explicit specs
- **General recursion without decreases clause** — termination undecidable; unsound to assume termination

**User decision:** Implement ALL 7 features in v0.2 (including FP and concurrency, despite recommendation to defer). This increases scope but matches user's vision for comprehensive advanced verification.

### Architecture Approach

The existing 5-crate architecture (macros/, smtlib/, solver/, analysis/, driver/) provides clean extension points. Each advanced feature adds:
1. New IR variants in `analysis/ir.rs` (opt-in via `Option<T>`)
2. New encoding modules (`analysis/encode_*.rs` per feature)
3. New VCs (`VcKind` enum extended with `Termination`, `ClosureWellFormed`, etc.)
4. New SMT theories (`smtlib/<theory>.rs` modules)

**Major components to add:**
1. **analysis/termination.rs** + **recursion_encoding.rs** — uninterpreted functions + fuel-based unfolding
2. **analysis/closure_conversion.rs** — defunctionalization to first-order SMT datatypes
3. **analysis/vtable.rs** + **trait_encoding.rs** — sum types over trait implementors
4. **analysis/memory_model.rs** + **unsafe_analysis.rs** — heap-as-array + validity predicates
5. **analysis/lifetime_analysis.rs** — borrow graph + region ordering (extends existing prophecy)
6. **smtlib/fpa_theory.rs** — IEEE 754 floating-point terms
7. **analysis/concurrency.rs** — happens-before relations (bounded verification)

**Estimated effort:** ~14,200 LOC (10,800 new + 3,400 modified). Modular encoding pattern ensures incremental integration without disrupting v0.1 functionality.

### Critical Pitfalls

1. **Recursive function termination without measure functions** — SMT solver accepts non-terminating functions (soundness catastrophe). **Mitigation:** Require mandatory `#[decreases(expr)]` annotation, check well-founded measure decreases on every recursive call.

2. **Closure capture semantics mismodeling** — treating all closures as `Fn` (immutable) misses `FnMut` mutations and `FnOnce` consumption. **Mitigation:** Detect closure trait bounds in MIR, encode environment capture modes, use prophecy variables for mutable captures.

3. **Trait object vtable open-world vs closed-world assumptions** — assuming all trait impls known at verification time breaks when downstream crate adds new impl. **Mitigation:** Default to open-world for public traits (uninterpreted functions), closed-world opt-in via `#[sealed]`.

4. **Unsafe code verification soundness boundaries** — axiomatizing unsafe operations creates soundness holes when unsafe code has bugs. **Mitigation:** Separate unsafe analysis pipeline, require explicit `#[unsafe_requires]` annotations, mark unsafe functions as `#[verifier::trusted]` or `#[verifier::verify_unsafe]`.

5. **Non-lexical lifetimes (NLL) complexity** — using lexical scope for lifetimes rejects code accepted by NLL borrow checker (usability failure). **Mitigation:** Use NLL-based lifetime reasoning (track lifetime based on last use in CFG, not lexical scope).

6. **Floating-point NaN propagation breaks postcondition reasoning** — verifier proves `result > 0.0` but runtime produces NaN. **Mitigation:** Explicit NaN checks in VCs, require `!x.is_nan()` preconditions, use SMT-LIB FloatingPoint theory predicates.

7. **Concurrency state explosion with weak memory models** — enumerating all interleavings causes SMT timeout/OOM. **Mitigation:** Bounded verification (limit context switches), start with sequential consistency only, defer relaxed atomics to later phase.

## Implications for Roadmap

Based on research, suggested 7-phase structure for v0.2:

### Phase 1: Recursive Functions
**Rationale:** Foundation for other features; builds on existing inter-procedural verification; termination checking is well-understood (F*, Verus, Dafny all use decreases clauses).
**Delivers:** `#[decreases(measure)]` annotation support, termination VC generation, uninterpreted function encoding in SMT, mutual recursion support.
**Addresses Features:** Table stakes recursive verification.
**Avoids Pitfall:** Non-termination soundness bug (Pitfall #1) via mandatory measure checking.
**Stack Elements:** petgraph 0.8.3 for call graph SCC analysis, Z3 quantifiers (already available).
**Estimated LOC:** ~1,800 (termination.rs ~800, recursion_encoding.rs ~600, IR changes ~200, tests ~200).

### Phase 2: Closures
**Rationale:** Enables verification of iterator code (map, filter, fold); builds on ownership reasoning (DONE in v0.1); defunctionalization pattern well-established.
**Delivers:** `closure!(requires, ensures, |args| body)` syntax, environment capture encoding as SMT datatypes, `Fn` trait support (immutable captures).
**Addresses Features:** Table stakes simple closures.
**Avoids Pitfall:** Capture semantics mismodeling (Pitfall #2) via MIR trait bound detection.
**Stack Elements:** Z3 datatypes (already available), extend encode_sort.rs.
**Estimated LOC:** ~2,200 (closure_conversion.rs ~1,000, encode_closure.rs ~800, IR changes ~200, tests ~200).

### Phase 3: Trait Objects
**Rationale:** Common in real Rust code; builds on closure encoding patterns (sum types); Kani 2022 paper demonstrates vtable verification feasibility.
**Delivers:** Trait-level contracts, vtable modeling, closed-world verification for sealed traits, dynamic dispatch VCs.
**Addresses Features:** Table stakes basic trait objects.
**Avoids Pitfall:** Open-world unsoundness (Pitfall #3) via explicit `#[sealed]` requirement.
**Stack Elements:** Z3 uninterpreted functions for open-world fallback, sum types for closed-world.
**Estimated LOC:** ~1,800 (vtable.rs ~800, trait_encoding.rs ~700, IR changes ~100, tests ~200).

### Phase 4: Lifetime Reasoning
**Rationale:** Extends existing prophecy variables (v0.1 Phase 4); NLL-based tracking essential for usability; borrow graph analysis well-documented in Polonius.
**Delivers:** Lifetime parameter tracking, borrow expiry verification, region outlives constraints in SMT, NLL-based (not lexical) lifetime reasoning.
**Addresses Features:** Table stakes basic lifetime reasoning.
**Avoids Pitfall:** NLL divergence (Pitfall #5) via control-flow-sensitive tracking.
**Stack Elements:** Optional polonius 0.3.0 (start without, add if needed), extend encode_prophecy.rs.
**Estimated LOC:** ~2,000 (lifetime_analysis.rs ~900, region_encoding.rs ~700, IR changes ~200, tests ~200).

### Phase 5: Unsafe Code Detection
**Rationale:** Safety-critical for Rust verifier; basic checks (null, bounds) achievable with heap-as-array model; full separation logic deferred to research phase.
**Delivers:** Flag unsafe blocks, basic pointer validity checks, `#[unsafe_requires]` / `#[unsafe_ensures]` annotations, explicit trust boundaries.
**Addresses Features:** Table stakes unsafe detection.
**Avoids Pitfall:** Unsafe soundness boundaries (Pitfall #4) via separate analysis pipeline and explicit axiomatization.
**Stack Elements:** Z3 array theory (already available), memory model encoding.
**Estimated LOC:** ~2,400 (memory_model.rs ~1,000, unsafe_analysis.rs ~900, IR changes ~300, tests ~200).

### Phase 6: Floating-Point Verification
**Rationale:** SMT-LIB FPA theory standardized (IEEE 754); Z3 support mature; user wants ALL features in v0.2; deferred by other tools but achievable as opt-in.
**Delivers:** FPA theory integration, NaN/Inf handling in VCs, rounding mode encoding, IEEE 754 edge case tests.
**Addresses Features:** Differentiator FP correctness (opt-in for expert users).
**Avoids Pitfall:** NaN propagation unsoundness (Pitfall #6) via explicit `isNaN` checks in all float VCs.
**Stack Elements:** Z3 QF_FP/QF_FPBV (already available), new fpa_theory.rs module.
**Estimated LOC:** ~1,800 (fpa_theory.rs ~800, encode_term.rs changes ~600, vcgen.rs changes ~200, tests ~200).
**Performance Warning:** FPA theory 2-10x slower than bitvectors; document performance expectations.

### Phase 7: Concurrency Verification
**Rationale:** Highest complexity; user wants ALL features; bounded verification feasible (limit context switches); sequential consistency first, defer weak memory models.
**Delivers:** Bounded thread interleaving, happens-before analysis, atomic operation encoding (sequential consistency only), data race VCs.
**Addresses Features:** Differentiator concurrent separation logic (limited scope: bounded + SC only).
**Avoids Pitfall:** State explosion (Pitfall #7) via bounded model checking (configurable max threads/context switches).
**Stack Elements:** Z3 relations (already available), new concurrency.rs module.
**Estimated LOC:** ~2,200 (concurrency.rs ~1,000, sync_encoding.rs ~800, IR changes ~200, tests ~200).
**Limitation:** No weak memory models (Relaxed atomics) in v0.2; document as future work.

### Phase Ordering Rationale

- **Phases 1-2 (Recursion → Closures):** Both extend inter-procedural verification; recursion first because closures may capture recursive functions.
- **Phase 3 (Trait Objects):** Builds on closure encoding patterns (sum types, datatype matching); requires recursion/closures for trait method verification.
- **Phase 4 (Lifetimes):** Extends v0.1's prophecy variables; needed before unsafe (unsafe code reasoning requires lifetime validity).
- **Phase 5 (Unsafe):** Depends on lifetimes for pointer validity reasoning; memory model needed before concurrency.
- **Phases 6-7 (FP → Concurrency):** Most isolated/complex; can be implemented in parallel if resources allow; FP first because concurrency may need FP for atomic counters.

### Research Flags

**Phases needing deeper research during planning:**
- **Phase 3 (Trait Objects):** Vtable encoding for open-world (public traits) unclear; research spike on uninterpreted function approach vs sum type limitations.
- **Phase 7 (Concurrency):** Bounded verification strategy (partial order reduction vs full interleaving enumeration) needs prototyping; research spike on Verus/Creusot approaches.

**Phases with standard patterns (skip phase research):**
- **Phase 1 (Recursion):** Well-documented in F*/Dafny/Verus; uninterpreted function encoding proven.
- **Phase 2 (Closures):** Defunctionalization standard; Creusot/Prusti provide reference.
- **Phase 4 (Lifetimes):** NLL well-documented; Polonius provides borrow graph analysis reference.
- **Phase 6 (FP):** SMT-LIB FPA theory standardized; Z3 integration straightforward.

## Confidence Assessment

| Area | Confidence | Notes |
|------|------------|-------|
| Stack | HIGH | No major new dependencies; petgraph well-established; Z3 theories validated |
| Features | HIGH | All features documented in existing tools (Verus, Creusot, Kani); user expectations clear |
| Architecture | MEDIUM-HIGH | 5-crate structure proven extensible; LOC estimates based on similar projects; integration points identified |
| Pitfalls | MEDIUM-HIGH | Critical pitfalls well-documented (termination, NaN, state explosion); research papers provide mitigation strategies |

**Overall confidence:** MEDIUM-HIGH

Research is thorough (official docs + academic papers + 2024-2026 tools), but two areas have uncertainty:
1. **Trait objects open-world encoding:** No existing tool fully solves this; requires design decisions during implementation.
2. **Concurrency performance:** Bounded verification scalability depends on program structure (hard to predict).

### Gaps to Address

**Architecture gaps:**
- **Trait object vtable encoding:** Research identified sum types (closed-world) and uninterpreted functions (open-world), but hybrid approach unclear. **Resolution:** Prototype both in Phase 3, measure precision vs performance tradeoff.
- **Concurrency interleaving bounds:** What limits (max threads, max context switches) are practical? **Resolution:** Research spike in Phase 7 planning; benchmark against Creusot/CBMC approaches.

**Feature gaps:**
- **Higher-order closures (FnMut/FnOnce):** Specification entailments not fully detailed in research. **Resolution:** Phase 2 implements `Fn` only; defer FnMut/FnOnce to v0.3 if complexity exceeds estimates.
- **Floating-point performance:** FPA theory 2-10x slower, but exact impact on real code unknown. **Resolution:** Document performance expectations; offer bitvector fallback for bitwise-exact FP.

**Integration gaps:**
- **Polonius necessity:** Research unclear if polonius required or if rustc borrow checker output sufficient. **Resolution:** Start without polonius (Phase 4); add only if basic ownership reasoning insufficient.
- **Unsafe verification scope:** Full separation logic out of scope, but bounded verification (Kani-style) feasibility unclear. **Resolution:** Phase 5 implements detection + basic checks; defer bounded verification to v0.3.

## Sources

### Primary (HIGH confidence)

**Stack Research:**
- [petgraph 0.8.3 on crates.io](https://crates.io/crates/petgraph) — call graph analysis
- [SMT-LIB FloatingPoint Theory](https://smt-lib.org/theories-FloatingPoint.shtml) — IEEE 754 formalization
- [Z3 Guide: Datatypes](https://microsoft.github.io/z3guide/docs/theories/Datatypes/) — recursive datatype support
- [Rust Compiler Dev Guide: MIR](https://rustc-dev-guide.rust-lang.org/mir/index.html) — closure/trait representations

**Features Research:**
- [Verus decreases reference](https://verus-lang.github.io/verus/guide/reference-decreases.html) — recursive function termination
- [Prusti Closures](https://viperproject.github.io/prusti-dev/user-guide/verify/closure.html) — closure specification syntax
- [Verifying Dynamic Trait Objects in Rust (Kani 2022)](https://ieeexplore.ieee.org/document/9794041) — vtable verification
- [Creusot POPL 2026 Tutorial](https://popl26.sigplan.org/details/POPL-2026-tutorials/6/Creusot-Formal-verification-of-Rust-programs) — prophecy-based lifetimes

**Pitfalls Research:**
- [F* Termination Proofs](https://fstar-lang.org/tutorial/book/part1/part1_termination.html) — well-founded relations
- [Non-Lexical Lifetimes RFC](https://github.com/rust-lang/rfcs/blob/master/text/2094-nll.md) — NLL specification
- [SMT-LIB FloatingPoint Theory](https://smt-lib.org/theories-FloatingPoint.shtml) — NaN handling
- [RustBelt Meets Relaxed Memory](https://plv.mpi-sws.org/rustbelt/rbrlx/paper.pdf) — weak memory models

### Secondary (MEDIUM confidence)

**Architecture Research:**
- [Creusot: A Foundry for the Deductive Verification of Rust Programs](https://www.researchgate.net/publication/364287862_Creusot_A_Foundry_for_the_Deductive_Verification_of_Rust_Programs) — prophecy encoding patterns
- [Verus: Verifying Rust Programs using Linear Ghost Types](https://users.ece.cmu.edu/~chanheec/verus-ghost.pdf) — SMT-based architecture
- [Model Finding for Recursive Functions in SMT](https://www.cs.vu.nl/~jbe248/frf_conf.pdf) — uninterpreted function encoding

**Pitfalls Research:**
- [Modular Formal Verification of Rust Programs with Unsafe Blocks](https://arxiv.org/abs/2212.12976) — unsafe verification approaches
- [Miri: Practical UB Detection (POPL 2026)](https://research.ralfj.de/papers/2026-popl-miri.pdf) — unsafe code challenges
- [Creusot 0.9.0 devlog (Jan 2026)](https://creusot-rs.github.io/devlog/2026-01-19/) — AtomicInvariant concurrency verification

### Tertiary (LOW confidence, needs validation)

**Architecture Research:**
- [A hybrid approach to semi-automated Rust verification](https://arxiv.org/html/2403.15122v1) — Gillian-Rust separation logic (emerging research)
- [Towards Practical Formal Verification for a General-Purpose OS in Rust](https://asterinas.github.io/2025/02/13/towards-practical-formal-verification-for-a-general-purpose-os-in-rust.html) — concurrency verification challenges (production system, not research tool)

---
*Research completed: 2026-02-11*
*Ready for roadmap: yes*
