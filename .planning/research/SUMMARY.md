# Project Research Summary

**Project:** rust-fv (Formal Verification for Rust)
**Domain:** Compiler-integrated deductive verification tool
**Researched:** 2026-02-10
**Confidence:** MEDIUM-HIGH

## Executive Summary

rust-fv is a compiler-integrated formal verification tool for Rust that hooks into rustc via `rustc_driver::Callbacks`, extracts MIR, translates to SMT-LIB2, and verifies functional correctness properties using Z3. The v0.1.0 foundation already covers function contracts (`#[requires]`/`#[ensures]`), bitvector-precise integer encoding, arithmetic overflow detection, counterexample extraction, and basic VC generation. This is a strong starting position. Research across all four Rust verification leaders (Verus, Prusti, Kani, Creusot) confirms that rust-fv's architecture -- proc-macro specs, MIR extraction, WP-based VC generation, Z3 backend -- follows the proven pattern. The key differentiator is zero-friction cargo integration without a forked compiler, which positions rust-fv uniquely against Verus (forked compiler) while targeting Verus-quality expressiveness.

The recommended approach for the next development cycle is to fix two critical soundness issues first (SSA variable handling, overflow audit), then systematically complete table-stakes features (loop invariants, cargo integration, assertions, panic detection, ownership reasoning). After that, build differentiating capabilities (unbounded integers, ghost code, quantifiers, mutable borrow reasoning via prophecy variables, inter-procedural verification with function summaries). The stack evolution is incremental: add the z3 crate with `bundled` feature for typed SMT API alongside the existing subprocess backend, extend syn-based parsing for richer specification syntax, and add SMT datatype/array/UF theories as features demand them. No architectural pivots are needed.

The critical risks are: (1) SMT encoding soundness bugs -- the single most dangerous failure mode for any verification tool, mitigated by soundness/completeness test suites and differential testing against Kani/Prusti; (2) the existing SSA violation in VCGen which renders control-flow verification unsound -- must be fixed before any new features; (3) loop invariant usability -- this is universally the hardest verification UX problem, mitigated by excellent error messages and multi-strategy inference; (4) nightly rustc API instability, mitigated by the existing stable-IR decoupling pattern and quarterly pinned updates.

## Key Findings

### Recommended Stack

The current stack (nightly Rust, rustc_driver/rustc_middle/rustc_hir, proc-macro2/syn/quote, Z3 subprocess) is correct and needs incremental evolution, not replacement. All four major Rust verification tools use the same core: nightly rustc_private APIs for MIR access and Z3 as the primary SMT backend. See [STACK.md](STACK.md) for full details.

**Core technologies:**
- **Rust Nightly (pinned):** Compiler API access via rustc_private -- non-negotiable, same tradeoff accepted by Verus/Prusti/Kani/Creusot
- **z3 crate (0.19+, bundled):** Typed Rust API for Z3 -- replaces manual SMT-LIB2 string generation, enables incremental solving, reduces encoding bugs
- **SMT-LIB 2.6+ theories (Datatypes, Arrays, UF):** Required for structs, collections, and modular inter-procedural verification
- **syn 2.x (custom Parse impls):** Extend existing proc macros for loop invariants, quantifiers, prophecy operators without new dependencies
- **tracing:** Replace ad-hoc logging with structured, filterable tracing for debugging verification pipelines

**Critical version requirements:**
- Pin nightly in `rust-toolchain.toml`, update quarterly with regression tests
- z3 crate `bundled` feature to statically link Z3 (avoids system version conflicts)
- SMT-LIB 2.6+ for algebraic datatypes (Z3 4.13+ supports this)

### Expected Features

Research surveyed all major competitors and established clear feature tiers. See [FEATURES.md](FEATURES.md) for full analysis.

**Must have (v0.2 -- table stakes completion):**
- **Loop invariants** -- without this, cannot verify non-trivial loops; every competitor has this
- **Cargo integration** (`cargo verify`) -- Rust developers expect cargo-native workflows
- **Assertion verification** -- `assert!(x > 0)` must be statically checked
- **Panic detection** -- check `unwrap()`, `expect()`, indexing for panic-freedom
- **Basic ownership reasoning** -- leverage Rust's ownership for verification soundness

**Should have (v0.3 -- differentiation):**
- **Unbounded mathematical integers** (`int`/`nat`) -- Verus-style, prove correctness without overflow then refine
- **Ghost code** -- auxiliary specification state erased at runtime, essential for complex invariants
- **Quantifiers** (`forall`/`exists`) -- required for non-trivial properties over collections
- **Mutable borrow reasoning** -- prophecy-based (Creusot-style) for `&mut` parameters
- **Inter-procedural verification** -- function summaries with contracts, modular scalability
- **Trait/generic support** -- essential for real-world Rust code

**Defer (v1.0+):**
- Trigger customization, concurrency verification, unsafe code verification, IDE integration, AI-assisted proof generation
- These are either research-stage, very high complexity, or serve small initial user bases

**Anti-features to avoid:**
- Fully automatic verification (undecidable; be honest about 80-90% automation target)
- Forked compiler (maintenance nightmare; rust-fv's zero-friction approach is the differentiator)
- One-size-fits-all proof automation (different code needs different strategies)

### Architecture Approach

The architecture follows a proven 5-layer pipeline: Specification Frontend (proc macros) -> Compiler Integration (rustc_driver callbacks) -> Translation (MIR -> stable IR -> VCs) -> SMT Encoding (IR -> SMT-LIB AST) -> Solver Backend (Z3). The monorepo crate structure (macros/, smtlib/, solver/, analysis/, driver/) correctly isolates nightly-dependent code in the driver crate while keeping core verification logic testable on stable Rust. See [ARCHITECTURE.md](ARCHITECTURE.md) for full details.

**Major components:**
1. **driver/ (nightly-only)** -- Thin compiler integration layer: rustc_driver callbacks, MIR-to-IR conversion. Isolates all rustc API instability.
2. **analysis/ (stable Rust)** -- Core verification logic: stable IR, VC generation, type/expression encoding. Independently testable without compiler.
3. **smtlib/ (stable Rust)** -- Solver-agnostic SMT-LIB AST builder. Enables testing encoding without solver, supports multiple backends.
4. **solver/ (stable Rust)** -- SMT solver interface with Strategy pattern for subprocess and z3-native backends.
5. **macros/ (stable Rust)** -- Proc macro crate for specification syntax (`#[requires]`, `#[ensures]`, `#[invariant]`).

**Key architectural patterns to follow:**
- **Stable IR decoupling** (Pattern 1) -- already in place, continue isolating rustc changes
- **SSA-based VCGen** (Pattern 6) -- MUST implement to replace current unsound linear block-walking
- **Modular verification with function summaries** (Pattern 7) -- standard for scaling
- **Loop invariant framework** (Pattern 8) -- user-supplied initially, inference later

### Critical Pitfalls

The top 5 pitfalls are ranked by severity and likelihood. See [PITFALLS.md](PITFALLS.md) for all 15 pitfalls with prevention strategies.

1. **SSA violation in VCGen (CRITICAL, IMMEDIATE)** -- Current linear block-walking is unsound for branches/loops. Variable shadowing produces incorrect verification results. Fix: implement true SSA renaming with phi functions at merge points before adding any new features.

2. **Soundness bugs in SMT encoding (CRITICAL, ONGOING)** -- Incorrect Rust-to-SMT translation is the most dangerous failure mode. Prevention: formal encoding spec document, soundness test suite (wrong programs must be rejected), differential testing against Kani/Prusti, property-based testing of encoding correctness.

3. **Loop invariant usability (HIGH, Phase 2)** -- Universally the hardest verification UX problem. Even LLMs "show limited ability to leverage verifier-provided feedback when repairing incorrect invariants." Prevention: multi-strategy inference (templates, abstract interpretation, CEGIS), excellent error messages showing which clause fails (init/inductive/post), pattern library for common loops.

4. **MIR API instability (HIGH, ONGOING)** -- Nightly API breaks frequently; 15.28% of rustc bugs are MIR optimization issues. Prevention: pin nightly version, isolate MIR coupling to driver/mir_converter.rs, CI matrix testing multiple nightlies, track stable MIR project.

5. **SMT solver performance cliffs (MEDIUM, Phase 3)** -- Minor encoding changes can cause exponential performance degradation. Prevention: minimize quantifiers, formula simplification before solving, incremental solving with push/pop, multiple solver fallback (Z3 then CVC5), per-VC timeout budgets.

## Implications for Roadmap

Based on combined research, the following phase structure respects dependency ordering, groups architecturally coherent work, and addresses pitfalls at the right time.

### Phase 1: Soundness Foundation

**Rationale:** The SSA violation is a known critical bug that invalidates verification for any function with control flow. Bitvector overflow encoding needs auditing. These must be fixed before building on top of the current VCGen. This phase also establishes the testing infrastructure that all subsequent phases depend on.

**Delivers:** Sound VCGen for branching code, verified overflow semantics, soundness/completeness test suites, performance baseline.

**Addresses features:** None new -- fixes foundation for all future features.

**Avoids pitfalls:** SSA violation (#5), bitvector overflow mismatch (#4), inadequate verifier testing (#8).

**Stack:** Current stack only. No new dependencies.

**Work items:**
- Implement SSA variable renaming in VCGen (Pattern 6)
- Insert phi functions at control-flow merge points
- Audit all arithmetic encoding for overflow correctness
- Build soundness test suite (programs with known bugs must be rejected)
- Build completeness test suite (correct programs must verify)
- Add multi-path control flow test cases (if/else, match, early return)
- Pin nightly version explicitly with compatibility documentation

### Phase 2: Table Stakes Completion

**Rationale:** Research unanimously identifies loop invariants, cargo integration, assertion verification, and panic detection as table-stakes features every user expects. Without these, the tool feels incomplete. Aggregate type support (structs) is architecturally required for ownership reasoning and practical code.

**Delivers:** Verifiable loops, cargo-native workflow, assertion/panic checking, struct field verification, enhanced specification parsing.

**Addresses features:** Loop invariants, cargo integration, assertion verification, panic detection, aggregate types (structs/tuples).

**Avoids pitfalls:** Loop invariant failure (#3) via excellent error messages and starting with simple bounded loops; aggregate encoding loss (#9) via proper SMT datatypes; proc macro hygiene (#6) via audit and hygiene test suite.

**Stack additions:** z3 crate (bundled) for typed API and incremental solving, tracing for structured logging, compiletest_rs for UI tests, proptest for property-based testing, cargo-nextest and cargo-expand for development.

**Work items:**
- Add z3 crate backend with `SolverBackend` trait (keep subprocess as fallback)
- Parse `#[invariant(expr)]` via syn custom parsers
- Implement loop VC generation (3 VCs: init, preservation, exit)
- Implement `cargo verify` as cargo subcommand
- Extract and verify `assert!()` from MIR
- Detect and verify panic-freedom for `unwrap()`/`expect()`/indexing
- Encode structs as SMT datatypes with constructors/selectors
- Enhance spec parser to support richer expressions
- Add structured tracing throughout pipeline

### Phase 3: Modular Verification

**Rationale:** Inter-procedural verification is the scaling enabler. Without function summaries, verification is limited to small isolated functions. This phase also adds basic ownership reasoning, which depends on tracking borrows across function boundaries. Grouping these together is architecturally coherent because both require contract databases and modular VC encoding.

**Delivers:** Verify functions that call other verified functions, basic ownership-aware verification, function contract database.

**Addresses features:** Inter-procedural verification with function summaries, basic ownership reasoning.

**Avoids pitfalls:** Inter-procedural scaling (#10) via modular verification instead of inlining; inline-all anti-pattern via contracts.

**Stack additions:** SMT UF (uninterpreted functions) theory for function summaries.

**Work items:**
- Build function signature-to-contract map from HIR
- Implement modular call encoding (assert precondition, havoc return, assume postcondition)
- Add call graph analysis for dependency ordering
- Implement basic ownership tracking (moved values, immutable borrows)
- Generate VCs assuming ownership invariants from borrow checker

### Phase 4: Differentiation

**Rationale:** These features move rust-fv from "another verifier" to a competitive tool. Unbounded integers, ghost code, and quantifiers are the specification expressiveness tier that enables real verification. Mutable borrow reasoning is essential for practical Rust code. These build on the modular verification infrastructure from Phase 3.

**Delivers:** Verus-quality specification expressiveness, practical mutable borrow verification, ghost state for complex invariants.

**Addresses features:** Unbounded mathematical integers (`int`/`nat`), ghost code, quantifiers (`forall`/`exists`), mutable borrow reasoning via prophecy variables.

**Avoids pitfalls:** Prophecy encoding unsoundness via studying Creusot's proven model; SMT performance cliffs (#7) via quantifier-free encodings where possible and formula simplification.

**Stack additions:** SMT LIA/LRA theory for unbounded integers, prophecy variable encoding in IR.

**Work items:**
- Add `int`/`nat` spec-only types with SMT integer theory encoding
- Implement `#[ghost]` attribute with compile-time erasure
- Add `forall`/`exists` to specification parser with basic trigger inference
- Implement prophecy variables for `&mut` parameters (Creusot-style)
- Connect prophecy lifecycle to borrow expiration
- Add trait/generic support via monomorphization-based verification

### Phase 5: Performance and Polish

**Rationale:** With features complete, optimize for real-world usage. Performance work should come after features are stable (profile-guided, not speculative). Polish error messages and documentation for adoption.

**Delivers:** Production-ready performance, excellent error messages, user documentation.

**Addresses features:** Better error messages, documentation, performance optimization.

**Avoids pitfalls:** SMT performance cliffs (#7) via benchmarking and profiling; process spawning overhead (#14) via z3-native backend default; monolithic scripts (#15) via minimal VC context.

**Work items:**
- Benchmark suite with performance regression tests
- Formula simplification passes (constant folding, dead code elimination, CSE)
- VC caching for unchanged functions
- Parallel verification (independent VCs in separate solver instances)
- Default to z3-native backend, subprocess as fallback
- Comprehensive error message review with source locations and suggestions
- User guide with examples for each feature

### Phase 6: Advanced Features (v1.0+)

**Rationale:** These are high-complexity, niche-audience features that should wait for product-market validation. Each is individually large enough to be a major project.

**Delivers:** Trigger customization, stdlib contracts, IDE integration, concurrency verification, unsafe code support.

**Work items (each a separate initiative):**
- Trigger customization for SMT quantifier performance
- Standard library contracts for Vec, HashMap, Option, Result
- IDE integration (VSCode extension, rust-analyzer integration)
- Concurrency verification (atomics, locks, async)
- Unsafe code verification (partner with Kani for bounded MC complement)
- AI-assisted proof generation (LLM-based invariant inference, annotation generation)

### Phase Ordering Rationale

- **Phase 1 before everything:** SSA fix is a blocking soundness bug. Building features on an unsound foundation wastes time and creates false confidence. Testing infrastructure established here prevents regression in all subsequent phases.
- **Phase 2 groups "user-facing completeness":** Loop invariants + cargo integration + assertions + panic detection are all independently valuable table-stakes features. Aggregate types fit here because structs are needed for practical code and depend on the z3 crate also being added in this phase.
- **Phase 3 before Phase 4:** Mutable borrow reasoning (Phase 4) benefits from function summaries (Phase 3) because borrows cross function boundaries. Quantifiers (Phase 4) are more useful when combined with inter-procedural contracts (Phase 3).
- **Phase 5 after features:** Performance optimization guided by profiling real feature usage, not speculation. Error messages require the full feature set to be meaningful.
- **Phase 6 is a menu, not a sequence:** Features are independent and should be prioritized by user demand.

### Research Flags

**Phases likely needing deeper research during planning:**
- **Phase 2 (Loop Invariants):** Loop invariant usability is the hardest UX problem in verification. Research 3+ inference approaches before committing to one. Study Creusot 0.9.0's auto-detection of immutable loop variables.
- **Phase 4 (Prophecy Variables):** Research-level technique. Must read Creusot source code for exact encoding details. POPL 2020 prophecy paper + Creusot POPL 2026 tutorial are essential references. Soundness proof may be needed.
- **Phase 4 (Quantifiers):** Trigger inference is tricky. Study Verus's `#[trigger]` mechanism and recent "tunable automation" work (December 2025 paper).

**Phases with standard patterns (skip deep research):**
- **Phase 1 (SSA):** Textbook compiler technique (Cornell CS 6120, Software Foundations). Well-documented with clear algorithms.
- **Phase 2 (Cargo Integration):** Standard cargo subcommand pattern. Follow Kani (`cargo kani`) and Prusti (`cargo prusti`) implementations.
- **Phase 3 (Function Summaries):** Established modular verification technique (Dafny, Boogie, Why3, Prusti). Standard assume/assert encoding.
- **Phase 5 (Performance):** Standard optimization work. Profile, measure, optimize.

## Confidence Assessment

| Area | Confidence | Notes |
|------|------------|-------|
| Stack | MEDIUM-HIGH | Core technologies confirmed by 4 production tools. z3 crate migration is proven. Nightly pinning strategy standard. Gap: specific nightly API changes unpredictable. |
| Features | HIGH | Comprehensive competitor survey across Verus/Prusti/Kani/Creusot with academic papers + official docs. Feature tiers well-established by market. |
| Architecture | HIGH | Architecture directly mirrors proven patterns from Prusti (ETH Zurich), Creusot (Inria), Kani (AWS). Monorepo crate structure already validated in v0.1.0. |
| Pitfalls | HIGH | Drawn from real tool experience, academic papers on verification tool testing, known bugs in CBMC/Solidity verifiers. SSA violation confirmed in CONCERNS.md. |

**Overall confidence:** MEDIUM-HIGH

The high confidence in features, architecture, and pitfalls is offset slightly by inherent uncertainty in two areas: (1) prophecy variable encoding soundness for rust-fv's specific IR (proven in Creusot but must be validated for our encoding), and (2) SMT performance characteristics that can only be determined empirically after implementation.

### Gaps to Address

- **Prophecy encoding specifics:** Creusot's model is proven sound, but translating it to rust-fv's IR requires reading Creusot source code during Phase 4 implementation. The exact SMT encoding of prophecy lifecycle (creation at borrow, resolution at expiration) needs prototyping.
- **Datatype encoding for generics:** How to handle `struct Pair<T, U>` in SMT datatypes. Verus uses monomorphization; we should study their approach during Phase 2 when adding struct support.
- **Performance baselines:** No empirical data on VC generation or solver performance for rust-fv. Must establish benchmarks in Phase 1 to guide Phase 5 optimization.
- **Stable MIR migration timeline:** The project exists but is incomplete as of 2026. Monitor quarterly. Migration would reduce the MIR instability pitfall but is not actionable now.
- **Polonius (new borrow checker):** Still in development. May change borrow checker semantics that affect ownership reasoning. Monitor during Phase 3.

## Sources

### Primary (HIGH confidence)
- [Rust Compiler Development Guide: MIR](https://rustc-dev-guide.rust-lang.org/mir/index.html) -- MIR structure, API patterns
- [Z3 Rust Bindings (prove-rs/z3.rs)](https://github.com/prove-rs/z3.rs) -- z3 crate API, v0.19.7
- [SMT-LIB 2.7 Standard](https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-02-05.pdf) -- Algebraic datatypes, theories
- [Verus: Verifying Rust Programs using Linear Ghost Types](https://dl.acm.org/doi/10.1145/3586037) -- OOPSLA 2023, linear ghost types, trigger customization
- [Creusot: A Foundry for Deductive Verification of Rust Programs](https://inria.hal.science/hal-03737878/document) -- ICFEM 2022, prophecy variables, Why3 translation
- [The Prusti Project: Formal Verification for Rust](https://pm.inf.ethz.ch/publications/AstrauskasBilyFialaGrannanMathejaMuellerPoliSummers22.pdf) -- NFM 2022, modular verification architecture
- [Creusot 0.9.0 Release](https://creusot-rs.github.io/devlog/2026-01-19/) -- January 2026, auto-invariants, concurrency
- [Creusot POPL 2026 Tutorial](https://popl26.sigplan.org/details/POPL-2026-tutorials/6/Creusot-Formal-verification-of-Rust-programs) -- Loop invariants, prophecy model
- [Weakest Precondition Semantics](https://softwarefoundations.cis.upenn.edu/slf-current/WPsem.html) -- VC generation theory
- [RustBelt: Securing the Foundations of Rust](https://dl.acm.org/doi/pdf/10.1145/3158154) -- POPL 2018, separation logic foundations

### Secondary (MEDIUM confidence)
- [Kani Rust Verifier](https://github.com/model-checking/kani) -- Different approach (bounded MC) but informative for architecture
- [BALI: Branch-Aware Loop Invariant Inference with LLMs](https://arxiv.org/pdf/2601.00882) -- 2026, LLM-based invariant inference
- [AutoVerus: Automated Proof Generation for Rust Code](https://arxiv.org/pdf/2409.13082) -- AI-assisted verification
- [LLM For Loop Invariant Generation and Fixing](https://arxiv.org/html/2511.06552) -- LLM limitations for invariants
- [Tunable Automation in Automated Program Verification](https://arxiv.org/html/2512.03926v1) -- December 2025, automation tuning
- [An Empirical Study of Rust-Specific Bugs in the rustc Compiler](https://arxiv.org/html/2503.23985v1) -- MIR optimization bug statistics
- [ARGUZZ: Testing zkVMs for Soundness and Completeness Bugs](https://www.arxiv.org/pdf/2509.10819) -- Metamorphic testing methodology

### Tertiary (LOW confidence -- needs validation)
- Prophecy encoding for rust-fv's specific IR (must prototype during Phase 4)
- SMT performance characteristics for bitvector + datatype + UF theory combinations (must benchmark)
- Stable MIR project readiness timeline (monitor quarterly)
- Polonius borrow checker impact on ownership reasoning (monitor)

---
*Research completed: 2026-02-10*
*Ready for roadmap: yes*
