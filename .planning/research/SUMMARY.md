# Project Research Summary

**Project:** rust-fv v0.3 Production Usability Features
**Domain:** Formal Verification Tooling for Rust
**Researched:** 2026-02-14
**Confidence:** HIGH

## Executive Summary

This research examines production usability features for rust-fv v0.3, building on v0.2's comprehensive language support. While v0.1-v0.2 established formal verification capabilities for all major Rust features (recursion, closures, traits, lifetimes, unsafe, concurrency), v0.3 focuses on making verification practical for real-world use. The five researched features divide into two categories: must-haves (stdlib contracts, IDE integration) and differentiators (trigger customization, bv2int optimization).

The recommended approach centers on **stdlib contracts as the foundation**. Real Rust code depends heavily on Vec, Option, HashMap, and Iterator - without contracts for these types, verification remains limited to toy examples. The research reveals a proven external crate pattern (used by Prusti and Verus) where stdlib specifications live in a separate `rust-fv-std` crate, allowing independent versioning and opt-in adoption. IDE integration follows through a file-watching VSCode extension that displays JSON diagnostics, avoiding tight coupling. Trigger customization provides an expert-level escape hatch when automatic quantifier inference fails, while bv2int optimization targets arithmetic-heavy verification performance.

Key risks center on usability boundaries rather than correctness. Stdlib contracts create soundness exposure - specification-implementation mismatches propagate to all user code. IDE integration threatens adoption if performance degrades (typing latency > 100ms kills productivity). Trigger customization risks quantifier instantiation loops causing non-termination. bv2int optimization has documented cases causing 1s to 17-hour slowdowns if applied incorrectly. The research identifies concrete mitigation strategies: property-based testing for stdlib contracts, incremental verification with aggressive caching for IDE performance, static loop detection for triggers, and conservative applicability analysis for bv2int.

## Key Findings

### Recommended Stack

The research identifies proven patterns from existing verification tools (Prusti, Verus, Dafny, Kani) with specific technology recommendations for each feature. All technologies integrate cleanly with rust-fv's existing 5-crate architecture without requiring core changes.

**Core technologies:**
- **External stdlib contracts pattern** (separate `rust-fv-std` crate) - Proven by Prusti and Verus for versioning independence and opt-in adoption
- **tower-lsp + tokio** (LSP server foundation) - De facto standard for Rust LSP servers, enables VSCode extension with file watching
- **syn/quote proc macros** (trigger attribute parsing) - Already workspace dependencies, stable API for `#[trigger]` attribute
- **Z3 native API via existing z3 crate** (bv2int tactics) - Programmatic solver configuration through `Params` and `Tactic` combinators
- **notify crate** (file system watching) - Cross-platform file watching for real-time IDE diagnostics

**Critical version requirements:**
- tokio 1.47.x LTS (supported until Sept 2026)
- tower-lsp 0.20+ (requires tokio runtime)
- VSCode extension requires Node.js 20.x+
- Z3 bindings 0.19+ aligned with Z3 solver 4.13.x

### Expected Features

Research classifies features into table stakes (expected by users), differentiators (competitive advantage), and anti-features (explicit scope limits).

**Must have (table stakes):**
- **Standard Library Contracts** - Users expect to verify normal Rust code using Vec/HashMap/Option, not just toy examples. Blocks production adoption.
- **IDE Real-Time Feedback** - Inline diagnostics like rustc errors (red squiggles, hover info) are industry standard. Waiting 30s for CLI output breaks developer flow.
- **Incremental Verification** - Re-verifying entire codebase on every change kills workflow. Dafny shows 30x speedup is achievable.
- **Solver Performance Feedback** - Developers need to know why verification is slow (quantifiers, timeouts), not just "timeout after 60s".

**Should have (competitive differentiators):**
- **Trigger Customization** - Expert control over quantifier instantiation when auto-inference fails. Verus and Dafny provide this; can achieve 2-10x speedup by preventing matching loops.
- **bv2int Optimization** - Native bitvector-to-integer conversion for arithmetic-heavy verification. Expert-level feature with proven but unpredictable performance benefits.

**Defer (v2+ or never):**
- **Automatic Contract Inference** - Undecidable for general programs; 40+ years of research without breakthrough. Provide good defaults but require explicit annotations.
- **Full Separation Logic** - Years of research effort (Prusti/RustBelt scope); Rust borrow checker handles 95% of aliasing cases.
- **Weak Memory Model Support (v0.3)** - SeqCst atomics (already in v0.2) cover 95% of use cases; defer relaxed atomics to v0.4+.
- **Windows Support (v0.3)** - Focus on macOS/Linux first; add Windows post-v1.0 when core stable.

### Architecture Approach

All features integrate through existing extension points in rust-fv's 5-crate architecture (macros, driver, analysis, solver, smtlib). No core architectural changes required.

**Major components:**

1. **Stdlib Contract Registry** (analysis/stdlib_contracts.rs) - Preloaded function specifications for stdlib types (Vec, Option, HashMap, Iterator). Integrates with existing ContractDatabase, user contracts override stdlib.

2. **Trigger Customization Pipeline** - New `#[trigger]` proc macro in macros crate, parsed into SpecExpr metadata, consumed by existing encode_quantifier.rs during VCGen. User triggers override automatic inference when present.

3. **VSCode Extension** (new TypeScript project) - Passive file watcher reading JSON diagnostics from rust-fv-driver, displaying via VSCode DiagnosticCollection. Zero coupling with rust-analyzer or core tool.

4. **Z3 Tactic Pipeline** (solver/tactics.rs) - Optional optimization layer applying bv2int conversion through Z3's native Tactic API. Enabled via environment variable for conservative opt-in.

**Integration complexity:** Low to medium. Total new code approximately 1200 lines, modified code approximately 270 lines across existing crates. VSCode extension is separate project (500 lines TypeScript).

### Critical Pitfalls

Research identifies seven major pitfalls with specific prevention strategies. Unlike v0.1-v0.2 (correctness focus), v0.3 pitfalls center on usability boundaries where getting it wrong breaks adoption, not soundness.

1. **Incomplete Stdlib Specification Coverage** - Users hit "missing contract" errors on common operations. Prevention: Usage-based prioritization (Tier 1: 20 most-used functions blocks release; Tier 2: next 100; Tier 3: community contribution). Clear error messages pointing to coverage documentation.

2. **Specification-Implementation Mismatch** - Stdlib contracts claim properties that don't match actual implementation (panic conditions, overflow semantics, UB boundaries). Prevention: Property-based oracle testing comparing spec predictions against actual execution. Extract specs from MIR, not documentation. Test matrix for debug/release and 32/64-bit.

3. **Quantifier Instantiation Loops** - Custom triggers cause Z3 infinite loops, OOM crashes, non-termination. Prevention: Static termination checker detecting self-instantiating patterns. Bounded instantiation limits. Fallback to automatic triggers on failure. Comprehensive diagnostic tooling before exposing manual trigger API.

4. **IDE Integration Performance Degradation** - Verification makes IDE unusable (typing latency >500ms, freezes, memory leaks). Prevention: Incremental verification with MIR-hash caching, 500ms debouncing, verify only workspace crates (not deps), progressive verification (quick checks first), aggressive resource limits.

5. **bv2int Semantic Mismatch** - Optimization causes soundness bugs or 10x slowdowns due to theory mixing. Prevention: Conservative applicability (arithmetic-only, no bitwise ops), differential testing (bitvector encoding equivalent to integer), performance measurement before enabling, fallback mechanism.

6. **Trigger Pattern Usability Gap** - Users exposed to SMT expert feature without education. Prevention: Progressive disclosure design (automatic by default, manual for experts), high-quality error messages with concrete suggestions, trigger validation at macro expansion, comprehensive documentation.

7. **Contract-Specification Language Drift** - Stdlib contracts invalidated by spec syntax evolution. Prevention: Specification IR layer separating syntax from semantics, contract versioning with migration tool, compatibility shims for old syntax.

## Implications for Roadmap

Based on combined research, recommended phase structure follows dependency order with clear rationale:

### Phase 1: Standard Library Contracts Foundation (HIGHEST PRIORITY)

**Rationale:** Blocks all real-world usage. Can't verify production code without Vec/HashMap/Option contracts. Must establish specification methodology and Tier 1 coverage before other features provide value. IDE integration is worthless without stdlib support - users want to verify real code, not examples.

**Delivers:**
- `rust-fv-std` external crate with contracts for Tier 1 stdlib functions
- Property-based oracle testing framework validating specs against implementation
- Specification IR layer enabling syntax evolution without breaking contracts
- ContractDatabase integration with stdlib registry (user contracts override stdlib)
- Comprehensive coverage documentation

**Addresses features:**
- Standard Library Contracts (table stakes from FEATURES.md)
- Solver Performance Feedback (stdlib contracts exercise quantifiers heavily)

**Avoids pitfalls:**
- Incomplete Stdlib Coverage (usage-based Tier 1 prioritization)
- Specification-Implementation Mismatch (oracle testing catches divergence)
- Contract-Spec Language Drift (IR layer prevents breaking changes)

**Stack elements:**
- External crate pattern (Prusti `prusti-std` model)
- serde for contract metadata serialization
- Existing syn/quote for specification parsing

**Complexity:** HIGH (100-150 contracts, soundness-critical testing, Tier 1 scope: Vec, Option, Result, HashMap, Iterator basics)

**Estimated effort:** 6-8 weeks based on similar Prusti/Verus stdlib work

---

### Phase 2: Incremental Verification Enhancement (HIGH PRIORITY)

**Rationale:** Enables IDE integration viability. Without <1s re-verification target, IDE feedback is too slow (30s = broken workflow). Must come before Phase 3 (IDE) to provide foundation. Dafny demonstrates 30x speedup achievable.

**Delivers:**
- Enhanced dependency tracking (function call graph, trait impl graph)
- MIR-hash-based VC caching with invalidation correctness
- Z3 incremental solving (push/pop, solver state reuse)
- Benchmark suite demonstrating 20-30x speedup on 1000-line codebases
- Performance regression tests ensuring incremental never slower

**Addresses features:**
- Incremental Verification (table stakes from FEATURES.md)
- Enables IDE integration performance requirements (<1s re-verification)

**Avoids pitfalls:**
- IDE Performance Degradation (incremental verification prerequisite)

**Stack elements:**
- Existing Z3 native API for push/pop
- File watching via notify crate (preparation for LSP)
- Existing VC caching infrastructure (v0.1 Phase 5) enhanced

**Complexity:** MEDIUM-HIGH (LSP protocol integration, cache invalidation correctness is soundness-critical)

**Estimated effort:** 4-5 weeks

---

### Phase 3: Trigger Customization with Diagnostics (MEDIUM PRIORITY)

**Rationale:** Performance escape hatch for quantifiers in stdlib contracts. Differentiates from Prusti/Creusot. Low risk if diagnostic tooling built BEFORE exposing manual API. Stdlib contracts (Phase 1) will reveal quantifier performance bottlenecks this addresses.

**Delivers:**
- `#[trigger(expr)]` attribute macro (extend macros crate)
- Spec parser extracting triggers from attributes
- Manual trigger override in encode_quantifier.rs (fallback to auto-inference)
- Static termination analysis detecting matching loops
- SMT-LIB PATTERN generation with validation
- Comprehensive error messages for common mistakes

**Addresses features:**
- Trigger Customization (competitive differentiator from FEATURES.md)
- Solver Performance Feedback (quantifier instantiation diagnostics)

**Avoids pitfalls:**
- Quantifier Instantiation Loops (static loop detection, bounded instantiation)
- Trigger Pattern Usability Gap (progressive disclosure, error message quality)

**Stack elements:**
- syn/quote for attribute parsing (already workspace deps)
- Existing quantifier encoder (encode_quantifier.rs)
- SMT-LIB PATTERN support (already in smtlib crate)

**Complexity:** MEDIUM (well-defined integration, diagnostic quality critical)

**Estimated effort:** 2-3 weeks

---

### Phase 4: VSCode Extension (MEDIUM PRIORITY)

**Rationale:** User-facing integration validating stdlib contracts are usable in real workflow. Incremental verification (Phase 2) makes this feasible (<1s feedback). Stdlib contracts (Phase 1) provide value to show. Simplest integration (passive file watcher) minimizes risk.

**Delivers:**
- VSCode extension (TypeScript) published to marketplace
- File watcher consuming JSON diagnostics from rust-fv-driver
- Inline error highlighting (red squiggles, hover descriptions)
- Status bar "Verifying..." indicator with progress
- Output panel for detailed VC failures
- Configuration for enable/disable, timeouts, Z3 path

**Addresses features:**
- IDE Real-Time Feedback (table stakes from FEATURES.md)
- Integration with rust-analyzer diagnostics (separate diagnostic source)

**Avoids pitfalls:**
- IDE Performance Degradation (passive observer, no coupling, incremental foundation from Phase 2)

**Stack elements:**
- Existing JSON output from driver (v0.1 Phase 5)
- notify crate for file watching
- VSCode Extension API (TypeScript, well-documented)

**Complexity:** MEDIUM (VSCode API mature, UI/UX design, testing across versions)

**Estimated effort:** 3-4 weeks

---

### Phase 5: bv2int Optimization (LOWEST PRIORITY)

**Rationale:** Optimization, not capability. Tackle after stdlib contracts prove performance bottleneck. High risk (Z3 tactic unpredictability, documented 17hr cases). Differential testing mandatory before enabling. Expert-level feature for specific use cases.

**Delivers:**
- Tactic pipeline in solver crate (bv2int, simplify, solve-eqs)
- Z3 native API integration via Tactic combinators
- Selective application (arithmetic-only, bounded integers)
- Differential testing suite (bitvector ≡ integer encoding validation)
- Performance regression tests
- Environment variable opt-in (RUST_FV_BV2INT=1)
- Documentation on when/how to use

**Addresses features:**
- bv2int Optimization (competitive differentiator from FEATURES.md)
- Solver performance for arithmetic-heavy stdlib verification

**Avoids pitfalls:**
- bv2int Semantic Mismatch (conservative applicability, differential testing, opt-in only)

**Stack elements:**
- Existing z3 crate with Tactic API
- Z3 native solver backend (already implemented)

**Complexity:** MEDIUM (Z3 tactic interaction complex, performance unpredictable)

**Estimated effort:** 2-3 weeks

---

### Phase Ordering Rationale

**Dependency-driven ordering:**
- Phase 1 (Stdlib) must come first - all other features depend on real code verification
- Phase 2 (Incremental) must precede Phase 4 (IDE) - performance foundation required
- Phase 3 (Triggers) depends on Phase 1 exposing quantifier bottlenecks
- Phase 5 (bv2int) deferred until performance measurement justifies complexity

**Risk-based sequencing:**
- Highest-risk items (stdlib soundness, IDE performance) tackled when fresh, with time to iterate
- Lower-risk optimizations (triggers, bv2int) at end when core value delivered

**Value-first strategy:**
- Phases 1-2 deliver table stakes (stdlib + performance) - essential for production use
- Phases 3-5 deliver differentiators (expert features, optimizations) - nice-to-have

**Architecture-informed grouping:**
- Each phase maps to clean integration points in existing architecture
- No phase requires architectural refactoring of core pipeline
- All features integrate via extension points (contract DB, VCGen, solver backend)

### Research Flags

**Phases needing deeper research during planning:**
- **Phase 1 (Stdlib Contracts):** Specification patterns for complex iterator combinators may need dedicated research. Basic iterator contracts well-documented, but map/filter/fold with closure contracts may hit specification entailment challenges.
- **Phase 2 (Incremental):** LSP protocol integration details (debouncing strategies, diagnostic lifecycle) may need targeted research when implementing.
- **Phase 5 (bv2int):** Z3 tactic parameter tuning likely needs experimentation-based research; documentation sparse on tactic interaction.

**Phases with standard patterns (skip research-phase):**
- **Phase 3 (Triggers):** SMT-LIB PATTERN generation well-documented; Verus/Dafny provide clear patterns to follow.
- **Phase 4 (IDE):** VSCode extension development well-documented; existing JSON output provides clean integration point.

## Confidence Assessment

| Area | Confidence | Notes |
|------|------------|-------|
| Stack | HIGH | All technologies verified with official docs, active maintenance, proven in similar tools |
| Features | HIGH | Feature classification based on multiple verification tools (Prusti, Verus, Dafny, Kani) with converging patterns |
| Architecture | HIGH | Integration points analyzed against existing rust-fv codebase; all modifications localized and clean |
| Pitfalls | MEDIUM-HIGH | Pitfalls documented in academic literature and tool issue trackers; prevention strategies proven but require discipline |

**Overall confidence:** HIGH

Research benefited from:
- Official documentation for all stack technologies (z3, tower-lsp, VSCode API)
- Multiple reference implementations (Prusti, Verus, Dafny, Kani) demonstrating convergent patterns
- Academic literature on quantifier triggers, incremental verification, stdlib specification
- Existing rust-fv codebase providing clear architecture to integrate against

### Gaps to Address

**Stdlib contract complexity boundary:** Research identifies Tier 1 functions clearly (Vec, Option, HashMap basics), but complex iterator combinators (fold, scan, filter_map with closure specs) may hit specification entailment limits. Address during Phase 1 planning by prototyping challenging contracts early.

**Incremental verification invalidation granularity:** Research establishes function-level caching, but optimal granularity (function vs trait impl vs module) needs experimentation. Benchmark suite in Phase 2 will guide tuning.

**bv2int applicability heuristics:** When to apply bv2int optimization lacks clear rules beyond "arithmetic-only". Research documents what NOT to do (don't mix theories, don't apply to bitwise ops) but positive criteria need refinement. Extensive benchmarking in Phase 5 required.

**Trigger termination analysis soundness:** Static detection of matching loops is heuristic (halting problem). Research provides known-bad patterns to detect, but false positives/negatives expected. Diagnostic tooling in Phase 3 should guide refinement, not block manual triggers entirely.

**VSCode extension multi-platform support:** Research focuses on macOS/Linux development workflow; Windows support deferred but will need investigation for marketplace distribution. Document limitation clearly in Phase 4.

## Sources

### Primary (HIGH confidence)

**Official Documentation & Crates:**
- [z3 crate 0.19](https://docs.rs/z3/latest/z3/) - Tactic API, Params configuration
- [tower-lsp 0.20](https://docs.rs/tower-lsp/latest/tower_lsp/) - LSP server foundation
- [lsp-types 0.97](https://docs.rs/lsp-types/latest/lsp_types/) - LSP 3.17 diagnostic types
- [tokio LTS releases](https://github.com/tokio-rs/tokio/releases) - Version 1.47.x stability
- [VSCode Extension Guide](https://code.visualstudio.com/api/language-extensions/language-server-extension-guide) - LSP integration
- [Z3 Tactics Summary](https://microsoft.github.io/z3guide/docs/strategies/summary/) - bv2int configuration
- [SMT-LIB 2.7 Reference](https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-02-05.pdf) - PATTERN attribute spec

**Existing Verification Tools:**
- [Prusti external specifications](https://viperproject.github.io/prusti-dev/user-guide/verify/external.html) - External crate pattern
- [Verus Tutorial](https://verus-lang.github.io/verus/guide/) - Trigger syntax, stdlib (14k LOC)
- [Dafny Verification Optimization](https://dafny.org/latest/VerificationOptimization/VerificationOptimization) - Incremental patterns
- [Kani VSCode Extension](https://marketplace.visualstudio.com/items?itemName=model-checking.kani-vscode-extension) - IDE integration patterns

### Secondary (MEDIUM confidence)

**Academic Literature:**
- [Verifying Rust Std Lib (VSTTE 2024)](https://www.soundandcomplete.org/vstte2024/vstte2024-invited.pdf) - Stdlib verification challenges
- [Trigger Selection Strategies (Springer 2016)](https://link.springer.com/chapter/10.1007/978-3-319-41528-4_20) - Quantifier instantiation
- [Axiom Profiler (Springer 2019)](https://link.springer.com/chapter/10.1007/978-3-030-17462-0_6) - SMT debugging
- [Timeout Prediction (Springer 2023)](https://link.springer.com/chapter/10.1007/978-3-031-47115-5_19) - 30x incremental speedup
- [Tunable Automation (arXiv 2025)](https://arxiv.org/html/2512.03926) - Dafny vs Verus triggers

**GitHub Issues & Discussions:**
- [Z3 bv2int performance issue #1481](https://github.com/Z3Prover/z3/issues/1481) - 1s vs 17hr cases
- [Z3 bv2int semantic mismatch #1252](https://github.com/Z3Prover/z3/issues/1252) - bv2int vs bv2nat
- [rust-analyzer LSP integration](https://deepwiki.com/rust-lang/rust-analyzer/3-language-server-protocol-integration) - Custom diagnostic sources
- [rust-analyzer proc macro support](https://rust-analyzer.github.io/thisweek/2026/01/26/changelog-312.html) - Attribute expansion

### Tertiary (LOW confidence, requires validation)

- [Pyrefly incremental verification](https://pyrefly.org/blog/2026/02/06/performance-improvements/) - Incremental type checking strategies (analogous domain)
- [SMT-LIB bv/integer discussion](https://groups.google.com/g/smt-lib/c/-GJG1Pq61hI) - Theory mixing overhead (community discussion)

---
*Research completed: 2026-02-14*
*Ready for roadmap: yes*
