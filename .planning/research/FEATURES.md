# Feature Landscape: Production Usability Features (v0.3)

**Domain:** Production-Ready Formal Verification Tools
**Researched:** 2026-02-14
**Confidence:** MEDIUM-HIGH

## Context

This research focuses on **5 production usability features** for rust-fv v0.3, building on v0.2's comprehensive language support:

**Already implemented (v0.2 Complete - all major Rust features):**
- Recursive functions with termination checking (`#[decreases]`)
- Closures (Fn/FnMut/FnOnce with environment capture)
- Trait objects (behavioral subtyping, sealed traits, dynamic dispatch)
- Lifetime reasoning (NLL, prophecy variables, SSA-based &mut)
- Unsafe code detection (null checks, bounds checks, `#[unsafe_requires]`)
- Floating-point verification (IEEE 754, NaN/Inf VCs)
- Concurrency verification (happens-before, data race freedom, atomics)
- Path-sensitive VCGen, inter-procedural verification, quantifiers, prophecy variables
- Z3 subprocess + native API backends, formula simplification, VC caching
- cargo verify with diagnostics and JSON output

**New features to research (v0.3 focus):**
1. Standard library contracts (Vec, HashMap, Option, Result, Iterator)
2. Trigger customization (`#[trigger]` for quantifier performance)
3. VSCode extension (inline diagnostics, verification status)
4. rust-analyzer integration (LSP diagnostics, flycheck)
5. bv2int optimization (Z3 theory combination performance)

---

## Table Stakes

Features users expect from production verification tools. Missing = tool feels incomplete or academic-only.

| Feature | Why Expected | Complexity | Notes |
|---------|--------------|------------|-------|
| **Standard Library Contracts** | Real code depends on stdlib; can't verify `vec.push()` calls without Vec contracts. Users expect verification of "normal Rust code" not just toy examples. | High | Prusti provides iterator specs; Verus has "verification standard library" (14k LOC); Dafny has extensive stdlib lemmas; Kani verifies against Rust std. Blocks production adoption. |
| **Solver Performance Feedback** | Developers need to know *why* verification is slow (quantifiers, timeouts, theory combination) not just "timeout after 60s". | Medium | Dafny provides `measure-complexity` + dafny-reportgenerator for detecting unstable assertions; performance warnings common (e.g., "FP theory 2-10x slower"). Prevents "black box" frustration. |
| **Incremental Verification** | Re-verifying entire codebase on every change kills workflow; must cache results and re-verify only changed functions. | High | Dafny shows 30x speedup for incremental re-runs; push/pop frame stacks preserve solver state; LSP integration enables per-function verification. Critical for IDE integration. |
| **IDE Real-Time Feedback** | Waiting 30s for CLI output breaks developer flow; need inline diagnostics like rustc errors (red squiggles, hover info). | Medium | Kani VSCode shows harness tree, inline errors, debug traces; Dafny VSCode shows "Verifying..." status, F7 for verification trace, live-as-you-type checking. Industry standard for static analysis tools. |
| **Custom Diagnostics Integration** | Verification errors must appear in familiar IDE (VSCode, rust-analyzer) not separate tool window. Seamless cargo workflow. | Medium | rust-analyzer extends LSP with `rust-analyzer/*` custom requests; Why3 IDE shows green checkmarks for proved goals; Kani integrates into VSCode testing panel. Matches Rust ecosystem expectations. |
| **Timeout Handling** | Solver timeouts are expected (undecidable logic); tool must provide actionable guidance not just "timeout". | Low | Dafny docs recommend `{:isolate_assertions}`, opaque predicates, manual lemmas; timeout prediction via ML (Springer 2024); incremental solving reduces risk. Prevents "tool is broken" perception. |

## Differentiators

Features that set production tools apart from academic prototypes. Not expected, but highly valued by expert users.

| Feature | Value Proposition | Complexity | Notes |
|---------|-------------------|------------|-------|
| **Trigger Customization** | Quantifier instantiation is performance-critical; experts need manual control when auto-inference fails or causes matching loops. | Medium | Verus uses `#[trigger]` attribute; Dafny uses `{:trigger ...}` syntax; F* has pattern annotations. Allows 2-10x speedup by preventing matching loops. Differentiates from tools with "black box" quantifiers. |
| **Counterexample Generation** | When verification fails, concrete values (counterexample) reveal *why* vs abstract "assertion failed at line 42". | High | Kani generates unit tests from counterexamples (concrete playback); Why3 displays counterexamples in task tab and HTML; Debug Test button in Kani VSCode. Debugging productivity boost. |
| **Proof Isolation** | Complex proofs should be debuggable in parts; `assert P by { ... }` scopes reasoning so intermediate steps don't pollute solver context. | Medium | Dafny's `assert P by { }` hides intermediate steps; opaque predicates + reveal statements control information flow. Critical for managing solver complexity in large proofs. |
| **bv2int Optimization** | Bitvector+integer theory combination is expensive (Z3 default); native bv2int interprets BVs as unsigned integers, reducing overhead. | Medium-High | Z3's bv2int uses lazy intblasting; but performance mixed (1s vs 17hr in some cases per GitHub issues). Requires careful tactic configuration. Expert-level feature. |
| **Bounded Verification Mode** | For unsafe/concurrent code, bounded model checking (BMC) finds bugs fast; complements unbounded SMT verification. | High | Kani uses bounded MC for all verification (CBMC backend); Dafny deferred to future; bounded threads/context switches prevent concurrency state explosion. Different verification paradigm. |
| **Verification Visualization** | HTML reports, proof session trees, coverage highlighting make results shareable/reviewable (e.g., for code review, audit). | Low-Medium | Why3 exports HTML with green (proved) / red (failed) backgrounds; Kani shows coverage inline with source highlighting; Dafny IDE collapses proved goal subtrees. Team collaboration feature. |

## Anti-Features

Features to explicitly NOT build (scope creep, complexity traps, or ecosystem mismatch).

| Anti-Feature | Why Avoid | What to Do Instead |
|--------------|-----------|-------------------|
| **Automatic Contract Inference** | Undecidable for general programs; Hoare logic fundamentally requires explicit pre/post. Academic research has 40+ years without breakthrough. | Provide good defaults (e.g., auto-infer simple loop invariants for `i < n` patterns) but require annotations for complex logic. Invest in diagnostic quality over magic inference. |
| **Full Separation Logic** | Years of research effort (Prusti/RustBelt scope); requires Iris/Coq integration; high complexity for marginal ROI in Rust (borrow checker handles most aliasing). | Use conservative heap approximations; leverage borrow checker analysis. Add separation logic only if production users demonstrate concrete need. |
| **Custom SMT Solver** | Z3/CVC5 are industry-standard, battle-tested over 15+ years; reinventing wheel risks soundness bugs and years of optimization work. | Integrate with Z3 native API + subprocess fallback; contribute upstream if features needed (e.g., better bv2int tactics). |
| **Automatic Trigger Inference Always** | Inference works 80% of time; forcing automation for remaining 20% causes matching loops (instantiation explosion). Perfect inference is AI-complete. | Provide manual `#[trigger]` escape hatch for experts; emit warnings when inference uncertain ("no trigger found, quantifier may not instantiate"). Follow Verus/Dafny model. |
| **Weak Memory Model Support (v0.3)** | Relaxed atomics require formal memory models (C++11, Rust memory model); academic frontier with ongoing research. SeqCst is 95% of use cases. | Support SeqCst atomics (already done in v0.2 Phase 12); defer Acquire/Release to v0.4+ after research matures. Document limitation clearly. |
| **Full Iterator Combinator Auto-Verification** | Higher-order specification entailments (Fn bounds as contracts) are research-level; requires dependent function types. | Provide contracts for common patterns (map, filter, fold) in stdlib; require manual closure specs for complex cases. Prioritize 80% use cases. |
| **Windows Support (v0.3)** | Development on macOS/Linux first; Windows SMT solver integration has quirks (path handling, process spawning). Small user base currently. | Focus on Unix platforms for v0.3; add Windows support post-v1.0 when core stable and user demand proven. Use GitHub issue to track demand. |
| **Forked Rust Compiler** | Zero-friction cargo workflow is key differentiator; proc macros + MIR via rustc_driver sufficient for all v0.1-v0.3 features. | Stay within stable Rust + nightly rustc_driver; avoid forked compiler maintenance burden. Only fork if compiler integration absolutely required (not yet needed). |

## Feature Dependencies

**Dependencies on existing rust-fv capabilities (v0.1-v0.2):**

```
Standard Library Contracts
  → Requires: Inter-procedural verification (v0.1 Phase 3) ✓
  → Requires: Trait-level contracts (v0.2 Phase 8) ✓
  → Requires: Generic monomorphization (v0.1 Phase 2) ✓
  → Requires: Prophecy variables for &mut iterators (v0.1 Phase 2) ✓
  → Provides: Real-world code verification (blocks production adoption)

Trigger Customization
  → Requires: Quantifier support (v0.1 Phase 2) ✓
  → Requires: Spec parser extensions (v0.1 Phase 1) ✓
  → Requires: SMT-LIB PATTERN generation (new)
  → Provides: Performance control for experts (differentiator)

IDE Integration (VSCode)
  → Requires: Diagnostic infrastructure (v0.1 Phase 5) ✓
  → Requires: Structured error messages (v0.2 Phase 12) ✓
  → Requires: JSON output (v0.1 Phase 5) ✓
  → Provides: Developer-friendly workflow (table stakes)

rust-analyzer Integration
  → Requires: LSP-compatible diagnostics (v0.1 Phase 5) ✓
  → Requires: Fast verification (<5s for typical functions) ✓
  → Requires: Incremental verification (v0.1 Phase 5 basic, needs enhancement)
  → Provides: Inline feedback in native Rust IDE (table stakes)

bv2int Optimization
  → Requires: SMT-LIB2 encoding (v0.1 Phase 1) ✓
  → Requires: Z3 native API (v0.1 Phase 4) ✓
  → Requires: Bitvector theory (v0.1 Phase 1) ✓
  → Provides: Faster arithmetic verification (differentiator)

Incremental Verification (Enhanced)
  → Requires: Per-function VC caching (v0.1 Phase 5) ✓
  → Requires: Dependency tracking (v0.1 Phase 3) ✓
  → Requires: LSP protocol (new) for file change notifications
  → Provides: Sub-second re-verification (enables IDE integration)
```

**Inter-feature dependencies (v0.3):**

```
IDE Integration (VSCode)
  → Depends on: Incremental Verification (fast feedback required, <1s re-verification)
  → Depends on: Timeout Handling (graceful degradation, progress bars)
  → Enables: Standard Library usage validation (see errors inline)

rust-analyzer Integration
  → Depends on: IDE Integration (LSP protocol foundation, reuse diagnostics)
  → Depends on: Standard Library Contracts (verify real code in IDE, not just examples)
  → Enables: Zero-config workflow (works out-of-box with existing rust-analyzer)

bv2int Optimization
  → Enables: Faster IDE feedback (solver performance critical for <1s goal)
  → Enables: Standard Library verification (Vec/HashMap arithmetic-heavy)
  → Depends on: Benchmarking infrastructure (measure impact)

Standard Library Contracts
  → Blocks: IDE Integration value (users want to verify real code, not examples)
  → Blocks: Production adoption (all real code uses Vec/Option/Result)
  → Enables: Ecosystem growth (users can verify libraries depending on std)
```

## MVP Recommendation

Prioritize for v0.3 Production Usability (in dependency order):

### Phase 1: Standard Library Contracts (HIGHEST PRIORITY)
**Why first:** Blocks real-world usage. Can't verify production code without Vec/HashMap/Option contracts. Must come before IDE integration to provide value.

**Scope:**
1. **Vec<T>:** push, pop, len, get, index operations, capacity invariants
2. **Option<T> / Result<T, E>:** unwrap, map, and_then, is_some, is_none, ok_or
3. **HashMap<K, V>:** insert, get, remove, contains_key, len
4. **Iterator basics:** next, collect, map, filter (defer fold/scan/complex combinators)
5. **String/str:** len, chars, as_bytes (defer complex Unicode operations)

**Complexity:** HIGH
- Trait-level generic contracts (`impl<T> Vec<T>` with type bounds)
- Modular verification across crate boundaries (std is external crate)
- Prophecy variables for mutable iterators (IterMut)
- Soundness validation against actual Rust std (compare with Kani/Miri tests)
- Documentation and examples for each contract

**Estimated effort:** 6-8 weeks (100-150 contracts, testing against real codebases, soundness validation)

**Success criteria:**
- User verifies `fn sum(v: Vec<i32>) -> i32` with loop over `v.iter()`
- User verifies `fn safe_divide(x: i32, y: Option<i32>) -> Option<i32>` with `y.map(|n| x / n)`
- User verifies HashMap usage with `insert` + `get` proving key existence
- Zero false positives (unsound contracts) in 10+ real-world examples

---

### Phase 2: Incremental Verification (Enhanced) (HIGH PRIORITY)
**Why second:** Enables IDE integration (<1s re-verification target). Without this, IDE feedback is too slow (30s = broken workflow).

**Scope:**
1. **LSP file change notifications:** Watch for modified functions, recompute only affected VCs
2. **Enhanced dependency tracking:** Function call graph, changed function → invalidate callers
3. **Solver state reuse:** Z3 push/pop for unchanged context, incremental solving
4. **Benchmark suite:** Measure speedup on 10+ real codebases (target: 30x like Dafny)
5. **Performance regression tests:** Ensure incremental never slower than full re-verification

**Complexity:** MEDIUM-HIGH
- LSP protocol integration (file watchers, change notifications)
- Dependency graph maintenance (call graph, trait impl graph)
- Z3 incremental API (push/pop, solver state management)
- Cache invalidation correctness (soundness-critical)

**Estimated effort:** 4-5 weeks (LSP integration, dependency tracking, Z3 incremental API, benchmarks)

**Success criteria:**
- User modifies one function; re-verification completes in <1s (vs 30s full re-verification)
- User modifies trait impl; only affected call sites re-verified
- Benchmark shows 20-30x speedup on 1000-line codebase
- Zero cache invalidation bugs (all changes trigger necessary re-verification)

---

### Phase 3: Trigger Customization (MEDIUM PRIORITY)
**Why third:** Performance escape hatch for quantifiers in stdlib contracts. Differentiates from Prusti/Creusot. Low risk, high value.

**Scope:**
1. **`#[trigger(expr)]` attribute parsing:** Extend spec parser (follow Verus syntax)
2. **Manual trigger annotation in quantifiers:** `forall |x| #[trigger] f(x) ==> P(x)`
3. **SMT-LIB PATTERN generation:** `(forall ((x Int)) (! (=> (f x) (P x)) :pattern ((f x))))`
4. **Warning when auto-inference disabled:** "Manual trigger overrides inference; ensure completeness"
5. **Diagnostic for interpreted symbols:** "Trigger contains arithmetic (+); may not instantiate. Use function call."

**Complexity:** MEDIUM
- Spec parser extension (attribute syntax, AST representation)
- SMT-LIB PATTERN encoding (trivial, just `!` wrapper)
- Inference override logic (skip auto-inference if manual trigger present)
- Diagnostic quality (help users avoid common mistakes)

**Estimated effort:** 2-3 weeks (attribute parsing, SMT encoding, diagnostics, tests)

**Success criteria:**
- User annotates `forall |i| #[trigger] vec.get(i) ==> vec[i] < 100` and verification succeeds
- User writes trigger with arithmetic `#[trigger] (i + 1)` and gets warning
- User provides no trigger for complex quantifier and gets "no trigger inferred" warning
- Performance test: manual trigger reduces verification time 2-10x on pathological case

---

### Phase 4: VSCode Extension (MEDIUM PRIORITY)
**Why fourth:** IDE integration validates stdlib contracts are usable in real workflow. Incremental verification makes this feasible (<1s feedback).

**Scope:**
1. **VSCode extension scaffolding:** TypeScript + esbuild, published to VSCode marketplace
2. **Language server client:** LSP integration with rust-fv diagnostics (reuse cargo verify JSON)
3. **Inline error highlighting:** Red squiggly underlines for VC failures, hover for VC description
4. **Status bar "Verifying..." indicator:** Shows progress, click for output panel
5. **Output panel for detailed VCs:** Full SMT-LIB output, Z3 counterexample (if available)
6. **Configuration:** Enable/disable verification on save, timeout settings, Z3 path

**Complexity:** MEDIUM
- VSCode extension API (well-documented, TypeScript)
- LSP client integration (async messaging, error handling)
- UI/UX design (status bar, output panel, hover info)
- Testing (across VSCode versions, extension host debugging)

**Estimated effort:** 3-4 weeks (extension scaffolding, LSP client, diagnostics display, testing, marketplace publish)

**Success criteria:**
- User opens Rust file with `#[requires]` annotation; sees "Verifying..." in status bar
- User introduces VC failure; sees red squiggle, hover shows "postcondition not satisfied: x > 0"
- User clicks status bar; output panel shows detailed VC failure with SMT-LIB
- Extension published to VSCode marketplace with 5+ downloads, 0 critical bugs

---

### Phase 5: rust-analyzer Integration (MEDIUM PRIORITY)
**Why fifth:** Complements VSCode extension; enables zero-config IDE workflow for rust-analyzer users. Reuses LSP diagnostics from Phase 4.

**Scope:**
1. **rust-analyzer custom diagnostic source:** Integrate into `rust-analyzer.diagnostics.sources`
2. **`rust-analyzer.diagnostics.rust_fv.enable` configuration:** Enable/disable rust-fv diagnostics
3. **Flycheck integration:** Run `cargo verify` on save (like `cargo check`)
4. **Inline verification status:** Checkmarks for proved functions (like code lens)
5. **Documentation:** rust-analyzer integration guide, configuration examples

**Complexity:** MEDIUM-HIGH
- rust-analyzer codebase exploration (~200k LOC, complex)
- Custom diagnostic source integration (not well-documented, requires source reading)
- Flycheck integration (cargo runner hooks, process management)
- Testing across rust-analyzer versions (compatibility risk)

**Estimated effort:** 4-6 weeks (codebase exploration, custom diagnostic source, flycheck, testing, docs)

**Success criteria:**
- User enables `rust-analyzer.diagnostics.rust_fv.enable = true`; sees verification errors inline
- User modifies function; flycheck runs `cargo verify` on save (<1s with incremental)
- Checkmarks appear next to verified functions (code lens)
- Works with rust-analyzer 0.3.x (current stable) and 0.4.x (next release)

---

### Phase 6: bv2int Optimization (LOWEST PRIORITY)
**Why last:** Optimization, not capability. Tackle after stdlib contracts prove performance bottleneck. High risk (Z3 tactic unpredictability).

**Scope:**
1. **Z3 bv2int tactic configuration:** Use `bv2int` simplifier, `ctx-solver-simplify`
2. **Arithmetic-heavy benchmark suite:** Vec indexing, HashMap hashing, bit manipulation
3. **Selective bv2int for bounded integers:** Apply to u8/i32 (bounded), not usize (architecture-dependent)
4. **Performance regression tests:** Ensure bv2int doesn't slow down simple cases (1s → 17hr risk)
5. **Documentation:** When to use bv2int, performance characteristics, known issues

**Complexity:** MEDIUM
- Z3 tactic API (documented, but tactic interaction complex)
- Benchmark infrastructure (measure solver time, not just end-to-end)
- Selective encoding logic (type-based, configuration flags)
- Performance measurement (statistical significance, variance handling)

**Estimated effort:** 2-3 weeks (tactic configuration, benchmarks, selective encoding, performance tests)

**Success criteria:**
- Vec indexing benchmark: 2-5x speedup with bv2int (arithmetic-heavy)
- Simple arithmetic: 0.9-1.1x (no slowdown)
- Documentation warns about 17hr risk, recommends profiling first
- User can disable bv2int per-function with `#[verifier::no_bv2int]`

---

## Deferred Features (v0.4+)

| Feature | Reason to Defer | Revisit When | Estimated Effort |
|---------|----------------|--------------|------------------|
| **Counterexample Generation** | HIGH complexity; requires bounded model checker integration (Kani's CBMC approach) or Z3 model extraction + concretization. Marginal ROI vs effort. | User feedback requests concrete failure cases (vs VC description). Consider Z3 model API first (lower effort). | 8-12 weeks (bounded MC integration) or 4-6 weeks (Z3 model extraction) |
| **Bounded Verification Mode** | Requires separate BMC engine (CBMC integration) or bounded loop unrolling. Scope creep for v0.3. Different verification paradigm. | Unsafe code verification patterns stabilize; users request bounded checking for specific hotspots. | 10-15 weeks (CBMC integration, hybrid SMT+BMC) |
| **Weak Memory Model Support** | Academic frontier; C++11/Rust memory model formalization ongoing. SeqCst atomics (v0.2) cover 95% of use cases. Relaxed atomics rare. | SeqCst atomics validated in production; research matures (POPL papers on Rust relaxed atomics). | 15-20 weeks (memory model formalization, happens-before extension) |
| **Proof Visualization (HTML/GUI)** | LOW priority until user base >100; terminal output sufficient for early adopters. Why3-style HTML generation is easy, but UI/UX design is rabbit hole. | Community requests shareable proof artifacts (code review, audit, compliance). | 3-5 weeks (HTML generation, CSS/JS for interactive visualization) |
| **Automatic Iterator Combinator Verification** | Requires specification entailments (higher-order logic); research-level. Verus/Dafny still working on this. Hard dependency on closure contract inference. | Verus/Dafny establish patterns we can follow; research papers provide formalization. | 12-18 weeks (specification entailments, higher-order unification) |
| **Incremental Verification (Advanced: 100x speedup)** | Basic per-function caching in v0.1; enhanced dependency tracking in v0.3 Phase 2 (30x). Diminishing returns beyond 30x (solver time dominates). | Performance profiling shows VC re-computation bottleneck (vs solver time). Consider solver result caching, proof certificates. | 6-8 weeks (proof certificates, solver result caching, cache persistence) |
| **Separation Logic for Unsafe** | Requires Iris/Coq integration or custom separation logic encoding. Years of research effort (Prusti/RustBelt scope). Rust borrow checker handles 95% of cases. | Production users demonstrate concrete need (low-level data structures, FFI, concurrent data structures). | 20-30 weeks (Iris integration) or 30-40 weeks (custom separation logic) |
| **Multiple SMT Solvers (CVC5, Yices)** | Z3 is industry standard; covers 99% of use cases. CVC5 has better string theory (not used in Rust). Multi-solver adds maintenance burden. | Z3 timeout/performance issues demonstrated in production; CVC5 solves cases Z3 cannot. | 4-6 weeks (CVC5 integration, solver abstraction layer) |

---

## Complexity Notes

**Standard Library Contracts (HIGH):**
- Requires trait-level generic contracts (`impl<T> Vec<T>` with trait bounds like `T: Clone`)
- Modular verification across crate boundaries (std is external; need public contract API)
- Prophecy variables for mutable iterators (`IterMut<'a, T>` with lifetime prophecy)
- Soundness validation critical (unsound stdlib contract breaks all downstream code)
- Testing against real codebases (not just unit tests; verify cargo projects)
- **Risk:** Unsound contract discovered post-release (breaking change to fix)

**Incremental Verification Enhanced (MEDIUM-HIGH):**
- LSP protocol integration (file watchers, change notifications, async)
- Dependency graph maintenance (function call graph, trait impl graph, generic instantiation graph)
- Z3 incremental API (push/pop, check-sat-using, solver state)
- Cache invalidation correctness (soundness-critical; must re-verify all affected VCs)
- **Risk:** Cache invalidation bug (stale VCs, unsound verification)

**Trigger Customization (MEDIUM):**
- Spec parser extension well-understood (follow Verus `#[trigger]` syntax)
- SMT-LIB PATTERN generation straightforward (just `!` wrapper with `:pattern`)
- Interaction with auto-inference requires careful design (don't break existing code; prefer manual over auto)
- Diagnostic quality important (help users avoid interpreted symbols in triggers)
- **Risk:** Manual trigger worse than auto-inferred (user shoots self in foot; need good diagnostics)

**VSCode Extension (MEDIUM):**
- VSCode extension API mature, well-documented (TypeScript, esbuild, LSP client)
- LSP integration requires understanding protocol (async messaging, error handling, cancellation)
- UI/UX design non-trivial (status bar, output panel, hover info, configuration)
- Testing across VSCode versions (extension host debugging, E2E tests)
- **Risk:** Poor UX (slow, cluttered, confusing); requires user testing

**rust-analyzer Integration (MEDIUM-HIGH):**
- rust-analyzer codebase large (~200k LOC), complex architecture
- Custom diagnostic sources not well-documented (requires source code reading, experimentation)
- Flycheck integration requires understanding cargo runner hooks (spawning, output parsing, error handling)
- Version compatibility risk (rust-analyzer updates frequently; API churn)
- **Risk:** Version incompatibility (works on 0.3.x, breaks on 0.4.x); need testing matrix

**bv2int Optimization (MEDIUM):**
- Z3 tactic API documented, but tactic interaction complex (order matters, simplifiers compose unpredictably)
- bv2int performance unpredictable (1s vs 17hr cases in GitHub issues; need extensive benchmarking)
- Selective application requires type-based heuristics (bounded vs unbounded integers)
- Performance regression testing critical (ensure no slowdowns)
- **Risk:** bv2int makes common cases slower (17hr issue); need kill switch (`#[verifier::no_bv2int]`)

---

## Sources

### Standard Library Contracts
- [Verifying the Rust Standard Library (VSTTE 2024)](https://www.soundandcomplete.org/vstte2024/vstte2024-invited.pdf) - Rust std unsafe code statistics (5.5k unsafe functions, 40 soundness issues, 17 CVEs in 3 years), verification challenges
- [Prusti: Formal Verification for Rust (Springer 2022)](https://link.springer.com/chapter/10.1007/978-3-031-06773-0_5) - Iterator specification patterns (Iter, IterMut, IntoIter, vector-to-slice coercion)
- [Verus Tutorial and Reference](https://verus-lang.github.io/verus/guide/) - Verification standard library (14k LOC total implementation)
- [Kani Rust Verifier - Verify Rust Std Lib](https://model-checking.github.io/verify-rust-std/tools/kani.html) - Stdlib verification approach (bounded model checking)
- [Dafny Tutorial (arXiv 2017)](https://arxiv.org/pdf/1701.04481) - Standard library of useful Dafny functions and lemmas, unbounded and bounded quantifiers

### Trigger Customization
- [Tunable Automation in Automated Program Verification (arXiv 2025)](https://arxiv.org/html/2512.03926) - Dafny vs Verus trigger selection comparison; surface language level manual selection vs conservative defaults
- [Verus #[trigger] bugfix for nested quantifiers (PR #1343)](https://github.com/verus-lang/verus/pull/1343) - Trigger annotation syntax, nested quantifier handling
- [Trigger Selection Strategies to Stabilize Program Verifiers (Springer 2016)](https://link.springer.com/chapter/10.1007/978-3-319-41528-4_20) - Fine balance: not too restrictive (insufficient instantiations), not too permissive (excessive instantiations)
- [F* Quantifiers and Patterns Wiki](https://github.com/FStarLang/FStar/wiki/Quantifiers-and-patterns) - Pattern annotation syntax, trigger requirements
- [SMT-LIB 2.7 Reference (Feb 2025)](https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-02-05.pdf) - `:pattern` attribute specification for quantifiers

### IDE Integration (VSCode)
- [Kani VSCode Extension Marketplace](https://marketplace.visualstudio.com/items?itemName=model-checking.kani-vscode-extension) - One-click verification, counterexample unit tests, debug traces, coverage highlighting
- [Kani VSCode User Guide](https://github.com/model-checking/kani-vscode-extension/blob/main/docs/user-guide.md) - Harness discovery in testing panel, run with play button, inline error messages, concrete playback, debugger integration
- [Dafny VSCode Extension Marketplace](https://marketplace.visualstudio.com/items?itemName=dafny-lang.ide-vscode) - Syntax highlighting, IntelliSense, go-to-definition, hover information, compile and run
- [Making Verification Compelling: Dafny Visual Feedback (2023)](https://dafny.org/blog/2023/04/19/making-verification-compelling-visual-verification-feedback-for-dafny/) - Before: wait 30s for all diagnostics. After: incremental diagnostics as code verified. F7 for verification trace, F8 to hide. Context menu copy with `assume`.
- [Building VS Code Extensions in 2026: Complete Guide](https://abdulkadersafi.com/blog/building-vs-code-extensions-in-2026-the-complete-modern-guide) - TypeScript + esbuild, React for rich UIs, thoughtful API design

### rust-analyzer Integration
- [rust-analyzer LSP Integration (DeepWiki)](https://deepwiki.com/rust-lang/rust-analyzer/3-language-server-protocol-integration) - LSP requests → analysis queries, results → LSP responses. Custom requests prefixed `rust-analyzer/*`.
- [rust-analyzer Diagnostics Documentation](https://rust-analyzer.github.io/book/diagnostics.html) - Most errors from `cargo check` integration; growing number of native diagnostics. Some don't respect `#[allow]` yet.
- [rust-analyzer Configuration](https://rust-analyzer.github.io/book/configuration.html) - `rust-analyzer.diagnostics.enable`, `rust-analyzer.diagnostics.experimental.enable`, `rust-analyzer.diagnostics.disabled` settings

### bv2int Optimization
- [Z3 Bitvector Theory Guide](https://microsoft.github.io/z3guide/docs/theories/Bitvectors/) - bv2int, int2bv operations, bitvector arithmetic
- [Z3 bv2int Performance Issues (GitHub #1481)](https://github.com/Z3Prover/z3/issues/1481) - Comparison: bv2int version ran 17 hours, 3.5GB memory; bitblast version terminated <1s
- [SMT-LIB FixedSizeBitVectors Theory](https://smt-lib.org/theories-FixedSizeBitVectors.shtml) - bv2nat (non-negative) vs bv2int (2's complement). Z3 uses bv2int, CVC4 uses bv2nat.
- [Understanding Bit-vector Arithmetic in Z3 (TU Delft thesis)](https://repository.tudelft.nl/file/File_0517332f-750c-464e-ad27-0a144d8f672f) - Lazy intblasting approach, integer variables don't have bounds (need underflow/overflow constraints)
- [SMT-LIB Discussion: bv/integer conversions](https://groups.google.com/g/smt-lib/c/-GJG1Pq61hI) - bv2int may return negative integers; solver support varies

### Verification Performance
- [Dafny Verification Optimization Documentation](https://dafny.org/latest/VerificationOptimization/VerificationOptimization) - Assertion batch splitting (`{:split_here}`, `{:focus}`, `{:isolate_assertions}`), `measure-complexity` command, opacity/reveal, `assert P by { }` proof isolation
- [Timeout Prediction for Software Analyses (Springer 2023)](https://link.springer.com/chapter/10.1007/978-3-031-47115-5_19) - Machine learning to predict timeout; accumulated speedup 30x for incremental verification
- [Incremental Solving Techniques (Emergent Mind)](https://www.emergentmind.com/topics/incremental-solving-approach) - Push/pop frame stacks, selector literals to add/remove constraints, reuse learned clauses and partial models

### Ecosystem Patterns
- [Why3 Tools Documentation](https://www.why3.org/doc/manpages.html) - IDE marks proved goals with green checked icon, counterexamples in task tab, HTML output with green/red backgrounds
- [Creusot: Rust Verification (HAL 2022)](https://inria.hal.science/hal-03737878v1/document) - Pearlite specification language, prophecy-based, 14k LOC verification standard library (LGPL license)
- [VeriStruct: AI-Assisted Verification (arXiv 2025)](https://arxiv.org/html/2510.25015) - Verus data structure module verification, planner orchestrates abstractions/invariants/specs/proofs
