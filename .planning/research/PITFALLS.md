# Pitfalls Research: v0.3 Production Usability Features

**Domain:** Adding stdlib contracts, trigger customization, IDE integration, and bv2int optimization to existing Rust formal verification tool
**Researched:** 2026-02-14
**Confidence:** MEDIUM-HIGH

## Executive Summary

This research identifies pitfalls when adding production usability features to rust-fv v0.3. Unlike v0.1-v0.2 (core verification capabilities) or advanced features (recursive functions, concurrency), v0.3 focuses on **making verification practical**: standard library support, performance optimization, IDE integration, and expert-level customization.

**Critical insight:** These features sit at the usability boundary. Stdlib contracts determine what users *can* verify. IDE integration determines whether verification is *pleasant*. Trigger customization determines whether experts can *overcome* limitations. bv2int optimization determines whether verification is *fast enough*. Getting these wrong doesn't break correctness - it breaks adoption.

**Risk profile:**
- **Stdlib contracts:** Specification-implementation mismatch creates soundness bugs
- **Trigger customization:** Quantifier loops cause non-termination, poor UX drives misuse
- **IDE integration:** Performance degradation makes tool unusable
- **bv2int optimization:** Semantic mismatch between solvers creates unsoundness

---

## Critical Pitfalls

### Pitfall 1: Incomplete Stdlib Specification Coverage

**What goes wrong:**
Users enable stdlib contract verification expecting comprehensive coverage, but core stdlib functions remain unspecified. Verification succeeds falsely because postconditions aren't checked, or fails with "missing contract" errors on common operations like `Vec::push`, `Option::unwrap`, `slice::len`.

**Why it happens:**
- Attempting to specify entire stdlib at once is overwhelming (10,000+ functions)
- No systematic prioritization of which functions to specify first
- Specifications written without considering common user verification patterns
- Missing specifications discovered only when user code fails verification

**Root cause:**
Rust stdlib is vast. Writing specifications is labor-intensive. Without usage data to guide prioritization, effort goes to wrong functions. Verification-critical operations (collections, numeric ops, Option/Result) must be specified first, but "importance" is subjective without measurement.

**Consequences:**
- **User frustration**: "Why doesn't `x.len()` verify?" - trivial stdlib usage fails
- **Workaround hell**: Users add `#[trusted]` annotations, defeating verification purpose
- **False security**: Missing postconditions allow bugs to pass through
- **Documentation debt**: Each missing contract requires explanation

**Prevention:**
1. **Usage-based prioritization**:
   - Instrument existing rust-fv usage to identify most-called stdlib functions
   - Analyze popular Rust crates for common verification patterns
   - Create "tiers" of specification completeness:
     - **Tier 1 (Essential)**: 20 most-used functions - blocking v0.3 release
     - **Tier 2 (Common)**: Next 100 functions - best effort
     - **Tier 3 (Comprehensive)**: Remainder - community contribution
2. **Clear error messages**: "Function std::vec::Vec::push has no contract. Consider adding one or using #[trusted]. See: docs.rs/rust-fv/stdlib-coverage"
3. **Specification test suite**: Verify specs against known-correct/known-buggy examples
4. **Property-based validation**: Generate random inputs, compare spec prediction vs actual execution
5. **Documentation first**: Publish coverage matrix showing which stdlib modules are specified

**Warning signs:**
- Integration tests fail with "missing contract" errors on trivial stdlib usage
- Users file bugs asking why basic operations don't verify
- Specifications exist but are too weak (allow unsound behavior) or too strong (reject valid code)
- Verification time explodes because overly-detailed specifications create huge SMT formulas

**Phase to address:**
**Phase 1 (Stdlib Foundation)** - Must establish specification methodology and Tier 1 coverage before proceeding. Without this, v0.3 is unusable.

**Confidence:** HIGH - Standard issue in all verification tools with stdlib support (Dafny, F*, Prusti). Coverage gaps are inevitable; prioritization is critical.

**Sources:**
- [Dafny Standard Libraries Blog](https://dafny.org/blog/2023/12/20/standard-libraries/)
- [Prusti Stdlib Coverage Thesis](https://ethz.ch/content/dam/ethz/special-interest/infk/chair-program-method/pm/documents/Education/Theses/Patrick_Muntwiler_BS_Thesis.pdf)

---

### Pitfall 2: Specification-Implementation Mismatch

**What goes wrong:**
Stdlib contracts claim properties that don't match actual implementation behavior, especially around:
- **Panicking behavior**: Spec says "returns value" but impl panics on empty input
- **Overflow semantics**: Spec models mathematical integers, impl wraps on overflow
- **Undefined behavior boundaries**: Spec permits what rustc/LLVM treat as UB
- **Platform-specific behavior**: Spec assumes 64-bit, breaks on 32-bit

**Why it happens:**
- Writing specifications from documentation instead of implementation
- Not testing specifications against actual stdlib source code
- Rust stdlib has subtle panic conditions not documented
- Overflow/UB semantics differ between debug/release builds

**Root cause:**
Documentation describes *intended* behavior, implementation has *actual* behavior. Verification must match actual. Example: `slice::get_unchecked` documented as "no bounds check" but spec must still forbid out-of-bounds access (UB). Specification must capture panic conditions precisely.

**Consequences:**
- **Soundness catastrophe**: Verified code panics at runtime despite verification success
- **Debug/release divergence**: Debug builds have overflow checks, release doesn't - which does spec model?
- **Platform brittleness**: Code verified on 64-bit fails on 32-bit
- **User distrust**: "Verification said it was safe, but it crashed" - tool credibility destroyed

**Prevention:**
1. **Extract specifications from MIR**: Analyze stdlib MIR, not documentation
2. **Property-based oracle**: For each spec, generate random inputs, compare spec prediction vs actual execution
   ```rust
   #[test]
   fn spec_matches_impl_vec_push() {
       proptest!(|(mut v: Vec<i32>, x: i32)| {
           let spec_len_before = v.len();
           let spec_len_after = spec_len_before + 1;
           v.push(x);
           assert_eq!(v.len(), spec_len_after); // Spec matches impl
       });
   }
   ```
3. **Include panic preconditions explicitly**:
   ```rust
   #[requires(index < self.len())] // Panic condition as precondition
   fn get(&self, index: usize) -> &T
   ```
4. **Document overflow semantics**: Wrapping vs checked vs saturating - be explicit
5. **Cross-reference with Miri**: If Miri flags UB, spec must forbid it
6. **Test matrix**: All specs tested on debug/release, 32-bit/64-bit

**Warning signs:**
- Verified code panics at runtime despite verification success
- Counterexamples found that shouldn't be possible according to spec
- Specification accepts behavior that rustc would reject
- Debug builds fail but release builds pass (or vice versa)

**Phase to address:**
**Phase 1 (Stdlib Foundation)** - Specification validation must be built into specification authoring process. Every spec needs oracle test.

**Confidence:** HIGH - Specification-implementation mismatch is classic verification pitfall. Oracle testing is standard practice (Dafny, F*, Viper all use it).

**Sources:**
- [Smart Contract Formal Specification Survey](https://ramagururadhakrishnan.github.io/Blockchain-Papers/Formal_Methods/A_Survey_of_Smart_Contract_Formal_Specification_and_Verification.pdf) - Discusses specification-implementation gaps
- [Verification and Validation Pitfalls](https://criticalsoftware.com/en/news/common-pitfalls-in-verification-validation)

---

### Pitfall 3: Quantifier Instantiation Loops (Trigger Hell)

**What goes wrong:**
Custom trigger annotations intended to improve performance instead cause:
- Z3 enters infinite instantiation loops, consuming memory until OOM
- Verification times go from 1 second to timeout (60+ seconds)
- Previously-verifying proofs now return "unknown" because trigger patterns too restrictive
- Non-deterministic verification results (succeeds sometimes, fails others)

**Why it happens:**
- **Matching loops**: Triggers match terms that themselves create new trigger-matching terms
- **Overly restrictive triggers**: Prevent necessary quantifier instantiations
- **Mixing automatic and manual triggers**: Creates incompatible pattern sets
- **Triggers contain interpreted symbols**: Arithmetic operations (+, -, *, /) prevent matching
- **Nested quantifiers with interdependent triggers**: Exponential blowup

**Root cause:**
E-matching based instantiation is heuristic. Trigger selection is "an art" (per SMT literature). Pattern creates instantiation, instantiation creates new terms, new terms match pattern again - loop. Z3 has heuristics to break loops, but they're not foolproof. Exposing manual triggers to users without expertise is dangerous.

**Consequences:**
- **Non-termination**: Z3 never returns, verification times out
- **Memory exhaustion**: Z3 process grows to 8GB+ then OOM
- **Non-determinism**: Same code verifies sometimes, fails others (Z3 heuristics vary)
- **User confusion**: "I added a trigger hint, why did it get worse?"

**Prevention:**
1. **Termination checker**: Build static analysis that detects potential matching loops *before* SMT submission
   - Check for self-instantiating patterns: quantifier instantiation creates terms matching same pattern
   - Flag triggers containing interpreted symbols (+, -, *, /, <, >, etc.)
   - Detect mutually-recursive quantifier dependencies
2. **Quantifier diagnostics**: When verification times out/unknowns, emit quantifier instantiation statistics
   - Report: "Quantifier Q1 instantiated 10,000+ times - likely matching loop"
   - Show which ground terms triggered instantiation (use Z3 `-v` flag)
   - Suggest alternative trigger patterns
3. **Fallback strategy**: If custom triggers fail, retry with automatic trigger selection
4. **Bounded instantiation**: Set Z3 options to limit instantiation depth (`smt.qi.max_multi_patterns`, `qi.max_instances`)
5. **Testing protocol**:
   - Every custom trigger must pass "termination test" (verify with tight timeout: 5s)
   - Benchmark suite comparing automatic vs manual trigger performance
   - Track quantifier instantiation counts in CI (fail if >1000 for simple proofs)

**Warning signs:**
- Z3 process memory usage grows unbounded
- Verification never completes (timeout after 60s)
- Z3 `-st` statistics show millions of quantifier instantiations
- Adding seemingly-harmless axiom causes existing proofs to fail
- Verification success depends on term ordering (non-deterministic)

**Phase to address:**
**Phase 2 (Trigger Customization)** - Must build diagnostic tooling BEFORE exposing manual trigger API. Giving users rope to hang themselves without safety net is negligent.

**Confidence:** HIGH - Quantifier instantiation loops are well-documented problem in SMT-based verification. Axiom Profiler exists precisely to debug this issue.

**Sources:**
- [Identifying Overly Restrictive Matching Patterns in SMT-based Program Verifiers](https://dl.acm.org/doi/10.1145/3571748)
- [The Axiom Profiler: Understanding and Debugging SMT Quantifier Instantiations](https://link.springer.com/chapter/10.1007/978-3-030-17462-0_6)
- [A Formal Model to Prove Instantiation Termination for E-matching](https://arxiv.org/html/2404.18007)
- [Understanding how F* uses Z3 - SMT Guide](https://fstar-lang.org/tutorial/book/under_the_hood/uth_smt.html)
- [Z3 Quantifiers Guide](https://microsoft.github.io/z3guide/docs/logic/Quantifiers/)

---

### Pitfall 4: IDE Integration Performance Degradation

**What goes wrong:**
Verification integrated into LSP diagnostics makes IDE unusable:
- Typing has 500ms+ latency because verification runs on every keystroke
- IDE freezes for 10+ seconds when opening file
- Diagnostic flood: 100+ verification errors for incomplete code
- Memory leak: rust-analyzer process grows to 8GB+ over time
- Diagnostics from external crates (stdlib) spam error list

**Why it happens:**
- Running full verification on incomplete/invalid AST (before rustc type-checking)
- No incremental verification - re-verify entire project on every change
- Verification runs on background thread but blocks diagnostic publication
- Caching verification results by file content instead of semantic hash
- Proc macro expansion triggers verification in external crates
- No distinction between "quick check" and "deep verification" modes

**Root cause:**
LSP requires responsiveness (<100ms for typing). Verification is inherently slow (SMT solving). Naive integration runs expensive operation in latency-critical path. Need to decouple verification from diagnostic pipeline, cache aggressively, scope conservatively.

**Consequences:**
- **Usability catastrophe**: Users disable verification because IDE becomes sluggish
- **Adoption failure**: "rust-fv makes my editor unusable" - negative reviews, abandoned tool
- **Resource exhaustion**: rust-analyzer crashes, system becomes unresponsive
- **False negatives**: Users ignore diagnostic flood, miss real errors

**Prevention:**
1. **Incremental verification architecture**:
   - Cache verification results by semantic hash (MIR hash, not source hash)
   - Only re-verify functions whose MIR changed (not downstream dependents initially)
   - Debounce verification trigger: wait 500ms after last keystroke
2. **Verification scoping**:
   - Only verify functions in workspace crates (not dependencies/stdlib)
   - Add config: `rust-analyzer.verification.scope = ["workspace" | "current-file" | "none"]`
   - Disable verification on files with syntax/type errors
3. **Progressive verification**:
   - **Phase 1 (fast, 100ms)**: Quick checks only (no quantifiers, bounded unrolling)
   - **Phase 2 (medium, 1s)**: Standard verification
   - **Phase 3 (slow, manual)**: Deep verification with unbounded loops
   - Show "quick check passed ✓" immediately, upgrade to "verified ✓" later
4. **Resource management**:
   - Set per-verification memory limit (Z3 `-memory:` option)
   - Timeout: 500ms for IDE mode, 30s for explicit verify command
   - Cancel in-flight verification when new edit arrives
5. **Diagnostic filtering**:
   - Suppress verification diagnostics from external crates by default
   - Group related verification failures (don't show 50 errors from one failing postcondition)
   - Hide diagnostics on incomplete code (AST missing expressions)

**Warning signs:**
- User complaints about "IDE becomes unusable with rust-fv enabled"
- rust-analyzer CPU usage sustained >100%
- Verification results arrive 5+ seconds after edit
- Diagnostics panel shows errors in stdlib code user didn't write
- Memory usage grows continuously (500MB → 8GB over hours)

**Phase to address:**
**Phase 3 (IDE Integration)** - Performance must be measured from day 1; reject integration that degrades responsiveness. Benchmark suite with latency requirements.

**Confidence:** HIGH - IDE integration performance is critical for adoption. rust-analyzer has sophisticated incremental architecture - must leverage it, not fight it.

**Sources:**
- [Toward Practical Deductive Verification: Insights](https://arxiv.org/pdf/2510.20514)
- [A Practical Approach to Formal Methods: Eclipse IDE](https://www.mdpi.com/2079-9292/13/23/4660)
- [rust-analyzer IDE diagnostics documentation](https://rust-lang.github.io/rust-analyzer/ide_diagnostics/index.html)
- [rust-analyzer Configuration](https://rust-analyzer.github.io/book/configuration.html)

---

### Pitfall 5: bv2int Semantic Mismatch

**What goes wrong:**
Applying bv2int optimization causes:
- Previously-verifying code now fails (optimization changed semantics)
- Verification succeeds but code exhibits unexpected runtime behavior (soundness bug)
- Mixed bitvector/integer encoding creates performance cliff (10x slowdown)
- Counterexamples contain nonsensical values (bv2int result is negative when expected unsigned)

**Why it happens:**
- **bv2int is "essentially uninterpreted" in Z3**: Solver doesn't precisely model semantics
- **Mismatch between Z3's bv2int and SMT-LIB spec**: Z3 implementation differs from standard
- **Mixing bitvector and integer theories has "significant overhead"**: Per Z3 docs
- **Optimization applied blindly**: Without checking if integers actually simpler than bitvectors
- **Signed vs unsigned bitvector semantics lost**: Conversion to integer erases type information

**Root cause:**
bv2int is a theory bridge, not a first-class operation. Z3 treats it as uninterpreted function with minimal axioms. SMT-LIB spec says bv2int may return negative (2's complement), but Z3 implementation (actually bv2nat) returns non-negative. Solvers differ. Mixing theories is expensive. Optimization must be conservative.

**Consequences:**
- **Soundness bug**: Verifier proves property assuming bv2int semantics, but Z3 doesn't enforce them
- **Performance regression**: "Optimization" makes verification 10x slower due to theory mixing
- **Solver incompatibility**: Works with Z3, fails with CVC5 (different bv2int semantics)
- **Semantic confusion**: Unsigned bitvector converted to signed integer, overflow semantics change

**Prevention:**
1. **Conservative applicability analysis**:
   - Only apply bv2int when operations are purely arithmetic (no bitwise ops: &, |, ^, <<, >>)
   - Only for bitvectors representing counts/indices (provably non-negative)
   - Never mix: either full bitvector encoding OR full integer encoding, not both
   - Check solver support: CVC5 has better bv2int semantics than Z3 (per research)
2. **Semantic preservation validation**:
   - After bv2int transformation, generate test cases to validate equivalence
   - Add assertions that bv2int results are in expected range: `(assert (>= (bv2int x) 0))`
   - Track signedness metadata through conversion
3. **Performance measurement**:
   - Benchmark: bitvector-only vs integer-only vs mixed encoding
   - Only enable bv2int if it improves verification time by 20%+
   - Provide manual override: `#[verify(encoding = "bitvector")]` to disable optimization
4. **Fallback mechanism**:
   - If verification with bv2int returns "unknown", retry with pure bitvector encoding
   - Report to user: "bv2int optimization failed, using bitvector encoding"
5. **Correctness testing**:
   - Differential testing: verify same function with bitvector and integer encoding, compare results
   - SMT-LIB spec compliance: ensure bv2int semantics match SMT-LIB 2.6+ definition

**Warning signs:**
- Verification time increases after "optimization" enabled
- Different results with bv2int vs pure bitvector encoding
- Counterexamples show bit-patterns interpreted as wrong integer values
- Z3 returns "unknown" frequently on bv2int-heavy formulas
- Overflow checks fail in unexpected ways (2's complement vs unsigned confusion)

**Phase to address:**
**Phase 4 (bv2int Optimization)** - Must prove correctness before declaring optimization; performance is secondary to soundness. Differential testing is mandatory.

**Confidence:** MEDIUM-HIGH - bv2int issues documented in Z3 GitHub issues and SMT-LIB discussions. Semantic mismatch between Z3 and spec is known. Mixing theories being expensive is documented in Z3 guide.

**Sources:**
- [Z3 Bitvectors Guide](https://microsoft.github.io/z3guide/docs/theories/Bitvectors/) - "Mixing integers and bit-vectors has significant overhead"
- [bv2int and int2bv slow? Issue #1481](https://github.com/Z3Prover/z3/issues/1481)
- [bv2int and bv2nat Issue #1252](https://github.com/Z3Prover/z3/issues/1252) - Documents semantic mismatch
- [SMT-LIB FixedSizeBitVectors Theory](https://smt-lib.org/theories-FixedSizeBitVectors.shtml)
- [bv/integer conversions SMT-LIB discussion](https://groups.google.com/g/smt-lib/c/-GJG1Pq61hI)

---

### Pitfall 6: Trigger Pattern Usability Gap

**What goes wrong:**
Users exposed to manual trigger API but:
- No documentation explaining when/why to customize triggers
- Error messages are inscrutable: "no trigger found for quantifier" with no guidance
- Users copy-paste trigger patterns without understanding, breaking verification
- Trigger syntax differs from Rust syntax (SMT-LIB terms), causing confusion
- No tooling to validate trigger correctness (learned at verification time)

**Why it happens:**
- Trigger customization API designed for SMT experts, not Rust developers
- Exposing low-level SMT concept without proper abstraction
- Missing education: "trigger selection is an art" (per research) not taught to users
- No progressive disclosure: beginners shouldn't see trigger complexity

**Root cause:**
Triggers are SMT implementation detail, not user-level concept. Automatic trigger selection works 95% of time. Exposing manual control without education creates more problems than it solves. Users don't know when to use it, how to use it, or what good triggers look like.

**Consequences:**
- **User confusion**: "What's a trigger?" "Why is verification timing out?"
- **Cargo cult programming**: Copy-pasted trigger patterns without understanding
- **Support burden**: Every trigger-related bug requires SMT expertise to debug
- **Documentation debt**: Need tutorials, references, troubleshooting guides

**Prevention:**
1. **Progressive disclosure design**:
   - **Default**: Automatic trigger selection (current behavior) - no user annotation
   - **Advanced**: `#[trigger(expr)]` attribute for override - for experts only
   - **Expert**: `#[triggers([expr1], [expr2])]` for multi-pattern triggers
   - **Debug**: `#[verify(show_triggers)]` to see what was selected
2. **Error message quality**:
   - **Before**: "no trigger found for quantifier ∀x. P(x)"
   - **After**: "Cannot verify `forall x: i32. x + 1 > x` - automatic trigger selection failed. Trigger pattern contains arithmetic operation (+) which cannot be matched. Try `#[trigger(x)]` to specify manual trigger. See: docs.rs/rust-fv/triggers"
3. **Trigger validation**:
   - Lint triggers at macro expansion time (before SMT submission)
   - Check for common mistakes: interpreted symbols, missing quantified variables, duplicate patterns
   - Suggest alternatives: "Trigger `x + 1` contains arithmetic - try `f(x)` instead"
4. **Documentation requirements**:
   - Tutorial: "When to customize triggers" with examples
   - Reference: List of good vs bad trigger patterns
   - Diagnostics guide: "Verification timeout troubleshooting" → check quantifier instantiations
5. **Sensible defaults**:
   - Don't expose triggers until user encounters timeout on automatic selection
   - Provide "trigger advisor" that suggests patterns based on quantifier structure

**Warning signs:**
- User questions: "What's a trigger?" "Why is verification timing out?"
- Copy-pasted trigger patterns in user code without understanding
- Trigger-related bugs filed without clear reproduction steps
- Documentation PR needed after multiple support requests on same topic

**Phase to address:**
**Phase 2 (Trigger Customization)** - API design must include error message design and documentation plan. Usability is as important as functionality.

**Confidence:** MEDIUM - Trigger customization is expert feature. Exposing it requires education. Dafny, F* both provide trigger customization but also extensive documentation.

**Sources:**
- [Trigger Selection Strategies to Stabilize Program Verifiers](https://link.springer.com/chapter/10.1007/978-3-319-41528-4_20)
- [Tunable Automation in Automated Program Verification](https://arxiv.org/html/2512.03926) - Discusses automation vs manual control tradeoff
- [Dafny FAQ on Triggers](https://github.com/dafny-lang/dafny/wiki/FAQ)

---

### Pitfall 7: Contract-Specification Language Drift

**What goes wrong:**
Stdlib contracts written in specification language that evolves, causing:
- Breaking changes to spec syntax invalidate 100+ existing stdlib contracts
- Versioning nightmare: which stdlib contracts are compatible with which rust-fv version?
- New spec features can't be used in stdlib (locked to old syntax for compatibility)
- Compiler upgrades break stdlib contracts (MIR encoding changes)

**Why it happens:**
- Specification language still evolving (v0.3 is early!)
- Stdlib contracts committed directly to rust-fv codebase (tight coupling)
- No stable spec IR - contracts parsed directly from syntax
- No automated migration when spec syntax changes

**Root cause:**
Stdlib contracts are code that lives a long time. Specification language is young and will change. Tight coupling between syntax and semantics makes evolution painful. Need abstraction layer.

**Consequences:**
- **Breaking change avalanche**: Spec syntax change requires rewriting 50+ stdlib contracts
- **Version incompatibility**: Users report "verification broke after update" without code changes
- **Feature lock-in**: Can't add new spec features due to backward compatibility
- **Maintenance burden**: Multiple versions of same contract for different rust-fv versions

**Prevention:**
1. **Specification IR layer**:
   - Parse contracts to stable AST, not directly to SMT
   - Version spec IR separately from syntax (syntax is just parser frontend)
   - Allow multiple syntax versions targeting same IR
2. **Stdlib contract versioning**:
   - Tag contracts with spec version: `#![spec_version = "0.3"]`
   - Provide migration tool: `rust-fv migrate-specs --from 0.3 --to 0.4`
   - Maintain compatibility shims for old syntax (deprecated but working)
3. **Specification test suite**:
   - Every stdlib contract has test ensuring it verifies expected properties
   - Breaking change detection: CI fails if spec change invalidates existing contracts
   - Migration validation: run test suite with old and new syntax, ensure equivalence
4. **Decoupling strategy**:
   - Consider separate crate for stdlib contracts (`rust-fv-std-contracts`)
   - Versioned independently from core tool
   - Breaking changes to spec require major version bump
5. **Graceful degradation**:
   - If contract syntax parsing fails, emit warning (not error) and use `#[trusted]` fallback
   - Report: "Stdlib contract for Vec::push uses unsupported spec syntax; assuming correct"

**Warning signs:**
- Spec syntax change requires rewriting 50+ stdlib contracts
- Users report "verification broke after update" without code changes
- Multiple versions of same contract for different rust-fv versions
- Inability to add new spec features due to backward compatibility concerns

**Phase to address:**
**Phase 1 (Stdlib Foundation)** - Spec IR design is prerequisite for scalable stdlib contract library. Without it, first syntax evolution will be disaster.

**Confidence:** MEDIUM - Versioning and evolution are common software engineering problems. Spec IR is standard practice (Why3, Boogie, Viper all have IR layers).

---

## Technical Debt Patterns

| Shortcut | Immediate Benefit | Long-term Cost | When Acceptable |
|----------|-------------------|----------------|-----------------|
| **Weak stdlib contracts** (overly permissive postconditions) | Easier to write, fewer false positives | Users can't rely on contracts; defeats purpose of verification | Early tier-3 functions only; never for tier-1 |
| **Automatic triggers only** (skip manual customization phase) | Faster to ship, simpler UX | Users hit timeouts/unknowns with no recourse; limits proof expressiveness | If 95%+ of quantifiers auto-select well; measure first |
| **Synchronous verification in IDE** (block on verification before showing diagnostics) | Simpler implementation, no caching needed | IDE becomes unusable on large projects | Never - asynchronous is table stakes for LSP |
| **bv2int everywhere** (apply optimization to all bitvectors) | Simpler heuristic, fewer code paths | Soundness bugs, performance cliffs, semantic mismatches | Never - must be conservative applicability |
| **Inline stdlib contracts** (write contracts directly in stdlib source) | No separate contract library, single source of truth | Requires forking stdlib, upgrade nightmare | Only if upstreaming to rust-lang/rust (unlikely short-term) |
| **No quantifier instantiation limits** (unbounded Z3 search) | Avoids false unknowns from hitting limits | Timeouts, OOM crashes, non-termination | Early development only; production needs limits |

---

## Integration Gotchas

| Integration | Common Mistake | Correct Approach |
|-------------|----------------|------------------|
| **rust-analyzer LSP** | Running full verification on syntax-invalid code | Check `rustc_driver` compilation phase; only verify after type-checking succeeds |
| **Z3 subprocess** | Assuming Z3 outputs well-formed s-expressions | Parse defensively; Z3 error messages are free-form text; check for `(error ...)` format |
| **Proc macro contracts** | Emitting helpful errors from proc macros | Use `proc_macro::Diagnostic::spanned()` API; avoid panics; test error messages explicitly |
| **MIR-based stdlib specs** | Assuming MIR is stable across rustc versions | Pin to specific rustc nightly; test against multiple versions; use feature flags for differences |
| **Quantifier triggers** | Assuming automatic triggers are deterministic | Z3 heuristics are non-deterministic; same formula can get different triggers; design for variability |
| **IDE diagnostics** | Showing all verification failures immediately | Debounce, filter, and group; progressive disclosure (show critical first); suppress external crates |
| **bv2int conversion** | Using `int2bv` and `bv2int` from Z3 API directly | Validate semantics; Z3 implementation differs from SMT-LIB spec; test with other solvers (CVC5) |
| **Specification parser** | Parsing Rust expression syntax in specifications | Specs use Rust *syntax* but SMT *semantics*; `x + 1` may overflow in Rust, not in spec; make semantics explicit |

---

## Performance Traps

| Trap | Symptoms | Prevention | When It Breaks |
|------|----------|------------|----------------|
| **Quantifier explosion** | Verification takes 60+ seconds; Z3 memory grows to GB | Limit quantifier instantiation depth; use triggers; prefer quantifier-free when possible | >5 nested quantifiers; recursive data structures |
| **No incremental verification** | IDE re-verifies entire project on 1-char change | Cache by MIR hash; only verify changed functions; debounce edits | Projects >10k LOC; LSP integration |
| **bv2int mixed with bitvector** | 10x slowdown after "optimization" | Use pure integer or pure bitvector encoding, never mix | Any mixed formula; Z3 has "significant overhead" per docs |
| **SMT script regeneration** | Rebuilding identical SMT scripts repeatedly | Cache SMT script generation by function hash; reuse VCs across runs | Functions with complex contracts; >100 VCs |
| **Synchronous solver calls** | Single slow verification blocks others | Parallel verification with thread pool; timeout per-VC | Projects with >50 functions; any VC >5 seconds |
| **Unbounded specification inlining** | Inlining stdlib contracts creates 10MB SMT files | Bound inlining depth; use axioms for recursive specs; summarize deep calls | Call chains >10 deep; recursive stdlib functions |

---

## UX Pitfalls

| Pitfall | User Impact | Better Approach |
|---------|-------------|-----------------|
| **"Unknown" with no explanation** | User sees "verification unknown" - doesn't know if bug or tool limitation | Classify unknowns: timeout, quantifier limit, incomplete theory, Z3 gave up; suggest fixes |
| **Counterexample in SMT terms** | User sees `(model (_0 #x0000002a))` - meaningless | Map SMT variables to Rust names; show concrete values; highlight violated contract |
| **No incremental feedback** | Verification takes 30 seconds; no progress indicator | Stream results as VCs complete; show "5/10 VCs verified..."; allow cancellation |
| **Error in stdlib contract** | User code fails verification due to wrong stdlib spec | Mark stdlib errors clearly; link to contract source; allow override with `#[trusted]` |
| **Trigger customization required** | User hits timeout; told "try custom triggers" - no guidance on how | Suggest concrete trigger patterns based on quantifier structure; show automatic selection attempt |
| **IDE diagnostic spam** | 100+ verification errors for half-written function | Suppress diagnostics on incomplete code; show errors only on explicitly requested verification |

---

## "Looks Done But Isn't" Checklist

- [ ] **Stdlib contracts:** Tier-1 functions verified against property-based test oracle (not just "compiles")
- [ ] **Trigger customization:** Quantifier instantiation diagnostic tooling exists before manual trigger API exposed
- [ ] **IDE integration:** Performance benchmark suite passing (typing latency <100ms, file open <1s, memory stable)
- [ ] **bv2int optimization:** Differential testing suite validates bitvector ≡ integer encoding for all test cases
- [ ] **Specification syntax:** Migration tool exists and tested on real contracts before breaking change shipped
- [ ] **Error messages:** User testing conducted; at least 3 non-expert users could resolve common errors with provided messages
- [ ] **Incremental verification:** Cache invalidation correctness tested (changing function A re-verifies A but not unrelated B)
- [ ] **Quantifier termination:** Static loop detection catches known-bad patterns in test suite
- [ ] **Documentation:** Each new feature has: tutorial, reference, troubleshooting guide, FAQs from user testing
- [ ] **Soundness testing:** Fuzzer targeting new features (stdlib contracts, triggers, bv2int) run for 1M+ inputs

---

## Recovery Strategies

| Pitfall | Recovery Cost | Recovery Steps |
|---------|---------------|----------------|
| **Unsound stdlib contract shipped** | HIGH | 1. Yank version immediately<br>2. Add regression test<br>3. Patch and release within 24h<br>4. Postmortem: why wasn't caught in testing? |
| **Trigger pattern causes infinite loop** | MEDIUM | 1. Detect via timeout<br>2. Disable custom triggers for affected function<br>3. Fall back to automatic selection<br>4. Warn user |
| **IDE integration makes editor unusable** | LOW | 1. Add config to disable verification in LSP<br>2. Document workaround<br>3. Fix performance issue in next release |
| **bv2int optimization unsound** | HIGH | 1. Feature flag to disable (default off)<br>2. Comprehensive test suite<br>3. Prove correctness or remove feature |
| **Spec syntax breaking change** | MEDIUM | 1. Provide migration tool<br>2. Support old syntax for 2 versions<br>3. Automated migration in tool (`rust-fv fix`) |
| **Quantifier explosion in production** | LOW | 1. User adds `#[verify(skip)]` to affected function<br>2. Report for investigation<br>3. Adjust heuristics or suggest trigger |
| **Incomplete stdlib contract coverage** | LOW | 1. Document supported functions<br>2. Clear error on unsupported<br>3. Community contribution guide for adding contracts |

---

## Pitfall-to-Phase Mapping

| Pitfall | Prevention Phase | Verification |
|---------|------------------|--------------|
| Incomplete stdlib coverage | Phase 1: Stdlib Foundation | Tier-1 test suite passes; frequency analysis validates priority |
| Specification-implementation mismatch | Phase 1: Stdlib Foundation | Property-based oracle tests pass for all tier-1 contracts |
| Quantifier instantiation loops | Phase 2: Trigger Customization | Static termination analysis detects loops in test suite; timeout CI checks |
| IDE performance degradation | Phase 3: IDE Integration | Benchmark suite: typing <100ms, file open <1s, memory stable <500MB |
| bv2int semantic mismatch | Phase 4: bv2int Optimization | Differential testing: bitvector encoding ≡ integer encoding on 1000+ cases |
| Trigger usability gap | Phase 2: Trigger Customization | User study: 3 non-experts can resolve trigger timeout with error messages |
| Contract-spec language drift | Phase 1: Stdlib Foundation | Spec IR layer implemented; migration tool exists and tested |

---

## Sources

**Formal Verification Stdlib Contracts:**
- [A Survey of Smart Contract Formal Specification and Verification](https://ramagururadhakrishnan.github.io/Blockchain-Papers/Formal_Methods/A_Survey_of_Smart_Contract_Formal_Specification_and_Verification.pdf)
- [The Most Common Pitfalls in Verification and Validation](https://criticalsoftware.com/en/news/common-pitfalls-in-verification-validation)
- [Dafny Standard Libraries](https://dafny.org/blog/2023/12/20/standard-libraries/)
- [Evaluating and Documenting a Rust Verifier (Prusti)](https://ethz.ch/content/dam/ethz/special-interest/infk/chair-program-method/pm/documents/Education/Theses/Patrick_Muntwiler_BS_Thesis.pdf)

**SMT Quantifier Triggers:**
- [Understanding how F* uses Z3](https://fstar-lang.org/tutorial/book/under_the_hood/uth_smt.html)
- [Identifying Overly Restrictive Matching Patterns in SMT-based Program Verifiers](https://dl.acm.org/doi/10.1145/3571748)
- [Trigger Selection Strategies to Stabilize Program Verifiers](https://link.springer.com/chapter/10.1007/978-3-319-41528-4_20)
- [The Axiom Profiler: Understanding and Debugging SMT Quantifier Instantiations](https://link.springer.com/chapter/10.1007/978-3-030-17462-0_6)
- [A Formal Model to Prove Instantiation Termination for E-matching-Based Axiomatisations](https://arxiv.org/html/2404.18007)
- [Tunable Automation in Automated Program Verification](https://arxiv.org/html/2512.03926)
- [Z3 Quantifiers Guide](https://microsoft.github.io/z3guide/docs/logic/Quantifiers/)
- [Programming Z3](https://theory.stanford.edu/~nikolaj/programmingz3.html)

**IDE Integration:**
- [Toward Practical Deductive Verification: Insights from a](https://arxiv.org/pdf/2510.20514)
- [A Practical Approach to Formal Methods: An Eclipse IDE for Security Protocols](https://www.mdpi.com/2079-9292/13/23/4660)
- [An Interactive Verification Tool Meets an IDE](https://link.springer.com/chapter/10.1007/978-3-319-10181-1_4)
- [rust-analyzer IDE diagnostics documentation](https://rust-lang.github.io/rust-analyzer/ide_diagnostics/index.html)
- [rust-analyzer Configuration](https://rust-analyzer.github.io/book/configuration.html)

**Bitvector-Integer Optimization:**
- [Z3 Bitvectors Guide](https://microsoft.github.io/z3guide/docs/theories/Bitvectors/)
- [bv2int and int2bv slow? Issue #1481](https://github.com/Z3Prover/z3/issues/1481)
- [bv2int and bv2nat Issue #1252](https://github.com/Z3Prover/z3/issues/1252)
- [bv/integer conversions SMT-LIB discussion](https://groups.google.com/g/smt-lib/c/-GJG1Pq61hI)
- [SMT-LIB FixedSizeBitVectors Theory](https://smt-lib.org/theories-FixedSizeBitVectors.shtml)
- [Bit-Vector Optimization](https://link.springer.com/chapter/10.1007/978-3-662-49674-9_53)

**Proc Macro Error Handling:**
- [Tracking issue for error messages from proc-macro implementations](https://github.com/rust-lang/rust/issues/50054)
- [proc-macro-error crate](https://docs.rs/proc-macro-error/latest/proc_macro_error/)
- [Better diagnostics for proc macro attributes](https://github.com/rust-lang/rust/issues/102923)

**Compiler Integration:**
- [CompCert: formally verified optimizing C compiler](https://compcert.org/)
- [Formal Verification of a Realistic Compiler](https://xavierleroy.org/publi/compcert-CACM.pdf)

---

*Pitfalls research for: rust-fv v0.3 Production Usability Features*
*Researched: 2026-02-14*
*Confidence: MEDIUM-HIGH (Web research + existing codebase analysis + formal verification domain expertise)*
