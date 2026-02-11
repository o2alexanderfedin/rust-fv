# Feature Research: Rust Formal Verification Tools

**Domain:** Formal verification tools for Rust
**Researched:** 2026-02-10
**Confidence:** HIGH

## Feature Landscape

### Table Stakes (Users Expect These)

Features users assume exist. Missing these = product feels incomplete.

| Feature | Why Expected | Complexity | Notes |
|---------|--------------|------------|-------|
| **Function contracts** (`requires`, `ensures`) | Core of any verification tool - pre/postconditions are standard in Dafny, JML, ACSL | LOW | Verus, Prusti, Creusot all have this. Kani uses assertions instead. |
| **Assertion verification** | Universal across all verifiers - developers expect assert!() to be checked | LOW | All tools support this. Kani checks for panics automatically. |
| **Arithmetic overflow detection** | Rust doesn't prevent overflow - verification tools must catch it | LOW | Kani checks automatically. Verus/Prusti require bounded integer mode or explicit checks. |
| **Panic detection** | Rust-specific: unwrap(), expect(), index out of bounds | LOW | Kani checks automatically. Others require annotations or bounded checks. |
| **Basic integer arithmetic verification** | Table stakes for any SMT-based tool | LOW | All tools support via SMT encoding. |
| **Cargo integration** | Rust developers expect `cargo verify` workflow, not separate toolchains | MEDIUM | Kani: `cargo kani`. Prusti: `cargo prusti`. Verus requires custom build. |
| **Error reporting with source locations** | Developers need to know WHERE verification fails | MEDIUM | All tools provide this. Quality varies. |
| **Counterexample generation** | When verification fails, show concrete values that violate property | MEDIUM | Kani excels here (bounded MC produces traces). SMT-based tools (Verus, Prusti) provide model values. |
| **Safe Rust verification** | Primary use case - verify memory-safe Rust code for functional correctness | MEDIUM | All tools support safe Rust. Varies in expressiveness. |
| **Loop invariants** | Loops are ubiquitous - users expect to annotate and verify them | MEDIUM | Verus: manual `invariant`. Prusti: `body_invariant!`. Kani: bounded unrolling. Creusot: auto-infers some cases. |
| **Bounded integer types** | Rust uses i32, u64, etc. - tools must model bounded semantics | MEDIUM | Kani: bit-precise. Verus: optional via `u32::MAX`. Prusti: overflow checks. |
| **Basic ownership reasoning** | Rust's core value prop - verifiers must leverage ownership for soundness | HIGH | All tools exploit ownership. Verus uses linear ghost types. Prusti uses Viper's permissions. Creusot uses prophecies. |

### Differentiators (Competitive Advantage)

Features that set the product apart. Not required, but valued.

| Feature | Value Proposition | Complexity | Notes |
|---------|-------------------|------------|-------|
| **Zero-friction cargo workflow** | Standard `cargo verify` without forked compiler or custom rustc | HIGH | rust-fv goal. Verus requires forked compiler. Kani/Prusti use standard rustc. **CRITICAL DIFFERENTIATOR**. |
| **Unbounded mathematical integers** (`int`, `nat`) | Reason about correctness without overflow concerns, then refine to bounded | MEDIUM | Verus: `int`, `nat` types. Dafny-style. Prusti: limited support. Kani: no (bounded MC). **Differentiates from bounded MC**. |
| **Ghost code and ghost state** | Specify invariants using auxiliary state erased at runtime | MEDIUM | Verus: `ghost`, `tracked` modes. Prusti: limited `ghost!`. Creusot: ghost blocks. **Key for complex invariants**. |
| **Prophecy operators** (`^final`) | Reason about future values of mutable borrows without complex ghost state | HIGH | Creusot: core feature (`^` operator). Unique to Creusot. **Elegant handling of mutation**. |
| **Quantifiers in specifications** (`forall`, `exists`) | Express properties over collections, ranges, unbounded data | MEDIUM | Verus: full support. Prusti: limited. Kani: no (bounded). **Essential for non-trivial properties**. |
| **Trigger customization for SMT** | Control quantifier instantiation to avoid timeouts/incompleteness | HIGH | Verus: `#[trigger]` annotations. Recent work on tunable automation. **Expert feature for performance**. |
| **Automatic loop invariant inference** | Reduce annotation burden - tool infers some/all invariants | HIGH | Creusot 0.9.0: auto-detects immutable vars in loops. AutoVerus: LLM-based generation. **Major automation win**. |
| **Mutable borrow reasoning** | Verify code with `&mut` borrows without excessive annotations | HIGH | Verus: tracked borrows. Creusot: prophecies. Prusti: pledges. **Competitive moat for practical verification**. |
| **Trait/generic support** | Verify polymorphic code with trait bounds | HIGH | Verus: extensive trait support. Kani: trait objects verified. Prusti: limited. **Essential for real Rust code**. |
| **Concurrency verification** | Verify thread-safe code, atomics, locks | VERY HIGH | Miri: data race detection. Creusot 0.9.0: `AtomicI32`, `AtomicInvariant`. Verus: research. **Bleeding edge**. |
| **Bit-precise bounded verification** | Exact semantics of Rust's integer types at bit level | MEDIUM | Kani: CBMC-based, bit-precise. **Differentiator for safety-critical systems**. |
| **Unsafe code verification** | Verify raw pointers, unsafe blocks, FFI | VERY HIGH | Kani: supports unsafe. UnsafeCop: specialized. Miri: dynamic checking. Others: limited/no support. **Huge gap in ecosystem**. |
| **IDE integration** (rust-analyzer, VSCode) | Real-time verification as you type | HIGH | Prusti: VSCode extension. Others: command-line only. **UX differentiator**. |
| **AI-assisted proof generation** | LLM generates annotations, loop invariants, proofs | VERY HIGH | AutoVerus: GPT-4 for Verus. VeriStruct: data structures. **Emerging, high automation potential**. |
| **Standard library verification** | Pre-verified contracts for Vec, HashMap, etc. | HIGH | Rust Foundation challenge. Verus: some stdlib. **Ecosystem play - high leverage**. |

### Anti-Features (Commonly Requested, Often Problematic)

Features that seem good but create problems.

| Feature | Why Requested | Why Problematic | Alternative |
|---------|---------------|-----------------|-------------|
| **Fully automatic verification** (no annotations) | "Just press button and verify" sounds ideal | Undecidable for general programs. Even auto-active tools (Verus) need annotations for non-trivial code. False sense of completeness. | Be honest: 80-90% automation for common patterns. Require annotations for complex invariants. Flag what's unverified. |
| **Verify all unsafe Rust automatically** | Unsafe code is risky, automate verification | Unsafe breaks ownership guarantees. Pointer reasoning is hard. Aliasing is undecidable. | Bounded verification (Kani) OR manual annotations (RustBelt-style) OR dynamic checking (Miri). Be explicit about limitations. |
| **Forked compiler as a feature** | "We modify rustc for better integration" | Maintenance nightmare. Lags stable Rust. Users resist custom toolchains. | Use proc macros + MIR extraction + build scripts. rust-fv's zero-friction approach. |
| **Support every Rust feature from day 1** | "Comprehensive tool" | Massive scope. Delays launch. Most features unused initially. | MVP: i32/u64, structs, basic ownership, simple loops. Expand based on user demand. |
| **Real-time verification in IDE** | "Like type-checking but for correctness" | Verification is slow (seconds to minutes). False positives frustrate users. Background tasks complex. | Batch verification on save/commit. Clear progress indicators. Fast-path for incremental checks. |
| **Arbitrary precision for all integers** | "Math integers are easier to reason about" | Performance: SMT struggles with large domains. Doesn't match Rust semantics (bounded). | Offer unbounded integers (`int`, `nat`) for spec, but require refinement to bounded (`i32`) for exec. Best of both. |
| **One-size-fits-all proof automation** | "Automate everything with one strategy" | Different code needs different automation. Loops need invariants. Quantifiers need triggers. | Tunable automation (Verus 2025 approach). Let users/library authors set automation levels per module/function. |
| **Verify concurrency without explicit synchronization specs** | "Rust prevents data races, so auto-verify" | Rust prevents *data races*, not *race conditions*. Atomics have subtle semantics (acquire/release). | Require explicit atomic invariants (Creusot approach). Leverage Rust's `Send`/`Sync` but don't over-promise. |

## Feature Dependencies

```
Function Contracts
    └──requires──> Specification Language (basic)
                       └──requires──> SMT Solver Integration

Loop Invariants
    └──requires──> Specification Language (basic)
    └──enhances──> Function Contracts

Quantifiers (forall/exists)
    └──requires──> Specification Language (advanced)
    └──requires──> Trigger Customization (for performance)
    └──enhances──> Loop Invariants

Ghost Code
    └──requires──> Mode System (exec/spec/proof)
    └──enhances──> Mutable Borrow Reasoning

Prophecy Operators
    └──requires──> Ghost Code
    └──alternative-to──> Complex Ghost State
    └──enables──> Mutable Borrow Reasoning

Mutable Borrow Reasoning
    └──requires──> Ownership Reasoning
    └──uses-one-of──> [Ghost Code, Prophecy Operators]

Trait/Generic Support
    └──requires──> Function Contracts
    └──requires──> Type System Integration

Concurrency Verification
    └──requires──> Ownership Reasoning
    └──requires──> Ghost Code (for invariants)
    └──requires──> Atomic Operations Support

Unsafe Code Verification
    └──requires──> Pointer Reasoning
    └──conflicts-with──> Full Automation (undecidable)
    └──uses-one-of──> [Bounded MC, Manual Proofs, Dynamic Checking]

AI-Assisted Proof Generation
    └──requires──> Function Contracts
    └──requires──> Loop Invariants
    └──enhances──> All Features (reduces annotation burden)

IDE Integration
    └──requires──> Incremental Verification
    └──requires──> Fast Verification (< 5s)
```

## MVP Definition (Subsequent Milestone for rust-fv)

### Already Have (v0.1 foundation)
- [x] Function contracts (`#[requires]`, `#[ensures]`)
- [x] Bitvector encoding for all integer types
- [x] Arithmetic overflow detection
- [x] MIR-to-IR conversion
- [x] VC generation
- [x] Z3 integration
- [x] Precondition/postcondition verification
- [x] Counterexample extraction

### Add Next (v0.2 — Table Stakes Completion)

**Priority 1 - Missing Table Stakes:**
- [ ] **Loop invariants** — Core feature. Without it, can't verify non-trivial loops. COMPLEXITY: MEDIUM.
  - Syntax: `#[invariant(...)]` macro on loop
  - Generate VCs for initialization, preservation, and use after loop
  - Test case: summing array, binary search
- [ ] **Cargo integration** — `cargo verify` command. COMPLEXITY: MEDIUM.
  - Implement as cargo subcommand via binary in PATH
  - Read Cargo.toml, verify all annotated functions
  - Report results in cargo style
- [ ] **Assertion verification** — Users expect `assert!(x > 0)` to be checked. COMPLEXITY: LOW.
  - Extract assertions from MIR
  - Generate VCs for each assertion
  - Report violations with source location
- [ ] **Panic detection** — Check unwrap(), expect(), indexing. COMPLEXITY: LOW.
  - Detect panic-inducing operations in MIR
  - Generate VCs for panic-freedom
  - Integrate with assertion system
- [ ] **Basic ownership reasoning** — Leverage Rust's ownership for soundness. COMPLEXITY: HIGH.
  - Track moved values (can't use after move)
  - Track borrowed values (immutable during borrow)
  - Generate VCs that assume ownership invariants

**Priority 2 - Quality Improvements:**
- [ ] **Better error messages** — Show which require/ensure/invariant failed, with context.
- [ ] **Documentation** — User guide with examples for each feature.

### Add After Validation (v0.3 — Key Differentiators)

**Priority 1 - Competitive Advantage:**
- [ ] **Unbounded mathematical integers** (`int`, `nat`) — Verus-style. COMPLEXITY: MEDIUM.
  - Add `int`, `nat` types for specifications
  - Require refinement to bounded types for exec code
  - Test: prove correctness without overflow, then check bounded version
- [ ] **Ghost code** — Specify invariants with auxiliary state. COMPLEXITY: MEDIUM.
  - `#[ghost]` attribute for variables/functions
  - Erase ghost code during compilation
  - Check ghost code only affects specifications
- [ ] **Quantifiers** (`forall`, `exists`) — For non-trivial properties. COMPLEXITY: MEDIUM.
  - Extend specification language with quantifier syntax
  - Generate SMT queries with quantifiers
  - Basic trigger inference (avoid manual triggers initially)
- [ ] **Mutable borrow reasoning** — Verify code with `&mut`. COMPLEXITY: HIGH.
  - Prophecy-based (Creusot-style) OR tracked ghost types (Verus-style)
  - Test: verify in-place array reversal, tree mutation

**Priority 2 - Ecosystem:**
- [ ] **Trait/generic support** — Real Rust uses traits extensively. COMPLEXITY: HIGH.
  - Monomorphization-based: verify instantiations
  - Later: trait-level contracts
- [ ] **Standard library contracts** — Pre-verified Vec, Option, Result. COMPLEXITY: MEDIUM.
  - Annotate common stdlib types
  - Users inherit guarantees

### Future Consideration (v1.0+ — Advanced Features)

**Defer until product-market fit:**
- [ ] **Trigger customization** — Expert feature. Wait for user demand. COMPLEXITY: HIGH.
- [ ] **Concurrency verification** — Bleeding edge. Small user base initially. COMPLEXITY: VERY HIGH.
- [ ] **Unsafe code verification** — Hard problem. Bounded MC (Kani) covers many cases. COMPLEXITY: VERY HIGH.
- [ ] **IDE integration** — Significant engineering. Batch mode sufficient for MVP. COMPLEXITY: HIGH.
- [ ] **AI-assisted proof generation** — Exciting but experimental. Partner with research group. COMPLEXITY: VERY HIGH.

## Feature Prioritization Matrix

| Feature | User Value | Implementation Cost | Priority |
|---------|------------|---------------------|----------|
| Loop invariants | HIGH (can't verify loops without it) | MEDIUM | P1 |
| Cargo integration | HIGH (friction point) | MEDIUM | P1 |
| Assertion verification | HIGH (expected) | LOW | P1 |
| Panic detection | HIGH (Rust-specific) | LOW | P1 |
| Basic ownership reasoning | HIGH (soundness) | HIGH | P1 |
| Unbounded integers | MEDIUM (differentiator) | MEDIUM | P2 |
| Ghost code | MEDIUM (complex specs) | MEDIUM | P2 |
| Quantifiers | MEDIUM (non-trivial props) | MEDIUM | P2 |
| Mutable borrow reasoning | HIGH (practical code) | HIGH | P2 |
| Trait/generic support | HIGH (real Rust) | HIGH | P2 |
| Stdlib contracts | MEDIUM (ecosystem) | MEDIUM | P2 |
| Trigger customization | LOW (expert users) | HIGH | P3 |
| Concurrency verification | LOW (small user base) | VERY HIGH | P3 |
| Unsafe code verification | MEDIUM (niche) | VERY HIGH | P3 |
| IDE integration | MEDIUM (UX) | HIGH | P3 |
| AI-assisted proofs | LOW (experimental) | VERY HIGH | P3 |

**Priority key:**
- **P1**: Must have for v0.2 (table stakes completion)
- **P2**: Should have for v0.3 (differentiation)
- **P3**: Nice to have for v1.0+ (future)

## Competitor Feature Analysis

| Feature | Verus | Prusti | Kani | Creusot | rust-fv Goal |
|---------|-------|--------|------|---------|--------------|
| **Function contracts** | ✅ requires/ensures | ✅ requires/ensures | ❌ assertions only | ✅ requires/ensures | ✅ v0.1 DONE |
| **Loop invariants** | ✅ manual | ✅ body_invariant! | ❌ bounded unrolling | ✅ some auto-infer | ✅ v0.2 (manual) |
| **Cargo integration** | ⚠️ custom build | ✅ cargo prusti | ✅ cargo kani | ✅ cargo creusot | ✅ v0.2 |
| **Overflow detection** | ⚠️ requires bounded mode | ✅ automatic | ✅ automatic | ✅ automatic | ✅ v0.1 DONE |
| **Counterexamples** | ⚠️ SMT model | ⚠️ SMT model | ✅ trace + values | ⚠️ SMT model | ✅ v0.1 DONE |
| **Unbounded integers** | ✅ int/nat | ❌ | ❌ | ❌ | ✅ v0.3 |
| **Ghost code** | ✅ ghost/tracked modes | ⚠️ limited | ❌ | ✅ ghost blocks | ✅ v0.3 |
| **Prophecy operators** | ❌ | ❌ | ❌ | ✅ ^final | ❌ (use ghost instead) |
| **Quantifiers** | ✅ forall/exists | ⚠️ limited | ❌ | ✅ forall/exists | ✅ v0.3 |
| **Trigger customization** | ✅ #[trigger] | ❌ | ❌ | ⚠️ limited | ⏳ v1.0+ |
| **Mutable borrows** | ✅ tracked | ✅ pledges | ✅ bit-precise | ✅ prophecies | ✅ v0.3 |
| **Trait/generic** | ✅ extensive | ⚠️ limited | ✅ trait objects | ✅ via Why3 | ✅ v0.3 |
| **Concurrency** | 🔬 research | ❌ | ❌ | ✅ AtomicI32 (0.9.0) | ⏳ v1.0+ |
| **Unsafe code** | ❌ | ❌ | ✅ bounded | ❌ | ⏳ v1.0+ (partner with Kani?) |
| **IDE integration** | ❌ CLI only | ✅ VSCode extension | ❌ CLI only | ❌ CLI only | ⏳ v1.0+ |
| **Forked compiler** | ❌ YES (blocker) | ✅ NO | ✅ NO | ✅ NO | ✅ NO (differentiator) |

**Legend:**
- ✅ Full support
- ⚠️ Partial/limited support
- ❌ No support
- 🔬 Research/experimental
- ⏳ Planned

**rust-fv Positioning:**
- **v0.1**: Solid foundation (contracts, overflow, Z3, counterexamples)
- **v0.2**: Complete table stakes (loops, cargo, assertions, ownership)
- **v0.3**: Differentiate (unbounded int, ghost code, quantifiers, mut borrows)
- **v1.0+**: Advanced (triggers, concurrency, unsafe, IDE)

**Competitive advantage:**
1. **Zero-friction cargo workflow** — No forked compiler (unlike Verus)
2. **Verus-quality expressiveness** — Unbounded integers, ghost code, quantifiers
3. **Practical automation** — 80-90% automation target (Kani-like UX, Verus-like power)

## Feature Implementation Guidance

### Loop Invariants (v0.2, Priority 1)

**Design:**
- Syntax: `#[invariant(i < arr.len() && sum == arr[0..i].sum())]`
- Placement: Attribute on `loop` or `for`/`while` (desugar to loop)
- Semantics:
  - **Initialization**: VC that invariant holds before first iteration
  - **Preservation**: VC that if invariant holds at loop start, it holds at end of iteration
  - **Use**: After loop, assume invariant holds
- Generate 3 VCs per loop: init, preservation, postcondition
- Frame: automatically frame unchanged variables (leverage Rust's ownership)

**Test cases:**
1. Sum array: `sum == arr[0..i].sum()` for `i` in `0..arr.len()`
2. Binary search: `target in arr[lo..hi]` (if exists)
3. GCD: `gcd(a, b) == gcd(original_a, original_b)`

**Complexity factors:**
- Havoc analysis: which variables modified in loop? (MIR analysis)
- Frame inference: unchanged vars retain value (ownership helps)
- Termination: add decreases clause? (defer to v0.3)

### Cargo Integration (v0.2, Priority 1)

**Design:**
- Install binary `cargo-verify` in PATH
- Cargo invokes as `cargo verify` (via `cargo-verify verify` command)
- Read `Cargo.toml`, locate source files
- Parse Rust with syn, extract annotated functions
- Run verification on each, collect results
- Output:
  - Green ✓ for verified functions
  - Red ✗ with error for failed VCs
  - Yellow ⚠ for timeouts
- Exit code: 0 if all verified, 1 if any failed

**Integration points:**
- Use `cargo metadata` to get package structure
- Use `CARGO_MANIFEST_DIR` for paths
- Support workspace packages
- Respect `#[cfg(test)]` and `#[cfg(not(test))]`

**Example output:**
```
$ cargo verify
   Verifying my-crate v0.1.0
     Checked fn add (2 VCs) ... ok
     Checked fn factorial (3 VCs) ... FAILED
       VC failed: postcondition at src/lib.rs:42
       Counterexample: n=5, result=120, expected=125
   Verification failed: 1 of 2 functions
```

### Unbounded Mathematical Integers (v0.3, Priority 2)

**Design:**
- Add `int` and `nat` types (like Verus)
- `int`: unbounded integers (no overflow)
- `nat`: non-negative unbounded integers
- Use in specifications only (spec mode)
- Require refinement to bounded types for exec code
- SMT encoding: use Z3's integer theory (not bitvectors)

**Syntax:**
```rust
#[requires(x >= 0)]
#[ensures(result == x * (x + 1) / 2)]
fn sum_to(x: int) -> int { ... }

// Exec version with bounded refinement:
#[requires(x >= 0 && x <= i32::MAX)]
#[ensures(result == x * (x + 1) / 2)]
fn sum_to_bounded(x: i32) -> i64 { ... }
```

**Benefits:**
- Prove correctness without overflow concerns
- Then verify bounded version satisfies same spec (with overflow checks)
- Ergonomic for algorithm verification

### Ghost Code (v0.3, Priority 2)

**Design:**
- `#[ghost]` attribute on variables, functions, blocks
- Ghost code:
  - Typechecked and verified
  - Erased at compile time (zero runtime cost)
  - Can only affect specifications, not executable code
- Use cases:
  - Ghost variables for history (e.g., `old_value`)
  - Ghost functions for specification (e.g., `sorted(arr)`)
  - Ghost blocks for intermediate proofs

**Syntax:**
```rust
fn reverse(arr: &mut [i32]) {
    #[ghost] let old_arr = arr.clone();

    // ... in-place reversal ...

    #[ensures(forall(|i| arr[i] == old_arr[arr.len() - 1 - i]))]
}
```

**Implementation:**
- Extract ghost code in MIR phase
- Generate VCs using ghost state
- Erase ghost code before codegen
- Check: ghost code doesn't affect control flow of exec code

### Quantifiers (v0.3, Priority 2)

**Design:**
- `forall(|x| P(x))` — universal quantifier
- `exists(|x| P(x))` — existential quantifier
- Encode as SMT quantifiers
- Initial: no manual triggers (rely on SMT heuristics)
- Later (v1.0+): `#[trigger(f(x))]` for performance

**Syntax:**
```rust
#[requires(forall(|i| i < arr.len() ==> arr[i] >= 0))]
#[ensures(result >= 0)]
fn sum_positive(arr: &[i32]) -> i32 { ... }
```

**SMT encoding:**
```smt2
(assert (forall ((i Int)) (=> (< i (arr_len arr)) (>= (select arr i) 0))))
```

**Challenges:**
- Trigger inference: which terms should instantiate quantifier?
- Performance: SMT can timeout on complex quantifiers
- Start simple: bounded quantifiers over indices
- Defer unbounded quantifiers to v1.0+

## Sources

### Tool Documentation and Features
- [Verus overview - Verus Tutorial and Reference](https://verus-lang.github.io/verus/guide/)
- [GitHub - verus-lang/verus](https://github.com/verus-lang/verus)
- [Verus: Verifying Rust Programs using Linear Ghost Types (PDF)](https://www.andrew.cmu.edu/user/bparno/papers/verus-ghost.pdf)
- [GitHub - viperproject/prusti-dev](https://github.com/viperproject/prusti-dev)
- [The Prusti Project: Formal Verification for Rust (PDF)](https://pm.inf.ethz.ch/publications/AstrauskasBilyFialaGrannanMathejaMuellerPoliSummers22.pdf)
- [GitHub - model-checking/kani](https://github.com/model-checking/kani)
- [Getting started - The Kani Rust Verifier](https://model-checking.github.io/kani/)
- [Creusot: Formal verification of Rust programs (POPL 2026 - Tutorials)](https://popl26.sigplan.org/details/POPL-2026-tutorials/6/Creusot-Formal-verification-of-Rust-programs)
- [Creusot: A Foundry for the Deductive Verification of Rust Programs (PDF)](https://inria.hal.science/hal-03737878v1/document)
- [Flux: Liquid Types for Rust](https://dl.acm.org/doi/10.1145/3591283)
- [GitHub - flux-rs/flux](https://github.com/flux-rs/flux)

### Specific Features
- [Ghost code vs. exec code - Verus](https://verus-lang.github.io/verus/guide/ghost_vs_exec.html)
- [Specification code, proof code, executable code - Verus](https://verus-lang.github.io/verus/guide/modes.html)
- [Proofs about forall and exists - Verus](https://verus-lang.github.io/verus/guide/quantproofs.html)
- [Loop unwinding - The Kani Rust Verifier](https://model-checking.github.io/kani/tutorial-loop-unwinding.html)
- [Creusot 0.9.0 - Creusot Devlog](https://creusot-rs.github.io/devlog/2026-01-19/)
- [Tunable Automation in Automated Program Verification](https://arxiv.org/html/2512.03926v1)

### Unsafe Code and Memory Safety
- [deepSURF: Detecting Memory Safety Vulnerabilities in Rust](https://arxiv.org/html/2506.15648v2)
- [Miri: Practical Undefined Behavior Detection for Rust (2026)](https://research.ralfj.de/papers/2026-popl-miri.pdf)
- [UnsafeCop: Bounded Model Checking for Unsafe Rust](https://link.springer.com/chapter/10.1007/978-3-031-71177-0_19)
- [Ensuring Memory Safety in Unsafe Rust with TrustInSoft Analyzer](https://www.trust-in-soft.com/resources/blogs/ensuring-memory-safety-in-unsafe-rust-with-trustinsoft-analyzer)

### Concurrency
- [Miri: Practical Undefined Behavior Detection for Rust (2026)](https://research.ralfj.de/papers/2026-popl-miri.pdf)
- [RustMC: Extending the GenMC stateless model checker to Rust](https://arxiv.org/pdf/2502.06293)
- [Converos: Practical Model Checking for Verifying Rust OS](https://www.usenix.org/system/files/atc25-tang.pdf)

### Standard Library Verification
- [Verify the Safety of the Rust Standard Library - AWS Blog](https://aws.amazon.com/blogs/opensource/verify-the-safety-of-the-rust-standard-library/)
- [Lessons Learned From Verifying the Rust Standard Library](https://arxiv.org/html/2510.01072)
- [GitHub - model-checking/verify-rust-std](https://github.com/model-checking/verify-rust-std)

### Arithmetic and Overflow
- [0560-integer-overflow - The Rust RFC Book](https://rust-lang.github.io/rfcs/0560-integer-overflow.html)
- [Myths and Legends about Integer Overflow in Rust](https://huonw.github.io/blog/2016/04/myths-and-legends-about-integer-overflow-in-rust/)

### IDE Integration
- [Prusti Assistant - Visual Studio Marketplace](https://marketplace.visualstudio.com/items?itemName=viper-admin.prusti-assistant)
- [IDE integration - Prusti dev guide](https://viperproject.github.io/prusti-dev/dev-guide/development/ide.html)

### AI-Assisted Verification
- [AutoVerus: Automated Proof Generation for Rust Code](https://arxiv.org/pdf/2409.13082)
- [VeriStruct: AI-assisted Automated Verification](https://arxiv.org/pdf/2510.25015)

### SMT and Bitvector Reasoning
- [Interactive Bitvector Reasoning using Verified Bit-Blasting](https://dl.acm.org/doi/10.1145/3763167)
- [Expanding the Rust Formal Verification Ecosystem: Welcoming ESBMC](https://rustfoundation.org/media/expanding-the-rust-formal-verification-ecosystem-welcoming-esbmc/)

---

**Research Confidence:** HIGH
- All major tools surveyed (Verus, Prusti, Kani, Creusot, Flux)
- Official documentation + academic papers + recent developments (2025-2026)
- Feature comparison verified across multiple sources
- Implementation complexity assessed based on existing tool architectures
