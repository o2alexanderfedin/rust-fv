# Technology Stack Research

**Project:** rust-fv (Formal Verification for Rust)
**Researched:** 2026-02-10
**Confidence:** MEDIUM-HIGH

## Executive Summary

The current rust-fv v0.1.0 uses a minimal stack (proc-macro2/syn/quote, rustc internals, Z3 subprocess). For the next phase adding loop invariants, mutable borrow reasoning, aggregate types, inter-procedural verification, and enhanced parsing, the stack should evolve incrementally. The recommended approach keeps the existing foundation while adding targeted libraries for specific capabilities. Key additions: structured Z3 bindings (z3 crate), enhanced parser infrastructure (syn extensions), and modular verification support (function summaries, separation logic encoding).

## Recommended Stack

### Core Compiler Integration

| Technology | Version | Purpose | Why Recommended |
|------------|---------|---------|-----------------|
| Rust Nightly | 1.85.0+ (nightly-2026-02-11) | Compiler API access | REQUIRED. Unstable rustc_private APIs for MIR analysis. Pin specific nightly per release. Existing choice is correct. |
| rustc_driver | nightly | Compiler callbacks | REQUIRED. Only way to hook into compilation pipeline. Already in use, continue with current approach. |
| rustc_middle | nightly | MIR access, type context | REQUIRED. Central hub for MIR bodies, type information, trait resolution. Already in use. API is unstable but essential. |
| rustc_hir | nightly | HIR traversal | KEEP. Needed for specification attribute extraction. Already in use. |
| rustc_span | nightly | Source locations | KEEP. Critical for error reporting. Already in use. |
| rustc_abi | nightly | Type layout info | KEEP. Needed for aggregate type verification (structs, arrays). Already in use, will become more important for Phase 2. |

**Rationale:** These are non-negotiable for compiler-integrated verification. The nightly requirement is a known tradeoff accepted by all Rust verification tools (Verus, Kani, Prusti, Creusot). Pin to specific nightly in rust-toolchain.toml and update quarterly with compatibility testing.

**Alternatives Considered:**
- Stable MIR project: Not production-ready as of 2026. Monitor for future migration.
- rustc_plugin framework: Adds abstraction layer over rustc APIs. AVOID for now - direct API use is more reliable when pinning nightlies.

### Procedural Macro Infrastructure

| Technology | Version | Purpose | Why Recommended |
|------------|---------|---------|-----------------|
| syn | 2.0.114+ | Parse Rust syntax in macros | KEEP current version. Industry standard for proc macros. Features needed: "full", "parsing", "printing", "visit-mut" (add for traversal). |
| quote | 1.0.44+ | Code generation | KEEP. Pairs with syn, stable API, widely used. |
| proc-macro2 | 1.0.106+ | Proc macro foundations | KEEP. Dependency of syn/quote, enables testing outside proc macro context. |

**Enhanced Parsing Additions:**

| Library | Version | Purpose | When to Use |
|---------|---------|---------|-------------|
| syn custom parsers | (part of syn 2.x) | Parse custom specification syntax | For loop invariants `#[invariant(...)]`, prophecy operators `old(x)`, ghost state annotations. Implement using `syn::parse::Parse` trait. |
| darling | 0.20+ | Derive-style attribute parsing | OPTIONAL. Consider if specification attributes grow complex. Verus does NOT use this (manual syn parsing). Defer until syntax complexity warrants it. |

**Rationale:** Current stack is correct. Syn 2.x is stable, feature-complete, and what all major verification tools use. For enhanced specification parsing (loop invariants, prophecy operators), extend via custom `Parse` implementations rather than adding new dependencies.

### SMT Solver Integration

| Technology | Version | Purpose | Why Recommended |
|------------|---------|---------|-----------------|
| Z3 | 4.13.0+ | SMT solver backend | KEEP as primary solver. Most mature, best SMT-COMP performance, used by Verus/Prusti/Creusot. Current subprocess approach is sound. |
| z3 crate | 0.19.7+ | High-level Rust bindings | ADD. Replaces manual SMT-LIB2 string generation with typed API. Reduces encoding bugs, enables incremental solving, better error handling. |

**Current vs. Recommended Approach:**

**Current (v0.1.0):** Manual SMT-LIB2 AST construction + subprocess pipe
- Pros: Full control, no runtime linking issues
- Cons: Error-prone string encoding, no incremental solving, limited introspection

**Recommended (v0.2.0+):** z3 crate with optional fallback to subprocess
- Pros: Type-safe API, incremental solving, push/pop scopes for modular verification, better error messages
- Cons: Requires Z3 C library linkage (mitigated by `bundled` feature)

**Migration Path:**
1. Keep existing SMT-LIB2 infrastructure as fallback
2. Add z3 crate with `bundled` feature (statically links Z3)
3. Use z3 crate for new features (loop invariants, modular verification)
4. Migrate existing bitvector encoding gradually

**Z3 Crate Configuration:**
```toml
[dependencies]
z3 = { version = "0.19", features = ["bundled"] }
```

Features explained:
- `bundled`: Statically link Z3, avoids system installation issues
- Alternative: `vcpkg` for Windows builds

**Alternatives Considered:**

| Solver | Why Not Primary | When to Consider |
|--------|----------------|------------------|
| CVC5 | Comparable performance, good ADT support | If Z3 license becomes issue (BSD vs MIT), or specific theory performance (CVC5 faster on some datatypes) |
| SMT-LIB2 text only | Current approach | For portability across solvers, debugging. Keep as fallback. |
| rsmt2 crate | Process-based Z3 bindings | If bundled Z3 linking fails. Less ergonomic than z3 crate. |

**Confidence:** HIGH. Z3 + z3 crate is the industry standard for Rust verification (Verus uses Z3, Creusot via Why3 uses Z3, Prusti via Viper uses Z3).

### SMT Theory Support

| Theory | SMT-LIB2 Logic | Purpose | Implementation |
|--------|---------------|---------|----------------|
| Bitvectors | QF_BV | Bounded integer arithmetic | KEEP current implementation. Sound for u8/i8/u16/i16/u32/i32/u64/i64/usize/isize. |
| Algebraic Datatypes | (Q)DT | Structs, enums, tuples | ADD for aggregate type support. SMT-LIB 2.6+ feature. Use `z3::Datatype` API. |
| Arrays | (Q)Array | Vec, slices, fixed arrays | ADD for collections. Encode with select/store or quantified axioms. |
| Uninterpreted Functions | UF | Function summaries (inter-procedural) | ADD for modular verification. Each function → UF in caller context. |
| Linear Arithmetic | LIA/LRA | Unbounded integers, ghost math | OPTIONAL. For mathematical specs beyond machine integers. Lower priority than datatypes. |

**Rationale:** Current QF_BV is correct for v0.1.0 (safe arithmetic). Next phase REQUIRES datatypes (structs), arrays (Vec/slice), and UF (function calls). These are standard SMT theories with excellent Z3 support.

**SMT-LIB 2.7 (February 2025) Support:**
- Algebraic datatypes: Mature, supported by all major solvers
- Match expressions: Use for pattern matching in verification conditions
- Recursive datatypes: Essential for linked lists, trees (future)

**Confidence:** HIGH. SMT-LIB 2.6+ datatypes are standard, well-documented, supported by z3 crate.

### Verification Condition Generation

| Component | Technology | Purpose | Implementation Strategy |
|-----------|-----------|---------|------------------------|
| Weakest Precondition | Custom (MIR traversal) | Generate VCs for function bodies | KEEP current approach. Standard in verification (Boogie, Why3, ESC/Java). Extend for loops, conditionals, assignments. |
| Loop Invariants | Syn parsing + WP calculus | Verify loops with user annotations | ADD. Parse `#[invariant(P)]`, generate: (1) P holds on entry, (2) P preserved by iteration, (3) P + !cond → postcondition. |
| Prophecy Variables | Fresh variable generation + prophecy rules | Mutable borrow reasoning | ADD. Follow Creusot's approach: fresh prophecy var for `&mut`, track across mutations. Verus uses "linear ghost types" - more complex, defer. |
| Separation Logic Encoding | SMT + ownership analysis | Heap reasoning via ownership | OPTIONAL. Rust's borrow checker provides separation. For unsafe code only. Use symbolic heap model (base + offset). Defer to v0.3.0. |

**Rationale:** Weakest precondition is the standard VC generation technique (Dijkstra 1975, still state-of-the-art). Loop invariants are essential for Phase 2 (table stakes feature). Prophecy variables are proven approach for mutable borrows (Creusot POPL 2026 tutorial confirms viability).

**Confidence:** HIGH for WP/invariants (textbook techniques), MEDIUM for prophecies (research-level, but Creusot demonstrates feasibility).

### Inter-Procedural Verification

| Approach | Technology | Tradeoff | When to Use |
|----------|-----------|----------|-------------|
| Inlining | MIR inlining + VC gen | Precise, slow, doesn't scale | Functions <20 LOC, no recursion. Current v0.1.0 approach. |
| Function Summaries | UF + contracts | Scalable, modular, requires contracts | DEFAULT for Phase 2. Caller uses callee's contract (UF in SMT). |
| Fixed-point Iteration | Call graph + iterative solving | Handles recursion, complex | Defer to v0.3.0. Needed for recursive data structures. |

**Recommended (v0.2.0):** Function summaries with contracts
- Each verified function generates: precondition P, postcondition Q
- Callers: replace call with `assume P; havoc result; assume Q[result/return]`
- SMT encoding: uninterpreted function + axiom `∀args. P(args) → Q(f(args))`

**Implementation:**
```rust
// Caller verification:
// f: #[requires(x > 0)] #[ensures(result > x)]
let result = f(y); // → assume y > 0; let result = f_uf(y); assume result > y;
```

**Confidence:** HIGH. Function summaries are standard modular verification (ESC/Java, Dafny, Boogie, Why3, Verus).

### Development Tools

| Tool | Purpose | Configuration | Why |
|------|---------|--------------|-----|
| rustfmt | Code formatting | nightly, default config | KEEP. Already configured. Enforce via pre-commit. |
| clippy | Linting | nightly, all warnings | KEEP. Already configured. Enforce via pre-commit. |
| cargo-nextest | Fast test runner | Latest | ADD. Faster than `cargo test`, better output. Verus uses this. |
| cargo-expand | Macro debugging | Latest | ADD. Essential for debugging proc macro output. |
| tracing | Structured logging | 0.1+ | ADD. Replace ad-hoc logging with structured tracing. Filter by module. |

**Installation:**
```bash
# Core (already have)
rustup component add rustfmt clippy rust-src rustc-dev llvm-tools

# Add for Phase 2
cargo install cargo-nextest
cargo install cargo-expand

# Add dependency
cargo add tracing tracing-subscriber
```

**Confidence:** HIGH. These are standard Rust development tools.

### Testing Infrastructure

| Library | Version | Purpose | When to Use |
|---------|---------|---------|-------------|
| Built-in test | (stdlib) | Unit tests, integration tests | KEEP. Current approach is correct. |
| proptest | 1.5+ | Property-based testing | ADD. Generate random Rust programs, verify or find counterexamples. |
| compiletest_rs | 0.11+ | UI tests (error messages) | ADD. Test error reporting quality. Used by rustc, clippy. |
| insta | 1.40+ | Snapshot testing | OPTIONAL. For large AST/MIR outputs. Consider if debugging gets tedious. |

**Rationale:** Property-based testing is critical for verification tools (find edge cases in VC generation). Compiletest_rs ensures good error messages (UX requirement). Insta helps with regression testing of complex outputs.

**Confidence:** MEDIUM-HIGH. Proptest is standard for testing complex Rust logic. Compiletest_rs is standard for compiler-related tools.

## Alternatives Considered

### Why NOT Use These

| Avoid | Reason | Use Instead |
|-------|--------|-------------|
| Separate specification language (Dafny-style) | Increases learning curve, breaks Rust tooling (LSP, rustfmt) | Rust attributes with embedded syntax (like Verus) |
| Python for scripting | GC pauses, deployment complexity | Rust for everything (build.rs, xtask pattern) |
| Custom SMT solver | Years of effort, unlikely to match Z3 | Z3 via z3 crate |
| LLVM IR analysis | Too low-level, optimizations obscure semantics | MIR (higher-level, preserves Rust semantics) |
| Liquid Types (Flux-style) | Type inference is research-level, less predictable | Explicit contracts (Verus-style) |
| Automatic invariant inference | Unreliable in practice, confusing when fails | User-provided invariants with good error messages |

**Confidence:** HIGH. These alternatives were explicitly rejected by successful verification tools (see formal_verification_research_summary.md).

## Stack Patterns by Feature

### For Loop Invariants (Phase 2 Priority 1)

**Stack:**
- syn: Parse `#[invariant(expr)]` attributes
- MIR traversal: Identify loop headers/backedges
- WP calculus: Generate 3 VCs (entry, preservation, exit)
- z3 crate: Solve VCs with `Solver::check()`

**Pattern:**
```rust
#[invariant(i <= n)]  // syn::Attribute → syn::Expr
while i < n {         // MIR: Loop { body, ... }
    // VC1: entry: precondition → invariant
    // VC2: preserve: invariant + body → invariant
    // VC3: exit: invariant + !cond → postcondition
}
```

### For Mutable Borrow Reasoning (Phase 2 Priority 2)

**Stack:**
- Prophecy variables: Fresh SMT variables for `&mut T` final values
- Borrowck integration: Track borrow lifetimes from MIR
- z3 crate: Encode prophecy constraints as implications

**Pattern:**
```rust
fn increment(x: &mut i32) {  // x_old, x_new (prophecy)
    *x += 1;  // VC: x_new = x_old + 1
}
```

**Reference:** Creusot's prophecy model (POPL 2026 tutorial), proven sound for Rust.

### For Aggregate Types (Phase 2 Priority 3)

**Stack:**
- rustc_abi: Extract struct layout (field offsets, sizes)
- z3::Datatype: Declare SMT datatypes for structs
- SMT-LIB 2.6 declare-datatypes: Constructors, selectors, testers

**Pattern:**
```rust
struct Point { x: i32, y: i32 }
// SMT: (declare-datatype Point ((mk-point (x Int) (y Int))))
// Access: (x point_var) → Int
```

### For Inter-Procedural (Phase 2 Priority 4)

**Stack:**
- Function contracts: Extract pre/post from attributes
- Uninterpreted functions: Each fn → UF in SMT
- Modular VC gen: Callers use UF + contract axioms

**Pattern:**
```rust
#[requires(x > 0)]
#[ensures(result == x * 2)]
fn double(x: i32) -> i32 { x * 2 }

fn caller() {
    let y = double(5);  // VC: assume 5 > 0; let y = double_uf(5); assume y == 10;
}
```

## Version Compatibility

| Package | Version | Compatible With | Notes |
|---------|---------|-----------------|-------|
| syn | 2.0.114+ | proc-macro2 1.0.106+, quote 1.0.44+ | Syn 2.x is semver stable. |
| z3 crate | 0.19.7+ | Z3 4.13.0+ | Crate tracks Z3 releases closely. Use `bundled` feature to avoid version conflicts. |
| Rust nightly | 2026-02-11+ | rustc_private components | Pin in rust-toolchain.toml. Test updates in CI before merging. |
| SMT-LIB | 2.6+ | Z3 4.8.5+, CVC5 1.0.0+ | Datatypes require 2.6+. Z3 4.13 supports 2.6. |

**Critical Compatibility Notes:**

1. **Nightly Rust:** rustc_private API breaks frequently. Strategy:
   - Pin to specific nightly in rust-toolchain.toml
   - Update quarterly (Jan, Apr, Jul, Oct) with regression tests
   - Document breaking changes in CHANGELOG.md

2. **Z3 Bundled:** z3 crate with `bundled` feature statically links Z3 → no system Z3 version conflicts. Recommended.

3. **Syn 2.x:** Stable API since 2.0.0. Patch updates safe.

## What NOT to Use

| Technology | Why Avoid | Use Instead |
|-----------|-----------|-------------|
| Z3 Python bindings | Requires Python runtime, GC issues, FFI overhead | z3 crate (native Rust) |
| SMT2 manual parsing | Error-prone, no validation | z3 crate typed API |
| Stable Rust only | Cannot access rustc_private APIs | Nightly with pinned version |
| CBMC/ESBMC | Bounded model checking, cannot prove unbounded correctness | SMT-based (Z3) for functional correctness |
| Miri | Interpreter for detecting UB, not verification | Formal verification with proofs |
| rustc_plugin framework | Adds abstraction over unstable API, more breakage surface | Direct rustc_middle/rustc_hir use |

**Rationale:** These alternatives either don't support the required features (stable Rust), introduce unnecessary complexity (Python bindings), or solve different problems (Miri is testing, not verification).

## Installation Guide

### Core Dependencies

```bash
# Rust toolchain (already configured in rust-toolchain.toml)
rustup toolchain install nightly-2026-02-11
rustup component add rustc-dev llvm-tools rust-src rustfmt clippy --toolchain nightly-2026-02-11

# System Z3 (optional, z3 crate with 'bundled' feature includes Z3)
# macOS:
brew install z3
# Linux (Debian/Ubuntu):
sudo apt-get install z3
# Or skip if using bundled feature
```

### Cargo Dependencies (Additions for Phase 2)

```toml
[workspace.dependencies]
# Existing (keep)
rust-fv-smtlib = { path = "crates/smtlib" }
rust-fv-macros = { path = "crates/macros" }
rust-fv-solver = { path = "crates/solver" }
rust-fv-analysis = { path = "crates/analysis" }

# ADD for Phase 2: SMT solver
z3 = { version = "0.19", features = ["bundled"] }

# ADD for Phase 2: Logging
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }

# ADD for Phase 2: Testing (dev-dependencies)
proptest = "1.5"
compiletest_rs = "0.11"
```

### Development Tools

```bash
# ADD for Phase 2
cargo install cargo-nextest  # Fast test runner
cargo install cargo-expand   # Macro debugging
```

## Migration Strategy from v0.1.0 → v0.2.0

### Phase 1: Add z3 Crate (Week 1-2)

1. Add dependency: `z3 = { version = "0.19", features = ["bundled"] }`
2. Create `crates/solver/src/z3_backend.rs` alongside existing `subprocess.rs`
3. Implement `SolverBackend` trait for both
4. Add feature flag: `solver-backend = ["subprocess", "z3-native"]` (default: subprocess)
5. Test equivalence: run all v0.1.0 tests with both backends

**Success criteria:** 100% test pass rate with z3-native backend.

### Phase 2: Extend Parser for Loop Invariants (Week 3-4)

1. Add syn custom parser for `#[invariant(expr)]`
2. Store invariants in function metadata (HIR map)
3. Implement WP for loops with invariants (3 VCs)
4. Add integration tests: loops with invariants

**Success criteria:** Verify simple loop (sum, product, search).

### Phase 3: Add Datatypes for Aggregates (Week 5-6)

1. Use rustc_abi to extract struct layouts
2. Generate SMT datatypes via z3 crate (required: z3-native backend)
3. Encode struct field access in VC generation
4. Add tests: struct creation, field read/write

**Success criteria:** Verify function with struct parameter/return.

### Phase 4: Prophecy Variables for Mutable Borrows (Week 7-8)

1. Identify `&mut` parameters in function signatures
2. Generate prophecy variables (old, new pairs)
3. Thread prophecy constraints through VC generation
4. Add tests: functions with `&mut` parameters

**Success criteria:** Verify `increment(&mut x)` style functions.

### Phase 5: Function Summaries for Inter-Procedural (Week 9-10)

1. Extract contracts from called functions
2. Generate UF declarations in SMT
3. Replace call sites with assume(pre); havoc; assume(post)
4. Add tests: caller/callee with contracts

**Success criteria:** Verify function calling verified function.

## Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| Nightly API breakage | HIGH | HIGH | Pin nightly, quarterly updates with tests, CI checks |
| Z3 bundled linking issues | MEDIUM | MEDIUM | Keep subprocess backend as fallback, test on Linux/macOS/Windows |
| Prophecy encoding unsound | LOW | CRITICAL | Literature review (Creusot paper), formal soundness proof (defer to academia), extensive testing |
| Performance (SMT solver timeouts) | MEDIUM | MEDIUM | Incremental solving, push/pop, quantifier-free when possible, timeout limits |
| Datatype encoding complexity | MEDIUM | MEDIUM | Start with simple structs (no generics), add complexity incrementally, study Verus/Creusot encodings |

## Sources

### SMT Solvers and Theories
- [Z3 Rust Bindings (prove-rs/z3.rs)](https://github.com/prove-rs/z3.rs) — Latest: v0.19.7, Dec 2025. HIGH confidence.
- [z3 crate documentation](https://docs.rs/z3/) — Official API docs.
- [SMT-LIB 2.7 Standard](https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-02-05.pdf) — February 2025 release, algebraic datatypes. HIGH confidence.
- [SMT-LIB 2.6 Datatypes](https://smt-lib.org/papers/smt-lib-reference-v2.6-r2024-09-20.pdf) — September 2024, declare-datatypes. HIGH confidence.
- [Z3 Guide: Datatypes](https://microsoft.github.io/z3guide/docs/theories/Datatypes/) — Official Z3 documentation.

### Rust Verification Tools
- [Rust Formal Methods Interest Group](https://rust-formal-methods.github.io/) — Current ecosystem overview. HIGH confidence.
- [Verus: Verifying Rust Programs using Linear Ghost Types](https://dl.acm.org/doi/10.1145/3586037) — OOPSLA 2023, linear ghost types. HIGH confidence.
- [Creusot 0.9.0 Release](https://creusot-rs.github.io/devlog/2026-01-19/) — January 2026, prophecy-based verification. HIGH confidence.
- [Creusot POPL 2026 Tutorial](https://popl26.sigplan.org/details/POPL-2026-tutorials/6/Creusot-Formal-verification-of-Rust-programs) — January 2026, loop invariants. HIGH confidence.
- [Kani Rust Verifier](https://github.com/model-checking/kani) — AWS bounded model checker. MEDIUM confidence (different approach).
- [RustBelt: Securing the Foundations of Rust](https://dl.acm.org/doi/pdf/10.1145/3158154) — POPL 2018, separation logic foundations. HIGH confidence.

### Compiler Integration
- [Rust Compiler Development Guide: MIR](https://rustc-dev-guide.rust-lang.org/mir/index.html) — Official guide. HIGH confidence.
- [Stable MIR Project](https://github.com/rust-lang/project-stable-mir) — Future API, not ready. MEDIUM confidence.
- [rustc_middle API Docs](https://doc.rust-lang.org/stable/nightly-rustc/rustc_middle/index.html) — Official API reference. HIGH confidence.
- [rustc_plugin Framework](https://github.com/cognitive-engineering-lab/rustc_plugin) — Abstraction over rustc APIs. MEDIUM confidence (avoid for now).

### Verification Foundations
- [Weakest Precondition (Software Foundations)](https://softwarefoundations.cis.upenn.edu/slf-current/WPsem.html) — Formal semantics. HIGH confidence.
- [Why3 Verification Platform](https://www.why3.org/) — Intermediate verification language. HIGH confidence.
- [Separation Logic (Wikipedia)](https://en.wikipedia.org/wiki/Separation_logic) — Foundational concepts. MEDIUM confidence (general reference).

### Parsing and Macros
- [Syn Crate (GitHub)](https://github.com/dtolnay/syn) — Official repository. HIGH confidence.
- [Syn Documentation](https://lib.rs/crates/syn) — Lib.rs page with usage. HIGH confidence.
- [Rust Proc Macros: A Beginner's Journey](https://petanode.com/posts/rust-proc-macro/) — Tutorial. MEDIUM confidence (educational content).

### Testing and Development
- [Rust SMT Libraries (crates.io)](https://crates.io/keywords/smt) — Ecosystem overview. MEDIUM confidence.
- [smtlib Crate](https://lib.rs/crates/smtlib) — Alternative SMT-LIB library. MEDIUM confidence.
- [rsmt2 Crate](https://docs.rs/rsmt2) — Process-based SMT solver interaction. MEDIUM confidence.

### Inter-Procedural Verification
- [Modular Verification Research (VMCAI 2026)](https://conf.researchr.org/home/VMCAI-2026) — Conference proceedings. MEDIUM confidence.
- [Soft Contract Verification](https://dl.acm.org/doi/10.1145/3158139) — POPL 2018, higher-order contracts. MEDIUM confidence.

### Confidence Assessment

**HIGH Confidence Sources:**
- Official documentation (Rust compiler guide, Z3 guide, SMT-LIB standard)
- Published academic papers (POPL, OOPSLA)
- Official tool repositories (Verus, Creusot, z3.rs)

**MEDIUM Confidence Sources:**
- Community tutorials and guides
- Conference proceedings (not yet peer-reviewed papers)
- Alternative tools (not directly applicable but informative)

**LOW Confidence Areas:**
- Specific nightly API changes in 2026 (no official changelog found, relying on general instability knowledge)
- Prophecy variable soundness (proven by Creusot team, but not independently verified for our encoding)
- Performance characteristics (need empirical testing)

**Gaps Requiring Phase-Specific Research:**
- Exact prophecy encoding details (read Creusot source code during implementation)
- Datatype encoding for Rust generics (study Verus implementation)
- Performance optimization strategies (benchmark after basic implementation)

---

*Stack research for: rust-fv formal verification tool*
*Researched: 2026-02-10*
*Primary sources: Official Rust docs, Z3 docs, SMT-LIB standard, Verus/Creusot papers*
