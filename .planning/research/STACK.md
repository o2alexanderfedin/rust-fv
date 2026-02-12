# Technology Stack Additions for Advanced Verification Features

**Project:** rust-fv (Formal Verification for Rust)
**Milestone:** Advanced Verification Features (Recursive Functions, Closures, Traits, Unsafe, Lifetimes, Floating-Point, Concurrency)
**Researched:** 2026-02-11
**Context:** Stack additions for SUBSEQUENT milestone building on existing validated capabilities

## Executive Summary

This stack research focuses ONLY on what's needed for the new advanced features: recursive functions, closures, trait objects, unsafe code verification, lifetime reasoning, floating-point arithmetic, and concurrency verification. The existing foundation (Z3 with QF_BV/QF_UFBVDT, syn 2.0, subprocess+native API, 5-crate workspace) remains unchanged and is NOT re-researched per milestone context.

**Critical finding:** NO major new dependencies required beyond what's already in the codebase or was recommended in the base research. The advanced features are achievable through:

1. **Existing Z3 capabilities** (quantifiers, datatypes, floating-point theory, uninterpreted functions)
2. **Existing rustc APIs** (MIR closure/trait representations, borrow checker facts)
3. **One lightweight graph library** (petgraph 0.8.3 for call graph analysis)
4. **Optional polonius crate** (0.3.0 for lifetime facts if deeper borrow analysis needed)

The key insight is that these features are **encoding challenges**, not dependency challenges. The stack is stable; the work is in VCGen and SMT translation logic.

---

## Recommended Stack Additions

### Graph Analysis (Recursive Functions + Call Graph)
| Technology | Version | Purpose | Why |
|------------|---------|---------|-----|
| **petgraph** | 0.8.3 | Strongly connected component detection for recursion analysis | Tarjan's SCC algorithm (O(V+E)) to detect mutual recursion. Already used by rustc internally. Memory-efficient implementation. **Required for recursive function verification.** |

### Lifetime Analysis (Optional Enhancement)
| Technology | Version | Purpose | Why |
|------------|---------|---------|-----|
| **polonius** | 0.3.0 | Borrow checker facts (optional, for advanced lifetime reasoning) | Generates loan_killed_at, loan_invalidated_at, var_used_at facts. **Only if** rustc borrow checker output proves insufficient. May NOT be needed if basic ownership reasoning suffices. |

### NO New Core Dependencies Required

The following advanced features do NOT require new crate dependencies:

| Feature | Stack Needed | Already Have? |
|---------|--------------|---------------|
| **Recursive functions** | SMT quantifiers (forall), call graph analysis (SCC), termination metrics | YES: Z3 supports quantifiers via ALL logic; add petgraph for SCC |
| **Closures** | MIR closure representation (upvar capture modes), SMT datatypes for closure environments | YES: rustc_middle::mir has closure info; z3 crate supports datatypes |
| **Trait objects** | MIR vtable dispatch representation, SMT uninterpreted functions for dynamic dispatch | YES: rustc_middle::mir::TerminatorKind::Call; z3 supports UF theory |
| **Unsafe code** | Integration with Miri for runtime UB detection (complementary, not verifier responsibility) | NO: Verification of unsafe is out of scope; defer to Miri (state-of-art 2026) |
| **Lifetime reasoning** | Rustc borrow checker facts via rustc_borrowck, possibly polonius for advanced cases | MOSTLY: rustc APIs available; add polonius ONLY if needed |
| **Floating-point** | SMT-LIB FloatingPoint theory (IEEE 754), Z3's QF_FP/QF_FPBV logics | YES: Z3 4.13+ has native FP support; z3 crate exposes it |
| **Concurrency** | Happens-before partial order encoding, either symbolic execution of interleavings OR ownership-based data race freedom proofs | YES: Can encode with existing SMT; concurrency is HIGH complexity, Phase 6+ |

---

## Technology Specifications

### petgraph 0.8.3 (Graph Analysis)

**Installation:**
```toml
# In crates/analysis/Cargo.toml
[dependencies]
petgraph = "0.8.3"
```

**What it provides:**
- `petgraph::algo::tarjan_scc`: Tarjan's strongly connected components in O(V+E) time
- `petgraph::Graph`: Directed graph for call graphs
- `petgraph::algo::toposort`: Topological sort for non-recursive call ordering

**Why this version:**
- Latest stable (released Feb 2026)
- Rust 1.64+ compatible (rust-fv requires 1.85+)
- Used by rustc itself (`rustc_data_structures::graph::scc`)

**Use cases:**
1. **Recursive function detection:** Build call graph from MIR, run `tarjan_scc`, identify cycles
2. **Mutual recursion groups:** SCCs with >1 function require shared termination metrics
3. **Verification order:** Topological sort of non-recursive functions for bottom-up verification

**Confidence:** HIGH (standard graph algorithms, widely used in Rust ecosystem)

**Source:** [petgraph 0.8.3 on crates.io](https://crates.io/crates/petgraph), [tarjan_scc documentation](https://docs.rs/petgraph/latest/petgraph/algo/fn.tarjan_scc.html)

---

### polonius 0.3.0 (Optional Lifetime Facts)

**Installation:**
```toml
# In crates/driver/Cargo.toml (nightly-only crate)
[dependencies]
polonius = { version = "0.3", optional = true }

[features]
advanced-lifetimes = ["polonius"]
```

**What it provides:**
- `PoloniusFacts`: Datalog-style borrow checker facts
- `loan_killed_at(loan, point)`: When a borrow is invalidated
- `loan_invalidated_at(point, loan)`: Conflicting actions at program points
- `var_used_at(var, point)`: Variable usage tracking

**Why this version:**
- Latest stable (polonius is evolving toward rustc integration)
- Designed for external tooling consumption

**When to use:**
- **Use polonius if:** Need to prove properties about borrow lifetimes (e.g., "this borrow never escapes this scope")
- **Skip polonius if:** Basic ownership reasoning (moved values, immutable borrows) from rustc borrow checker output suffices

**Current recommendation:** START without polonius. Add only if Phase 3 ownership reasoning proves insufficient.

**Confidence:** MEDIUM (polonius is experimental, but facts generation is stable via `rustc -Znll-facts`)

**Source:** [polonius 0.3.0 on crates.io](https://docs.rs/crate/polonius/latest), [Polonius GitHub](https://github.com/rust-lang/polonius)

---

### Z3 Floating-Point Theory (No New Dependency)

**Already available via z3 crate 0.19:**
- `QF_FP` logic (quantifier-free floating-point)
- `QF_FPBV` logic (floating-point + bitvectors)
- IEEE 754 operations: add, sub, mul, div, sqrt, fma
- Rounding modes: RNE, RNA, RTP, RTN, RTZ
- Special values: +inf, -inf, NaN, +zero, -zero

**SMT-LIB syntax:**
```smt2
(declare-const x (_ FloatingPoint 11 53))  ; IEEE 754 double precision
(assert (fp.gt x (fp.roundToIntegral RNE x)))  ; x > round(x)
```

**Rust z3 crate API:**
```rust
use z3::ast::Float;
let ctx = z3::Context::new(&z3::Config::new());
let x = Float::new_const(&ctx, "x", 11, 53);  // double precision
```

**Encoding strategy:**
1. Rust `f32` -> SMT `(_ FloatingPoint 8 24)` (IEEE 754 single)
2. Rust `f64` -> SMT `(_ FloatingPoint 11 53)` (IEEE 754 double)
3. Bit-blast to bitvectors for mixed arithmetic (Z3 handles this internally)

**Performance note:** FP theory is slower than bitvectors. Z3 reduces FP to BV internally, adding overhead.

**Confidence:** HIGH (Z3's FP support is mature, used in production verifiers)

**Source:** [SMT-LIB FloatingPoint Theory](https://smt-lib.org/theories-FloatingPoint.shtml), [Z3 Guide: Floating-Point](https://microsoft.github.io/z3guide/docs/theories/Bitvectors/), [IEEE 754 Formal Model (Feb 2026)](https://devel.isa-afp.org/browser_info/current/AFP/IEEE_Floating_Point/document.pdf)

---

### Existing Dependencies: What's Already Sufficient

#### rustc_middle::mir (Closures & Trait Objects)

**Closure representation in MIR:**
- `TerminatorKind::Call` with `func: Operand` where operand is closure type
- Closure upvar capture modes: `ByValue`, `ByRef(BorrowKind)`, `ByMutRef`
- `UpvarDecl` tracks captured variables and their capture kinds

**Encoding strategy:**
1. Extract closure environment as struct: `struct Closure_env { field1: T1, field2: &T2 }`
2. Encode as SMT datatype (same as structs)
3. Closure call -> function call with explicit environment parameter

**Trait object representation in MIR:**
- `TerminatorKind::Call` with `func: Operand` of type `dyn Trait`
- Vtable dispatch via `Rvalue::Ref` to trait object
- `ProjectionElem::Downcast` for pattern matching on trait objects

**Encoding strategy (conservative):**
1. Encode vtable dispatch as SMT uninterpreted function: `(declare-fun vtable_call (TraitObject Method) ReturnType)`
2. Soundness: Over-approximate (any implementation could be called)
3. Precision improvement (Phase 6+): Encode all possible implementations if finite

**Confidence:** HIGH (MIR representation is stable for closures/traits; encoding is standard)

**Source:** [Rust Compiler Dev Guide: Closures](https://rustc-dev-guide.rust-lang.org/closure.html), [MIR Terminator Documentation](https://doc.rust-lang.org/beta/nightly-rustc/rustc_middle/mir/terminator/struct.Terminator.html)

#### Z3 Quantifiers (Recursive Functions)

**Already supported via z3 crate:**
- `(declare-fun f (Int) Int)` for function signature
- `(assert (forall ((x Int)) (=> (> x 0) (< (f x) (f (+ x 1))))))` for properties
- Quantifier instantiation via E-matching (pattern-based triggers)

**Recursive function encoding strategy:**
1. **Uninterpreted function approach:** `(declare-fun fib (Int) Int)` + axioms for base/recursive cases
2. **Termination obligation:** Separate VC proving termination metric decreases
3. **Induction:** Manual inductive proofs via loop invariants over recursion depth

**Limitations:**
- Z3 does NOT do automatic induction (per research: "important limitation")
- User must provide termination metrics (`decreases` clause, Dafny/Verus-style)
- Mutual recursion: requires well-founded lexicographic ordering

**Confidence:** MEDIUM-HIGH (quantifiers work but require careful trigger design; performance can be poor)

**Source:** [Z3 Guide: Datatypes (recursive types)](https://microsoft.github.io/z3guide/docs/theories/Datatypes/), [SMT quantifiers research](https://fstar-lang.org/tutorial/book/under_the_hood/uth_smt.html)

---

## Integration Points

### 1. Recursive Functions

**MIR extraction (driver crate):**
- Walk `rustc_middle::mir::Body::basic_blocks()` to extract `TerminatorKind::Call`
- Build call graph: nodes = functions, edges = caller -> callee
- Use `petgraph::algo::tarjan_scc` to detect recursion cycles

**VCGen (analysis crate):**
- Non-recursive functions: inline or use function summaries (Phase 3 approach)
- Recursive functions:
  1. Require `#[decreases(metric)]` annotation (user-supplied termination metric)
  2. Generate termination VC: `metric(args_recursive_call) < metric(args_current_call)`
  3. Encode function as uninterpreted function + axioms for base/recursive cases

**SMT encoding (smtlib crate):**
- `Command::DeclareFun(name, arg_sorts, return_sort)` for uninterpreted function
- `Command::Assert(Term::Forall(...))` for axioms encoding function body
- Separate VC for termination metric

**Pitfall:** Quantifier performance. Mitigation: Require explicit triggers in `#[decreases]` if SMT times out.

---

### 2. Closures

**MIR extraction (driver crate):**
- Extract closure type from `ty::TyKind::Closure(def_id, substs)`
- Extract upvar capture info from `rustc_middle::ty::ClosureSubsts`
- Map each upvar to its capture mode (`ByValue`, `ByRef`, `ByMutRef`)

**VCGen (analysis crate):**
- Model closure environment as struct: `{ captured_var1, captured_var2, ... }`
- Closure call -> function call with environment as first parameter
- Borrow rules for captured `&mut` variables follow Phase 4 prophecy model

**SMT encoding (smtlib crate):**
- Use existing SMT datatype encoding (same as structs)
- Selector functions for captured variables
- No new SMT features required

**Pitfall:** Nested closures (closure capturing another closure). Mitigation: Flatten environment transitively.

---

### 3. Trait Objects (Dynamic Dispatch)

**MIR extraction (driver crate):**
- Detect `ty::TyKind::Dynamic(trait_ref, _)` for trait objects
- Extract vtable dispatch from `Rvalue::Ref` to trait object
- Track possible implementations via trait solver queries (if finite, e.g., sealed traits)

**VCGen (analysis crate):**
- **Conservative encoding (initial):** Havoc return value (any implementation could run)
- **Precise encoding (Phase 6+):** Enumerate all implementations, generate VC for each, verify all paths

**SMT encoding (smtlib crate):**
- `(declare-fun dyn_call (TraitObject) ReturnType)` uninterpreted function
- No axioms (conservative: no assumptions about implementation)

**Pitfall:** Imprecision leads to false negatives (cannot verify properties requiring specific implementation). Mitigation: Documentation + sealed trait support.

---

### 4. Unsafe Code Verification

**Recommendation:** OUT OF SCOPE for deductive verification. Delegate to Miri.

**Rationale:**
- Miri (POPL 2026) is state-of-the-art for undefined behavior detection in unsafe Rust
- Miri detects: out-of-bounds access, use-after-free, alignment violations, data races
- Deductive verification of unsafe code requires low-level memory models (separation logic, RustBelt), which is research-level complexity

**Integration strategy (complementary tools):**
- rust-fv verifies safe Rust (functional correctness)
- Miri verifies unsafe Rust (UB freedom)
- `cargo verify` runs both: `cargo verify` (rust-fv) + `cargo miri test` (Miri)

**Confidence:** HIGH (Miri is the right tool; reinventing it is not worthwhile)

**Source:** [Miri: Practical UB Detection (POPL 2026)](https://research.ralfj.de/papers/2026-popl-miri.pdf), [Kani verifier approach](https://github.com/model-checking/kani) (bounded model checking for unsafe)

---

### 5. Lifetime Reasoning

**MIR borrow checker facts (driver crate):**
- Access via `rustc -Znll-facts` flag (generates Polonius facts in text format)
- Parse facts to extract: `borrow_region(loan, region)`, `outlives(region1, region2)`

**VCGen (analysis crate):**
- **Basic ownership:** Track moved values (value cannot be used after move), immutable borrows (value is read-only during borrow)
- **Advanced lifetimes (if polonius added):** Encode region outlives constraints as SMT implications

**SMT encoding (smtlib crate):**
- Model regions as fresh constants: `(declare-const r1 Region)`
- Outlives: `(assert (outlives r1 r2))` as uninterpreted relation
- Borrow validity: `(assert (=> (borrow_active loan) (region_alive region)))`

**Decision point:** START without polonius. Add ONLY if Phase 3 basic ownership reasoning cannot express needed properties.

**Confidence:** MEDIUM (basic ownership is well-understood; advanced lifetime reasoning is complex)

**Source:** [Polonius GitHub](https://github.com/rust-lang/polonius), [Polonius Facts Documentation](https://rust-lang.github.io/polonius/generate_inputs.html)

---

### 6. Floating-Point Arithmetic

**MIR extraction (driver crate):**
- Detect `ty::TyKind::Float(FloatTy::F32 | FloatTy::F64)`
- Extract float ops from `Rvalue::BinaryOp(BinOp::Add | Sub | Mul | Div, ...)`

**VCGen (analysis crate):**
- Map Rust float ops to SMT-LIB FP ops: `+` -> `fp.add RNE`, `*` -> `fp.mul RNE`
- Rounding mode: Default to RNE (round-to-nearest, ties-to-even) per IEEE 754
- Special value handling: NaN propagation, infinity, signed zero

**SMT encoding (smtlib crate):**
```rust
// In smtlib/src/sort.rs
pub enum Sort {
    // ... existing variants
    FloatingPoint { exponent: u32, significand: u32 },  // ((_ FloatingPoint e s))
}

// In smtlib/src/term.rs
pub enum Term {
    // ... existing variants
    FpLiteral(f64),  // Converts to (fp #b0 #b01111111111 #x0000000000000) format
    FpOp(FpOp, Vec<Term>),  // fp.add, fp.mul, etc.
}
```

**z3 crate API:**
```rust
use z3::ast::Float;
let x = Float::new_const(&ctx, "x", 11, 53);
let y = Float::new_const(&ctx, "y", 11, 53);
let sum = Float::add(&ctx, &[&x, &y], z3::ast::RoundingMode::RoundNearestTiesToEven);
```

**Performance:** FP theory is SLOWER than bitvectors (Z3 internally reduces FP to BV). Expect 2-10x slower solving.

**Confidence:** HIGH (IEEE 754 support in Z3 is mature, SMT-LIB 2.6 standard)

**Source:** [SMT-LIB FloatingPoint Theory](https://smt-lib.org/theories-FloatingPoint.shtml), [IEEE 754 formalization](https://devel.isa-afp.org/browser_info/current/AFP/IEEE_Floating_Point/document.pdf)

---

### 7. Concurrency Verification

**Complexity assessment:** VERY HIGH. Recommend Phase 6+ (post-v1.0).

**Two approaches:**

#### Approach A: Symbolic Execution of Interleavings (ESBMC-style)
- Enumerate all thread interleavings up to context bound
- Generate separate VC for each interleaving
- Check data races, deadlocks, assertion violations per interleaving
- **Tooling:** No new dependencies (encode interleavings as branching in VCGen)
- **Limitation:** Combinatorial explosion (K threads, N steps -> O(N^K) interleavings)

#### Approach B: Ownership-Based Data Race Freedom (Creusot 0.9.0 / VerusSync-style)
- Leverage Rust's Send/Sync traits for data race freedom by construction
- Encode happens-before relation as partial order in SMT
- Verify atomics via sequential consistency axioms
- **Tooling:** Requires encoding of Rust's memory model (RustBelt-style)
- **Limitation:** Only proves data race freedom, not full functional correctness

**Recommendation:** Approach B (ownership-based) aligns better with rust-fv's philosophy. But defer to Phase 6 due to complexity.

**What to add (when Phase 6):**
- Partial order encoding for happens-before: `(declare-fun hb (Event Event) Bool)`
- Axioms for partial order: reflexive, transitive, antisymmetric
- Atomics encoding: `Ordering::SeqCst` -> total order, `Ordering::Relaxed` -> no constraints

**Confidence:** LOW for near-term (needs significant research), MEDIUM for long-term (proven approaches exist)

**Source:** [ESBMC concurrency verification](https://github.com/esbmc/esbmc), [VerusSync (Creusot 0.9.0 devlog)](https://creusot-rs.github.io/devlog/2026-01-19/), [Asterinas formal verification approach](https://asterinas.github.io/2025/02/13/towards-practical-formal-verification-for-a-general-purpose-os-in-rust.html)

---

## Alternatives Considered

| Category | Recommended | Alternative | Why Not Alternative |
|----------|-------------|-------------|---------------------|
| **Call graph analysis** | petgraph 0.8.3 | rustc_data_structures::graph::scc | Nightly-only API; couples analysis crate to rustc; petgraph is stable Rust |
| **Recursive function encoding** | Z3 quantifiers + termination metrics | Bounded unrolling (Kani-style) | Loses completeness; cannot prove unbounded recursion correct; users expect full verification |
| **Closure encoding** | SMT datatypes for environment | Defunctionalization (convert to function pointers) | More complex; loses type precision; datatype approach mirrors MIR structure |
| **Trait object encoding** | Uninterpreted functions (conservative) | Enumerate all impls + verify each | Requires whole-program analysis; doesn't scale; phase 6+ feature |
| **Unsafe verification** | Defer to Miri (complementary tool) | Build separation logic verifier | Years of research effort; Miri already state-of-art; not differentiating for rust-fv |
| **Lifetime facts** | rustc borrow checker output | polonius crate | Start with simpler rustc output; add polonius ONLY if insufficient |
| **Floating-point** | Z3 native FP theory | Bit-blast to custom BV encoding | Reinventing Z3's internals; FP theory is standard; no benefit |
| **Concurrency** | Ownership-based (Phase 6+) | Interleaving enumeration (ESBMC) | Combinatorial explosion; doesn't leverage Rust's ownership; ownership aligns with rust-fv philosophy |

---

## Installation Summary

### Immediate Additions (for recursive functions + closures + traits + FP)

```toml
# crates/analysis/Cargo.toml
[dependencies]
# ... existing dependencies
petgraph = "0.8.3"  # Call graph analysis for recursion detection
```

### Optional (only if needed during implementation)

```toml
# crates/driver/Cargo.toml (nightly-only crate)
[dependencies]
# ... existing dependencies
polonius = { version = "0.3", optional = true }  # Advanced lifetime facts

[features]
advanced-lifetimes = ["polonius"]
```

### Already Available (no installation needed)

- **Z3 floating-point theory:** via z3 crate 0.19+ (already in workspace dependencies)
- **Z3 quantifiers:** via `ALL` logic (already used for current quantifiers)
- **SMT datatypes:** via `QF_UFBVDT` (already used for structs/enums)
- **Uninterpreted functions:** via `UF` theory (already available in Z3)
- **rustc MIR APIs:** via rustc_middle (already accessed in driver crate)

---

## Integration Testing Strategy

### New Test Categories Needed

1. **Recursive functions:**
   - Simple recursion (factorial, fibonacci)
   - Mutual recursion (even/odd check)
   - Termination metric tests (decreases clause violations should fail)

2. **Closures:**
   - Closure capturing immutable references
   - Closure capturing mutable references (requires Phase 4 prophecy variables)
   - Nested closures

3. **Trait objects:**
   - Sealed trait with finite implementations (precise verification)
   - Open trait (conservative havoc-based verification)

4. **Floating-point:**
   - Basic arithmetic (addition, multiplication)
   - Special values (NaN, infinity)
   - Rounding mode tests (verify FP is NOT exact like integers)

5. **Lifetimes:**
   - Basic ownership (moved values)
   - Immutable borrows (multiple concurrent readers)
   - Mutable borrows (exclusive access - Phase 4)

### Testing Tools (already in codebase or planned)

- `compiletest_rs`: UI tests for error messages
- `proptest`: Property-based testing of encodings
- `criterion`: Performance benchmarks for SMT encoding

---

## Performance Considerations

### Expected Performance Impact

| Feature | Expected Overhead | Mitigation |
|---------|------------------|------------|
| **Recursive functions** | 2-5x slower (quantifiers) | Explicit triggers in `#[decreases]`; bounded unrolling fallback |
| **Closures** | <10% overhead (struct encoding) | None needed; closures are lightweight |
| **Trait objects** | Minimal (havoc is fast) | Conservative encoding is cheap; precise encoding expensive (Phase 6+) |
| **Floating-point** | 2-10x slower (FP->BV reduction) | Warn users; offer bitvector fallback for bitwise-exact FP |
| **Lifetimes** | <5% overhead (extra facts) | None needed; mostly analysis-time cost |
| **Concurrency** | 10-100x slower (interleaving explosion) | Phase 6+ only; ownership-based approach avoids worst case |

### Benchmarking Plan

- Add `recursive_bench.rs` in `crates/analysis/benches/`
- Measure VC generation time vs. baseline (non-recursive functions)
- Measure SMT solving time with/without quantifiers
- Track performance regression in CI

---

## Sources

### High Confidence (Official Documentation & Recent Research)

- [petgraph 0.8.3 on crates.io](https://crates.io/crates/petgraph) - Graph analysis library, latest version
- [tarjan_scc API documentation](https://docs.rs/petgraph/latest/petgraph/algo/fn.tarjan_scc.html) - SCC algorithm for recursion detection
- [polonius 0.3.0 on crates.io](https://docs.rs/crate/polonius/latest) - Borrow checker facts
- [SMT-LIB FloatingPoint Theory](https://smt-lib.org/theories-FloatingPoint.shtml) - IEEE 754 formalization
- [IEEE 754 Formal Model (Feb 2026)](https://devel.isa-afp.org/browser_info/current/AFP/IEEE_Floating_Point/document.pdf) - Recent formalization
- [Rust Compiler Dev Guide: MIR](https://rustc-dev-guide.rust-lang.org/mir/index.html) - MIR structure for closures/calls
- [Rust Compiler Dev Guide: Closures](https://rustc-dev-guide.rust-lang.org/closure.html) - Closure capture inference
- [MIR Terminator Documentation](https://doc.rust-lang.org/beta/nightly-rustc/rustc_middle/mir/terminator/struct.Terminator.html) - Call representation
- [Z3 Guide: Datatypes](https://microsoft.github.io/z3guide/docs/theories/Datatypes/) - Recursive datatypes limitations
- [Z3 Rust Bindings](https://github.com/prove-rs/z3.rs) - z3 crate 0.19 API

### Medium Confidence (Research Papers & Tool Documentation)

- [Miri: Practical UB Detection (POPL 2026)](https://research.ralfj.de/papers/2026-popl-miri.pdf) - Unsafe code verification state-of-art
- [ESBMC Concurrency Verification](https://github.com/esbmc/esbmc) - Interleaving-based approach
- [Creusot 0.9.0 Devlog (Jan 2026)](https://creusot-rs.github.io/devlog/2026-01-19/) - VerusSync concurrency verification
- [Asterinas Formal Verification (Feb 2026)](https://asterinas.github.io/2025/02/13/towards-practical-formal-verification-for-a-general-purpose-os-in-rust.html) - Ownership-based concurrency proofs
- [SMT Quantifiers Tutorial](https://fstar-lang.org/tutorial/book/under_the_hood/uth_smt.html) - F* use of Z3 quantifiers
- [Polonius GitHub](https://github.com/rust-lang/polonius) - Borrow checker implementation
- [VCGen for Recursive Programs](https://www.why3.org/doc/vcgen.html) - Why3's approach to recursion

### Low Confidence (Needs Validation During Implementation)

- Exact trigger patterns for recursive function quantifiers (must experiment with Z3)
- Polonius necessity for rust-fv's use cases (may not be needed; try without first)
- Concurrency encoding performance (highly variable based on program structure)

---

**Research confidence:** MEDIUM-HIGH

**Rationale:** Stack additions are minimal and well-understood (petgraph is standard, Z3 theories are documented, polonius is optional). The complexity is in ENCODING (VCGen + SMT translation), not in dependencies. Concurrency is LOW confidence due to inherent complexity, correctly deferred to Phase 6+.

**Ready for roadmap planning:** YES

---

*Research completed: 2026-02-11*
*Researcher: GSD Project Researcher (Phase 6: Stack Research)*
