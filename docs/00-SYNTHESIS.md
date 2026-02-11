# Formal Verification for Rust: Implementation Synthesis and Roadmap

## Executive Summary

Based on comprehensive analysis of state-of-the-art formal verification research, this document presents a pragmatic, phased approach for building a Rust formal verification tool. The recommended approach combines:

1. **SMT-based verification** for automation (following Verus's success model)
2. **Procedural macro annotations** for stable, Rust-native specification syntax
3. **MIR-level analysis** for semantic verification condition generation
4. **Prophecy-based reasoning** for handling mutable borrows
5. **80%+ automation target** for common patterns, with graceful fallback to manual proofs

This strategy balances three critical constraints:
- **Usability**: Rust developers need minimal learning curve
- **Capability**: Must handle real-world ownership, lifetimes, and borrowing patterns
- **Maintainability**: Stable API, predictable toolchain integration, manageable proof burden

The phased implementation plan focuses on delivering value incrementally: starting with function contracts and safe code, then expanding to unsafe code, concurrency, and advanced automation.

---

## 1. Recommended Architecture

### 1.1 Verification Approach: SMT-Based with Interactive Fallback

**Primary Strategy: SMT-Based Automated Verification**

Research shows Verus achieved the best balance of automation and industrial adoption, with two of three OSDI 2024 best papers using it. Key advantages:

- 80-90% automation for standard verification conditions
- Fast feedback cycles (crucial for developer adoption)
- Proven scalability (Microsoft, Amazon production use)
- Strong theoretical foundations while remaining practical

**Comparison with Alternatives:**

| Approach | Automation | Expressiveness | Proof Burden | Best For |
|----------|-----------|----------------|--------------|----------|
| **SMT-based (Verus)** | High (80-90%) | Medium-High | Low-Medium | Production systems |
| Model checking (Kani) | Very High (90%+) | Medium | Very Low | Bug finding, unsafe code |
| Proof assistants (Coq/Isabelle) | Low (30-40%) | Highest | Very High | Safety-critical systems |
| Deductive (Creusot/Prusti) | Medium (60-70%) | High | Medium-High | Research, exploration |

**Decision:** SMT-based verification with Z3/CVC5 backend, supplemented by optional interactive proving for complex invariants.

**Rationale:**
- Research shows 80-90% automation achievable for safe Rust
- Rust's type system already eliminates memory safety issues, reducing verification burden
- SMT solvers mature and actively maintained (Z3 won SMT-COMP 2024)
- Verus demonstrates production viability

**Fallback Strategy:**
- For the 10-20% of cases where SMT automation fails, support manual proof hints
- Future integration with Lean/Coq for highest-assurance scenarios
- Clear error messages guiding users to manual intervention points

---

### 1.2 Compiler Integration Strategy

**Multi-Layer Integration Architecture**

Based on analysis of existing tools (Prusti, Creusot, MIRAI), the recommended approach combines three integration layers:

#### Layer 1: User Interface - Procedural Macros

**Technology:** Attribute-based procedural macros

**Advantages:**
- Stable API (works on stable Rust, no nightly pinning)
- Familiar Rust syntax (`#[requires]`, `#[ensures]`)
- Low maintenance burden
- Zero runtime overhead
- Non-invasive (code remains valid Rust without verification)

**Implementation:**
```rust
#[requires(x > 0)]
#[ensures(result >= x)]
fn increment(x: i32) -> i32 {
    x + 1
}
```

**Decision Justification:**
- All successful verification tools (Verus, Prusti, Creusot) use procedural macros
- Stable API critical for long-term maintainability
- Rust community familiar with attribute syntax

#### Layer 2: Analysis - MIR via rustc_plugin Framework

**Technology:** MIR (Mid-level IR) analysis using rustc_plugin framework

**Advantages:**
- Access to full type information and borrow checking results
- Simplified representation compared to AST/HIR
- Proven approach (used by Flowistry, Aquascope, Paralegal)
- Structured abstraction over raw rustc_driver complexity
- Handles toolchain setup and marshalling automatically

**Trade-offs:**
- Requires nightly Rust with version pinning
- Unstable compiler API (requires periodic updates)
- Worth it for semantic analysis capabilities

**Alternative Considered:** Full custom rustc_driver
- **Rejected:** Too complex, high maintenance burden
- **When to Reconsider:** If needing custom query providers or compilation phase modifications

**Decision Justification:**
- MIR is the right level for verification condition generation
- Semantic information essential for handling lifetimes and ownership
- rustc_plugin framework reduces complexity vs. raw driver
- Research tools demonstrate feasibility

#### Layer 3: Verification Backend - Cargo Build Scripts

**Technology:** Cargo build scripts (build.rs) invoking SMT solvers

**Advantages:**
- Works with stable Rust
- Standard Cargo integration pattern
- Easy CI/CD integration
- Flexibility to invoke external tools (Z3, CVC5)
- Can generate verification reports and artifacts

**Implementation Pattern:**
```rust
// build.rs
fn main() {
    // Extract verification conditions from MIR analysis
    // Invoke Z3/CVC5 to check VCs
    // Generate verification reports
    // Fail build if verification fails
}
```

**Decision Justification:**
- Separates verification logic from compiler internals
- Allows flexible SMT solver integration
- Standard pattern familiar to Rust developers
- Enables gradual adoption (opt-in verification)

---

### 1.3 Specification Language Design

**Syntax Philosophy:** Rust-native with minimal new concepts

Based on analysis of ACSL, JML, Dafny, and SPARK, the specification language should:

1. **Use Rust syntax as base** (like JML uses Java)
2. **Add minimal logical extensions** (quantifiers, logical operators)
3. **Leverage Rust's type system** (ownership implicit where possible)
4. **Support progressive precision** (partial specifications valid)

#### Core Specification Constructs

**Function Contracts:**
```rust
#[requires(precondition)]
#[ensures(postcondition)]
fn function_name(params) -> ReturnType { ... }
```

**Special Values:**
- `result` - return value in postconditions
- `old(expr)` - pre-state value
- `*x@` - logical model of current value (Creusot-style)
- `^x@` - prophesied final value of mutable borrow

**Logical Operators:**
- Standard: `&&`, `||`, `!`, `==`, `!=`, `<`, `<=`, `>`, `>=`
- Extended: `==>` (implication), `<==>` (iff)
- Quantifiers: `forall(|x: T| ...)`, `exists(|x: T| ...)`

**Type Invariants:**
```rust
#[invariant(self.len <= self.capacity)]
struct Vec<T> {
    ptr: *mut T,
    len: usize,
    capacity: usize,
}
```

**Loop Invariants:**
```rust
#[invariant(i <= arr.len())]
#[invariant(sum == total_of(arr, 0, i))]
while i < arr.len() { ... }
```

**Pure Functions:**
```rust
#[pure]
fn max(a: i32, b: i32) -> i32 {
    if a > b { a } else { b }
}
```

**Ghost Code:**
```rust
#[ghost]
fn abstract_value(&self) -> Seq<T> {
    // Specification-only, erased at runtime
}
```

#### Handling Rust-Specific Features

**Ownership Transfer:**
```rust
#[ensures(owns(result))]
fn new_box(x: i32) -> Box<i32> { Box::new(x) }
```

**Mutable Borrows (Prophecy-based):**
```rust
#[requires(*x@ < 100)]
#[ensures(*x@ == old(*x@))]  // Current unchanged during call
#[ensures(^x@ == *x@ + 1)]    // Final value after mutation
fn increment(x: &mut i32) { *x += 1; }
```

**Shared Borrows:**
```rust
#[requires(arr@.len() > 0)]
#[ensures(forall(|i| i < arr@.len() ==> result@ <= arr@[i]))]
fn find_min(arr: &[i32]) -> i32 { ... }
```

**Lifetimes:**
```rust
#[requires(valid(data, 'a))]
#[ensures(valid(result, 'a))]
fn get<'a, T>(data: &'a [T], index: usize) -> &'a T { ... }
```

**Decision Justification:**
- Prophecy variables (`^`) proven effective for mutable borrows (RustHornBelt, Creusot)
- Model operator (`@`) cleanly separates logical and concrete values
- Attribute syntax non-invasive and familiar
- Implicit ownership reasoning where Rust's type system suffices

---

### 1.4 Automation Level Targets

Based on research showing realistic automation expectations:

**Target Automation Rates:**

| Code Category | Automation Target | Manual Effort |
|--------------|------------------|---------------|
| Safe Rust, simple ownership | 85-95% | Loop invariants for complex algorithms |
| Safe Rust, complex borrowing | 60-80% | Lifetime relationships, nested borrows |
| Unsafe code | 40-60% | Pointer reasoning, memory invariants |
| Concurrent algorithms | 30-50% | Linearizability, coupling invariants |
| Standard library patterns | 90%+ | Pre-verified lemma libraries |

**Automation Strategy:**

1. **Conservative SMT Instantiation**
   - Fast, predictable verification times
   - Clear failures when automation insufficient
   - Prefer speed over aggressive heuristics

2. **Type-Guided VC Generation**
   - Leverage Rust's type system to reduce VCs
   - Trust borrow checker for memory safety
   - Focus verification on functional correctness

3. **Lemma Libraries**
   - Pre-verified lemmas for common patterns
   - Standard library specifications
   - Data structure invariant templates

4. **Clear Failure Feedback**
   - When automation fails, explain why
   - Suggest manual proof strategies
   - Show failed VC in user-friendly form

**Decision Justification:**
- Research shows 80-90% automation achievable with conservative approach
- Predictable behavior crucial for developer adoption
- Fast feedback more valuable than occasional complex proof success
- Manual fallback essential for production use

---

## 2. Phased Implementation Plan

### Phase 1: Foundation (Months 1-4)

**Goal:** Basic function contracts for safe Rust, working end-to-end pipeline

**Deliverables:**

1. **Specification Macro Crate** (Month 1)
   - Procedural macros for `#[requires]`, `#[ensures]`, `#[pure]`
   - Parse specification expressions into AST
   - Validate syntax and basic type checking
   - Generate verification metadata

2. **MIR Analysis Plugin** (Month 2)
   - rustc_plugin integration
   - Extract MIR for annotated functions
   - Basic type and ownership information extraction
   - Generate simple verification conditions

3. **SMT Backend Integration** (Month 3)
   - Z3 integration via Rust bindings
   - VC translation to SMT-LIB format
   - Result interpretation and error reporting
   - Basic counterexample generation

4. **End-to-End Examples** (Month 4)
   - Verify simple pure functions
   - Integer arithmetic properties
   - Array bounds checking
   - Option/Result type reasoning
   - Documentation and tutorials

**Success Criteria:**
- Can verify simple functions with pre/postconditions
- Clear error messages when verification fails
- Fast feedback (<1s for simple functions)
- Works on stable Rust (for macros) + pinned nightly (for MIR)

**Technical Risks:**
- MIR API instability (mitigate: pin specific nightly version)
- Z3 binding complexity (mitigate: use proven Rust Z3 crates)
- VC translation correctness (mitigate: extensive testing)

---

### Phase 2: Core Capabilities (Months 5-9)

**Goal:** Handle ownership, borrowing, lifetimes, and loop verification

**Deliverables:**

1. **Ownership Reasoning** (Month 5)
   - Track ownership transfer in specifications
   - Verify ownership discipline
   - Handle move semantics
   - Support `owns()` predicate

2. **Prophecy-Based Mutable Borrows** (Month 6-7)
   - Implement prophecy variable encoding
   - Support `*x@` (current) and `^x@` (final) operators
   - Verify mutable borrow specifications
   - Handle borrow resolution at lifetime end

3. **Loop Invariants** (Month 8)
   - `#[invariant]` macro for loops
   - VC generation for loop correctness
   - Induction proof obligations
   - Termination verification (optional)

4. **Type Invariants** (Month 9)
   - `#[invariant]` on struct definitions
   - Automatic checking at construction/modification
   - Integration with ownership system
   - Standard library type specifications

**Success Criteria:**
- Verify functions with mutable borrows
- Handle common ownership patterns automatically
- Support loop verification with manual invariants
- Verify data structures with type invariants

**Technical Risks:**
- Prophecy encoding complexity (mitigate: follow RustHornBelt/Creusot models)
- Lifetime inference limitations (mitigate: require explicit annotations initially)
- Loop invariant discovery (accept: manual specification required)

---

### Phase 3: Advanced Features (Months 10-15)

**Goal:** Unsafe code, ghost state, enhanced automation, tooling maturity

**Deliverables:**

1. **Unsafe Code Verification** (Month 10-11)
   - Pointer validity predicates
   - Memory layout specifications
   - FFI boundary specifications
   - Unsafe block pre/postconditions

2. **Ghost Code and Resources** (Month 12)
   - `#[ghost]` functions and variables
   - Ghost state for protocol reasoning
   - Separation logic predicates
   - Abstract data type models

3. **Automation Enhancements** (Month 13-14)
   - Automatic loop invariant inference (heuristic-based)
   - Lemma synthesis for common patterns
   - Improved SMT encoding strategies
   - Proof caching for incremental verification

4. **Tooling and Integration** (Month 15)
   - Cargo plugin (`cargo verify`)
   - IDE integration (LSP server)
   - CI/CD templates
   - Verification dashboard

**Success Criteria:**
- Verify realistic unsafe code with manual annotations
- Ghost state enables protocol verification
- Improved automation reduces manual effort by 10-20%
- Professional tooling experience

**Technical Risks:**
- Unsafe code verification inherently complex (accept: manual effort required)
- Automation improvements limited by fundamental decidability (accept: incremental gains)
- IDE integration complexity (mitigate: start with basic LSP support)

---

## 3. Risk Assessment and Mitigation

### 3.1 Technical Risks

**Risk 1: MIR API Instability**
- **Impact:** High - Breaking changes could require significant rework
- **Probability:** Medium - Rust compiler evolves rapidly
- **Mitigation:**
  - Pin to specific nightly version (document in rust-toolchain.toml)
  - Plan quarterly updates to track compiler changes
  - Abstract MIR access behind internal API layer
  - Monitor rustc development via Zulip and RFCs

**Risk 2: SMT Solver Limitations**
- **Impact:** Medium - May fail to verify valid code
- **Probability:** High - Known limitation of automated approaches
- **Mitigation:**
  - Target conservative automation (80% vs. 95%)
  - Provide clear manual proof fallback
  - Support multiple solvers (Z3 and CVC5)
  - Build lemma libraries for common patterns

**Risk 3: Prophecy Encoding Complexity**
- **Impact:** High - Core to handling mutable borrows
- **Probability:** Medium - Proven in research but implementation challenging
- **Mitigation:**
  - Follow established models (RustHornBelt, Creusot)
  - Extensive testing on borrow patterns
  - Start with restricted borrowing patterns, expand gradually
  - Consult with Creusot/RustHornBelt authors

**Risk 4: Proof Burden Too High**
- **Impact:** High - Users won't adopt if too much manual work
- **Probability:** Medium - Depends on automation quality
- **Mitigation:**
  - Target 80-90% automation for common patterns
  - Provide pre-verified standard library specifications
  - Build lemma libraries for data structures
  - Support partial verification (opt-in annotations)

**Risk 5: Compilation Performance**
- **Impact:** Medium - Slow verification blocks CI/CD adoption
- **Probability:** Medium - MIR analysis and SMT solving can be slow
- **Mitigation:**
  - Conservative SMT instantiation (fast vs. complete)
  - Proof caching and incremental verification
  - Parallel verification of independent functions
  - Make verification opt-in (not default build)

---

### 3.2 Adoption Risks

**Risk 6: Limited User Base**
- **Impact:** High - Without users, tool development unsustainable
- **Probability:** Medium - Formal verification still niche
- **Mitigation:**
  - Focus on critical-path verification (crypto, parsers, security)
  - Excellent documentation and tutorials
  - Showcase success stories (case studies)
  - Engage Rust community early (RFCs, blog posts, talks)

**Risk 7: Competition from Existing Tools**
- **Impact:** Medium - Verus, Kani already established
- **Probability:** High - Multiple tools already available
- **Mitigation:**
  - Differentiate on specific features (better UX, faster feedback)
  - Interoperability with existing tools
  - Focus on under-served use cases
  - Contribute to ecosystem (not just compete)

**Risk 8: Expertise Required**
- **Impact:** Medium - Users need verification knowledge
- **Probability:** High - Formal methods have steep learning curve
- **Mitigation:**
  - Progressive disclosure (simple contracts first)
  - Excellent error messages with suggestions
  - Interactive tutorials and workshops
  - Pre-verified examples and templates

---

### 3.3 Maintenance Risks

**Risk 9: Long-Term Maintenance Burden**
- **Impact:** High - Abandoned tool loses all value
- **Probability:** Medium - Single-developer projects often stall
- **Mitigation:**
  - Clean architecture with separation of concerns
  - Comprehensive test suite (avoid regressions)
  - Document internal architecture
  - Seek collaborators early
  - Consider foundation backing (Rust Foundation)

**Risk 10: Rust Language Evolution**
- **Impact:** Medium - New features may require verification support
- **Probability:** High - Rust actively evolving
- **Mitigation:**
  - Monitor RFC process
  - Participate in language design discussions
  - Modular architecture allows feature additions
  - Focus on stable core features first

---

## 4. Success Metrics

### 4.1 Technical Metrics

**Phase 1 (Foundation):**
- Verify 10+ simple functions with 100% success
- Verification time <1s for functions <50 LOC
- Zero false positives on correct code
- SMT query success rate >80%

**Phase 2 (Core Capabilities):**
- Verify 50+ functions with diverse ownership patterns
- Handle mutable borrows with <20% manual annotation overhead
- Loop verification for 10+ algorithms
- Type invariants for 5+ data structures

**Phase 3 (Advanced Features):**
- Verify 5+ unsafe modules with full specifications
- Automation rate 80%+ for safe Rust
- Incremental verification speedup 5x
- IDE integration with <500ms feedback

### 4.2 Adoption Metrics

**Community Engagement:**
- 100+ GitHub stars (Phase 1 completion)
- 500+ GitHub stars (Phase 2 completion)
- 1000+ GitHub stars (Phase 3 completion)
- 10+ external contributors
- 3+ blog posts/talks about the tool

**Usage Metrics:**
- 10+ production users (critical-path verification)
- 100+ downloads/month from crates.io
- 5+ published case studies
- Integration with 1+ popular crate

### 4.3 Quality Metrics

**Correctness:**
- 95%+ test coverage
- Zero known soundness bugs
- Formal correctness argument for VC generation
- Validation against verification benchmarks

**Usability:**
- User survey: >80% satisfaction
- Average onboarding time <2 hours
- Documentation coverage 100% of public API
- <10% questions duplicate in issue tracker

---

## 5. Next Steps: Concrete Actions

### Immediate Actions (Week 1-2)

1. **Set Up Project Infrastructure**
   - Create GitHub repository with MIT/Apache-2.0 dual license
   - Set up Rust workspace with sub-crates:
     - `rust-fv-macros`: Procedural macros
     - `rust-fv-analysis`: MIR analysis and VC generation
     - `rust-fv-backend`: SMT solver integration
     - `rust-fv`: Main crate and CLI
   - Configure CI/CD (GitHub Actions):
     - Automated testing on multiple Rust versions
     - Linting (clippy, rustfmt)
     - Documentation generation
   - Pin nightly Rust version in `rust-toolchain.toml`

2. **Technology Validation**
   - Prototype procedural macro for `#[requires]`
   - Minimal rustc_plugin integration (print MIR)
   - Basic Z3 query (prove simple arithmetic property)
   - Validate end-to-end feasibility

3. **Community Engagement**
   - Draft RFC for Rust Formal Methods Interest Group
   - Post on Rust internals forum (seek feedback)
   - Reach out to Verus/Creusot/Prusti authors (advice)
   - Create project roadmap and share publicly

### Short-Term Actions (Week 3-8)

4. **Implement Phase 1 Foundation**
   - Complete specification macro crate:
     - Parse `#[requires]`, `#[ensures]`, `#[pure]` attributes
     - Build AST representation of specifications
     - Generate metadata for MIR analysis
   - Build MIR analysis plugin:
     - Extract MIR for annotated functions
     - Traverse MIR to identify verification points
     - Generate simple VCs (pure function pre/post)
   - Integrate Z3 backend:
     - Translate VCs to SMT-LIB
     - Invoke Z3 and parse results
     - Generate error reports

5. **Create Initial Documentation**
   - Tutorial: "Your First Verified Function"
   - Specification language reference
   - Architecture documentation
   - Contributing guide

6. **Develop Test Suite**
   - Unit tests for each component
   - Integration tests (end-to-end examples)
   - Negative tests (reject invalid specifications)
   - Benchmark suite for performance tracking

### Medium-Term Actions (Month 3-6)

7. **Expand to Phase 2 Capabilities**
   - Implement ownership tracking
   - Add prophecy-based mutable borrow reasoning
   - Support loop invariants
   - Verify first non-trivial data structure (Vec or LinkedList)

8. **Gather Early Feedback**
   - Recruit 5-10 alpha testers
   - Conduct user studies (observe usage patterns)
   - Iterate on error messages and UX
   - Address pain points proactively

9. **Publish Initial Release**
   - Release v0.1.0 to crates.io
   - Write launch blog post
   - Submit talk proposals (RustConf, academic workshops)
   - Create demonstration video

### Long-Term Actions (Month 7-15)

10. **Complete Phase 3 Features**
    - Unsafe code verification
    - Ghost code and resources
    - Automation enhancements
    - Professional tooling (cargo plugin, IDE integration)

11. **Build Ecosystem**
    - Verify popular crates (showcase capability)
    - Collaborate with safety-critical Rust projects
    - Contribute verified stdlib specifications
    - Engage with Rust Foundation verification initiative

12. **Evaluate and Iterate**
    - Measure against success metrics
    - Gather production user feedback
    - Identify most valuable future features
    - Plan Phase 4 (concurrency, advanced automation)

---

## 6. Decision Framework for Trade-offs

Throughout implementation, trade-offs will arise. Use this framework:

### Usability vs. Expressiveness
**Guideline:** Favor usability for common cases, expressiveness for rare cases
- **Example:** Simple syntax for 80% patterns, advanced syntax for 20%
- **Decision Process:** Prototype both, user test, measure adoption

### Automation vs. Predictability
**Guideline:** Favor predictability and fast feedback
- **Example:** Conservative SMT vs. aggressive heuristics
- **Decision Process:** Benchmark both, measure success rate and time

### Soundness vs. Completeness
**Guideline:** Soundness non-negotiable, completeness best-effort
- **Example:** Reject valid code rather than accept invalid code
- **Decision Process:** Formal argument for soundness, user feedback for completeness

### Innovation vs. Proven Approaches
**Guideline:** Follow proven approaches, innovate in tooling/UX
- **Example:** Use RustHornBelt prophecy model, innovate in error messages
- **Decision Process:** Literature review, prototype, validate against benchmarks

---

## 7. Conclusion

The Rust formal verification landscape in 2025-2026 demonstrates that practical, automated verification is achievable. The combination of:

1. Rust's strong type system (eliminating whole classes of bugs)
2. Modern SMT solvers (Z3, CVC5 achieving 80-90% automation)
3. Proven specification techniques (prophecies, separation logic)
4. Industrial validation (Verus at Microsoft/Amazon, Kani at AWS)

...creates an opportunity to build a verification tool that balances rigor with pragmatism.

**The path forward is clear:**

- **Start with proven approaches:** SMT-based verification, procedural macros, MIR analysis
- **Focus on developer experience:** Fast feedback, clear errors, progressive disclosure
- **Build incrementally:** Function contracts → ownership → loops → unsafe code
- **Engage community early:** Feedback shapes usability, collaboration ensures sustainability

**The vision:** A verification tool that Rust developers can adopt incrementally for critical code paths, with automation handling the majority of verification burden, and clear paths for manual proof when needed.

This synthesis provides the foundation for implementation decisions. Refer to the detailed research documents for specific technical approaches, and use the phased plan to maintain focus on delivering value incrementally.

---

## References

This synthesis draws from four detailed research documents:

1. **formal_verification_research_summary.md**: Overview of verification approaches, tools (Verus, Kani, Prusti, Creusot), and success stories
2. **compiler-integration-research.md**: Analysis of integration strategies (procedural macros, MIR passes, rustc driver, cargo integration)
3. **specification-language-research.md**: Specification language design (ACSL, JML, Dafny, SPARK) and Rust-specific operators (prophecies, model operator)
4. **proof-automation-strategies.md**: Automation techniques, realistic expectations (80-90% for safe code), and manual effort requirements

For detailed citations and academic sources, consult the individual research documents.

---

**Document Version**: 1.0
**Date**: 2026-02-10
**Author**: AI Hive(R)
**Status**: Implementation guidance for rust-fv project
