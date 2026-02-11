# Domain Pitfalls

**Domain:** Rust Formal Verification (SMT-based)
**Researched:** 2026-02-10
**Confidence:** HIGH

## Critical Pitfalls

Mistakes that cause rewrites or major issues.

### Pitfall 1: Soundness Bugs in SMT Encoding

**What goes wrong:**
Incorrect translation from Rust semantics to SMT formulas leads to the verifier accepting unsound programs (proving correctness when bugs exist) or rejecting sound programs (false positives). This is the most severe failure mode - the tool becomes untrustworthy.

**Why it happens:**
- Subtle semantic mismatches between Rust operations and SMT theories (e.g., overflow behavior, type casts, pointer arithmetic)
- Incomplete handling of type system features (e.g., treating aggregate types as uninterpreted sorts loses field structure)
- SMT solver abstractions that are too coarse (e.g., abstracting unsupported types as 256-bit integers)
- Missing edge cases in encoding (e.g., object size identifiers not properly quoted in SMT2 format - real bug from CBMC)

**Consequences:**
- False negatives: Verifier claims code is safe when it has bugs (catastrophic for safety-critical use)
- False positives: Verifier rejects correct code, forcing unnecessary refactoring
- Loss of user trust in the tool
- Potential need for complete rewrite of encoding layer

**Prevention:**
- Formalize encoding correctness: Use proof assistant (Coq/Lean) to prove SMT encoding preserves Rust semantics
- Implement bi-directional testing: Generate Rust code from SMT models, verify they match original semantics
- Use differential testing: Compare results with other verifiers (Kani, Prusti, Verus) on same code
- Build comprehensive test suite covering all type/operation combinations
- Document encoding decisions explicitly with soundness arguments
- Start with decidable, well-understood theories (bitvectors, arrays) before extending

**Warning signs:**
- Verifier accepts code that panics at runtime
- Verifier rejects obviously correct code
- Different results when semantically equivalent code is rewritten
- SMT solver returns "unknown" frequently (suggests encoding issues)
- Test failures when expanding type coverage

**Phase to address:**
Phase 2 (Type System Enhancement) - when adding aggregate types, mutable borrows, this risk peaks. Requires:
- Formal encoding specification document
- Soundness test suite (wrong programs should be rejected)
- Completeness test suite (correct programs should be accepted)
- Cross-validation against existing tools

---

### Pitfall 2: MIR API Instability Across Nightly Versions

**What goes wrong:**
Rust's MIR (Mid-level Intermediate Representation) is an unstable compiler internal with frequent breaking changes. Code working on nightly-2026-01 breaks on nightly-2026-02. This creates maintenance burden and version compatibility hell.

**Why it happens:**
- MIR is explicitly unstable with "no attempt to make anything work besides what the rustc test suite needs"
- MIR optimization passes evolve rapidly (15.28% of rustc bugs are MIR optimization issues)
- Stable MIR project exists but incomplete (as of 2026)
- New MIR passes/transformations added regularly without backwards compatibility

**Consequences:**
- Tool breaks on new nightly versions, requiring constant updates
- Users stuck on specific rustc version, can't use latest language features
- CI pipeline fragile - nightly updates break builds
- Difficult to reproduce verification results across machines with different rustc versions

**Prevention:**
- Pin specific nightly version in rust-toolchain.toml
- Implement rustc version detection and compatibility checks at startup
- Create abstraction layer over MIR types to isolate breaking changes
- Track stable MIR project progress, migrate when available
- Document supported rustc versions explicitly
- Add CI matrix testing multiple nightly versions (e.g., last 3 releases)
- Consider alternative: HIR-level analysis if sufficient (less unstable)

**Warning signs:**
- Compilation errors in mir_converter.rs on rustc update
- New MIR terminators/rvalues/operands appear that aren't handled
- MIR structure changes (e.g., new basic block types, changed terminator variants)
- rustc-driver API changes requiring code updates

**Phase to address:**
Immediate (Phase 1 completion) - establish version compatibility strategy:
- Document compatibility matrix
- Add rustc version tests
- Isolate MIR dependencies in mir_converter module
- Prepare migration path to stable APIs when available

---

### Pitfall 3: Loop Invariant Inference Failure

**What goes wrong:**
Loop invariants are notoriously difficult to infer automatically. When automation fails, users must write invariants manually. If manual invariants are wrong or too weak, verification fails. Loop invariants are "the most challenging problem in program verification."

**Why it happens:**
- Obvious properties frequently overlooked in manual specification
- Invariants must be inductive (maintain through loop iteration) - non-obvious requirement
- Invariants must be strong enough to prove postcondition but weak enough to maintain
- SMT solvers can't reason about unbounded loops without invariants
- Automated invariant synthesis struggles with complex loop patterns
- LLMs show "limited ability to leverage verifier-provided feedback when repairing incorrect invariants"

**Consequences:**
- Verification fails on loops, even trivial ones
- Users spend hours debugging invariant formulations
- Proof burden explodes (loop verification is most time-consuming part)
- Tool abandoned as "too hard to use"
- Targeting 80-90% automation becomes unachievable

**Prevention:**
- Implement multi-strategy invariant inference:
  - Template-based (common patterns: `0 <= i < n`, array bounds)
  - Abstract interpretation (octagon domain, intervals)
  - SMT-based CEGIS (counterexample-guided inductive synthesis)
  - Reinforcement learning enhanced synthesis (recent research direction)
- Provide high-quality error messages when invariant checking fails
- Include invariant debugging tools (show which clause fails: init, inductive, or post)
- Create library of common invariants for standard patterns
- Support incremental invariant strengthening (tool suggests additions)
- Don't make loops mandatory for Phase 2 - start with simple bounded loops

**Warning signs:**
- Users frequently report "verification timeout on loops"
- Manual invariants require 5+ iterations to get right
- Invariants become longer than the loop body
- Verification succeeds/fails unpredictably based on minor loop changes

**Phase to address:**
Phase 2 (Loop Invariants) - this will be the hardest feature:
- Research phase: Survey 3+ inference approaches before committing
- Prototype with simple loops (for, while with bounds)
- Build debugging/explanation tools in parallel
- Defer complex invariants (nested loops, complex data structures) to later phases

---

### Pitfall 4: Bitvector Overflow Semantics Mismatch

**What goes wrong:**
Rust has specific overflow semantics (wrapping in release, panic in debug, checked operations). SMT bitvector operations have different semantics. Naive encoding leads to verification accepting code that panics or wraps unexpectedly.

**Why it happens:**
- Rust overflow behavior mode-dependent (debug vs release)
- SMT bitvector arithmetic is modular (wraps) by default
- Overflow predicates exist (`bvuaddo`, `bvsaddo`, etc.) but must be added explicitly
- Easy to forget overflow checks in every arithmetic operation
- Carry bit handling requires explicit zero-extension
- Signed/unsigned distinction must be preserved through encoding

**Consequences:**
- Verifier accepts code that panics in debug mode
- Verifier accepts code with unintended wrapping behavior
- Security vulnerabilities if overflow leads to buffer overrun
- Integer overflow bugs are common source of verification unsoundness

**Prevention:**
- Use SMT-LIB overflow predicates consistently (`bvumul_noovfl`, `bvsmul_noovfl`, etc.)
- For addition: zero-extend arguments by one bit, check MSB is 0 in result
- Generate separate VCs for overflow conditions
- Respect Rust's overflow mode:
  - `cfg!(debug_assertions)` → add overflow checks
  - Release mode → verify wrapping semantics match intent
- Test encoding with known overflow cases (e.g., binary search bug: `mid = (lo + hi) / 2`)
- Add property-based tests: Rust operation result should match SMT model value

**Warning signs:**
- Code verified but panics in debug mode at runtime
- Arithmetic on large values produces wrong verification results
- Difference in verification results between i32/u32 and i64/u64

**Phase to address:**
Phase 1 (completion) - already using bitvector theory, verify overflow handling:
- Audit all arithmetic encoding in encode_term.rs
- Add overflow test cases (addition, multiplication, subtraction of edge values)
- Document overflow semantics in encoding specification

---

### Pitfall 5: SSA Violation Causing Variable Shadowing Bugs

**What goes wrong:**
Multiple assignments to the same variable overwrite each other in SMT encoding instead of creating new SSA versions. This causes verification to use wrong values from incorrect control flow paths, leading to false positives or false negatives.

**Why it happens:**
- VCGen assumes linear execution, walks blocks in order
- SSA counter declared but unused (known bug in CONCERNS.md)
- MIR CFG has arbitrary loops/branches, but encoding assumes straight-line code
- Assignment collection walks all blocks, doesn't track which path reaches which statement

**Consequences:**
- False negatives: Bug in one branch hidden by value from other branch
- False positives: Correct code rejected because unrelated assignment creates conflict
- Non-deterministic results based on basic block ordering
- Verification results invalid for functions with control flow

**Prevention:**
- Implement true SSA renaming:
  - Each assignment creates new variable: `x_0`, `x_1`, `x_2`
  - Track current SSA version per variable per basic block
  - Insert phi functions at control flow merge points
- Use path-sensitive analysis:
  - Generate separate VCs for each path through CFG
  - Track assignments per path, not globally
- Add tests specifically for multi-path scenarios:
  - If-then-else with assignments to same variable in both branches
  - Loops with counters
  - Early returns

**Warning signs:**
- Verification result changes when reordering statements
- Different results for semantically equivalent control flow (if/else vs match)
- Users report "verified function still has bugs"
- VCs reference wrong variable versions

**Phase to address:**
Immediate (Phase 1 fix) - this is a known critical bug:
- Implement SSA variable renaming in vcgen.rs
- Add phi-function insertion at block joins
- Test with multi-path control flow examples

---

### Pitfall 6: Procedural Macro Hygiene Violations

**What goes wrong:**
Procedural macros for specifications are "entirely unhygienic" - they don't respect Rust's namespace rules. Generated code can accidentally capture or shadow user variables, or fail to find standard library items.

**Why it happens:**
- Proc macros operate on token streams with manual span manipulation
- No automatic name resolution - macro must fully qualify all names
- `quote!` macros generate code in macro's context, not call site context
- Span information underspecified and underdocumented
- Easy to forget `::std::` prefix on stdlib types

**Consequences:**
- Specification code compiles but has wrong semantics (captures wrong variable)
- Mysterious errors when user code shadows standard names
- Different behavior in different modules based on imports
- Tooling (IDE, rust-analyzer) shows wrong information due to span issues

**Prevention:**
- Always fully qualify paths in macro-generated code: `::std::result::Result`, not `Result`
- Use `quote_spanned!` to preserve user code spans for error messages
- Test macros in modules with unusual imports/shadowing
- Document macro hygiene requirements explicitly
- Consider structured attributes (when stabilized) instead of doc attributes
- Add round-trip tests: expand macro → parse → verify structure matches expected

**Warning signs:**
- Compilation errors about missing items that clearly exist
- Different behavior when `use std::*` is present vs absent
- IDE shows errors but code compiles, or vice versa
- Error messages point to wrong source locations

**Phase to address:**
Phase 2 (Specification Enhancement) - when extending spec language:
- Audit existing macros for hygiene issues
- Add hygiene test suite (macros in strange contexts)
- Document qualification requirements
- Consider migration to `#[register_tool]` custom attributes

---

### Pitfall 7: SMT Solver Performance Cliffs

**What goes wrong:**
Minor changes to SMT encoding cause exponential performance degradation. Queries that solved in milliseconds now timeout after minutes. This unpredictability makes verification unreliable.

**Why it happens:**
- SMT solvers rely on heuristics (branching, simplification, lemma generation)
- Performance "very sensitive to problem encoding"
- Quantifier instantiation heuristics are non-deterministic
- Once formulas grow large/complex, solving time can "explode exponentially"
- Theory combination interactions (arrays + integers + bitvectors) compound complexity
- Syntactic changes to logically equivalent formulas affect solver strategy

**Consequences:**
- Verification timeouts on realistic code
- Non-deterministic verification (sometimes passes, sometimes times out)
- Users can't predict what code will verify
- Tool perceived as "too slow for real use"

**Prevention:**
- Minimize quantifiers: Use quantifier-free fragments when possible
- Simplify formulas before sending to solver:
  - Constant folding
  - Dead code elimination
  - Common subexpression elimination
- Generate minimal SMT scripts (only necessary context per VC)
- Use incremental solving with push/pop instead of separate processes
- Profile SMT queries, identify patterns that cause slowdown
- Add timeout budget per VC, report which VCs timeout
- Consider multiple solvers: try Z3, fallback to CVC5 on timeout
- Use SMT solver diagnostics (`-v` flag) to understand bottlenecks

**Warning signs:**
- Verification time unpredictable (same code takes different time)
- Small code changes cause huge performance swings
- Solver returns "unknown" frequently
- Generated SMT scripts grow to multi-megabyte size
- Profiling shows solver taking >90% of verification time

**Phase to address:**
Phase 3 (Performance Optimization):
- Benchmark suite with performance regression tests
- SMT query profiler/analyzer tool
- Formula simplification passes before solver submission
- Multiple solver backend support

---

### Pitfall 8: Inadequate Testing of the Verifier Itself

**What goes wrong:**
Verification tools have bugs like any software. Without rigorous testing of the verifier, soundness bugs ship to users. "Who verifies the verifier?"

**Why it happens:**
- Metamorphic testing for verifiers is non-obvious
- Generating test cases requires understanding both Rust semantics and SMT
- Focus on positive tests (correct code verifies) neglects negative tests (wrong code rejected)
- Incomplete coverage of language features
- Edge cases in MIR translation not tested

**Consequences:**
- Soundness bugs: Tool accepts unsafe code (critical failure)
- Completeness bugs: Tool rejects safe code (usability failure)
- User discovers bugs in production, loses trust
- Difficult to add features without breaking existing verification

**Prevention:**
- Implement comprehensive test strategy:
  - **Soundness tests**: Programs known to have bugs should be rejected (use mutation testing)
  - **Completeness tests**: Correct programs should verify (curated examples)
  - **Differential testing**: Compare results with Kani, Prusti, Verus on same code
  - **Metamorphic testing**: Transform verified program, verify transformation preserves verification
- Add interrogation testing (from recent research):
  - Generate program pairs with known relationships
  - Verify tool respects those relationships
- Test coverage for all MIR constructs:
  - Every terminator type
  - Every rvalue kind
  - Every operand type
- Fuzzing: Generate random MIR, verify tool doesn't crash
- Regression tests from user bug reports

**Warning signs:**
- Users report bugs not caught by tests
- New features break existing verification
- Can't explain why certain code verifies or doesn't
- Test suite has low coverage (<80% of vcgen/encoder code)

**Phase to address:**
Immediate (Phase 1):
- Add soundness test suite (wrong programs)
- Add completeness test suite (right programs)
- Implement metamorphic testing framework
Ongoing: Add tests for every feature in every phase

---

## Moderate Pitfalls

### Pitfall 9: Aggregate Type Encoding Loses Structure

**What goes wrong:**
Encoding structs/tuples/enums as uninterpreted sorts means verifier can't reason about field access, pattern matching, or structural properties.

**Prevention:**
Use SMT datatypes with proper constructors/selectors. This is planned work for Phase 2.

**Warning signs:**
- Can't verify code accessing struct fields
- Enum pattern matching fails verification
- Tuple destructuring loses type information

---

### Pitfall 10: Inter-procedural Verification Scaling

**What goes wrong:**
Inlining all function calls causes exponential blowup. Without function summaries, verification limited to small functions.

**Prevention:**
- Implement modular verification with function contracts
- Use summary repair for incremental verification
- Cache verification results per function
- Maintain under-approximations (traces) and over-approximations (summaries)

**Warning signs:**
- Verification timeout increases super-linearly with code size
- Functions with many calls verify much slower
- Re-verifying unchanged functions takes same time as first verification

---

### Pitfall 11: Float Encoding as Uninterpreted

**What goes wrong:**
Floating-point operations encoded as uninterpreted constants block verification of any code using floats.

**Prevention:**
Use SMT-LIB FloatingPoint theory (`(_ FloatingPoint e s)`). Infrastructure exists in smtlib crate.

**Warning signs:**
- All functions with float parameters fail verification
- Float operations produce placeholder values

---

### Pitfall 12: Reference and Borrow Tracking

**What goes wrong:**
Treating references as transparent loses Rust's aliasing guarantees. Can't verify mutation safety or borrow checker reasoning.

**Prevention:**
- Implement prophecy variables for mutable borrows
- Track lifetime relationships in encoding
- Use separation logic or fractional permissions

**Warning signs:**
- Can't verify code with `&mut` parameters
- Aliasing-related bugs not caught
- Borrow checker errors not reflected in verification

---

## Minor Pitfalls

### Pitfall 13: Error Message Quality

**What goes wrong:**
Poor error messages when verification fails leave users unable to fix code.

**Prevention:**
- Show which VC failed with source location
- Explain what property was being checked
- Provide counterexample from SMT model
- Suggest common fixes

---

### Pitfall 14: Process Spawning Overhead

**What goes wrong:**
Spawning Z3 process per VC causes slow verification even for small functions.

**Prevention:**
Use Z3 API in-process or server mode for incremental solving.

---

### Pitfall 15: Monolithic SMT Scripts

**What goes wrong:**
Large functions generate multi-MB SMT scripts that solver struggles with.

**Prevention:**
Generate minimal scripts with only necessary context per VC.

---

## Technical Debt Patterns

Shortcuts that seem reasonable but create long-term problems.

| Shortcut | Immediate Benefit | Long-term Cost | When Acceptable |
|----------|-------------------|----------------|-----------------|
| Uninterpreted aggregate types | Fast implementation, no encoding complexity | Can't verify real data structures, blocks adoption | MVP/Phase 1 only - must fix in Phase 2 |
| Linear block walking | Simple VCGen implementation | SSA violations, incorrect results | Never - fix immediately |
| Doc attribute contracts | No rustc changes needed | Fragile parsing, hygiene issues | Until `#[register_tool]` stabilizes |
| Per-VC process spawning | Simple implementation, no state management | 10-100x slower than needed | Phase 1-2, fix in Phase 3 perf work |
| No loop invariants | Avoid hardest verification problem | Can't verify real code with loops | Phase 1 only |
| Single solver (Z3) | Simple architecture, no abstraction needed | Vendor lock-in, no fallback | Acceptable with detection/error handling |
| Regex-based SMT parsing | No dependency on SMT-LIB parser library | Fragile to Z3 output changes | Acceptable with version pinning + tests |

---

## Integration Gotchas

Common mistakes when connecting to external services.

| Integration | Common Mistake | Correct Approach |
|-------------|----------------|------------------|
| Z3 solver | Assuming Z3 always available, no version check | Auto-detect with fallback, version compatibility check, clear error |
| rustc driver | Using unstable APIs without version guard | Pin rustc version, test compatibility matrix, isolate in one module |
| Proc macros | Expecting hygiene, using relative paths | Fully qualify all names, use quote_spanned!, test in strange contexts |
| SMT-LIB format | Trusting solver output format never changes | Pin solver version, parse defensively, test with malformed output |
| MIR conversion | Assuming all MIR constructs handled | Explicit match on all variants, panic on unknown, exhaustive tests |

---

## Performance Traps

Patterns that work at small scale but fail as usage grows.

| Trap | Symptoms | Prevention | When It Breaks |
|------|----------|------------|----------------|
| Inlining all function calls | Exponential VC size growth | Function summaries, modular verification | >3 levels of calls, recursive functions |
| Per-VC process spawn | Linear slowdown with function size | In-process Z3 API, incremental solving | >20 VCs per function (~50ms each) |
| Global variable namespace | String operation overhead, solver confusion | Numeric indices with encoding table | >500 variables, deep projections |
| Monolithic SMT scripts | Solver timeout, memory exhaustion | Minimal context per VC, script composition | >1000 LOC functions, complex VCs |
| Walking all blocks per VC | O(N*M) where N=statements, M=VCs | Cache assignments per block | >100 basic blocks |
| No VC caching | Re-verify unchanged functions | Result cache keyed by function signature | Large codebases, incremental compilation |

---

## Security Mistakes

Domain-specific security issues beyond general web security.

| Mistake | Risk | Prevention |
|---------|------|------------|
| Unsanitized solver arguments | Command injection if extra_args exposed | Whitelist allowed arguments, validate inputs |
| Trusting unverified code paths | False sense of security if coverage incomplete | Track which code produced VCs, require 100% coverage |
| Missing overflow checks | Accept code with integer overflow vulnerabilities | Add overflow VCs for all arithmetic, test with edge values |
| Soundness bugs in encoding | Accept unsafe programs as safe (catastrophic) | Formal encoding proof, differential testing, soundness test suite |
| Incomplete unsafe handling | Unsafe code verified same as safe code | Separate unsafe analysis path (Phase 3 feature) |

---

## "Looks Done But Isn't" Checklist

Things that appear complete but are missing critical pieces.

- [ ] **Aggregate type encoding:** Type defined but uninterpreted - verify field access actually works
- [ ] **Loop support:** MIR has loops but no invariants - verify unbounded loops actually terminate verification
- [ ] **Reference handling:** Reference types exist but transparent - verify mutable borrow actually tracked
- [ ] **Overflow checking:** Bitvector ops exist but no overflow VCs - verify arithmetic edge cases have checks
- [ ] **Error messages:** Verification reports "failed" - verify user can understand why and fix
- [ ] **Function calls:** Can see call in MIR - verify inter-procedural verification works, not just inlining
- [ ] **Specification parser:** Parses simple specs - verify complex expressions, quantifiers, function calls
- [ ] **MIR coverage:** Handles basic terminators - verify all terminator/rvalue/operand types implemented
- [ ] **Testing:** E2E tests pass - verify soundness tests (wrong programs rejected) exist
- [ ] **Z3 integration:** Can call Z3 - verify timeout handling, error cases, version compatibility

---

## Recovery Strategies

When pitfalls occur despite prevention, how to recover.

| Pitfall | Recovery Cost | Recovery Steps |
|---------|---------------|----------------|
| Soundness bug in encoding | HIGH | 1. Add to soundness test suite (prevent recurrence)<br>2. Audit similar encodings<br>3. Consider formal proof of encoding<br>4. Public disclosure if affects users |
| MIR API breakage | LOW-MEDIUM | 1. Update mir_converter.rs for new API<br>2. Add compatibility shim if possible<br>3. Update supported version docs<br>4. Add regression test for this MIR construct |
| SSA violation | MEDIUM | 1. Implement full SSA renaming (not quick fix)<br>2. Add phi functions at joins<br>3. Re-verify all existing test cases |
| SMT performance cliff | LOW-MEDIUM | 1. Profile to identify problematic formula<br>2. Try formula simplification<br>3. Try alternative solver (CVC5)<br>4. Increase timeout<br>5. Report to user with actionable feedback |
| Loop invariant inference fail | LOW | 1. Explain which invariant clause failed (init/inductive/post)<br>2. Suggest invariant strengthening<br>3. Provide template for manual invariant<br>4. Document pattern for future auto-inference |
| Proc macro hygiene issue | LOW | 1. Add fully qualified paths<br>2. Fix span information<br>3. Add test case reproducing issue |
| Aggregate encoding incomplete | HIGH | 1. Requires SMT datatype implementation<br>2. Not patchable - must complete Phase 2 work |
| Bitvector overflow mismatch | MEDIUM | 1. Add missing overflow predicates<br>2. Test with known overflow cases<br>3. Audit all arithmetic encodings |

---

## Pitfall-to-Phase Mapping

How roadmap phases should address these pitfalls.

| Pitfall | Prevention Phase | Verification |
|---------|------------------|--------------|
| Soundness bugs (encoding) | Phase 1-2 (ongoing) | Soundness test suite with mutation testing, differential testing vs Kani/Prusti |
| MIR API instability | Phase 1 (immediate) | Compatibility matrix tests, CI against multiple nightlies |
| Loop invariant failure | Phase 2 (Loop Support) | Test suite with common loop patterns, invariant debugger shows failures |
| Bitvector overflow | Phase 1 (immediate) | Test with INT_MAX, INT_MIN, overflow edge cases |
| SSA violations | Phase 1 (immediate fix) | Multi-path control flow tests, phi function insertion verified |
| Proc macro hygiene | Phase 2 (Spec Enhancement) | Macro expansion tests in unusual contexts, hygiene test suite |
| SMT performance cliffs | Phase 3 (Performance) | Performance regression tests, timeout budgets, profiler |
| Inadequate verifier testing | Ongoing (all phases) | Metamorphic tests, interrogation tests, coverage >90% |
| Aggregate encoding | Phase 2 (Type System) | Struct/enum/tuple field access verification, SMT datatype tests |
| Inter-procedural scaling | Phase 2 (Function Summaries) | Benchmark call-heavy code, verify summary caching works |
| Float encoding | Phase 2 (Type System) | IEEE 754 test cases, float operation verification |
| Reference/borrow tracking | Phase 2 (Mutable Borrows) | Aliasing tests, prophecy variable tests, lifetime tracking |

---

## Phase-Specific Warnings

| Phase Topic | Likely Pitfall | Mitigation |
|-------------|---------------|------------|
| Phase 1 completion | SSA violations, bitvector overflow, MIR instability | Fix immediately before Phase 2, blocking issues |
| Phase 2: Aggregate Types | Soundness bugs in datatype encoding, SMT performance | Formal encoding spec, extensive testing, start with simple types |
| Phase 2: Loop Invariants | Inference failure, proof burden explosion | Multi-strategy inference, excellent error messages, defer complex cases |
| Phase 2: Mutable Borrows | Unsound prophecy encoding, borrow tracking complexity | Study Prusti/Verus approaches, formal model first |
| Phase 2: Function Summaries | Summary imprecision, inter-procedural unsoundness | Start with simple contracts, validate against inlining |
| Phase 3: Performance | Premature optimization, complexity explosion | Benchmark first, profile-guided optimization only |
| Phase 3: Unsafe Support | Soundness gaps in raw pointer reasoning | Separate unsafe from safe analysis, conservative approximations |

---

## Research-Specific Warnings

Based on surveying the formal verification research literature:

**Loop Invariants:**
- LLMs cannot yet reliably infer or repair invariants (2025 research shows limited feedback utilization)
- Reinforcement learning shows promise but still research-stage
- Template-based approaches work for common patterns but don't generalize
- Expect this to be the bottleneck for automation percentage

**Rust-Specific:**
- Iterator verification is a known open problem (non-deterministic, infinite, higher-order, effectful)
- Unsafe Rust still challenging for all tools (Kani/Verus can verify it but with limitations)
- Standard library verification blocked by specification gap, not just tool capability
- Polonius (improved borrow checker) still in development - may invalidate borrow reasoning

**SMT Solver:**
- Quantifier handling is the weak point - use quantifier-free encodings when possible
- Z3 and CVC5 comparable but complement each other (try both on timeout)
- Bitvector theory well-supported, but theory combination (bitvectors + arrays + arithmetic) can be slow
- Floating-point theory exists but performance varies

**Concurrency (Future):**
- Concurrent verification is "key challenge" even with Rust's safety
- VerusSync (permission-based toolkit) is promising but very recent
- Deadlock analysis remains open problem (both thread deadlocks and Rc/borrow cycles)

---

## Sources

**Rust Formal Verification:**
- [Towards Practical Formal Verification for a General-Purpose OS in Rust](https://asterinas.github.io/2025/02/13/towards-practical-formal-verification-for-a-general-purpose-os-in-rust.html) - Concurrency challenges, Verus limitations
- [What Rust Got Wrong on Formal Verification](https://gavinhoward.com/2024/05/what-rust-got-wrong-on-formal-verification/) - Design critique
- [Rust Formal Methods Interest Group](https://rust-formal-methods.github.io/) - Ecosystem overview
- [The Prusti Project: Formal Verification for Rust](https://pm.inf.ethz.ch/publications/AstrauskasBilyFialaGrannanMathejaMuellerPoliSummers22.pdf) - Lessons learned from Prusti
- [Verus: A Practical Foundation for Systems Verification](https://www.cs.utexas.edu/~hleblanc/pdfs/verus.pdf) - Iterator verification challenges, linear ghost types
- [Verify the Safety of the Rust Standard Library](https://aws.amazon.com/blogs/opensource/verify-the-safety-of-the-rust-standard-library/) - Specification gap challenges

**SMT Solvers:**
- [Programming Z3](https://theory.stanford.edu/~nikolaj/programmingz3.html) - Z3 usage patterns
- [Using BitVector Theory to find the overflow bug in Binary Search](https://verificationglasses.wordpress.com/2020/12/17/bitvector-overflow/) - Bitvector overflow detection
- [Check for overflow on bitvector operations](https://github.com/Z3Prover/z3/discussions/5138) - Z3 overflow predicates
- [SMTChecker and Formal Verification - Solidity](https://docs.soliditylang.org/en/latest/smtchecker.html) - SMT encoding soundness/completeness
- [A soundness bug in SMT encoding of pointer objects](https://github.com/diffblue/cbmc/issues/5952) - Real soundness bug example

**MIR and Rust Compiler:**
- [The MIR (Mid-level IR) - Rust Compiler Development Guide](https://rustc-dev-guide.rust-lang.org/mir/index.html) - MIR documentation
- [An Empirical Study of Rust-Specific Bugs in the rustc Compiler](https://arxiv.org/html/2503.23985v1) - MIR optimization bugs (15.28%)
- [Rust in 2026 - Rust Project Goals](https://rust-lang.github.io/rust-project-goals/2026/flagships.html) - Stable MIR progress

**Loop Invariants:**
- [Loop Invariant Inference through SMT Solving Enhanced Reinforcement Learning](https://dl.acm.org/doi/10.1145/3597926.3598047) - RL-based synthesis
- [LLM For Loop Invariant Generation and Fixing: How Far Are We?](https://arxiv.org/html/2511.06552) - LLM limitations
- [Loop Invariant Generation: A Hybrid Framework of Reasoning optimised LLMs and SMT Solvers](https://arxiv.org/html/2508.00419) - Hybrid approaches

**Ownership and Borrow Checking:**
- [Place Capability Graphs: A General-Purpose Model of Rust's Ownership and Borrowing Guarantees](https://arxiv.org/html/2503.21691v5) - Flow-sensitivity challenges
- [Tracking issue for procedural macros and "hygiene 2.0"](https://github.com/rust-lang/rust/issues/54727) - Hygiene issues

**Formal Verification Practice:**
- [On the Impact of Formal Verification on Software Development](https://ranjitjhala.github.io/static/oopsla25-formal.pdf) - Proof burden (10x code expansion)
- [Lessons from Formally Verified Deployed Software Systems](https://arxiv.org/html/2301.02206v3) - Real-world experience

**Testing Verification Tools:**
- [ARGUZZ: Testing zkVMs for Soundness and Completeness Bugs](https://www.arxiv.org/pdf/2509.10819) - Metamorphic testing approach
- [Interrogation Testing of Program Analyzers for Soundness and Precision Issues](https://repositum.tuwien.at/bitstreams/20.500.12708/204589/1/Kaindlstorfer-2024-Interrogation%20Testing%20of%20Program%20Analyzers%20for%20Soundne...-vor.pdf) - Interrogation testing methodology

**Inter-procedural Verification:**
- [SMT-Based Model Checking for Recursive Programs](https://link.springer.com/chapter/10.1007/978-3-319-08867-9_2) - Summary-based approaches
- [SMT-based verification of program changes through summary repair](https://link.springer.com/article/10.1007/s10703-023-00423-0) - Incremental verification

**Aggregate Types:**
- [Efficient Verification of Programs with Complex Data Structures](https://publikationen.bibliothek.kit.edu/1000084545/15671070) - SMT encoding strategies
- [SMT-Based Bounded Model Checking for Embedded ANSI-C Software](https://ssvlab.github.io/lucasccordeiro/papers/tse2012.pdf) - Structure encoding as arrays

---

*Pitfalls research for: Rust Formal Verification (SMT-based)*
*Researched: 2026-02-10*
*Confidence: HIGH - based on official docs, research papers, real tool experience (Verus, Prusti, Kani)*
