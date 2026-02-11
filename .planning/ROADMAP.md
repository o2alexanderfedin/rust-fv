# Roadmap: rust-fv

## Overview

rust-fv evolves from a working v0.1.0 proof-of-concept (248 tests, 5-crate workspace, end-to-end pipeline) into a production-quality formal verification tool for Rust. The roadmap fixes a critical soundness bug first, then systematically completes table-stakes features, enables modular scaling, adds differentiating specification expressiveness, and finishes with performance optimization and error polish. Every phase builds on the previous one's verified foundation -- soundness is non-negotiable throughout.

## Phases

**Phase Numbering:**
- Integer phases (1, 2, 3): Planned milestone work
- Decimal phases (2.1, 2.2): Urgent insertions (marked with INSERTED)

Decimal phases appear between their surrounding integers in numeric order.

- [x] **Phase 1: Soundness Foundation** - Fix SSA violation, audit overflow encoding, establish soundness/completeness test suites
- [x] **Phase 2: Table Stakes Completion** - Loops, cargo verify, assertions, panics, structs, z3 crate, spec parser
- [x] **Phase 3: Modular Verification** - Function summaries, inter-procedural verification, ownership reasoning
- [ ] **Phase 4: Differentiation** - Unbounded integers, ghost code, quantifiers, prophecy variables, traits/generics
- [ ] **Phase 5: Performance and Polish** - Benchmarks, caching, parallelism, formula simplification, error messages

## Phase Details

### Phase 1: Soundness Foundation
**Goal**: Verification results are mathematically sound for all control-flow patterns and arithmetic operations
**Depends on**: Nothing (first phase)
**Requirements**: SND-01, SND-02, SND-03, SND-04, SND-05, SND-06, PERF-01
**Research flag**: No -- SSA is textbook compiler technique, overflow audit is systematic
**Plans:** 3 plans
**Success Criteria** (what must be TRUE):
  1. A function with if/else branches where each branch assigns different values to the same variable produces correct verification results (not unsound due to variable shadowing)
  2. A program containing a known integer overflow bug is rejected by the verifier with a counterexample showing the overflow
  3. A correct program with multi-path control flow (if/else, match arms, early return) verifies successfully without false alarms
  4. A soundness test suite of at least 20 programs with known bugs all fail verification, and a completeness test suite of at least 20 correct programs all pass verification
  5. Single-function contract verification completes in under 1 second

Plans:
- [x] 01-01-PLAN.md -- SSA variable renaming and path-condition-based VCGen for sound control-flow handling
- [x] 01-02-PLAN.md -- Arithmetic overflow audit and soundness/completeness test suites (40+ tests)
- [x] 01-03-PLAN.md -- Nightly toolchain pinning, compatibility docs, and performance benchmark baseline

### Phase 2: Table Stakes Completion
**Goal**: Developers can verify loops, assertions, panic-freedom, and struct-manipulating code through a cargo-native workflow
**Depends on**: Phase 1
**Requirements**: VER-01, VER-02, VER-03, VER-04, VER-05, TYP-01, TYP-02, TYP-03, TYP-04, SPEC-01, SPEC-05, TOOL-01, TOOL-02, TOOL-03, TOOL-04
**Research flag**: YES -- Loop invariant usability is the hardest UX problem in verification. Research 3+ inference approaches before committing. Study Creusot 0.9.0 auto-detection of immutable loop variables.
**Plans:** 5 plans
**Success Criteria** (what must be TRUE):
  1. A while loop with a user-supplied `#[invariant(expr)]` annotation verifies successfully, and the verifier reports which of the three VCs (initialization, preservation, use-after-loop) fails when the invariant is wrong
  2. Running `cargo verify` in a Rust project produces colored per-function output (OK/FAIL/TIMEOUT) showing verification status for all annotated functions
  3. An `assert!(x > 0)` statement in Rust source is statically verified from MIR, and a failing assert produces a counterexample
  4. Code calling `unwrap()` on a potentially-None value, or indexing an array with an out-of-bounds index, is flagged as a potential panic with the specific failure location
  5. A struct with named fields can be used in specifications (`#[ensures(result.x > 0)]`), and struct field access is correctly encoded in SMT

Plans:
- [x] 02-01-PLAN.md -- Z3 native API backend (z3 crate with bundled feature) and structured tracing via tracing crate
- [x] 02-02-PLAN.md -- Loop invariant verification with 3-VC generation (initialization, preservation, exit)
- [x] 02-03-PLAN.md -- Assertion verification and panic detection (unwrap, bounds, div-by-zero) with specific error messages
- [x] 02-04-PLAN.md -- Aggregate type encoding: structs, tuples, enums as SMT datatypes, arrays as SMT arrays
- [x] 02-05-PLAN.md -- Full specification parser via syn, old() operator, and cargo verify subcommand with colored output

### Phase 3: Modular Verification
**Goal**: Functions that call other verified functions are verified using contracts as summaries, without inlining callee bodies
**Depends on**: Phase 2
**Requirements**: MOD-01, MOD-02, MOD-03, MOD-04
**Research flag**: No -- Function summaries are an established technique (Dafny, Boogie, Why3, Prusti). Standard assume/assert encoding.
**Plans:** 2 plans
**Success Criteria** (what must be TRUE):
  1. A function `foo` calling a verified function `bar` with `#[requires]`/`#[ensures]` contracts is verified by asserting `bar`'s precondition at the call site and assuming `bar`'s postcondition for the return value, without analyzing `bar`'s body
  2. If a call site violates the callee's precondition, the verifier reports the specific precondition that was violated and the values that caused the violation
  3. Verification of a 10-function call chain completes without exponential blowup because each function is verified against its contract independently
  4. The verifier leverages Rust's ownership guarantees (moved values cannot be used, immutable borrows cannot be mutated) to strengthen verification without additional annotations

Plans:
- [x] 03-01-PLAN.md -- Contract database and inter-procedural call-site encoding (assert precondition, havoc return, assume postcondition)
- [x] 03-02-PLAN.md -- Ownership reasoning integration (move/copy/borrow classification, value preservation for shared borrows)

### Phase 4: Differentiation
**Goal**: Specifications can express properties using unbounded math, ghost state, quantifiers over collections, and mutable borrow reasoning
**Depends on**: Phase 3
**Requirements**: SPEC-02, SPEC-03, SPEC-04, BRW-01, BRW-02, BRW-03
**Research flag**: YES -- Prophecy variables are research-level. Must read Creusot source for exact encoding. POPL 2020 prophecy paper + Creusot POPL 2026 tutorial essential. Quantifier trigger inference is tricky -- study Verus's `#[trigger]` and tunable automation paper.
**Plans:** 4 plans
**Success Criteria** (what must be TRUE):
  1. A specification using `int` (unbounded mathematical integer) proves a property about arithmetic that would be unsound with fixed-width bitvectors (e.g., proving `a + b > a` for positive values without overflow concern)
  2. A `#[ghost]` annotated variable is usable in specifications but completely erased from compiled output -- `cargo build --release` produces identical binary with and without ghost annotations
  3. A specification with `forall(|x: i32| x > 0 ==> f(x) > 0)` or `exists(|x: i32| f(x) == 0)` is parsed, encoded to SMT quantifiers, and verified
  4. A function taking `&mut Vec<i32>` can be specified with `#[ensures(v.len() == old(v.len()) + 1)]` using prophecy variables to reason about the final value of the mutable borrow
  5. A generic function `fn max<T: Ord>(a: T, b: T) -> T` is verified via monomorphization for concrete type instantiations used in the crate

Plans:
- [ ] 04-01-PLAN.md -- Unbounded integers (int/nat), ghost code (#[ghost] attribute), bitvector-to-Int conversion
- [ ] 04-02-PLAN.md -- Quantifier support (forall/exists) with conservative trigger inference and :pattern annotations
- [ ] 04-03-PLAN.md -- Prophecy variables for mutable borrow reasoning (creation, resolution, final_value operator)
- [ ] 04-04-PLAN.md -- Generic function verification via monomorphization (type substitution, per-instantiation VCs)

### Phase 5: Performance and Polish
**Goal**: Verification is fast enough for interactive development and error messages guide developers to fixes
**Depends on**: Phase 4
**Requirements**: TOOL-05, PERF-02, PERF-03, PERF-04, PERF-05
**Research flag**: No -- Standard optimization work. Profile, measure, optimize.
**Success Criteria** (what must be TRUE):
  1. Functions with loops and inter-procedural calls verify in under 5 seconds on the benchmark suite
  2. Re-running `cargo verify` after changing only one function skips re-verification of unchanged functions via VC caching
  3. Verification of a crate with 20+ annotated functions runs solver instances in parallel, completing faster than sequential verification
  4. Verification failure messages include: source file and line number, the specific property that failed, and a counterexample showing concrete values that violate the property
  5. Formula simplification (constant folding, dead code elimination, common subexpression elimination) measurably reduces solver time on the benchmark suite compared to unsimplified formulas
**Plans**: TBD

Plans:
- [ ] 05-01: Benchmark suite and formula simplification
- [ ] 05-02: VC caching and parallel verification
- [ ] 05-03: Error message polish and documentation

## Progress

**Execution Order:**
Phases execute in numeric order: 1 -> 2 -> 3 -> 4 -> 5

| Phase | Plans Complete | Status | Completed |
|-------|----------------|--------|-----------|
| 1. Soundness Foundation | 3/3 | Complete | 2026-02-11 |
| 2. Table Stakes Completion | 5/5 | Complete | 2026-02-11 |
| 3. Modular Verification | 2/2 | Complete | 2026-02-11 |
| 4. Differentiation | 0/4 | Planned | - |
| 5. Performance and Polish | 0/3 | Not started | - |

---
*Roadmap created: 2026-02-10*
*Last updated: 2026-02-11 (Phase 4 planned)*
