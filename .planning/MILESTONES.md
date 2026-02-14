# Milestones

## v0.1 Formal Verification POC (Shipped: 2026-02-12)

**Phases completed:** 5 phases, 17 plans
**Tests:** 1,741 passing (0 failures)
**Lines of code:** 43,621 Rust across 53 source files
**Timeline:** 2 days (2026-02-10 to 2026-02-11)
**Feature commits:** 33

**Key accomplishments:**
1. Path-sensitive VCGen with soundness/completeness test suites (44 regression tests proving both soundness and completeness)
2. Loop invariant verification with classical 3-VC approach (initialization, preservation, sufficiency)
3. Modular inter-procedural verification with Rust ownership-aware contract summaries
4. Quantified specifications (forall/exists) with automatic trigger inference for SMT instantiation
5. Generic function verification via monomorphization with per-instantiation VCs
6. Production-quality cargo verify with incremental caching, parallel verification, and rustc-style error diagnostics

**Delivered:** Sound, automated formal verification tool for Rust with 37/37 requirements shipped -- from soundness foundations through performance optimization, covering control flow, loops, assertions, structs, inter-procedural verification, ownership reasoning, quantifiers, ghost code, prophecy variables, generics, caching, parallelism, and IDE-ready diagnostics.

---


## v0.2 Advanced Verification (Shipped: 2026-02-14)

**Phases completed:** 7 phases (6-12), 21 plans
**Tests:** 2,264 passing (0 failures), up from 1,741 in v0.1
**Lines of code:** 66,133 Rust across 77 source files (up from 43,621)
**Timeline:** 3 days (2026-02-12 to 2026-02-14)
**New LOC:** ~22,500 (+52% over v0.1)

**Key accomplishments:**
1. Recursive function verification with `#[decreases]` termination measures and Tarjan's SCC mutual recursion detection via petgraph
2. Closure verification via defunctionalization (Reynolds 1972) with Fn/FnMut/FnOnce support and explicit environment encoding
3. Trait object verification with behavioral subtyping (LSP), sealed trait closed-world analysis, and open-world uninterpreted encoding
4. Lifetime and borrow reasoning with NLL-based tracking, transitive outlives resolution, reborrow chain detection, and nested prophecy variables
5. Unsafe code detection with heap-as-array memory model, null/bounds checks, `#[verifier::trusted]` trust boundaries, and provenance tracking
6. IEEE 754 floating-point verification with SMT FPA theory, NaN propagation and infinity overflow VCs, and one-time performance warning
7. Bounded concurrency verification with happens-before encoding for all 5 C11 atomic orderings, data race freedom VCs, lock invariant verification, Tarjan's SCC deadlock detection, and channel safety

**Delivered:** Extended formal verification to cover all major Rust language features -- recursive functions, closures, trait objects, lifetimes, unsafe code, floating-point arithmetic, and concurrent programs. All 44/44 v0.2 requirements implemented with 523 new tests and comprehensive E2E validation.

---

