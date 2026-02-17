# Roadmap: rust-fv

## Milestones

- ✅ **v0.1 Formal Verification POC** - Phases 1-5 (shipped 2026-02-12)
- ✅ **v0.2 Advanced Verification** - Phases 6-12 (shipped 2026-02-14)
- ✅ **v0.3 Production Usability** - Phases 13-18 (shipped 2026-02-17)

## Phases

<details>
<summary>✅ v0.1 Formal Verification POC (Phases 1-5) - SHIPPED 2026-02-12</summary>

Delivered sound, automated formal verification tool for Rust with 37/37 requirements shipped -- from soundness foundations through performance optimization, covering control flow, loops, assertions, structs, inter-procedural verification, ownership reasoning, quantifiers, ghost code, prophecy variables, generics, caching, parallelism, and IDE-ready diagnostics.

**Key accomplishments:**
- Path-sensitive VCGen with soundness/completeness test suites (44 regression tests)
- Loop invariant verification with classical 3-VC approach
- Modular inter-procedural verification with ownership-aware contract summaries
- Quantified specifications (forall/exists) with automatic trigger inference
- Generic function verification via monomorphization
- Production-quality cargo verify with incremental caching and parallel verification

**Tests:** 1,741 passing | **LOC:** 43,621 Rust across 53 files | **Timeline:** 2 days

</details>

<details>
<summary>✅ v0.2 Advanced Verification (Phases 6-12) - SHIPPED 2026-02-14</summary>

Extended formal verification to cover all major Rust language features -- recursive functions, closures, trait objects, lifetimes, unsafe code, floating-point arithmetic, and concurrent programs. All 44/44 v0.2 requirements implemented with 523 new tests.

**Key accomplishments:**
- Recursive function verification with termination measures and Tarjan's SCC
- Closure verification via defunctionalization (Reynolds 1972)
- Trait object verification with behavioral subtyping (LSP)
- Lifetime reasoning with NLL tracking and nested prophecy variables
- Unsafe code detection with heap-as-array memory model
- IEEE 754 floating-point verification with SMT FPA theory
- Bounded concurrency verification with happens-before encoding

**Tests:** 2,264 passing | **LOC:** 66,133 Rust across 77 files | **Timeline:** 3 days

</details>

<details>
<summary>✅ v0.3 Production Usability (Phases 13-18) - SHIPPED 2026-02-17</summary>

Made rust-fv production-ready with standard library contracts, sub-second incremental verification, VSCode/rust-analyzer IDE integration, manual trigger customization, and bv2int arithmetic solver optimization. All 17/17 v0.3 requirements implemented.

**Key accomplishments:**
- Standard library contracts (Vec, HashMap, Option, Result, Iterator) with SMT Seq theory and proptest oracle validation
- Incremental verification with <1s re-verification via dual-hash MIR+contract cache and transitive invalidation
- Manual trigger customization (`#[trigger(expr)]`) with self-instantiation detection and interpreted symbol warnings
- VSCode extension with inline diagnostics, status bar, output panel, SMT-LIB viewer, and Z3 bundling
- rust-analyzer integration via `--message-format=json`, flycheck `overrideCommand`, and diagnostic deduplication
- bv2int optimization with `--bv2int` activation, differential testing, `--bv2int-report` summary table, and slowdown warnings

**Tests:** 1,613 lib tests passing | **LOC:** 82,642 Rust + TypeScript VSCode extension | **Timeline:** 3 days

Plans:
- [x] 13-01-PLAN.md — SMT sequence theory infrastructure + stdlib contract data model
- [x] 13-02-PLAN.md — Vec, Option, Result contracts (TDD)
- [x] 13-03-PLAN.md — HashMap, Iterator, String/str/slice contracts (TDD)
- [x] 13-04-PLAN.md — Contract loading, override mechanism, CLI integration
- [x] 13-05-PLAN.md — Oracle tests (proptest) + E2E integration tests
- [x] 14-01-PLAN.md — Dual-hash cache infrastructure + transitive invalidation engine
- [x] 14-02-PLAN.md — Pipeline integration, per-function status, cargo verify clean
- [x] 14-03-PLAN.md — Benchmark suite + incremental correctness tests
- [x] 14-04-PLAN.md — E2E performance benchmark on real 1000-line codebase
- [x] 15-01-PLAN.md — Trigger validation engine (TDD) + Rustc-style diagnostics (V015-V018)
- [x] 15-02-PLAN.md — Trigger annotation parsing in spec_parser + IR propagation (TDD)
- [x] 15-03-PLAN.md — Pipeline integration, verbose mode, and integration tests
- [x] 16-01-PLAN.md — Extension scaffolding + core verification loop with diagnostics and status bar
- [x] 16-02-PLAN.md — Output panel with structured failure reports, SMT-LIB command, and gutter decorations
- [x] 16-03-PLAN.md — Z3 bundling, packaging scripts, auto-install prompt, and marketplace preparation
- [x] 17-01-PLAN.md — Rustc-compatible JSON diagnostic output for cargo verify (--message-format=json)
- [x] 17-02-PLAN.md — VSCode extension RA mode detection, overrideCommand, deduplication, gutter updates
- [x] 18-01-PLAN.md — Core bv2int encoding infrastructure (EncodingMode, applicability analysis, integer encoding with overflow guards)
- [x] 18-02-PLAN.md — Differential testing engine and equivalence caching
- [x] 18-03-PLAN.md — CLI/env integration, --bv2int-report, pipeline wiring, output formatting

</details>

## Progress

| Phase | Milestone | Plans Complete | Status | Completed |
|-------|-----------|----------------|--------|-----------|
| 1. Soundness Foundation | v0.1 | 3/3 | Complete | 2026-02-10 |
| 2. Control Flow & Loops | v0.1 | 3/3 | Complete | 2026-02-10 |
| 3. Modular Verification | v0.1 | 3/3 | Complete | 2026-02-11 |
| 4. Quantifiers & Prophecy | v0.1 | 4/4 | Complete | 2026-02-11 |
| 5. Production Pipeline | v0.1 | 4/4 | Complete | 2026-02-12 |
| 6. Recursive Functions | v0.2 | 3/3 | Complete | 2026-02-12 |
| 7. Closures | v0.2 | 3/3 | Complete | 2026-02-12 |
| 8. Trait Objects | v0.2 | 3/3 | Complete | 2026-02-13 |
| 9. Lifetimes & Borrows | v0.2 | 3/3 | Complete | 2026-02-13 |
| 10. Unsafe Code | v0.2 | 3/3 | Complete | 2026-02-13 |
| 11. Floating Point | v0.2 | 3/3 | Complete | 2026-02-14 |
| 12. Concurrency | v0.2 | 3/3 | Complete | 2026-02-14 |
| 13. Standard Library Contracts | v0.3 | 5/5 | Complete | 2026-02-15 |
| 14. Incremental Verification | v0.3 | 4/4 | Complete | 2026-02-15 |
| 15. Trigger Customization | v0.3 | 3/3 | Complete | 2026-02-16 |
| 16. VSCode Extension | v0.3 | 3/3 | Complete | 2026-02-16 |
| 17. rust-analyzer Integration | v0.3 | 2/2 | Complete | 2026-02-17 |
| 18. bv2int Optimization | v0.3 | 3/3 | Complete | 2026-02-17 |

---

*Roadmap created: 2026-02-14*
*Last updated: 2026-02-17 after v0.3 milestone completion*
