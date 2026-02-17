# Roadmap: rust-fv

## Milestones

- ✅ **v0.1 Formal Verification POC** - Phases 1-5 (shipped 2026-02-12)
- ✅ **v0.2 Advanced Verification** - Phases 6-12 (shipped 2026-02-14)
- 🚧 **v0.3 Production Usability** - Phases 13-18 (in progress)

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

### 🚧 v0.3 Production Usability (In Progress)

**Milestone Goal:** Make existing verification capabilities production-ready with standard library support, performance tuning, IDE integration, and solver optimization.

#### Phase 13: Standard Library Contracts

**Goal**: Developer can verify real-world Rust code using Vec, HashMap, Option, Result, and Iterator operations with preloaded contracts

**Depends on**: Phase 12 (v0.2 complete)

**Requirements**: STDLIB-01, STDLIB-02, STDLIB-03, STDLIB-04, STDLIB-05

**Success Criteria** (what must be TRUE):
  1. Developer can verify functions using Vec<T> operations (push, pop, len, get) without writing stdlib contracts
  2. Developer can verify functions using Option<T> and Result<T,E> operations (unwrap, map, is_some, ok_or) with automatic contract loading
  3. Developer can verify functions using HashMap<K,V> operations (insert, get, remove, contains_key) with preloaded specifications
  4. Developer can verify functions using Iterator operations (next, collect, map, filter) with working contracts
  5. Developer can override stdlib contracts with custom specifications when stdlib contracts are insufficient

**Plans:** 5 plans

Plans:
- [x] 13-01-PLAN.md — SMT sequence theory infrastructure + stdlib contract data model
- [x] 13-02-PLAN.md — Vec, Option, Result contracts (TDD)
- [x] 13-03-PLAN.md — HashMap, Iterator, String/str/slice contracts (TDD)
- [x] 13-04-PLAN.md — Contract loading, override mechanism, CLI integration
- [x] 13-05-PLAN.md — Oracle tests (proptest) + E2E integration tests

---

#### Phase 14: Incremental Verification

**Goal**: Modified function re-verifies in <1s via enhanced dependency tracking and MIR-hash caching, enabling real-time IDE feedback

**Depends on**: Phase 13

**Requirements**: PERF-01, PERF-02

**Success Criteria** (what must be TRUE):
  1. Changing single function body re-verifies in <1s for 1000-line codebase via MIR-hash caching
  2. Unchanged functions skip re-verification entirely using VC cache with correct invalidation
  3. Z3 solver state persists across verification runs via push/pop for incremental solving
  4. Benchmark suite demonstrates 20-30x speedup compared to full re-verification
  5. Incremental verification never produces different results than full verification (cache invalidation is sound)

NOTE: Success criteria #3 is OVERRIDDEN by user decision -- cache VC results only, no Z3 push/pop persistence.

**Plans:** 4 plans

Plans:
- [ ] 14-01-PLAN.md — Dual-hash cache infrastructure + transitive invalidation engine
- [ ] 14-02-PLAN.md — Pipeline integration, per-function status, cargo verify clean
- [ ] 14-03-PLAN.md — Benchmark suite + incremental correctness tests
- [ ] 14-04-PLAN.md — E2E performance benchmark on real 1000-line codebase (gap closure)

---

#### Phase 15: Trigger Customization

**Goal**: Developer can manually control quantifier instantiation with `#[trigger]` attribute when automatic inference fails, with diagnostics preventing common mistakes

**Depends on**: Phase 13 (stdlib contracts exercise quantifiers heavily)

**Requirements**: PERF-03, PERF-04

**Success Criteria** (what must be TRUE):
  1. Developer can annotate quantified expressions with `#[trigger(expr)]` to specify manual instantiation patterns
  2. Tool warns when no trigger is inferred or trigger contains interpreted symbols (arithmetic, equality)
  3. Static analysis detects and prevents self-instantiating trigger patterns that cause infinite loops
  4. Manual triggers override automatic inference when present, falling back to auto-inference on validation failure
  5. Error messages provide concrete examples of good triggers when validation fails

**Plans:** 3/3 plans complete

Plans:
- [ ] 15-01-PLAN.md — Trigger validation engine (TDD) + Rustc-style diagnostics (V015-V018)
- [ ] 15-02-PLAN.md — Trigger annotation parsing in spec_parser + IR propagation (TDD)
- [ ] 15-03-PLAN.md — Pipeline integration, verbose mode, and integration tests

---

#### Phase 16: VSCode Extension

**Goal**: Developer receives real-time verification feedback in VSCode with inline diagnostics, status indicators, and detailed error reporting

**Depends on**: Phase 14 (incremental verification makes <1s feedback feasible)

**Requirements**: IDE-01, IDE-02, IDE-03, IDE-06

**Success Criteria** (what must be TRUE):
  1. VSCode extension shows red squiggles for verification failures with hover descriptions
  2. Status bar displays "Verifying..." indicator with progress during verification runs
  3. Output panel provides detailed verification failure messages including VC failures and SMT-LIB
  4. Extension is published to VSCode marketplace with configuration for enable/disable, timeout, and Z3 path
  5. File changes trigger re-verification automatically with debouncing to avoid typing latency

**Plans:** 3 plans

Plans:
- [ ] 16-01-PLAN.md — Extension scaffolding + core verification loop with diagnostics and status bar
- [ ] 16-02-PLAN.md — Output panel with structured failure reports, SMT-LIB command, and gutter decorations
- [ ] 16-03-PLAN.md — Z3 bundling, packaging scripts, auto-install prompt, and marketplace preparation

---

#### Phase 17: rust-analyzer Integration

**Goal**: rust-analyzer displays rust-fv diagnostics inline via custom diagnostic source and runs cargo verify on save

**Depends on**: Phase 16 (VSCode extension established)

**Requirements**: IDE-04, IDE-05

**Success Criteria** (what must be TRUE):
  1. rust-analyzer shows rust-fv diagnostics inline alongside rustc errors with custom diagnostic source
  2. Saving file triggers `cargo verify` automatically via flycheck integration
  3. rust-fv diagnostics appear within 2s of file save for typical functions
  4. Diagnostics from rust-fv are visually distinguished from rustc diagnostics
  5. User can disable rust-fv integration via rust-analyzer settings

**Plans:** 2 plans

Plans:
- [ ] 17-01-PLAN.md — Rustc-compatible JSON diagnostic output for cargo verify (--message-format=json)
- [ ] 17-02-PLAN.md — VSCode extension RA mode detection, overrideCommand, deduplication, gutter updates

---

#### Phase 18: bv2int Optimization

**Goal**: Developer can enable bv2int optimization for arithmetic-heavy verification with proven equivalence and performance measurement

**Depends on**: Phase 15 (trigger customization), Phase 17 (rust-analyzer integration complete)

**Requirements**: PERF-05, PERF-06

**Success Criteria** (what must be TRUE):
  1. Developer can enable bv2int optimization via RUST_FV_BV2INT=1 environment variable
  2. Differential testing suite proves equivalence between bitvector and bv2int encodings across all test cases
  3. Conservative applicability analysis restricts bv2int to arithmetic-only verification (no bitwise operations)
  4. Performance regression tests detect cases where bv2int causes slowdowns (>2x slower triggers warning)
  5. Documentation clearly explains when/how to use bv2int and known limitations

**Plans:** 3/3 plans complete

Plans:
- [ ] 18-01-PLAN.md — Core bv2int encoding infrastructure (EncodingMode, applicability analysis, integer encoding with overflow guards)
- [ ] 18-02-PLAN.md — Differential testing engine and equivalence caching
- [ ] 18-03-PLAN.md — CLI/env integration, --bv2int-report, pipeline wiring, output formatting

---

## Progress

**Execution Order:**
Phases execute in numeric order: 13 → 14 → 15 → 16 → 17 → 18

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
| 14. Incremental Verification | v0.3 | 0/3 | Not started | - |
| 15. Trigger Customization | v0.3 | Complete    | 2026-02-16 | - |
| 16. VSCode Extension | v0.3 | 3/3 | Complete | 2026-02-16 |
| 17. rust-analyzer Integration | v0.3 | 0/2 | Not started | - |
| 18. bv2int Optimization | v0.3 | Complete    | 2026-02-17 | - |

---

*Roadmap created: 2026-02-14*
*Last updated: 2026-02-16 after Phase 17 planning*
