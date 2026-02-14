# Requirements: rust-fv

**Defined:** 2026-02-14
**Core Value:** Sound, automated verification of Rust code properties with minimal developer burden -- if the tool says "verified", it must be mathematically correct; if a developer can write a spec, the tool should prove it automatically 80-90% of the time for safe Rust.

## v0.3 Requirements

Requirements for v0.3 Production Usability milestone. Each maps to roadmap phases.

### Standard Library Support

- [ ] **STDLIB-01**: Developer can verify functions using Vec<T> operations (push, pop, len, get, index) with preloaded contracts
- [ ] **STDLIB-02**: Developer can verify functions using Option<T> / Result<T,E> operations (unwrap, map, and_then, is_some, ok_or) with preloaded contracts
- [ ] **STDLIB-03**: Developer can verify functions using HashMap<K,V> operations (insert, get, remove, contains_key, len) with preloaded contracts
- [ ] **STDLIB-04**: Developer can verify functions using basic Iterator operations (next, collect, map, filter) with preloaded contracts
- [ ] **STDLIB-05**: Developer can override stdlib contracts with custom specifications when needed

### Performance & Solver

- [ ] **PERF-01**: Modified function re-verifies in <1s via enhanced dependency tracking and MIR-hash caching
- [ ] **PERF-02**: Z3 solver state reused across incremental re-verification via push/pop
- [ ] **PERF-03**: Developer can annotate manual triggers with `#[trigger(expr)]` to control quantifier instantiation
- [ ] **PERF-04**: Tool warns when no trigger inferred or trigger contains interpreted symbols
- [ ] **PERF-05**: Developer can enable bv2int optimization for arithmetic-heavy verification via environment variable
- [ ] **PERF-06**: bv2int differential testing ensures equivalence with bitvector encoding

### IDE Integration

- [ ] **IDE-01**: VSCode extension shows inline error highlighting (red squiggles) for verification failures
- [ ] **IDE-02**: VSCode extension shows "Verifying..." status bar indicator with progress
- [ ] **IDE-03**: VSCode extension provides output panel with detailed VC failures and SMT-LIB
- [ ] **IDE-04**: rust-analyzer shows rust-fv diagnostics inline via custom diagnostic source
- [ ] **IDE-05**: rust-analyzer runs `cargo verify` on save via flycheck integration
- [ ] **IDE-06**: VSCode extension published to marketplace with configuration (enable/disable, timeout, Z3 path)

## Future Requirements

Deferred to v0.4+. Tracked but not in current roadmap.

### Advanced Verification

- **ADV-01**: Counterexample generation with concrete failure values
- **ADV-02**: Bounded verification mode (BMC integration)
- **ADV-03**: Weak memory model support (Relaxed, Acquire, Release atomics)
- **ADV-04**: Proof visualization (HTML reports, session trees)
- **ADV-05**: Automatic iterator combinator verification (fold, scan, filter_map)
- **ADV-06**: Separation logic for heap reasoning

### Platform

- **PLAT-01**: Windows support
- **PLAT-02**: Multiple SMT solver backends (CVC5, Yices)

## Out of Scope

| Feature | Reason |
|---------|--------|
| Automatic contract inference | Undecidable for general programs; 40+ years without breakthrough |
| Forked Rust compiler | Zero-friction cargo workflow is key differentiator |
| Custom SMT solver | Z3/CVC5 ecosystem is industry standard |
| Full dependent types | Academic complexity; stick to refinement types |
| Formal proof certificates | Too heavy for developer workflow |
| Full separation logic | Years of research effort; borrow checker handles 95% of cases |

## Traceability

Which phases cover which requirements. Updated during roadmap creation.

| Requirement | Phase | Status |
|-------------|-------|--------|
| STDLIB-01 | Phase 13 | Pending |
| STDLIB-02 | Phase 13 | Pending |
| STDLIB-03 | Phase 13 | Pending |
| STDLIB-04 | Phase 13 | Pending |
| STDLIB-05 | Phase 13 | Pending |
| PERF-01 | Phase 14 | Pending |
| PERF-02 | Phase 14 | Pending |
| PERF-03 | Phase 15 | Pending |
| PERF-04 | Phase 15 | Pending |
| PERF-05 | Phase 18 | Pending |
| PERF-06 | Phase 18 | Pending |
| IDE-01 | Phase 16 | Pending |
| IDE-02 | Phase 16 | Pending |
| IDE-03 | Phase 16 | Pending |
| IDE-04 | Phase 17 | Pending |
| IDE-05 | Phase 17 | Pending |
| IDE-06 | Phase 16 | Pending |

**Coverage:**
- v0.3 requirements: 17 total
- Mapped to phases: 17
- Unmapped: 0

**Coverage validation:** ✓ All requirements mapped to exactly one phase

---
*Requirements defined: 2026-02-14*
*Last updated: 2026-02-14 after roadmap creation*
