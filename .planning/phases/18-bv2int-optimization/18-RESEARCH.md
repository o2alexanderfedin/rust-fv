# Phase 18: bv2int Optimization - Research

**Researched:** 2026-02-16
**Domain:** SMT solver optimization for arithmetic-heavy verification via bitvector-to-integer encoding
**Confidence:** MEDIUM

## Summary

Phase 18 enables bv2int optimization to replace bitvector SMT encoding with integer arithmetic encoding for arithmetic-heavy verification tasks. Research reveals this is a well-established SMT technique with proven performance benefits for specific workloads, but requires careful soundness preservation, conservative applicability analysis, and equivalence testing.

The optimization leverages Z3's built-in `bv2int` and `int2bv` conversion functions to translate bitvector operations to unbounded integer arithmetic, which can be significantly faster for arithmetic-dominated formulas (potential 4-5x speedup). However, bitwise operations (&, |, ^, <<, >>) cannot be naturally represented in integer arithmetic without expensive encodings, making conservative applicability analysis critical.

**Primary recommendation:** Implement bv2int as an opt-in per-function optimization with automatic differential testing to ensure equivalence, storing results in Phase 14's existing cache infrastructure (dual-hash model with 30-day TTL). Focus on safety-first conservative analysis that rejects functions with any bitwise operations.

<user_constraints>
## User Constraints (from CONTEXT.md)

### Locked Decisions

#### Activation & Controls
- Both CLI flag (--bv2int) and environment variable (RUST_FV_BV2INT=1) supported, CLI takes precedence
- Global enable with per-function opt-out via #[fv::no_bv2int] attribute
- Auto-detect eligible functions and suggest bv2int candidates in output (user enables manually)
- When enabled globally, warn per ineligible function explaining why bv2int was skipped (not silent fallback)

#### Equivalence Reporting
- Divergence between bitvector and bv2int encodings reported as error with counterexample showing specific input
- Equivalence testing runs automatically on first use of bv2int for a function
- Results cached per function content hash — only re-check when function changes
- Always show timing comparison: both encoding times and speedup factor (e.g., "bitvector: 1.2s, bv2int: 0.3s (4x faster)")

#### Applicability Boundaries
- Eligibility excludes only bitwise operations (&, |, ^, <<, >>) — most permissive approach (arithmetic + comparisons allowed)
- Mixed expressions: Claude's discretion toward safety and precision (conservative approach for soundness)
- Overflow semantics: Claude's discretion toward safety and precision (sound approach based on SMT semantics)
- Rejection messages: Claude's discretion toward safety and precision (detailed enough for developer action)

#### Performance Feedback
- Regression detection uses stored bitvector baseline, compares against bv2int run
- Summary report mode: rust-fv --bv2int-report showing table of all functions with encoding, time, speedup
- Slowdown warning threshold is configurable via env var or CLI flag (default 2x)
- Auto-detect suggestions: Claude's discretion — no speculative estimates, candidate list based on static analysis

### Claude's Discretion

- Mixed expression handling strategy (entire function vs per-expression) — lean toward safety
- Overflow guard implementation for wrapping arithmetic — choose sound approach
- Rejection message detail level — provide actionable information
- Auto-detect suggestion format — practical without speculative speedup estimates
- Baseline storage format and location — consistent with incremental verification cache (Phase 14)

### Deferred Ideas (OUT OF SCOPE)

None — discussion stayed within phase scope

</user_constraints>

<phase_requirements>
## Phase Requirements

| ID | Description | Research Support |
|----|-------------|-----------------|
| PERF-05 | Developer can enable bv2int optimization for arithmetic-heavy verification via environment variable | Z3's native bv2int/int2bv conversion functions enable this. Z3 API documentation confirms Z3_OP_BV2INT and Z3_OP_INT2BV operators exist. Implementation pattern: add encoding mode flag to VcGen, wrap bitvector terms with bv2int calls. |
| PERF-06 | bv2int differential testing ensures equivalence with bitvector encoding | Counterexample-guided verification pattern well-established. Run both encodings on same VC, compare SAT/UNSAT results. If divergent, extract counterexample from SAT encoding and test against other. Cache results using Phase 14's existing dual-hash model (mir_hash + contract_hash). |

</phase_requirements>

## Standard Stack

### Core

| Library | Version | Purpose | Why Standard |
|---------|---------|---------|--------------|
| Z3 (z3 crate) | 0.13+ | SMT solver with native bv2int support | Used throughout rust-fv; Z3_OP_BV2INT and Z3_OP_INT2BV operators built-in |
| rust-fv-smtlib | current | SMT-LIB AST representation | Existing infrastructure for term construction and manipulation |
| sha2 | current (from Phase 14) | SHA-256 hashing for cache keys | Already used in cache.rs for dual-hash model |
| serde_json | current | Cache serialization | Already used for CacheEntry persistence |

### Supporting

| Library | Version | Purpose | When to Use |
|---------|---------|---------|-------------|
| rust-fv-analysis | current | IR and encoding infrastructure | Extend encode_binop/encode_unop to support integer encoding mode |
| tracing | current | Debug logging | Log bv2int decisions and differential test results |

### Alternatives Considered

| Instead of | Could Use | Tradeoff |
|------------|-----------|----------|
| Z3 native API | CVC5 CLI with custom conversion | CVC5 uses ubv_to_int (unsigned only), Z3 has both bv2int (signed) and bv2nat (unsigned). Z3 already integrated with native API. |
| Function-level caching | VC-level caching | Function-level matches Phase 14's cache granularity and user's "per function content hash" decision. |

**Installation:**
No new dependencies required — all components already present in rust-fv workspace.

## Architecture Patterns

### Recommended Project Structure

```
crates/analysis/src/
├── encode_term.rs        # Add bv2int encoding mode
├── encode_sort.rs        # Add Int sort mapping
├── bv2int.rs             # New: applicability analysis & conversion logic
└── differential.rs       # New: equivalence testing infrastructure

crates/driver/src/
├── cache.rs              # Extend CacheEntry with bv2int_equiv_tested: bool
└── config.rs             # Add bv2int flags (CLI + env var)
```

### Pattern 1: Encoding Mode Selection

**What:** VcGen parameterized by encoding mode (Bitvector vs Integer)

**When to use:** At VC generation time, choose encoding based on function eligibility and user flags

**Example:**
```rust
pub enum EncodingMode {
    Bitvector,  // Default: use BitVec sorts
    Integer,    // bv2int: use Int sorts with conversion guards
}

pub fn encode_binop_with_mode(
    op: BinOp,
    lhs: &Term,
    rhs: &Term,
    ty: &Ty,
    mode: EncodingMode,
) -> Term {
    match mode {
        EncodingMode::Bitvector => encode_binop(op, lhs, rhs, ty),
        EncodingMode::Integer => encode_binop_as_int(op, lhs, rhs, ty),
    }
}
```

### Pattern 2: Conservative Applicability Analysis

**What:** Static analysis of function IR to determine bv2int eligibility

**When to use:** Before enabling bv2int, scan IR for disqualifying operations

**Example:**
```rust
pub fn is_bv2int_eligible(func: &Function) -> Result<(), IneligibilityReason> {
    // Scan all operations in function
    for bb in &func.basic_blocks {
        for stmt in &bb.statements {
            if let Some(op) = extract_binop(stmt) {
                if matches!(op, BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr) {
                    return Err(IneligibilityReason::BitwiseOperation(op));
                }
            }
        }
    }
    Ok(())
}
```

### Pattern 3: Differential Testing with Caching

**What:** Run both encodings, compare results, cache equivalence

**When to use:** First time bv2int is used for a function (or after function changes)

**Example:**
```rust
pub struct EquivalenceResult {
    pub equivalent: bool,
    pub bitvec_time_ms: u64,
    pub bv2int_time_ms: u64,
    pub counterexample: Option<Model>,
}

pub fn test_equivalence(
    func: &Function,
    cache: &mut VcCache,
) -> EquivalenceResult {
    // Check cache first
    if let Some(cached) = cache.get_equivalence_result(func) {
        return cached;
    }

    // Run both encodings
    let (bv_result, bv_time) = verify_with_mode(func, EncodingMode::Bitvector);
    let (int_result, int_time) = verify_with_mode(func, EncodingMode::Integer);

    // Compare
    let equiv = match (bv_result, int_result) {
        (Unsat, Unsat) => true,
        (Sat(m1), Sat(m2)) => models_agree(&m1, &m2),
        _ => false,  // Divergence detected
    };

    // Cache and return
    let result = EquivalenceResult { equivalent: equiv, ... };
    cache.store_equivalence_result(func, &result);
    result
}
```

### Anti-Patterns to Avoid

- **Silent fallback:** Don't silently fall back to bitvector encoding when bv2int is ineligible — user requested transparency via "warn per ineligible function"
- **Speculative speedup estimates:** Auto-detect candidates should not include estimated speedup (user decision: "no speculative estimates")
- **Whole-program bv2int:** Don't convert non-arithmetic operations to integers (expensive and unsound for bitwise ops)

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Bitvector ↔ Integer conversion | Custom wrapping/unwrapping | Z3's bv2int/int2bv operators | Z3 handles bit-width, signedness, modular arithmetic semantics correctly. Custom implementation risks soundness bugs. |
| Overflow guards for wrapping arithmetic | Ad-hoc modulo constraints | Rust's overflow semantics + bv2int bounds | Rust RFC 0560 defines precise overflow behavior. Match MIR semantics exactly. |
| Equivalence testing infrastructure | New cache format | Extend Phase 14 CacheEntry | Dual-hash model (mir_hash + contract_hash) already handles function change detection. Reuse existing 30-day TTL and eviction logic. |
| Bitwise operation encoding in integers | Boolean arithmetic simulation | Reject functions with bitwise ops | SMT literature confirms: "operations that involve boolean arithmetic cannot be tackled by an integer solver natively, so they need to be simulated using integer arithmetic" — expensive and complex. Conservative rejection is safer. |

**Key insight:** bv2int is a solver-level optimization, not a verification technique. Leverage Z3's built-in support rather than reimplementing conversion logic.

## Common Pitfalls

### Pitfall 1: Overflow Semantics Mismatch

**What goes wrong:** Bitvector operations have modular arithmetic (wrapping), but SMT Int is unbounded. Without proper guards, `i32::MAX + 1` would succeed in integer encoding but panic in bitvector encoding.

**Why it happens:** Z3's Int theory has no overflow — it represents mathematical integers. Rust integers have defined wrapping/checked/saturating modes.

**How to avoid:**
- For wrapping arithmetic (default in Rust --release), add explicit modulo constraints: `(mod (+ a b) (2^32))`
- For checked arithmetic, add overflow predicates as separate VCs
- Follow Rust RFC 0560 semantics exactly: "operations +, -, * can underflow and overflow. When checking is disabled this will two's complement wrap."

**Warning signs:** Differential testing shows SAT/UNSAT divergence on arithmetic-heavy functions

### Pitfall 2: Bitwise Operations in Integer Encoding

**What goes wrong:** Attempting to encode `x & y` or `x << 3` using integer arithmetic produces exponentially complex formulas with quantifiers.

**Why it happens:** SMT literature: "operators like bitwise AND and OR don't have natural representations in integer arithmetic. While definable using function encodings, such translation is expensive."

**How to avoid:**
- Conservative static analysis: reject any function containing BinOp::BitAnd, BitOr, BitXor, Shl, Shr
- Entire-function rejection (not per-expression) for simplicity and predictability
- Clear rejection message: "Function uses bitwise operation `&` at line X — bv2int optimization not applicable"

**Warning signs:** User reports verification slowdown with bv2int enabled, or equivalence testing times out

### Pitfall 3: Cache Invalidation Races

**What goes wrong:** Function body changes but equivalence result is stale, or equivalence test runs multiple times for same function.

**Why it happens:** Concurrent cache access or insufficient granularity in cache keys.

**How to avoid:**
- Reuse Phase 14's dual-hash model: mir_hash (function body) + contract_hash (specs)
- Store equivalence result in CacheEntry with timestamp
- Re-test equivalence whenever mir_hash changes (body modification)
- Implement cache locking for equivalence testing (prevent duplicate runs)

**Warning signs:** Equivalence errors on unchanged functions, or CI logs show redundant equivalence tests

### Pitfall 4: bv2nat vs bv2int Confusion

**What goes wrong:** Using unsigned conversion for signed integers or vice versa produces wrong results.

**Why it happens:** Z3 historically aliased bv2int → bv2nat (unsigned). SMT-LIB 2.7 standardized ubv_to_int (unsigned) and sbv_to_int (signed).

**How to avoid:**
- For Rust unsigned types (u8, u16, u32, u64, u128, usize): use Z3_OP_BV2NAT or ubv_to_int
- For Rust signed types (i8, i16, i32, i64, i128, isize): use Z3_OP_BV2INT or sbv_to_int (two's complement)
- Map Ty::Uint → unsigned conversion, Ty::Int → signed conversion

**Warning signs:** Differential testing shows model discrepancies on negative values

## Code Examples

Verified patterns from research and existing codebase:

### Conservative Eligibility Check

```rust
// Source: Research findings + existing encode_term.rs patterns
pub fn check_bv2int_eligibility(func: &Function) -> Result<(), String> {
    for bb in &func.basic_blocks {
        for stmt in &bb.statements {
            if let Statement::Assign(_, rvalue) = stmt {
                if let Rvalue::BinaryOp(op, _, _) = rvalue {
                    match op {
                        BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor => {
                            return Err(format!(
                                "Bitwise operation {:?} at {:?} — bv2int not applicable",
                                op, stmt.source_info
                            ));
                        }
                        BinOp::Shl | BinOp::Shr => {
                            return Err(format!(
                                "Shift operation {:?} at {:?} — bv2int not applicable",
                                op, stmt.source_info
                            ));
                        }
                        _ => {} // Arithmetic and comparisons are OK
                    }
                }
            }
        }
    }
    Ok(())
}
```

### Integer Encoding with Overflow Guards

```rust
// Source: Existing encode_term.rs + Rust RFC 0560 overflow semantics
pub fn encode_binop_as_int(op: BinOp, lhs: &Term, rhs: &Term, ty: &Ty) -> Term {
    let width = ty.bit_width().expect("bv2int only for fixed-width integers");
    let lhs_int = Term::BV2Int(Box::new(lhs.clone()), ty.is_signed());
    let rhs_int = Term::BV2Int(Box::new(rhs.clone()), ty.is_signed());

    let result = match op {
        BinOp::Add => Term::IntAdd(Box::new(lhs_int), Box::new(rhs_int)),
        BinOp::Sub => Term::IntSub(Box::new(lhs_int), Box::new(rhs_int)),
        BinOp::Mul => Term::IntMul(Box::new(lhs_int), Box::new(rhs_int)),
        BinOp::Div => if ty.is_signed() {
            Term::IntDiv(Box::new(lhs_int), Box::new(rhs_int))
        } else {
            Term::IntDiv(Box::new(lhs_int), Box::new(rhs_int))
        },
        _ => panic!("Non-arithmetic op in integer encoding"),
    };

    // Wrapping arithmetic: apply modulo
    let modulus = Term::IntLit(1i128 << width);
    let wrapped = Term::IntMod(Box::new(result), Box::new(modulus));

    // Convert back to bitvector
    Term::Int2BV(Box::new(wrapped), width)
}
```

### Differential Testing Pattern

```rust
// Source: Research on counterexample-guided refinement + existing solver.rs patterns
pub fn verify_with_differential_test(
    func: &Function,
    cache: &mut VcCache,
) -> VerificationResult {
    // Check cache for previous equivalence result
    let cache_key = cache.compute_mir_hash(&func.name, &format!("{:?}", func));
    if let Some(entry) = cache.get(&cache_key) {
        if entry.bv2int_equiv_tested {
            // Equivalence confirmed previously, use faster encoding
            return verify_with_mode(func, EncodingMode::Integer);
        }
    }

    // First use: run differential test
    let bv_start = Instant::now();
    let bv_result = verify_with_mode(func, EncodingMode::Bitvector);
    let bv_time_ms = bv_start.elapsed().as_millis() as u64;

    let int_start = Instant::now();
    let int_result = verify_with_mode(func, EncodingMode::Integer);
    let int_time_ms = int_start.elapsed().as_millis() as u64;

    // Compare results
    match (&bv_result, &int_result) {
        (Unsat, Unsat) => {
            // Equivalent — cache success
            cache.store_equivalence(func, true, bv_time_ms, int_time_ms);
            println!("✓ Equivalence confirmed (bitvector: {}ms, bv2int: {}ms, {:.1}x speedup)",
                bv_time_ms, int_time_ms, bv_time_ms as f64 / int_time_ms as f64);
            int_result
        }
        (Sat(m1), Sat(m2)) if models_agree(m1, m2) => {
            cache.store_equivalence(func, true, bv_time_ms, int_time_ms);
            int_result
        }
        _ => {
            // Divergence detected — report error
            eprintln!("✗ Encoding divergence detected in {}", func.name);
            eprintln!("  Bitvector: {:?}, bv2int: {:?}", bv_result, int_result);
            cache.store_equivalence(func, false, bv_time_ms, int_time_ms);
            bv_result  // Fall back to bitvector encoding
        }
    }
}
```

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| Manual tactic application in Z3 Python API | Z3 native API with direct operator calls | Z3 4.0+ (2015) | Rust z3 crate exposes native API — no need for Python wrapper or tactic strings |
| bv2nat only (unsigned) | bv2int (signed) + bv2nat (unsigned) | SMT-LIB 2.7 (2021) | Proper signed/unsigned distinction now standardized |
| Bitvector-only encoding for all integer types | Hybrid bitvector/integer encoding based on workload | Active research (2020-2025) | Arithmetic-heavy workloads show 4-5x speedup with integer encoding |
| Eager bitblasting (always convert to SAT) | Lazy bitblasting + theory solvers | Z3 2.0+ (2010) | Z3 decides encoding strategy automatically based on formula structure |

**Deprecated/outdated:**
- Python z3 tactic strings like "bv2int" — use native API with Z3_OP_BV2INT operator instead
- Assuming bv2int is always faster — research shows it's workload-dependent (arithmetic vs bitwise)

## Open Questions

1. **What granularity for mixed expressions?**
   - What we know: User decided "Claude's discretion toward safety" and "entire function vs per-expression"
   - What's unclear: Should we reject entire function if any bitwise op present, or encode bitvector subterms and integer arithmetic separately?
   - Recommendation: Entire-function rejection for simplicity and predictability. Conservative analysis is safer, and per-expression mode adds significant complexity (tracking which variables are bitvector vs integer).

2. **How to handle function calls in bv2int mode?**
   - What we know: Phase 3 uses function summaries (contracts as black boxes)
   - What's unclear: If caller uses bv2int encoding but callee was verified with bitvector, do encodings compose soundly?
   - Recommendation: Require both caller and callee to use same encoding mode. Propagate encoding mode transitively through call graph. Reject bv2int if any transitive callee is ineligible.

3. **Cache storage location for equivalence results?**
   - What we know: User decided "consistent with incremental verification cache (Phase 14)"
   - What's unclear: Extend CacheEntry struct or separate .equiv.json files?
   - Recommendation: Extend CacheEntry with fields `bv2int_equiv_tested: bool`, `bv2int_speedup_factor: Option<f64>`. Single JSON file per function maintains cache coherence.

## Sources

### Primary (HIGH confidence)

- [Z3 API Documentation](https://z3prover.github.io/api/html/group__capi.html) - Z3_OP_BV2INT and Z3_OP_INT2BV operators
- [Online Z3 Guide - Tactics](https://microsoft.github.io/z3guide/docs/strategies/tactics/) - Built-in tactics reference
- [SMT-LIB Fixed-Size Bitvectors Theory](https://smt-lib.org/theories-FixedSizeBitVectors.shtml) - bv2int/bv2nat semantics
- [Rust RFC 0560: Integer Overflow](https://rust-lang.github.io/rfcs/0560-integer-overflow.html) - Definitive overflow semantics
- Existing codebase: `crates/solver/src/backend.rs`, `crates/analysis/src/encode_term.rs`, `crates/driver/src/cache.rs`

### Secondary (MEDIUM confidence)

- [Understanding Bit-vector Arithmetic in Z3](https://repository.tudelft.nl/file/File_0517332f-750c-464e-ad27-0a144d8f672f) - TU Delft thesis on Z3 bitvector handling
- [SMT-LIB bv/integer conversions discussion](https://groups.google.com/g/smt-lib/c/-GJG1Pq61hI) - Community insights on bv2int vs bv2nat
- [Z3 Issue #1481: bv2int and int2bv slow?](https://github.com/Z3Prover/z3/issues/1481) - Performance discussion
- [Constraints in Dynamic Symbolic Execution: Bitvectors or Integers?](https://srg.doc.ic.ac.uk/files/papers/intbv-tap-19.pdf) - TAP 2019 paper on encoding tradeoffs
- [Counterexample-Guided Bit-Precision Selection](https://link.springer.com/chapter/10.1007/978-3-319-71237-6_26) - CAV 2017 paper on precision refinement
- [Incremental Computation via Function Caching](https://dl.acm.org/doi/10.1145/75277.75305) - POPL 1989 foundational work on function-level caching

### Tertiary (LOW confidence)

- [Bit-Vector Optimization](https://link.springer.com/chapter/10.1007/978-3-662-49674-9_53) - TACAS 2016 paper on OMT for bitvectors
- [Parametric Bit-Vectors](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2025.4) - SAT 2025 paper on bit-width independent verification
- WebSearch results on SMT solver tactics and performance tuning (multiple sources, awaiting verification)

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH - Z3 bv2int/int2bv operators confirmed via official API docs, existing solver integration tested
- Architecture: MEDIUM - Patterns based on existing encode_term.rs and cache.rs, but bv2int-specific logic is new
- Pitfalls: HIGH - Overflow semantics from Rust RFC 0560, bitwise encoding complexity from SMT literature, cache races from Phase 14 lessons learned

**Research date:** 2026-02-16
**Valid until:** 2026-03-16 (30 days for SMT solver stability, Z3 API unlikely to change rapidly)
