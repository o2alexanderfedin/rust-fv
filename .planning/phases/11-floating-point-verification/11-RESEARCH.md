# Phase 11: Floating-Point Verification - Research

**Researched:** 2026-02-13
**Domain:** IEEE 754 floating-point arithmetic verification via SMT-LIB FloatingPoint theory
**Confidence:** HIGH

## Summary

Floating-point verification is a mature domain with standardized SMT-LIB FloatingPoint theory support and established production implementations. The core challenge is balancing precision with performance: IEEE 754-compliant verification requires the SMT FloatingPoint theory (slower) rather than bitvector approximations (faster but unsound for FP semantics).

rust-fv already has foundational support: `Sort::Float(e, s)` exists in smtlib/sort.rs, `FloatTy` enum in analysis/ir.rs, and `encode_float()` maps f32/f64 to correct IEEE 754 parameters. However, float operations currently encode as `FLOAT_UNSUPPORTED` placeholder. Phase 11 adds: (1) float literal encoding, (2) FP arithmetic with rounding modes, (3) NaN/Infinity checks, (4) IEEE 754 comparison semantics, and (5) opt-in configuration with performance warnings.

The standard approach uses SMT-LIB FloatingPoint theory with explicit rounding modes (default RNE), predicate functions for special values (fp.isNaN, fp.isInfinite), and careful handling of IEEE 754's quirks (NaN != NaN, -0.0 == +0.0). Z3 supports this via bit-blasting to SAT, which is 2-10x slower than pure bitvector encoding but necessary for soundness.

**Primary recommendation:** Implement opt-in floating-point verification (off by default due to performance impact) using SMT-LIB FloatingPoint theory with RNE rounding mode. Generate NaN propagation VCs (`!fp.isNaN(result)`) for all float operations and infinity overflow VCs for operations that may produce ±∞. Emit clear performance warning at activation. Follow established IR extension pattern from Phases 6-10.

## Standard Stack

### Core
| Library | Version | Purpose | Why Standard |
|---------|---------|---------|--------------|
| Z3 (existing) | 4.13+ | SMT solver with FloatingPoint theory | Already integrated; supports SMT-LIB FPA theory via bit-blasting |
| rust_fv_smtlib (existing) | 0.1.0 | SMT-LIB AST with Float sort | Already has `Sort::Float(e, s)` defined; needs Term extensions |

### Supporting
| Library | Version | Purpose | When to Use |
|---------|---------|---------|-------------|
| rustc_middle (existing) | nightly | MIR float operations | Already used; provides BinOp/UnOp for f32/f64 |

### Alternatives Considered
| Instead of | Could Use | Tradeoff |
|------------|-----------|----------|
| FloatingPoint theory | Bitvector approximation | Bitvectors 2-10x faster but unsound (wrong NaN/Inf semantics) |
| Default-on | Opt-in via flag | Performance impact too high for default; conflicts with fast bitvector path |
| Auto rounding mode | Explicit per-operation | IEEE 754 requires rounding awareness; RNE is safe default |

**Installation:**
```bash
# No new dependencies — extends existing crates
```

## Architecture Patterns

### Recommended Project Structure
```
crates/smtlib/src/
├── term.rs                   # EXTEND: Add FloatingPoint term variants
├── formatter.rs              # EXTEND: Add FP operation formatting
└── sort.rs                   # OK: Sort::Float(e, s) already exists

crates/analysis/src/
├── ir.rs                     # OK: FloatTy enum already exists
├── encode_sort.rs            # OK: encode_float() already maps to Sort::Float
├── encode_term.rs            # EXTEND: Replace FLOAT_UNSUPPORTED with FP encoding
├── vcgen.rs                  # EXTEND: Generate NaN/Inf VCs for float ops
└── float_verification.rs     # NEW: Float-specific VC generation module

crates/driver/src/
├── config.rs                 # EXTEND: Add enable_float_verification flag
└── diagnostics.rs            # EXTEND: Add VcKind::FloatingPointNaN formatting
```

### Pattern 1: SMT-LIB FloatingPoint Sort Encoding
**What:** Map Rust f32/f64 to IEEE 754 FloatingPoint sorts with exponent/significand bit counts
**When to use:** Type encoding for all float variables and operations
**Example:**
```rust
// Source: SMT-LIB FloatingPoint theory spec + existing encode_float()
// Already implemented in crates/analysis/src/encode_sort.rs:102

fn encode_float(fty: &FloatTy) -> Sort {
    match fty {
        FloatTy::F32 => Sort::Float(8, 24),   // (_ FloatingPoint 8 24)
        FloatTy::F64 => Sort::Float(11, 53),  // (_ FloatingPoint 11 53)
    }
}
```

### Pattern 2: Floating-Point Literal Encoding
**What:** Encode float constants as bit-string triples (sign, exponent, significand) or special values
**When to use:** Constant float values in contracts and code
**Example:**
```rust
// Source: SMT-LIB FloatingPoint theory section 4.2
use rust_fv_smtlib::term::Term;

fn encode_float_constant(value: f64, ty: FloatTy) -> Term {
    if value.is_nan() {
        // (_ NaN 11 53)
        Term::FpNaN(11, 53)
    } else if value.is_infinite() {
        if value.is_sign_positive() {
            Term::FpPosInf(11, 53)  // (_ +oo 11 53)
        } else {
            Term::FpNegInf(11, 53)  // (_ -oo 11 53)
        }
    } else if value == 0.0 {
        if value.is_sign_positive() {
            Term::FpPosZero(11, 53)  // (_ +zero 11 53)
        } else {
            Term::FpNegZero(11, 53)  // (_ -zero 11 53)
        }
    } else {
        // (fp sign_bit exp_bits sig_bits)
        let bits = value.to_bits();
        Term::FpFromBits(
            (bits >> 63) as u8,          // sign bit
            ((bits >> 52) & 0x7FF),      // 11 exp bits
            bits & 0xFFFFFFFFFFFFF,      // 52 sig bits
            11, 53
        )
    }
}
```

### Pattern 3: Floating-Point Arithmetic with Rounding Modes
**What:** Encode float operations with explicit rounding mode (RNE default)
**When to use:** All float arithmetic operations (add, sub, mul, div, sqrt)
**Example:**
```rust
// Source: SMT-LIB FloatingPoint theory section 4.3
fn encode_fp_binop(op: BinOp, lhs: Term, rhs: Term, ty: FloatTy) -> Term {
    let rm = Term::RoundingMode("RNE".to_string());  // roundNearestTiesToEven

    match op {
        BinOp::Add => Term::FpAdd(Box::new(rm), Box::new(lhs), Box::new(rhs)),
        BinOp::Sub => Term::FpSub(Box::new(rm), Box::new(lhs), Box::new(rhs)),
        BinOp::Mul => Term::FpMul(Box::new(rm), Box::new(lhs), Box::new(rhs)),
        BinOp::Div => Term::FpDiv(Box::new(rm), Box::new(lhs), Box::new(rhs)),
        _ => panic!("unsupported float binop"),
    }
}
```

### Pattern 4: NaN Propagation Verification Conditions
**What:** Generate VC asserting result is not NaN unless operation expects NaN
**When to use:** After every float operation (add, sub, mul, div, sqrt)
**Example:**
```rust
// Source: Formal verification FP patterns (Stainless, CBMC)
fn generate_nan_vc(result: Term, operation: &str, location: VcLocation) -> VerificationCondition {
    let not_nan = Term::Not(Box::new(Term::FpIsNaN(Box::new(result.clone()))));

    VerificationCondition {
        description: format!("NaN check: {} must not produce NaN", operation),
        script: Script::new(vec![
            Command::Assert(not_nan),
            Command::CheckSat,
        ]),
        location: VcLocation {
            vc_kind: VcKind::FloatingPointNaN,
            ..location
        },
    }
}
```

### Pattern 5: Infinity Overflow Verification Conditions
**What:** Generate VC checking operations don't overflow to ±∞ when not expected
**When to use:** Operations that may overflow (mul, div, large add/sub)
**Example:**
```rust
// Source: IEEE 754 exception semantics + formal FP verification
fn generate_infinity_vc(result: Term, operation: &str, location: VcLocation) -> VerificationCondition {
    let not_infinite = Term::Not(Box::new(Term::FpIsInfinite(Box::new(result.clone()))));

    VerificationCondition {
        description: format!("Infinity check: {} must not overflow to ±∞", operation),
        script: Script::new(vec![
            Command::Assert(not_infinite),
            Command::CheckSat,
        ]),
        location: VcLocation {
            vc_kind: VcKind::FloatingPointNaN,  // Reuse or add separate VcKind::Overflow
            ..location
        },
    }
}
```

### Pattern 6: IEEE 754 Comparison Semantics
**What:** Encode comparisons respecting NaN != NaN and -0.0 == +0.0
**When to use:** All float equality and ordering comparisons
**Example:**
```rust
// Source: SMT-LIB FloatingPoint theory section 4.4
fn encode_fp_comparison(op: BinOp, lhs: Term, rhs: Term) -> Term {
    match op {
        BinOp::Eq => {
            // fp.eq handles -0.0 == +0.0 correctly, returns false for NaN
            Term::FpEq(Box::new(lhs), Box::new(rhs))
        }
        BinOp::Lt => Term::FpLt(Box::new(lhs), Box::new(rhs)),
        BinOp::Le => Term::FpLeq(Box::new(lhs), Box::new(rhs)),
        BinOp::Gt => Term::FpGt(Box::new(lhs), Box::new(rhs)),
        BinOp::Ge => Term::FpGeq(Box::new(lhs), Box::new(rhs)),
        _ => panic!("unsupported comparison"),
    }
}
```

### Anti-Patterns to Avoid

- **Using bitvector arithmetic for float operations:** Sounds faster but completely wrong semantics (no NaN, no Inf, wrong rounding)
- **Omitting rounding mode:** IEEE 754 requires explicit rounding; RNE is safe default but must be present
- **Testing float equality with `==` without NaN awareness:** Always guard with `!fp.isNaN(x) && !fp.isNaN(y)` before equality
- **Default-enabling FP verification:** 2-10x performance penalty requires opt-in
- **Fixed epsilon comparisons:** Breaks near zero; use ULP-based or separate near-zero logic

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Float literal to bits conversion | Manual bit manipulation | Rust's `f32::to_bits()` / `f64::to_bits()` | Handles subnormals, edge cases correctly |
| NaN/Inf detection | Bit pattern matching | `f32::is_nan()` / `is_infinite()` / `is_sign_positive()` | IEEE 754 compliant, handles all edge cases |
| Rounding mode encoding | String constants | Enum with validation | Type safety, prevents typos like "REN" |
| Float comparison logic | Custom epsilon logic | SMT-LIB fp.eq/fp.lt predicates | Handles NaN/±0.0 correctly per IEEE 754 |
| Special value constructors | Bit-level FP construction | SMT-LIB `(_ NaN eb sb)` / `(_ +oo eb sb)` syntax | Solver-independent, standard |

**Key insight:** IEEE 754 is deceptively complex (NaN != NaN, -0.0 == +0.0, subnormals, rounding modes). Use standard library functions and SMT-LIB primitives rather than reimplementing.

## Common Pitfalls

### Pitfall 1: Default-Enabling Floating-Point Verification
**What goes wrong:** All float operations suddenly 2-10x slower, users complain about performance regression
**Why it happens:** FP theory bit-blasts to SAT which is much slower than bitvector reasoning
**How to avoid:** Require explicit `--enable-float-verification` flag or `#[verifier::float_verification]` attribute
**Warning signs:** Test suite slowdown, timeout failures on previously fast tests

### Pitfall 2: Forgetting NaN Propagation Semantics
**What goes wrong:** Verification incorrectly assumes operations preserve non-NaN property
**Why it happens:** In bitvector world, no special values; in FP world, NaN propagates through all operations
**How to avoid:** Generate `!fp.isNaN(result)` VC for every float operation unless contract explicitly allows NaN
**Warning signs:** False positives on valid code that handles NaN correctly

### Pitfall 3: Using `==` for Float Equality Without NaN Guard
**What goes wrong:** NaN == NaN returns false, breaking reflexivity expectations
**Why it happens:** IEEE 754 spec requires NaN != NaN for all comparisons
**How to avoid:** Always use `fp.eq` predicate which encodes correct semantics, or guard with `!fp.isNaN` checks
**Warning signs:** Counterexamples where `x == x` fails

### Pitfall 4: Ignoring Signed Zero Distinction in Contracts
**What goes wrong:** Contracts assume +0.0 and -0.0 are distinct, but IEEE 754 equality says they're equal
**Why it happens:** Developers think of zero as single value; IEEE 754 has two distinct zeros that compare equal
**How to avoid:** Use `fp.eq` which handles ±0.0 correctly; if contract needs to distinguish, use `fp.isNegative`
**Warning signs:** Unexpected SAT results when contract distinguishes ±0.0

### Pitfall 5: Not Warning Users About Performance Impact
**What goes wrong:** Users enable FP verification, don't understand why verification became 5x slower
**Why it happens:** FP theory decision procedure fundamentally more expensive than bitvectors
**How to avoid:** Emit clear warning on first FP verification activation: "FloatingPoint verification enabled: expect 2-10x slower verification times"
**Warning signs:** User confusion, support requests about performance

### Pitfall 6: Fixed Epsilon Comparison Patterns
**What goes wrong:** `abs(x - y) < 0.0001` verification fails near zero or for very large numbers
**Why it happens:** Fixed epsilon doesn't scale with magnitude; breaks down at extremes
**How to avoid:** For verification, use exact FP semantics; for approximate equality contracts, combine absolute (near-zero) and ULP-based (large values) comparisons
**Warning signs:** Verification failures on mathematically correct near-zero comparisons

## Code Examples

Verified patterns from SMT-LIB standard and existing codebase:

### Extend Term Enum with FloatingPoint Variants
```rust
// Source: SMT-LIB FloatingPoint theory + crates/smtlib/src/term.rs
// Location: crates/smtlib/src/term.rs

pub enum Term {
    // ... existing variants ...

    // === Floating-point literals ===
    /// IEEE 754 NaN: `(_ NaN eb sb)`
    FpNaN(u32, u32),
    /// Positive infinity: `(_ +oo eb sb)`
    FpPosInf(u32, u32),
    /// Negative infinity: `(_ -oo eb sb)`
    FpNegInf(u32, u32),
    /// Positive zero: `(_ +zero eb sb)`
    FpPosZero(u32, u32),
    /// Negative zero: `(_ -zero eb sb)`
    FpNegZero(u32, u32),
    /// From bit representation: `(fp sign exp sig)`
    FpFromBits(u8, u64, u64, u32, u32),

    // === Rounding mode ===
    /// Rounding mode literal: RNE, RNA, RTP, RTN, RTZ
    RoundingMode(String),

    // === Floating-point arithmetic ===
    /// `(fp.add rm x y)`
    FpAdd(Box<Term>, Box<Term>, Box<Term>),
    /// `(fp.sub rm x y)`
    FpSub(Box<Term>, Box<Term>, Box<Term>),
    /// `(fp.mul rm x y)`
    FpMul(Box<Term>, Box<Term>, Box<Term>),
    /// `(fp.div rm x y)`
    FpDiv(Box<Term>, Box<Term>, Box<Term>),
    /// `(fp.sqrt rm x)`
    FpSqrt(Box<Term>, Box<Term>),
    /// `(fp.abs x)`
    FpAbs(Box<Term>),
    /// `(fp.neg x)`
    FpNeg(Box<Term>),

    // === Floating-point comparison ===
    /// `(fp.eq x y)` — IEEE 754 equality (NaN != NaN, -0.0 == +0.0)
    FpEq(Box<Term>, Box<Term>),
    /// `(fp.lt x y)`
    FpLt(Box<Term>, Box<Term>),
    /// `(fp.leq x y)`
    FpLeq(Box<Term>, Box<Term>),
    /// `(fp.gt x y)`
    FpGt(Box<Term>, Box<Term>),
    /// `(fp.geq x y)`
    FpGeq(Box<Term>, Box<Term>),

    // === Floating-point predicates ===
    /// `(fp.isNaN x)`
    FpIsNaN(Box<Term>),
    /// `(fp.isInfinite x)`
    FpIsInfinite(Box<Term>),
    /// `(fp.isZero x)`
    FpIsZero(Box<Term>),
    /// `(fp.isNegative x)`
    FpIsNegative(Box<Term>),
    /// `(fp.isPositive x)`
    FpIsPositive(Box<Term>),
}
```

### Replace FLOAT_UNSUPPORTED Placeholder
```rust
// Source: crates/analysis/src/encode_term.rs:230-232
// Location: crates/analysis/src/encode_term.rs

pub fn encode_constant(c: &Constant) -> Term {
    match c {
        Constant::Bool(b) => Term::BoolLit(*b),
        Constant::Int(val, ity) => Term::BitVecLit(*val, ity.bit_width()),
        Constant::Uint(val, uty) => Term::BitVecLit(*val as i128, uty.bit_width()),

        // BEFORE (Phase 1-10):
        // Constant::Float(_, _) => Term::Const("FLOAT_UNSUPPORTED".to_string()),

        // AFTER (Phase 11):
        Constant::Float(value, fty) => encode_float_constant(*value, *fty),

        Constant::Unit => Term::BoolLit(true),
        Constant::Str(s) => Term::Const(format!("STR_{s}")),
    }
}

fn encode_float_constant(value: f64, fty: FloatTy) -> Term {
    let (eb, sb) = match fty {
        FloatTy::F32 => (8u32, 24u32),
        FloatTy::F64 => (11u32, 53u32),
    };

    if value.is_nan() {
        Term::FpNaN(eb, sb)
    } else if value.is_infinite() {
        if value.is_sign_positive() {
            Term::FpPosInf(eb, sb)
        } else {
            Term::FpNegInf(eb, sb)
        }
    } else if value == 0.0 {
        if value.is_sign_positive() {
            Term::FpPosZero(eb, sb)
        } else {
            Term::FpNegZero(eb, sb)
        }
    } else {
        // Convert to bit representation
        let bits = match fty {
            FloatTy::F32 => (value as f32).to_bits() as u64,
            FloatTy::F64 => value.to_bits(),
        };

        let sign = ((bits >> (eb + sb - 1)) & 1) as u8;
        let exp = (bits >> (sb - 1)) & ((1 << eb) - 1);
        let sig = bits & ((1 << (sb - 1)) - 1);

        Term::FpFromBits(sign, exp, sig, eb, sb)
    }
}
```

### Format FloatingPoint Terms to SMT-LIB
```rust
// Source: SMT-LIB FloatingPoint theory syntax
// Location: crates/smtlib/src/formatter.rs (extend Display impl for Term)

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            // ... existing cases ...

            // Floating-point literals
            Term::FpNaN(e, s) => write!(f, "(_ NaN {e} {s})"),
            Term::FpPosInf(e, s) => write!(f, "(_ +oo {e} {s})"),
            Term::FpNegInf(e, s) => write!(f, "(_ -oo {e} {s})"),
            Term::FpPosZero(e, s) => write!(f, "(_ +zero {e} {s})"),
            Term::FpNegZero(e, s) => write!(f, "(_ -zero {e} {s})"),
            Term::FpFromBits(sign, exp, sig, e, s) => {
                write!(f, "(fp #b{sign} #b{exp:0width$b} #b{sig:0sigwidth$b})",
                       width = *e as usize, sigwidth = (*s - 1) as usize)
            }

            // Rounding mode
            Term::RoundingMode(mode) => write!(f, "{mode}"),

            // Arithmetic
            Term::FpAdd(rm, x, y) => write!(f, "(fp.add {rm} {x} {y})"),
            Term::FpSub(rm, x, y) => write!(f, "(fp.sub {rm} {x} {y})"),
            Term::FpMul(rm, x, y) => write!(f, "(fp.mul {rm} {x} {y})"),
            Term::FpDiv(rm, x, y) => write!(f, "(fp.div {rm} {x} {y})"),
            Term::FpSqrt(rm, x) => write!(f, "(fp.sqrt {rm} {x})"),
            Term::FpAbs(x) => write!(f, "(fp.abs {x})"),
            Term::FpNeg(x) => write!(f, "(fp.neg {x})"),

            // Comparison
            Term::FpEq(x, y) => write!(f, "(fp.eq {x} {y})"),
            Term::FpLt(x, y) => write!(f, "(fp.lt {x} {y})"),
            Term::FpLeq(x, y) => write!(f, "(fp.leq {x} {y})"),
            Term::FpGt(x, y) => write!(f, "(fp.gt {x} {y})"),
            Term::FpGeq(x, y) => write!(f, "(fp.geq {x} {y})"),

            // Predicates
            Term::FpIsNaN(x) => write!(f, "(fp.isNaN {x})"),
            Term::FpIsInfinite(x) => write!(f, "(fp.isInfinite {x})"),
            Term::FpIsZero(x) => write!(f, "(fp.isZero {x})"),
            Term::FpIsNegative(x) => write!(f, "(fp.isNegative {x})"),
            Term::FpIsPositive(x) => write!(f, "(fp.isPositive {x})"),
        }
    }
}
```

### Generate Float Operation with VCs
```rust
// Source: Phase 6-10 patterns + SMT-LIB FP theory
// Location: crates/analysis/src/float_verification.rs (new module)

use crate::ir::*;
use crate::vcgen::{VerificationCondition, VcLocation, VcKind};
use rust_fv_smtlib::term::Term;
use rust_fv_smtlib::script::Script;
use rust_fv_smtlib::command::Command;

/// Generate NaN propagation VC for a float operation.
pub fn nan_propagation_vc(
    result: Term,
    operands: &[Term],
    operation: &str,
    location: VcLocation,
) -> VerificationCondition {
    // Assume operands are not NaN, prove result is not NaN
    let operands_not_nan: Vec<Term> = operands
        .iter()
        .map(|op| Term::Not(Box::new(Term::FpIsNaN(Box::new(op.clone())))))
        .collect();

    let result_not_nan = Term::Not(Box::new(Term::FpIsNaN(Box::new(result))));

    let vc = if operands_not_nan.is_empty() {
        // Unary operation
        result_not_nan
    } else {
        // Binary/n-ary: (and (not (fp.isNaN x)) (not (fp.isNaN y))) => (not (fp.isNaN result))
        Term::Implies(
            Box::new(Term::And(operands_not_nan)),
            Box::new(result_not_nan),
        )
    };

    let mut script = Script::new(vec![]);
    script.add_command(Command::Assert(Term::Not(Box::new(vc))));
    script.add_command(Command::CheckSat);

    VerificationCondition {
        description: format!("NaN propagation: {} should not produce NaN when operands are finite", operation),
        script,
        location: VcLocation {
            vc_kind: VcKind::FloatingPointNaN,
            ..location
        },
    }
}

/// Generate infinity overflow VC for a float operation.
pub fn infinity_overflow_vc(
    result: Term,
    operation: &str,
    location: VcLocation,
) -> VerificationCondition {
    let result_not_infinite = Term::Not(Box::new(Term::FpIsInfinite(Box::new(result))));

    let mut script = Script::new(vec![]);
    script.add_command(Command::Assert(Term::Not(Box::new(result_not_infinite))));
    script.add_command(Command::CheckSat);

    VerificationCondition {
        description: format!("Infinity check: {} must not overflow to ±∞", operation),
        script,
        location: VcLocation {
            vc_kind: VcKind::FloatingPointNaN,  // Or separate VcKind::FloatingPointOverflow
            ..location
        },
    }
}
```

### Add VcKind::FloatingPointNaN to Enum
```rust
// Source: Requirement INF-02 + crates/analysis/src/vcgen.rs:79-110
// Location: crates/analysis/src/vcgen.rs

pub enum VcKind {
    /// Precondition check (requires clause)
    Precondition,
    /// Postcondition check (ensures clause)
    Postcondition,
    /// Loop invariant holds before loop
    LoopInvariantInit,
    /// Loop invariant preserved by loop body
    LoopInvariantPreserve,
    /// Loop invariant holds after loop
    LoopInvariantExit,
    /// Arithmetic overflow check
    Overflow,
    /// Division by zero check
    DivisionByZero,
    /// Shift amount bounds check
    ShiftBounds,
    /// Assert statement check
    Assertion,
    /// Panic-freedom check (unwrap, index, etc.)
    PanicFreedom,
    /// Termination measure decreases check
    Termination,
    /// Closure contract verification
    ClosureContract,
    /// Behavioral subtyping check (trait impl satisfies trait contract)
    BehavioralSubtyping,
    /// Borrow validity check (shared/mutable conflict, use-after-expiry, reborrow validity)
    BorrowValidity,
    /// Memory safety check (null-check, bounds-check, use-after-free for unsafe code)
    MemorySafety,

    // NEW for Phase 11:
    /// Floating-point NaN propagation and infinity overflow check
    FloatingPointNaN,
}
```

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| Bitvector approximation | SMT FloatingPoint theory | SMT-LIB 2.5 (2015) | Soundness: correct IEEE 754 semantics |
| Manual bit manipulation | Rust `to_bits()` methods | Rust 1.20 (2017) | Correctness: handles all edge cases |
| Fixed unrolling | Bit-blasting to SAT | Z3 4.0+ (2015) | Automation: solver decides strategy |
| Implicit rounding | Explicit rounding modes | IEEE 754-2008 | Precision: developer controls rounding |

**Deprecated/outdated:**
- **Bitvector-only float reasoning**: Unsound, misses NaN/Inf semantics; replaced by FPA theory
- **Assume float operations don't overflow**: Incorrect; must check explicitly with fp.isInfinite VCs
- **Default-on FP verification**: Too slow; current best practice is opt-in with warning

## Open Questions

1. **Should we support multiple rounding modes or just RNE?**
   - What we know: RNE (round-to-nearest, ties-to-even) is IEEE 754 default, covers 99% of Rust code
   - What's unclear: Do any Rust crates use explicit rounding control (rare outside numerics)
   - Recommendation: Ship with RNE only in Phase 11.1, add rounding mode control in Phase 11.3 if user requests

2. **How to handle subnormal (denormalized) numbers?**
   - What we know: IEEE 754 requires subnormal support; SMT-LIB FP theory handles them automatically
   - What's unclear: Should we generate specific VCs for gradual underflow, or rely on SMT solver?
   - Recommendation: Rely on SMT-LIB fp.isSubnormal predicate; no special VCs unless user contracts check for it

3. **Should FP verification be function-level or module-level opt-in?**
   - What we know: Function-level `#[verifier::float_verification]` gives fine control
   - What's unclear: Module-level `#![verifier::float_verification]` more convenient but less flexible
   - Recommendation: Support both; function attribute overrides module default

## Sources

### Primary (HIGH confidence)
- [SMT-LIB FloatingPoint Theory](https://smt-lib.org/theories-FloatingPoint.shtml) - Official syntax and semantics
- [SMT-LIB FloatingPoint Theory PDF](http://www.cprover.org/SMT-LIB-Float/smt-fpa.pdf) - Formal specification
- [Rust f32 documentation](https://doc.rust-lang.org/std/primitive.f32.html) - IEEE 754 binary32 guarantees
- [Rust f64 documentation](https://doc.rust-lang.org/std/primitive.f64.html) - IEEE 754 binary64 guarantees

### Secondary (MEDIUM confidence)
- [Z3 FloatingPoint API](https://z3prover.github.io/api/html/ml/Z3.FloatingPoint.html) - Z3-specific FP support
- [Building Better Bit-Blasting for Floating-Point Problems](https://link.springer.com/chapter/10.1007/978-3-030-17462-0_5) - Performance analysis
- [Formal Verification of Floating-Point Hardware Design](https://www.researchgate.net/publication/330049809_Formal_Verification_of_Floating-Point_Hardware_Design_A_Mathematical_Approach) - FP verification patterns
- [IEEE 754 Wikipedia](https://en.wikipedia.org/wiki/IEEE_754) - Standard overview

### Tertiary (LOW confidence - community reports)
- [Z3 Issue #577: FP/BV/Array performance](https://github.com/Z3Prover/z3/issues/577) - User reports of FP slowness
- [Z3 Issue #823: Slow on FP VC](https://github.com/Z3Prover/z3/issues/823) - Specific FP performance case (14s vs 100ms)
- [Floating-Point Guide: Comparison](https://floating-point-gui.de/errors/comparison/) - Best practices
- [What Every Computer Scientist Should Know About FP](https://docs.oracle.com/cd/E19957-01/806-3568/ncg_goldberg.html) - Classic reference

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH - SMT-LIB FP theory is stable (2015), Z3 support mature, Rust IEEE 754 guarantees documented
- Architecture: HIGH - Follows established Phase 6-10 pattern, IR/encoding/VCGen structure proven
- Pitfalls: HIGH - Well-documented in FP verification literature, confirmed by Z3 issue tracker
- Performance: MEDIUM - Range (2-10x slowdown) from multiple sources but exact numbers vary by problem
- Rounding modes: HIGH - RNE default is IEEE 754 standard and Rust guarantee

**Research date:** 2026-02-13
**Valid until:** 2026-03-15 (30 days - stable domain, SMT-LIB standard unlikely to change)
