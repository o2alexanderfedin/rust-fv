# bv2int Optimization Reference

**Summary:** The bv2int optimization switches eligible functions from bitvector SMT encoding (QF\_BV) to integer arithmetic encoding (QF\_LIA / QF\_NIA). When applicable, this can significantly reduce solver time for arithmetic-heavy verification tasks.

---

## When to Use

Use `--bv2int` when verifying functions that:

- Perform **pure arithmetic** — addition, subtraction, multiplication, division, modulo
- Work with **integer ranges** and modular arithmetic (e.g. wrapping add, checked arithmetic)
- Have specifications expressed in linear or nonlinear integer arithmetic
- **Do not** use bitwise or shift operations

**Good candidates:**

```rust
#[requires(a >= 0 && b >= 0)]
#[ensures(result == a + b)]
fn add(a: i64, b: i64) -> i64 { a + b }

#[requires(n >= 1)]
#[ensures(result >= n)]
fn factorial(n: u64) -> u64 { /* ... */ }
```

**Poor candidates (will be skipped automatically):**

```rust
fn bitflags(x: u32) -> u32 { x & 0xFF }   // bitwise op — IneligibilityReason::BitwiseOp
fn shift_key(x: u64, n: u32) -> u64 { x << n }  // shift op — IneligibilityReason::ShiftOp
```

The eligibility check runs automatically per-function. Functions that use bitwise or shift operations are silently kept in bitvector mode — no manual exclusion needed.

---

## How to Activate

**Via CLI flag (recommended):**

```sh
cargo verify --bv2int
```

**Via environment variable:**

```sh
RUST_FV_BV2INT=1 cargo verify
```

CLI flag takes precedence over the environment variable.

**To see per-function timing and encoding decisions:**

```sh
cargo verify --bv2int --bv2int-report
```

The report shows which functions used integer encoding, which were skipped (with reason), and the speedup factor for each verified function.

**Without `--bv2int`, to preview eligible candidate functions:**

```sh
cargo verify --bv2int-report
```

---

## Known Limitations

### Ineligibility Conditions

A function is ineligible for bv2int if it contains any of the following MIR operations:

| `IneligibilityReason` variant | Operations | Example |
|-------------------------------|-----------|---------|
| `BitwiseOp { op_symbol, location }` | `&`, `\|`, `^` | `x & mask` |
| `ShiftOp { op_symbol, location }` | `<<`, `>>` | `bits >> 4` |
| `OptOut` | `#[fv::no_bv2int]` attribute | Explicit opt-out |

The eligibility check (`is_bv2int_eligible`) is conservative: if any ineligible operation is detected anywhere in the function body, the entire function stays in bitvector mode. Partial encoding is not supported.

### Soundness

When bv2int is active, both encoding modes are tested via differential testing:

- Bitvector encoding (QF\_BV) and integer encoding (QF\_LIA/QF\_NIA) are run separately
- If both return UNSAT, the result is accepted (equivalence confirmed)
- If results diverge (one SAT, one UNSAT), a `V002` divergence diagnostic is emitted and the bitvector result is used as ground truth

This means bv2int results are sound: a verified result under integer encoding implies verified under bitvector encoding (divergence is caught and reported).

### No Float Support

Functions using floating-point types are not eligible for bv2int. Float operations remain in bitvector (IEEE 754) encoding regardless of `--bv2int`.

### Wrapping Arithmetic

For wrapping arithmetic, the integer encoding adds modular constraints (e.g. `result mod 2^N`) per Rust RFC 0560. These constraints preserve correctness but may reduce the QF\_LIA speedup compared to pure unbounded integer arithmetic.

---

## Performance Characteristics

### When bv2int Helps

- Functions with many arithmetic operations and few control flow branches
- Verification conditions that are long chains of linear equalities/inequalities
- Specifications using `+`, `-`, `*`, `/` on bounded integer ranges
- Functions where Z3's QF\_LIA solver is faster than the QF\_BV solver (common for large bit widths like `i64`, `u64`)

### When bv2int Hurts

- Functions with both arithmetic and bitwise operations (automatically skipped, so no impact)
- Complex modular arithmetic requiring many modular constraints (wrapping reduces the benefit)
- Short functions where solver overhead dominates — bv2int adds differential-testing overhead

### Slowdown Detection

If bv2int is **slower** than bitvector encoding by more than the configured threshold, a warning is emitted:

```
warning[V001]: bv2int slowdown: 3.2x slower than bitvector (threshold: 2.0x) for function `foo`
```

Default threshold: `2.0` (bv2int must be at most 2x slower before warning).

---

## Environment Variables

| Variable | Default | Description |
|----------|---------|-------------|
| `RUST_FV_BV2INT` | unset | Set to `1` to enable bv2int (same as `--bv2int`) |
| `RUST_FV_BV2INT_REPORT` | unset | Set to `1` to enable timing report (same as `--bv2int-report`) |
| `RUST_FV_BV2INT_THRESHOLD` | `2.0` | Slowdown warning threshold (same as `--bv2int-threshold`) |

**Examples:**

```sh
# Enable bv2int with default threshold
RUST_FV_BV2INT=1 cargo verify

# Enable bv2int with report and custom threshold (warn only if 5x slower)
RUST_FV_BV2INT=1 RUST_FV_BV2INT_REPORT=1 RUST_FV_BV2INT_THRESHOLD=5.0 cargo verify

# Equivalent using CLI flags
cargo verify --bv2int --bv2int-report --bv2int-threshold 5.0
```

---

## Source References

- Eligibility logic and `IneligibilityReason` variants: `crates/analysis/src/bv2int.rs`
- CLI flag parsing: `crates/driver/src/cargo_verify.rs` (`parse_bv2int_flag`, `parse_bv2int_report_flag`, `parse_bv2int_threshold`)
- Differential testing: `crates/analysis/src/differential.rs` (`test_encoding_equivalence`)
- Slowdown warning: `crates/driver/src/output.rs` (`check_slowdown_warning`)
- Divergence diagnostic (V002): `crates/driver/src/diagnostics.rs` (`report_bv2int_divergence`)
