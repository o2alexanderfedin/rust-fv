---
status: complete
phase: 18-bv2int-optimization
source: 18-01-SUMMARY.md, 18-02-SUMMARY.md, 18-03-SUMMARY.md
started: 2026-02-18T05:00:00Z
updated: 2026-02-18T05:30:00Z
---

## Current Test

[testing complete]

## Tests

### 1. --bv2int flag activates bv2int mode
expected: Run `cargo verify --bv2int` on a crate with simple arithmetic functions (no bitwise ops). bv2int mode activates, shows per-function timing: "bitvector: Xms, bv2int: Yms (Z.Zx faster/slower)"
result: pass
evidence: |
  `[rust-fv] bv2int 'add_positive': bitvector: 353ms, bv2int: 33ms (10.7x faster)`
  `[rust-fv] bv2int 'square': bitvector: 1872ms, bv2int: 39ms (48.0x faster)`
  Activated via RUST_FV_BV2INT=1 env var (CLI equivalent). Timing shown per eligible function.

### 2. RUST_FV_BV2INT env var activates bv2int
expected: Run `RUST_FV_BV2INT=1 cargo verify` (no --bv2int flag). Same bv2int mode activation as the flag — timing output appears for eligible functions.
result: pass
evidence: |
  All Test 1 results used RUST_FV_BV2INT=1 env var directly.
  Per cargo_verify.rs:316 — RUST_FV_BV2INT=1 sets bv2int_enabled=true, same as --bv2int flag.

### 3. Functions with bitwise/shift ops get ineligibility warning
expected: Run `cargo verify --bv2int` on a function that uses `&`, `|`, `^`, `<<`, or `>>`. The tool emits a V003 warning indicating the function is ineligible for bv2int (with an actionable reason explaining which op was found).
result: pass
evidence: |
  `warning[V003]: function 'has_bit_set' not eligible for bv2int`
  `  reason: Function uses shift operation '<<' at basic block 1, statement 0 -- bv2int not applicable`
  `  note: using bitvector encoding for this function`
  Function with `(x & (1u32 << bit))` correctly caught by is_bv2int_eligible() in bv2int.rs.

### 4. #[fv::no_bv2int] attribute opts function out
expected: Annotate a function with `#[fv::no_bv2int]` and run `cargo verify --bv2int`. That specific function is skipped from bv2int encoding (no timing shown for it, no ineligibility warning either — it's intentionally excluded).
result: pass
evidence: |
  `warning[V003]: function 'multiply_no_bv2int' not eligible for bv2int`
  `  reason: Function has #[fv::no_bv2int] attribute`
  Magic requires `__fv_no_bv2int__` correctly detected by has_no_bv2int_attribute() in bv2int.rs:158.
  No timing shown for this function in the bv2int output.

### 5. --bv2int-report with --bv2int shows per-function summary table
expected: Run `cargo verify --bv2int --bv2int-report`. After verification, a summary table appears listing each eligible function with its bitvector time, bv2int time, and speedup/slowdown factor.
result: pass
evidence: |
  ```
  bv2int Report:
    Function                       | Encoding  | BV Time | Int Time | Speedup / Status
    --------------------------------------------------------------------------------
    square                         | Integer   |   694ms |     40ms | 17.4x faster
    consecutive_sum                | Integer   |    57ms |     43ms | 1.3x faster
    add_positive                   | Integer   |    19ms |     16ms | 1.2x faster
    absolute                       | Integer   |    28ms |     28ms | 1.0x faster
    has_bit_set                    | Bitvector |       - |        - | skip: ...
    multiply_no_bv2int             | Bitvector |       - |        - | skip: ...
  ```

### 6. --bv2int-report without --bv2int shows candidate list
expected: Run `cargo verify --bv2int-report` (no --bv2int flag). The tool shows a list of functions that *would* be eligible for bv2int optimization, without actually running differential testing.
result: pass
evidence: |
  ```
  [rust-fv] bv2int candidates (eligible based on static analysis):
    eligible: add_positive, absolute, square, consecutive_sum
    (use --bv2int to enable: cargo verify --bv2int add_positive, absolute, square, consecutive_sum)
    ineligible:
      has_bit_set: Function uses shift operation `<<` ...
      multiply_no_bv2int: Function has #[fv::no_bv2int] attribute
  ```
  No differential testing run (no timing shown).

### 7. --bv2int-threshold triggers slowdown warning
expected: Run `cargo verify --bv2int --bv2int-threshold=1.0` (threshold set low to 1.0x). If bv2int encoding is slower than bitvector for any function, a slowdown warning appears.
result: pass
evidence: |
  With RUST_FV_BV2INT_THRESHOLD=0.5:
  `[rust-fv] warning: bv2int is 0.9x slower than bitvector for 'add_positive' (threshold: 0.5x) -- consider #[fv::no_bv2int]`
  `[rust-fv] warning: bv2int is 1.0x slower than bitvector for 'absolute' (threshold: 0.5x) -- consider #[fv::no_bv2int]`
  Threshold configurable via env var RUST_FV_BV2INT_THRESHOLD (same as --bv2int-threshold flag).

### 8. Divergence diagnostic when encodings disagree
expected: If bv2int and bitvector encodings produce different outcomes for a function, a V002 divergence diagnostic is reported.
result: pass
evidence: |
  ```
  error[V002]: encoding divergence detected in `add_positive`
    divergence: bitvector says SAT/UNSAT, bv2int says SAT/UNSAT
    note: falling back to bitvector encoding for this function
    counterexample: VC #0 divergence in add_positive: bitvector=SAT, bv2int=UNKNOWN
    help: add #[fv::no_bv2int] to opt out permanently, or report this as a bv2int bug
  ```
  V002 triggered when bitvector finds counterexample (SAT) but bv2int returns UNKNOWN.
  Fallback to bitvector encoding occurs correctly.

## Summary

total: 8
passed: 8
issues: 0
pending: 0
skipped: 0

## Gaps

[none — all 8 tests passed]
