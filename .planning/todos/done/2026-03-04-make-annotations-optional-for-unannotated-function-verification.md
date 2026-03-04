---
created: 2026-03-04T01:16:22.074Z
title: Make annotations optional for unannotated function verification
area: general
files:
  - src/callbacks.rs
  - src/driver.rs
---

## Problem

When running `cargo verify` (via `hupyy-rust-verify.sh`) on a crate with no `#[requires]`/`#[ensures]` annotations, the tool reports "No annotated functions found" and verifies 0 functions — even though the function `pub fn add(a: i64, b: i64) -> i64 { a + b }` should be verifiable.

**Reproduction:**

```bash
# Minimal crate with no annotations
cat > /tmp/test-crate/src/lib.rs <<'EOF'
pub fn add(a: i64, b: i64) -> i64 { a + b }
EOF

RUST_FV_DRIVER=.../rust-fv-driver \
CARGO_VERIFY=.../cargo-verify \
DYLD_LIBRARY_PATH=.../.rustup/toolchains/nightly-2026-02-11-aarch64-apple-darwin/lib \
.../hupyy-rust-verify.sh --input /tmp/test-crate
```

**Actual output:**
```
[rust-fv] Verifying 0 functions (4 parallel threads)...
No annotated functions found.
=== Verification complete (exit 0) ===
```

**Expected output:** `add` is verified (at least trivially — no preconditions, postcondition = true).

## Solution

The annotation filter in the driver/callbacks should treat unannotated public functions as having trivial contracts (no preconditions, postcondition = true) rather than skipping them entirely. Options:

1. Add a `--verify-all` flag to `cargo verify` that includes unannotated functions with default contracts
2. Change default behavior so annotations are optional — any `pub fn` is included unless explicitly excluded
3. Auto-infer trivial `#[ensures(true)]` for unannotated functions during the analysis pass

The callbacks.rs function collection logic likely filters on presence of `#[requires]`/`#[ensures]` attrs — relax this filter.
