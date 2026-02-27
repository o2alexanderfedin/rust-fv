---
created: 2026-02-27T02:51:59.278Z
title: Fix v0.1 milestone tech debt and human-pending items
area: planning
files:
  - .planning/phases/14-incremental-verification/14-VERIFICATION.md
  - .planning/phases/18-bv2int-optimization/18-VERIFICATION.md
  - .planning/phases/10-unsafe-code-detection/10-VERIFICATION.md
  - .planning/phases/15-trigger-customization/15-VERIFICATION.md
  - .planning/phases/11-floating-point-verification/11-VERIFICATION.md
  - .planning/v0.1-MILESTONE-AUDIT.md
---

## Problem

The v0.1 milestone audit (2026-02-27, status: tech_debt) identified the following non-blocking items that need resolution before archiving the milestone:

**Phase 14 — E2E incremental perf test (environment constraint)**
- `e2e_incremental_body_change_under_1s` and `e2e_no_change_all_cached` tests are `#[ignore]`d because they require a live Rust toolchain + Z3 in the test environment
- The 1083-line e2e-bench crate is fully implemented; only the actual hardware measurement is missing
- Need to run: `cargo test -p rust-fv-driver --test e2e_performance -- --ignored --nocapture`
- Expected: <1s re-verification, 85%+ cache hit rate, 99%+ cache hit when no changes

**Phase 18 — bv2int docs format decision (product decision)**
- Criterion: "Documentation clearly explains when/how to use bv2int and known limitations"
- Inline docs exist: `--help` text in `crates/driver/src/cargo_verify.rs` lines 486-529, module doc comments in `bv2int.rs` lines 1-9
- Open question: is inline sufficient, or should a standalone `docs/bv2int.md` be created?
- Decision affects whether Phase 18 score changes from 4/5 → 5/5

**Phase 10, 15 — minor edge cases (documented but not E2E tested)**
- Phase 10: 12 DEBTLINES in VERIFICATION.md about raw pointer aliasing edge cases
- Phase 15: 9 DEBTLINES about trigger interaction edge cases with complex quantifier schemas

**Phase 11 — placeholder terms (by design, but worth documenting clearly)**
- Float VCs use placeholder terms (lhs/rhs/result) — intentional infrastructure design
- Real IEEE 754 encoding pipeline in `encode_term.rs` is complete
- Status: PASS WITH NOTES — no fix needed, but design rationale could be better documented

## Solution

1. **Phase 14:** Set up a proper CI environment with Z3 installed and run the `e2e_performance` tests un-ignored. If they pass (<1s), remove `#[ignore]` and commit. If they fail, diagnose bottleneck (rustc overhead vs verification subsystem).

2. **Phase 18:** Make product decision — recommend creating `docs/bv2int.md` as a short user-facing reference (when to use, limitations, env vars). Would close the 4/5 → 5/5 gap. Update Phase 18 VERIFICATION.md status to `passed` after.

3. **Phase 10, 15:** Review DEBTLINES and determine if any need code fixes or if they're acceptable long-term documentation.

4. **Phase 11:** No code change needed — design is correct. Consider adding a brief architecture note in `encode_term.rs` or `float_verification.rs` explaining the placeholder strategy.

After all items resolved: re-run `/gsd:audit-milestone` and upgrade status from `tech_debt` → `passed`, then run `/gsd:complete-milestone v0.1`.
