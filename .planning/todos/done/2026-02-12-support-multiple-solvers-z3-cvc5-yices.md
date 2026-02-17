---
created: 2026-02-12T07:16:19.835Z
title: Support multiple solvers: Z3, CVC5, Yices
area: solver
files:
  - crates/solver/src/lib.rs
  - crates/solver/src/z3.rs
---

## Problem

Currently rust-fv only supports Z3 as the SMT solver backend. For broader compatibility, performance comparison, and resilience, we should support multiple SMT solvers: Z3, CVC5, and Yices. This would allow users to choose their preferred solver and potentially cross-validate verification results across solvers.

The solver crate already has a strategy pattern (Z3 via CLI, Z3 via bindings) that could be extended to CVC5 and Yices backends.

## Solution

Extend the solver crate's strategy pattern to support CVC5 and Yices:
- CVC5: Already has CLI approach pattern from v0.1 (CVC5 CLI strategy exists)
- Yices: Add as new backend, uses SMT-LIB2 format (compatible with existing smtlib crate)
- Allow solver selection via CLI flag (`--solver z3|cvc5|yices`) or config
- Ensure all three produce consistent results on the SMT-LIB2 scripts we generate
