---
created: 2026-02-27T20:30:30.345Z
title: Emphasize annotations are optional in README
area: docs
files:
  - README.md (root — NOT docs/README.md)
---

## Problem

The README.md currently leads with annotations (requires/ensures/invariant) from the very beginning, giving the impression they are required to use the tool. This may deter users who don't know SMT or contract-style specifications.

The key selling point — that rust-fv **infers SMT constraints directly from Rust code** with zero annotations — is not prominently communicated. Users should understand they can get value immediately without writing a single annotation, and that annotations are an *optional* enhancement for finer-grained verification.

## Solution

Restructure or augment the README.md to:
1. Lead with the zero-annotation workflow: "run `cargo verify` on your existing Rust code"
2. Show a before/after showing inferred verification working out of the box
3. Move the annotations section to a later "Advanced" or "Enhancing Verification" section
4. Add a clear callout box or sentence near the top: "Annotations are optional — rust-fv infers SMT constraints from your code automatically"
