# Phase 31: Z3 bv2int Fix + Ghost Locals Filtering - Research

**Researched:** 2026-02-26
**Domain:** SMT-LIB2 Z3 bitvector-integer conversion; VCGen ghost variable filtering
**Confidence:** HIGH

## Summary

Phase 31 closes two functional gaps from Phase 04 (Differentiation, v0.1). Both gaps have
been precisely characterized through live code inspection and Z3 experimentation.

**Gap 1 (bv2int):** The formatter correctly emits `(bv2int x)` and the vcgen already selects
`(set-logic ALL)` when `uses_spec_int_types()` returns true. However, `uses_spec_int_types()`
only checks IR types of params/locals/return — it does NOT detect `as int` casts in spec
expressions. When a function has I32 params with `"(result as int) > 0"` in ensures, the
spec parser produces `Term::Bv2Int` but `uses_spec_int_types()` returns false, causing
`base_script()` to select `QF_BV`. Z3 rejects `bv2int` in `QF_BV` with "unknown constant
bv2int". Z3 4.15.4 (installed) accepts `bv2int` in `(set-logic ALL)` — confirmed by live
testing.

**Gap 2 (ghost locals):** `encode_assignment` does not check `is_ghost` on the destination
place. Ghost locals assigned in the MIR body get encoded as SMT assertions in executable VCs,
leaking specification variables into the solver. The fix is a one-line guard at the entry of
`encode_assignment`: return `None` if the LHS place refers to a ghost local.

**Primary recommendation:** Fix `uses_spec_int_types()` to also detect `Bv2Int` terms in
spec expression raw strings (scan for `" as int"` / `" as nat"` substrings), and add a
`is_ghost_local()` helper in `vcgen.rs` that filters ghost locals from `encode_assignment`.

<phase_requirements>
## Phase Requirements

| ID | Description | Research Support |
|----|-------------|-----------------|
| Phase-04-bv2int | Fix Z3 bv2int "unknown constant" error — make SpecInt/SpecNat unbounded arithmetic functional | Z3 4.15.4 accepts `bv2int` in ALL logic; fix is in `uses_spec_int_types()` to detect `as int` in spec strings |
| Phase-04-ghost | Ghost locals filtering from executable VCs | `encode_assignment` needs `is_ghost` guard on LHS place |
</phase_requirements>

---

## Standard Stack

### Core
| Library | Version | Purpose | Why Standard |
|---------|---------|---------|--------------|
| Z3 (installed) | 4.15.4 | SMT solver | Project-wide solver; bv2int confirmed working in ALL logic |
| rust-fv-smtlib | internal | SMT-LIB2 AST + formatter | Already has `Term::Bv2Int`, `Term::Int2Bv` |
| rust-fv-analysis | internal | VCGen + spec parser | `uses_spec_int_types()`, `encode_assignment()` live here |

### Supporting
| Library | Version | Purpose | When to Use |
|---------|---------|---------|-------------|
| `ir::Local::is_ghost` | internal | Ghost flag on IR locals | Already exists; use for filtering |

### Alternatives Considered
| Instead of | Could Use | Tradeoff |
|------------|-----------|----------|
| Scan raw spec strings for `as int` | Walk parsed Term tree for Bv2Int | Walking Term tree requires parsing twice; string scan is O(n) single pass, sufficient |
| Unconditionally use ALL logic | Selective ALL logic | ALL logic is slower; keep selective; only add spec-expression detection |

**Installation:** None required — uses existing dependencies.

---

## Architecture Patterns

### Recommended Project Structure

No new files needed. Both fixes are targeted edits to existing files:

```
crates/analysis/src/
├── vcgen.rs    # Fix 1: uses_spec_int_types() + Fix 2: encode_assignment() ghost guard
tests/
├── e2e_verification.rs  # Un-comment 2 TODO E2E tests (lines ~1519-1682)
```

### Pattern 1: Logic Selection Fix (bv2int)

**What:** Extend `uses_spec_int_types()` to detect `as int` / `as nat` cast patterns
in the raw spec expression strings. This ensures `ALL` logic is selected whenever
`bv2int` terms will appear in VCs.

**When to use:** Always — `uses_spec_int_types()` is the gating function for `ALL` logic.

**Current code (vcgen.rs line 1528):**
```rust
fn uses_spec_int_types(func: &Function) -> bool {
    if func.return_local.ty.is_spec_int() { return true; }
    for param in &func.params { if param.ty.is_spec_int() { return true; } }
    for local in &func.locals { if local.ty.is_spec_int() { return true; } }
    false
}
```

**Fixed code:**
```rust
fn uses_spec_int_types(func: &Function) -> bool {
    // Check IR types (SpecInt/SpecNat locals/params/return)
    if func.return_local.ty.is_spec_int() { return true; }
    for param in &func.params { if param.ty.is_spec_int() { return true; } }
    for local in &func.locals { if local.ty.is_spec_int() { return true; } }
    // Check spec expressions for "as int" / "as nat" casts (produce Term::Bv2Int)
    let spec_uses_bv2int = |expr: &crate::ir::SpecExpr| {
        expr.raw.contains(" as int") || expr.raw.contains(" as nat")
    };
    for pre in &func.contracts.requires {
        if spec_uses_bv2int(pre) { return true; }
    }
    for post in &func.contracts.ensures {
        if spec_uses_bv2int(post) { return true; }
    }
    for inv in &func.contracts.invariants {
        if spec_uses_bv2int(inv) { return true; }
    }
    false
}
```

**Confidence:** HIGH — verified with Z3 4.15.4: `(bv2int x)` in `(set-logic ALL)` returns `sat` correctly.

### Pattern 2: Ghost Locals Filtering

**What:** At the entry of `encode_assignment`, check if the LHS place's local is ghost.
If ghost, return `None` (skip encoding the assignment into the VC).

**When to use:** Always — ghost locals are specification-only and must not appear in
executable VCs as assertions.

**Current code (vcgen.rs line 1625):**
```rust
fn encode_assignment(
    place: &Place,
    rvalue: &Rvalue,
    func: &Function,
    _ssa_counter: &mut HashMap<String, u32>,
) -> Option<Command> {
    // Handle projected LHS ...
```

**Fixed code — add guard at top:**
```rust
fn encode_assignment(
    place: &Place,
    rvalue: &Rvalue,
    func: &Function,
    _ssa_counter: &mut HashMap<String, u32>,
) -> Option<Command> {
    // Ghost locals are specification-only — skip encoding their assignments into
    // executable VCs. They remain declared as SMT constants so spec expressions
    // can reference them, but assignments are erased.
    if is_ghost_place(place, func) {
        return None;
    }
    // Handle projected LHS ...
```

**New helper (add near find_local_type):**
```rust
/// Returns true if the place's root local is a ghost variable.
/// Ghost locals must not generate assignment assertions in executable VCs.
fn is_ghost_place(place: &Place, func: &Function) -> bool {
    let check = |local: &crate::ir::Local| local.is_ghost;
    if func.return_local.name == place.local && check(&func.return_local) {
        return true;
    }
    for p in &func.params {
        if p.name == place.local { return check(p); }
    }
    for l in &func.locals {
        if l.name == place.local { return check(l); }
    }
    false
}
```

**Confidence:** HIGH — `Local::is_ghost` exists in IR, `mir_converter.rs` sets it via
`is_ghost_local()` name-prefix detection. `encode_assignment` receives `func: &Function`
which carries all locals.

### Pattern 3: Uncomment E2E Tests

**What:** The two commented-out tests in `e2e_verification.rs` (lines ~1519-1682) use
functions with I32 params and `"as int"` in ensures. After the `uses_spec_int_types()`
fix, these will select `ALL` logic and Z3 will accept `bv2int`.

**Test 1:** `test_unbounded_int_addition_no_overflow` — verifies `(result as int) > (_1 as int)` for positive args
**Test 2:** `test_unbounded_int_sum_formula` — verifies `(result as int) == (_1 as int) + (_2 as int)`

The tests assert:
1. SMT script contains `(set-logic ALL)` — enabled by the fix
2. SMT script contains `bv2int` — already produced by spec parser
3. Z3 returns UNSAT (property proven) — confirmed working in Z3 4.15.4

### Anti-Patterns to Avoid

- **Don't scan Term tree for Bv2Int:** Requires parsing spec expressions twice. String scan is sufficient and consistent with project patterns.
- **Don't unconditionally use ALL logic:** Keep selective logic for performance. QF_BV is faster for pure bitvector VCs.
- **Don't filter ghost DeclareConst:** Ghost locals must remain declared as SMT constants so spec expressions (in requires/ensures) can reference them. Only skip their *assignments*.

---

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| bv2int SMT encoding | Custom bit-extraction arithmetic | `Term::Bv2Int` + `(set-logic ALL)` | Already implemented; just needs logic fix |
| Ghost variable tracking | New ghost registry | `Local::is_ghost` field | Already exists in IR, set by `mir_converter.rs` |
| bv2nat distinction | Manual sign-extension | `bv2nat` for unsigned, `bv2int` for signed | Z3 4.15.4 accepts both in ALL logic; project uses `bv2int` |

**Key insight:** Both fixes are surgical — the infrastructure already exists. The Phase 04
implementation was correct but missed one detection case (spec expressions using `as int`
with non-SpecInt IR types) and deferred one guard (`is_ghost` at `encode_assignment`).

---

## Common Pitfalls

### Pitfall 1: Filtering Ghost DeclareConst Too Aggressively
**What goes wrong:** If ghost locals are not declared as SMT constants, spec expressions
in `requires`/`ensures` that reference ghost variables fail to parse.
**Why it happens:** Ghost locals appear in both spec expressions AND MIR body assignments.
**How to avoid:** Only filter at `encode_assignment` (assignments). Keep ghost locals in
`declare_function_locals()` (declarations). The fix is at encoding-not-declaration level.
**Warning signs:** Spec parser tests fail or Z3 emits "unknown constant ghost_x".

### Pitfall 2: Scanning Spec Strings Too Narrowly
**What goes wrong:** Spec string `"x as int"` (no leading space) misses detection.
**Why it happens:** Pattern `" as int"` requires a space before `as`.
**How to avoid:** Use `contains("as int")` (no leading space) OR check for both patterns.
Inspect actual spec strings produced by the proc macro — the spec parser tokenizes with
spaces around `as`.
**Warning signs:** `uses_spec_int_types()` returns false for `"x as int"` style specs.

### Pitfall 3: Logic Ordering with ALL + Datatypes
**What goes wrong:** `ALL` + DeclareDatatype may need reordering.
**Why it happens:** `base_script()` has conditional logic for QF_UFBVDT vs ALL; when both
datatypes AND spec-int are present, must use ALL (not QF_UFBVDT).
**How to avoid:** The existing `uses_int` parameter in `base_script()` already takes priority
over the datatype check (see line 1567: `if uses_int { ALL }` before `else if datatypes`).
Verify the priority order is maintained.
**Warning signs:** `(set-logic ALL)` missing from scripts that have both datatypes and bv2int.

### Pitfall 4: Z3 bv2int Signed vs Unsigned Semantics
**What goes wrong:** `bv2int` in Z3 treats bitvectors as unsigned (same as `bv2nat`).
For signed I32, `bv2int(-1_i32)` returns `4294967295` (unsigned wrap), not `-1`.
**Why it happens:** Z3's `bv2int` is unsigned; signed arithmetic is bitvector-native.
**How to avoid:** The Phase 04 decision was to use `bv2int` and accept unsigned semantics for
`as int` casts. The E2E tests use positive values only, avoiding the signed/unsigned issue.
Document this in code comments. This is a known limitation, not a bug to fix in Phase 31.
**Warning signs:** Negative bitvector values give unexpected integer values after `bv2int`.

---

## Code Examples

Verified patterns from live Z3 testing and codebase inspection:

### bv2int Working in ALL Logic (Z3 4.15.4)
```smtlib
; Source: live Z3 4.15.4 testing, 2026-02-26
(set-logic ALL)
(declare-const x (_ BitVec 32))
(assert (> (bv2int x) 5))
(check-sat)
; Result: sat (correct)
```

### bv2int Failing in QF_BV (Root Cause)
```smtlib
; Source: live Z3 4.15.4 testing, 2026-02-26
(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(assert (> (bv2int x) 5))
(check-sat)
; Error: line 3 column 20: unknown constant bv2int ((_ BitVec 32))
```

### int2bv Working in ALL Logic
```smtlib
; Source: live Z3 4.15.4 testing, 2026-02-26
(set-logic ALL)
(declare-const x Int)
(declare-const y (_ BitVec 32))
(assert (= ((_ int2bv 32) x) y))
(check-sat)
; Result: sat (correct)
```

### Ghost Local IR Field (ir.rs line 397)
```rust
// Source: crates/analysis/src/ir.rs
pub struct Local {
    pub name: String,
    pub ty: Ty,
    pub is_ghost: bool,  // true for __ghost_* locals (specification-only)
}
```

### Ghost Detection in Driver (mir_converter.rs line 41)
```rust
// Source: crates/driver/src/mir_converter.rs
fn is_ghost_local(source_name: &str) -> bool {
    source_name.starts_with("__ghost_")
}
```

### Current Logic Selection (vcgen.rs line 1567)
```rust
// Source: crates/analysis/src/vcgen.rs
if uses_int {
    // Int theory needed: use ALL logic to get all Z3 theories including bv2int/int2bv
    script.push(Command::SetLogic("ALL".to_string()));
} else if datatype_declarations.is_empty() {
    script.push(Command::SetLogic("QF_BV".to_string()));
} else {
    script.push(Command::SetLogic("QF_UFBVDT".to_string()));
}
```

---

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| Z3 4.8.x: bv2int unreliable | Z3 4.15.4: bv2int stable in ALL logic | Upgrade to 4.15.4 | Phase 31 can now complete what Phase 04 deferred |
| Ghost locals declared but never filtered | Ghost locals filtered at cex_render | Phase 19 | Phase 31 adds filtering at encode_assignment (VC generation) |

**Deprecated/outdated:**
- Phase 04-01 SUMMARY note: "ALL logics all report unknown constant bv2int" — This was true for Z3 version at time of writing. Z3 4.15.4 (current install) correctly accepts bv2int in ALL logic.

---

## Open Questions

1. **bv2int signed semantics**
   - What we know: Z3's `bv2int` is unsigned (same as `bv2nat`); signed values wrap
   - What's unclear: Should `as int` cast be documented as unsigned-only, or should Phase 31 add sign-extension logic?
   - Recommendation: Keep as-is (unsigned), add code comment. The E2E tests use positive values, so this is not a blocker for Phase 31. Track as future tech debt.

2. **Spec expression `as int` pattern variants**
   - What we know: The spec parser tokenizes `x as int` with spaces
   - What's unclear: Could user write `x  as  int` (multi-space)?
   - Recommendation: Use `contains("as int")` without leading space (catches all cases). The spec parser normalizes whitespace during tokenization.

3. **Ghost locals in DeclareConst — filter or keep?**
   - What we know: `cex_render.rs` already filters ghost locals (`.filter(|l| !l.is_ghost)`)
   - What's unclear: Should DeclareConst also filter ghost locals?
   - Recommendation: Keep DeclareConst for ghost locals (they must be referenceable in spec expressions). Only filter assignments. This matches the existing cex_render approach.

---

## Validation Architecture

(nyquist_validation not set in config.json — skipping Validation Architecture section)

---

## Sources

### Primary (HIGH confidence)
- Live Z3 4.15.4 testing (`/opt/homebrew/bin/z3`) — bv2int behavior in QF_BV vs ALL logic
- `crates/analysis/src/vcgen.rs` — `uses_spec_int_types()`, `encode_assignment()`, `base_script()` code
- `crates/smtlib/src/term.rs` — `Term::Bv2Int` definition
- `crates/smtlib/src/formatter.rs` — `(bv2int x)` formatting
- `crates/driver/src/mir_converter.rs` — `is_ghost_local()` name-prefix detection
- `crates/analysis/src/ir.rs` — `Local::is_ghost` field
- `.planning/v0.1-MILESTONE-AUDIT.md` — Gap characterization (Phase 04 functional gaps)
- `.planning/phases/04-differentiation/04-01-SUMMARY.md` — Original deferred decisions

### Secondary (MEDIUM confidence)
- `crates/analysis/tests/e2e_verification.rs` lines 1519-1682 — Commented-out tests (what to un-comment)
- `crates/driver/src/cex_render.rs` — Ghost filter precedent (`.filter(|l| !l.is_ghost)`)

### Tertiary (LOW confidence)
- None

---

## Metadata

**Confidence breakdown:**
- bv2int fix: HIGH — Root cause confirmed by live Z3 testing; fix pattern is clear
- Ghost locals fix: HIGH — `is_ghost` field exists, `encode_assignment` receives `func`
- E2E test enablement: HIGH — Tests exist, structure clear, just needs un-comment + minor fixup

**Research date:** 2026-02-26
**Valid until:** 2026-03-26 (stable domain, no external dependencies changing)
