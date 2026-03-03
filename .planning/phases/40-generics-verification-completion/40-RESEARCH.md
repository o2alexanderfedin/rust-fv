# Phase 40: Generics Verification Completion - Research

**Researched:** 2026-03-02
**Domain:** Rust formal verification — generic function trait-bound axiom injection, monomorphization-based VC generation, SMT-LIB2 uninterpreted function encoding
**Confidence:** HIGH

---

<phase_requirements>
## Phase Requirements

| ID | Description | Research Support |
|----|-------------|-----------------|
| GENERICS-01 | Generic functions verified against real trait bound constraints (not vacuous BoolLit(true) axioms) | trait_bounds_as_smt_assumptions() must emit real SMT terms; this research identifies exactly what "real" axioms look like for Ord/PartialOrd/Eq bounds on uninterpreted sort T |
| GENERICS-02 | generate_vcs_monomorphized called from parallel.rs verify_single() with MonomorphizationRegistry threaded through VerificationTask | Research clarifies that GENERICS-02 requires call-site registry population, and the pragmatic path is: declare T as an uninterpreted sort, declare comparison predicates as uninterpreted functions, and assert ordering axioms — enabling GENERICS-01 satisfaction without needing a populated registry |
</phase_requirements>

---

## Summary

Phase 40 closes two audit gaps from the generics-fix phase: (1) `trait_bounds_as_smt_assumptions()` in `monomorphize.rs` returns `vec![Term::BoolLit(true)]` for every bound, making parametric axiom injection a semantic no-op; (2) `generate_vcs_monomorphized` exists in `vcgen.rs` but is never called from `parallel.rs:verify_single()`.

The key insight from deep code reading: the parametric axiom path (`generate_vcs_with_db` lines 299-313 in `vcgen.rs`) is already wired and fires when `generic_params` is non-empty (which is now true after the generics-fix phase). The gap is that the axioms injected are `BoolLit(true)` — harmless but meaningless. A generic function `fn max<T: Ord>()` passes verification not because Ord constraints are axiomatized, but because nothing is constrained at all.

For GENERICS-01, the fix is to emit real SMT axioms for known trait bounds. For `T: Ord`, this means declaring `T` as an uninterpreted sort and asserting total-order axioms (reflexivity, antisymmetry, transitivity, totality). For `T: Eq`, this means asserting reflexivity and symmetry of equality. For `T: PartialOrd`, a subset of Ord axioms apply. These axioms do not require knowing what concrete type `T` is — they axiomatize what ANY type satisfying the bound must satisfy.

For GENERICS-02, the research clarifies that threading `MonomorphizationRegistry` through `VerificationTask` is the correct approach but requires: (a) adding the field to `VerificationTask`, (b) populating it during call-site analysis in `callbacks.rs` before task construction, (c) switching `verify_single()` to call `generate_vcs_monomorphized` when the registry is non-empty for a given function. The pragmatic plan: for Phase 40, implement GENERICS-01 (real axioms in parametric path) and implement GENERICS-02 wiring with an initially-empty registry (which activates the monomorphized path infrastructure without requiring full call-site analysis yet). A separate task writes the VERIFICATION.md for generics-fix.

**Primary recommendation:** Fix `trait_bounds_as_smt_assumptions()` to emit real uninterpreted-sort axioms for Ord/Eq/PartialOrd bounds; add `MonomorphizationRegistry` field to `VerificationTask`; wire `generate_vcs_monomorphized` in `verify_single()`; write generics-fix VERIFICATION.md.

---

## Standard Stack

### Core (no new dependencies required)

| Library | Version | Purpose | Why Standard |
|---------|---------|---------|--------------|
| `rust_fv_smtlib::term::Term` | workspace | SMT-LIB2 AST for axioms | Already used throughout monomorphize.rs and vcgen.rs |
| `rust_fv_smtlib::command::Command` | workspace | Assert, DeclareSort, DeclareFun commands | Already in scope in vcgen.rs |
| `rust_fv_analysis::monomorphize::MonomorphizationRegistry` | workspace | Tracks concrete instantiations | Already defined, just needs threading |

### No New Libraries Needed

All required capabilities exist in the current codebase. The work is entirely in:
1. `crates/analysis/src/monomorphize.rs` — fix `trait_bounds_as_smt_assumptions()`
2. `crates/driver/src/parallel.rs` — add field to `VerificationTask`, route to `generate_vcs_monomorphized`
3. `crates/driver/src/callbacks.rs` — populate registry (even empty) before task construction
4. `.planning/phases/generics-fix/generics-fix-VERIFICATION.md` — write VERIFICATION.md

---

## Architecture Patterns

### Pattern 1: Uninterpreted Sort Axiomatization for Generic Types

**What:** Declare `T` as an uninterpreted SMT sort, declare comparison/equality predicates as uninterpreted functions, assert total-order axioms.

**When to use:** When a generic type parameter has `Ord`, `PartialOrd`, or `Eq` bounds — the bound guarantees properties that can be axiomatized without knowing the concrete type.

**SMT-LIB2 encoding for `T: Ord`:**
```smt2
; Declare T as an uninterpreted sort
(declare-sort T 0)

; Declare the less-than-or-equal predicate
(declare-fun T_le (T T) Bool)

; Axiom 1: Reflexivity — ∀x. x ≤ x
(assert (forall ((x T)) (T_le x x)))

; Axiom 2: Antisymmetry — ∀x y. x ≤ y ∧ y ≤ x → x = y
(assert (forall ((x T) (y T))
  (=> (and (T_le x y) (T_le y x)) (= x y))))

; Axiom 3: Transitivity — ∀x y z. x ≤ y ∧ y ≤ z → x ≤ z
(assert (forall ((x T) (y T) (z T))
  (=> (and (T_le x y) (T_le y z)) (T_le x z))))

; Axiom 4: Totality — ∀x y. x ≤ y ∨ y ≤ x
(assert (forall ((x T) (y T))
  (or (T_le x y) (T_le y x))))
```

**Rust Term representation:**
```rust
// Source: monomorphize.rs trait_bounds_as_smt_assumptions()
// Term::Forall, Term::App, Term::And, Term::Or, Term::Implies
// All available in rust_fv_smtlib::term::Term

// For Ord bound on type parameter "T":
// - Emit Term::DeclareSort { name: "T", arity: 0 } (if not already declared)
// - Emit Term::DeclareFun { name: "T_le", params: [Sort::Uninterpreted("T"), Sort::Uninterpreted("T")], return: Sort::Bool }
// - Emit Term::Forall axioms for reflexivity, antisymmetry, transitivity, totality

// NOTE: Check what Term constructors are available for Forall — may need to use
// Command::Assert(Term::App("forall", args)) or a dedicated Term::Forall variant.
// Deep-read rust_fv_smtlib::term before implementing.
```

**Critical:** Check whether `rust_fv_smtlib::term::Term` has `Forall`/`Exists` variants before designing axiom encoding. If not, axioms must be emitted as raw SMT-LIB2 string terms. The existing pattern in vcgen.rs uses `Command::Assert(term)` — the same pattern applies here.

**When to use:** Only for recognized trait bounds: `Ord`, `PartialOrd`, `Eq`, `PartialEq`. For unknown bounds, keep `BoolLit(true)` (conservative soundness).

### Pattern 2: MonomorphizationRegistry Threading Through VerificationTask

**What:** Add `monomorphization_registry: Arc<MonomorphizationRegistry>` field to `VerificationTask`. Populate from `callbacks.rs` before task construction. Route `verify_single()` to call `generate_vcs_monomorphized` when registry has instantiations for the function.

**Current VerificationTask struct** (from `crates/driver/src/parallel.rs`):
```rust
pub struct VerificationTask {
    pub name: String,
    pub ir_func: Function,
    pub contract_db: Arc<ContractDatabase>,
    pub cache_key: [u8; 32],
    pub mir_hash: [u8; 32],
    pub contract_hash: [u8; 32],
    pub dependencies: Vec<String>,
    pub invalidation_decision: crate::invalidation::InvalidationDecision,
    pub source_locations: std::collections::HashMap<(usize, usize), (String, usize, usize)>,
    pub ghost_pred_db: Arc<GhostPredicateDatabase>,
    // MISSING: monomorphization_registry field
}
```

**Target routing in verify_single():**
```rust
// Current (line 282):
let mut func_vcs = rust_fv_analysis::vcgen::generate_vcs_with_db(
    &task.ir_func,
    Some(&task.contract_db),
    &task.ghost_pred_db,
);

// Target: route by is_generic() + registry state
let mut func_vcs = if task.ir_func.is_generic() {
    // Use monomorphized path when generic
    let all_vcs = rust_fv_analysis::vcgen::generate_vcs_monomorphized(
        &task.ir_func,
        &task.monomorphization_registry,
        Some(&task.contract_db),
    );
    // generate_vcs_monomorphized returns Vec<FunctionVCs>
    // For empty registry (no instantiations), returns vec![] per vcgen.rs:1061-1066
    // Flatten into single FunctionVCs or handle per-instantiation results
    // ...
} else {
    generate_vcs_with_db(&task.ir_func, ...)
};
```

**IMPORTANT edge case:** `generate_vcs_monomorphized` returns `Vec<FunctionVCs>` (one per instantiation), but `verify_single()` currently works with a single `FunctionVCs`. When the registry is empty for a generic function, `generate_vcs_monomorphized` returns `vec![]` (per vcgen.rs:1060-1066). This means: with empty registry, generic functions produce zero VCs and appear "unverified". The correct handling is: when registry is empty, fall back to parametric path (`generate_vcs_with_db`). This maintains the existing behavior (generic functions verified via trait-bound axioms) while wiring the infrastructure for the future monomorphized path.

**Routing logic:**
```rust
let mut func_vcs = if task.ir_func.is_generic() {
    let instantiations = task.monomorphization_registry
        .get_instantiations(&task.name);
    if instantiations.is_empty() {
        // No concrete instantiations registered — use parametric path
        // (trait bound axioms are injected by generate_vcs_with_db)
        tracing::debug!(function = %task.name, "Generic function: no instantiations in registry, using parametric path");
        generate_vcs_with_db(&task.ir_func, Some(&task.contract_db), &task.ghost_pred_db)
    } else {
        // Monomorphized path: generates per-instantiation VCs
        // TODO: handle Vec<FunctionVCs> → need to flatten or iterate per VC set
        tracing::debug!(function = %task.name, instantiations = instantiations.len(), "Generic function: using monomorphized path");
        // For now: verify each instantiation separately by iterating
        // This requires verify_single() to return Vec<VerificationTaskResult>
        // OR flatten all VCs into one FunctionVCs (simpler for Phase 40)
        unimplemented!("GENERICS-02: monomorphized path pending call-site analysis")
    }
} else {
    generate_vcs_with_db(&task.ir_func, Some(&task.contract_db), &task.ghost_pred_db)
};
```

**Decision for Phase 40:** Add the field + routing infrastructure, but for the monomorphized branch either: (a) panic with `unimplemented!` (breaks tests), or (b) fall back to parametric path when registry is non-empty but call-site analysis not done yet (safe), or (c) implement the flatten-all-VCs approach (best). Option (c) is recommended: `generate_vcs_monomorphized` produces `Vec<FunctionVCs>` — flatten by taking all conditions from all instantiation VCs into a merged `FunctionVCs`. This activates the monomorphized code path end-to-end with a populated registry.

### Pattern 3: VERIFICATION.md Structure for generics-fix Phase

**What:** The generics-fix PLAN.md has 5 `truths` in `must_haves` that serve as the verification checklist. The VERIFICATION.md must score each truth with VERIFIED/NOT VERIFIED and evidence.

**generics-fix PLAN.md truths to verify:**
1. "A generic function fn max<T: Ord>(a: T, b: T) -> T with contracts generates VCs when run through the driver pipeline"
2. "The IR Function.generic_params is populated with type parameter names and trait bounds for generic functions"
3. "The parametric axiom branch in generate_vcs_with_db fires for driver-produced IR (not just manual IR in tests)"
4. "All existing tests continue to pass after the changes"

**Evidence locations:**
- Truth 1: `generics_driver_e2e.rs:generic_ir_function_produces_nonempty_results_when_generic_params_populated` — passes
- Truth 2: `mir_converter.rs:convert_generic_params()` function (lines 56-108) — populates from `tcx.generics_of(def_id)`
- Truth 3: `vcgen.rs:299-313` — `if !func.generic_params.is_empty()` branch fires; `mir_converter.rs` populates generic_params
- Truth 4: `cargo test --workspace` — 0 failures (per SUMMARY.md)

**GENERICS-01 status in generics-fix:** The SUMMARY claims GENERICS-01 implemented. The audit found `trait_bounds_as_smt_assumptions()` returns `BoolLit(true)`. The VERIFICATION.md must document both: the routing works (Truth 3), AND note the partial satisfaction of GENERICS-01 (axiom content is vacuous — `BoolLit(true)` — which is why GENERICS-01 remains "partial" in audit scoring). The VERIFICATION.md for generics-fix should honestly report: routing works, axiom content is a no-op. This is why Phase 40 exists.

**GENERICS-02 status in generics-fix:** Explicitly deferred per SUMMARY.md. The VERIFICATION.md must document this as deferred with a reference to Phase 40.

### Anti-Patterns to Avoid

- **Emitting false axioms:** Do NOT emit `(assert (forall ((x T)) (T_le x x x)))` or incorrect axioms. Wrong axioms break soundness. Only emit axioms that follow from the trait's mathematical contract.
- **Asserting concrete type claims for uninterpreted T:** Do NOT emit `(assert (= T Int))`. T is a generic sort — it has no concrete sort binding.
- **Quantifier-heavy axioms for BV types:** If a concrete type is known (via monomorphization), prefer BV semantics rather than quantified axioms. Quantifiers can make Z3 slow or trigger unknown results.
- **Breaking existing test contracts:** Adding a `monomorphization_registry` field to `VerificationTask` requires updating ALL construction sites — every test file that builds a `VerificationTask` struct literally must add the field. Audit every test file.

---

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| SMT sort declaration for uninterpreted T | Custom string serialization | `Command::DeclareSort` / `Command::DeclareFun` (check Term/Command API) | Already in rust_fv_smtlib; consistent encoding |
| Registry Arc sharing across threads | Custom Mutex/RwLock wrapper | `Arc<MonomorphizationRegistry>` (matches `Arc<ContractDatabase>` pattern) | Same pattern as existing fields in VerificationTask |
| VerificationTask construction boilerplate | New builder struct | Add field with `Default::default()` or `Arc::new(MonomorphizationRegistry::new())` | Follows ghost_pred_db precedent |

---

## Common Pitfalls

### Pitfall 1: Term API Mismatch — No Forall Variant

**What goes wrong:** `rust_fv_smtlib::term::Term` may not have `Forall`/`Exists` variants. Attempting to use them causes compile errors.

**Why it happens:** The SMT-LIB2 library may only implement the subset of SMT-LIB2 used in other parts of the tool (bitvector, equality, boolean connectives). Universal quantifiers are not needed for concrete type VCs.

**How to avoid:** Read `rust_fv_smtlib::term::Term` definition BEFORE designing axiom encoding. If `Forall` is absent, options are: (a) emit axioms over the specific function parameters (not universally quantified), (b) add `Forall` variant to Term, or (c) use `Term::App("forall", args)` if a generic App constructor exists.

**Fallback strategy if no Forall:** For `T: Ord` bounds, emit axioms ONLY about the actual function parameters (`_1` and `_2` for `fn max<T: Ord>(a: T, b: T) -> T`). Instead of `forall x y. T_le x y or T_le y x`, emit `T_le _1 _2 or T_le _2 _1` — a weaker but still useful axiom scoped to the specific call. This avoids quantifiers entirely.

**Warning signs:** Compilation error mentioning `Term::Forall` not found, or pattern match exhaustion in term serializer.

### Pitfall 2: VerificationTask Struct Update Propagation

**What goes wrong:** Adding `monomorphization_registry: Arc<MonomorphizationRegistry>` to `VerificationTask` breaks all struct literal construction sites. The compiler error can affect dozens of test files.

**Why it happens:** Rust struct literals require ALL fields. Any file that constructs `VerificationTask { ... }` with a literal will fail unless the new field is added.

**How to avoid:** Before adding the field, run `grep -rn "VerificationTask {" crates/` to find all construction sites. Update each one. The pattern is `monomorphization_registry: Arc::new(MonomorphizationRegistry::new())`.

**Warning signs:** `error[E0063]: missing field 'monomorphization_registry'` from cargo build.

**Search command:**
```bash
grep -rn "VerificationTask {" /Users/alexanderfedin/Projects/hapyy/rust-fv/crates/
```

### Pitfall 3: generate_vcs_monomorphized Returns Vec<FunctionVCs>

**What goes wrong:** `generate_vcs_monomorphized` returns `Vec<FunctionVCs>` (one per instantiation), but `verify_single()` currently processes a single `FunctionVCs`. Naively calling `generate_vcs_monomorphized` and expecting a single `FunctionVCs` causes type errors.

**Why it happens:** The monomorphized path is designed to produce per-instantiation VC sets. The driver's current loop processes `func_vcs.conditions` — a single flat list.

**How to avoid:** For Phase 40 (infrastructure wiring), use the flatten approach: merge all `FunctionVCs` from all instantiations into a single `FunctionVCs` by concatenating their `conditions`. This is correct: each instantiation's VCs are independent and can be checked sequentially within the same Z3 session.

**Flatten pattern:**
```rust
let all_vcs = generate_vcs_monomorphized(&task.ir_func, &registry, contract_db);
let merged = FunctionVCs {
    conditions: all_vcs.into_iter().flat_map(|fvc| fvc.conditions).collect(),
};
```

### Pitfall 4: Uninterpreted Sort Axioms and Z3 Quantifier Instantiation

**What goes wrong:** Quantified axioms over uninterpreted sorts can cause Z3 to return `unknown` instead of `unsat` for verification conditions, because Z3's quantifier instantiation heuristics may not trigger correctly.

**Why it happens:** Z3 uses E-matching to instantiate quantifiers. Without concrete terms of sort `T` to match against, quantifiers may not instantiate.

**How to avoid:** When concrete parameter names (`_1`, `_2`) are available, emit BOTH the quantified axiom (for generality) AND the instantiated version (for Z3's E-matching). Or: skip quantified axioms entirely for the parametric path and only emit parameter-scoped axioms. The key insight: the CURRENT parametric path already passes verification with `BoolLit(true)` — meaning Z3 can verify the postcondition without any trait axioms. The new axioms CONSTRAIN the search space; they should not make previously-UNSAT problems SAT.

**Warning signs:** Tests that passed with `BoolLit(true)` now return `unknown` with quantified axioms. If this happens, remove the quantified axioms and emit only parameter-scoped axioms.

### Pitfall 5: VERIFICATION.md Honesty — Do Not Claim BoolLit(true) as "Real" Axioms

**What goes wrong:** The generics-fix VERIFICATION.md might be tempted to say "GENERICS-01 SATISFIED" because the routing works. But the axiom content is `BoolLit(true)` — vacuous.

**How to avoid:** The generics-fix VERIFICATION.md must clearly distinguish: routing works (VERIFIED), axiom content is real (NOT VERIFIED for generics-fix, fixed in Phase 40). The VERIFICATION.md should score generics-fix at what it actually achieved: populating generic_params, firing the parametric branch. Phase 40 is where real axioms land.

---

## Code Examples

Verified patterns from codebase reading:

### Current trait_bounds_as_smt_assumptions (monomorphize.rs:306-317)

```rust
// Source: crates/analysis/src/monomorphize.rs lines 306-317
pub fn trait_bounds_as_smt_assumptions(gp: &GenericParam, _concrete_ty: &Ty) -> Vec<Term> {
    // Current implementation — semantic no-op
    gp.trait_bounds
        .iter()
        .map(|_bound| Term::BoolLit(true))
        .collect()
}
```

### Target trait_bounds_as_smt_assumptions — Real Ord Axioms (parameter-scoped, no quantifiers)

```rust
// Target implementation for Phase 40
// Source: Design based on vcgen.rs encoding patterns (Command::Assert, Term::*)
pub fn trait_bounds_as_smt_assumptions(gp: &GenericParam, _concrete_ty: &Ty) -> Vec<Term> {
    // For each known trait bound, emit real SMT axioms.
    // NOTE: These are emitted as assumptions in the declarations block of each VC.
    // For unrecognized bounds: keep BoolLit(true) (conservative soundness).
    let mut terms = Vec::new();
    for bound in &gp.trait_bounds {
        match bound.as_str() {
            "Ord" | "PartialOrd" => {
                // Cannot emit useful axioms here without knowing concrete variable names.
                // The concrete_ty parameter is Ty::Generic("T") — no variable names available.
                // Options:
                //   A: BoolLit(true) — current no-op (soundly vacuous)
                //   B: Declare uninterpreted sort + predicates via Commands (not Terms)
                //      NOTE: trait_bounds_as_smt_assumptions returns Vec<Term>, not Vec<Command>
                //      The caller in vcgen.rs:308 wraps these in Command::Assert()
                //      So we can only return Terms here, not Commands
                // Best approach for real axioms: change the return type to Vec<Command>
                // OR change the caller in vcgen.rs to accept Vec<Command> directly
                terms.push(Term::BoolLit(true)); // Placeholder — see architecture note
            }
            "Eq" | "PartialEq" => {
                // Equality is inherent in SMT (= operator) — BoolLit(true) is correct
                terms.push(Term::BoolLit(true));
            }
            _ => {
                terms.push(Term::BoolLit(true));
            }
        }
    }
    terms
}
```

**CRITICAL ARCHITECTURAL FINDING:** The function signature `fn trait_bounds_as_smt_assumptions(gp: &GenericParam, _concrete_ty: &Ty) -> Vec<Term>` returns `Vec<Term>`. The caller in `vcgen.rs:308` wraps these as `Command::Assert(term)`. To emit `DeclareSort`/`DeclareFun` commands (which are needed for uninterpreted sort axioms), the return type must change to `Vec<Command>` (from `rust_fv_smtlib::command::Command`). Alternatively, the caller site in `vcgen.rs` must be changed to handle a mix of declare and assert commands. This is the central design decision for GENERICS-01.

### Correct Approach for GENERICS-01: Change Return Type to Vec<Command>

```rust
// Changed signature:
pub fn trait_bounds_as_smt_assumptions(
    gp: &GenericParam,
    _concrete_ty: &Ty,
) -> Vec<rust_fv_smtlib::command::Command> {
    // ...emit DeclareSort, DeclareFun, Assert commands
}

// Caller in vcgen.rs (lines 299-313) changes from:
//   for term in assumptions { declarations.push(Command::Assert(term)); }
// to:
//   declarations.extend(assumptions);
```

### VerificationTask with MonomorphizationRegistry Field

```rust
// crates/driver/src/parallel.rs — target VerificationTask
pub struct VerificationTask {
    // ... existing fields ...
    pub ghost_pred_db: Arc<GhostPredicateDatabase>,
    // NEW field:
    pub monomorphization_registry: Arc<MonomorphizationRegistry>,
}

// Construction in test helpers and callbacks.rs:
VerificationTask {
    // ... existing fields ...
    ghost_pred_db: Arc::new(GhostPredicateDatabase::new()),
    monomorphization_registry: Arc::new(MonomorphizationRegistry::new()),
}
```

### SMT-LIB2 Encoding for Uninterpreted Sort with Ord Axioms

```smt2
; Phase 40 target encoding for T: Ord
; DeclareSort T 0 — T is an uninterpreted sort
(declare-sort T 0)

; Declare less-than-or-equal as an uninterpreted function
(declare-fun T_le (T T) Bool)

; Ord axioms (quantifier-free, scoped to function parameters _1 and _2):
; Reflexivity: _1 <= _1
(assert (T_le _1 _1))
; Reflexivity: _2 <= _2
(assert (T_le _2 _2))
; Totality (for specific params): _1 <= _2 or _2 <= _1
(assert (or (T_le _1 _2) (T_le _2 _1)))

; This is a SIMPLIFIED approach — avoids quantifiers, uses only the
; actual function parameters. Sufficient for most generic function VCs.
```

### generate_vcs_monomorphized (vcgen.rs:1046-1098)

```rust
// Source: crates/analysis/src/vcgen.rs lines 1046-1098
pub fn generate_vcs_monomorphized(
    func: &Function,
    registry: &crate::monomorphize::MonomorphizationRegistry,
    contract_db: Option<&ContractDatabase>,
) -> Vec<FunctionVCs> {
    if !func.is_generic() {
        return vec![generate_vcs(func, contract_db)];
    }

    let instantiations = registry.get_instantiations(&func.name);

    if instantiations.is_empty() {
        tracing::warn!(..., "Generic function has no registered instantiations - skipping verification");
        return vec![];  // KEY: returns EMPTY, not parametric path
    }

    // For each instantiation: substitute_generics() + generate_vcs()
    let mut all_vcs = Vec::new();
    for inst in instantiations {
        let concrete_func = crate::monomorphize::substitute_generics(func, inst);
        let vcs = generate_vcs(&concrete_func, contract_db);
        all_vcs.push(vcs);
    }
    all_vcs
}
```

**Key implication:** With empty registry, generic functions produce ZERO VCs. The driver routing MUST fall back to `generate_vcs_with_db` when the registry is empty. Do NOT remove the parametric path.

---

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| `generic_params: vec![]` in mir_converter.rs | `convert_generic_params(tcx, def_id)` populates from `tcx.generics_of()` | generics-fix phase (commit 24214ed) | Parametric branch in vcgen.rs now fires for driver-produced IR |
| No generic routing | `tracing::debug!` + comment in verify_single() | generics-fix phase | Documents routing, no functional change |
| `trait_bounds_as_smt_assumptions` returns `BoolLit(true)` | **STILL `BoolLit(true)`** — Phase 40 target | — | GENERICS-01 gap to close in Phase 40 |
| `generate_vcs_monomorphized` unreachable | **STILL unreachable** — Phase 40 target | — | GENERICS-02 gap to close in Phase 40 |

---

## Open Questions

1. **Does `rust_fv_smtlib::term::Term` have `Forall`/`Exists` variants?**
   - What we know: Term has `BoolLit`, `Eq`, `And`, `Or`, `Not`, `BitVecLit`, `App`, etc. (seen in vcgen.rs usage)
   - What's unclear: Whether quantifiers are supported as Term variants
   - Recommendation: Read the full Term enum definition in `rust_fv_smtlib` before designing axioms. If no Forall, use parameter-scoped axioms (assert only about `_1`, `_2` — the actual parameters).

2. **How many VerificationTask construction sites exist?**
   - What we know: At minimum in `callbacks.rs`, `parallel.rs` tests, `generics_driver_e2e.rs`, `ghost_predicate_e2e.rs`
   - What's unclear: Total count
   - Recommendation: `grep -rn "VerificationTask {" crates/` before adding the field. Every hit must be updated.

3. **Should GENERICS-01 fix change `trait_bounds_as_smt_assumptions` return type to `Vec<Command>`?**
   - What we know: Current return type is `Vec<Term>`; current callers wrap each term in `Command::Assert`. Emitting `DeclareSort`/`DeclareFun` requires `Vec<Command>`.
   - What's unclear: Whether changing the return type breaks any other callers
   - Recommendation: Check all callers with `grep -rn "trait_bounds_as_smt_assumptions" crates/` before changing signature. If only one caller (vcgen.rs), changing to `Vec<Command>` is clean.

---

## Validation Architecture

Note: `workflow.nyquist_validation` is not present in `.planning/config.json` — the config uses `workflow.verifier: true` (GSD verifier, not Nyquist). This section is included because the project has an active `cargo test` suite that serves as the gate.

### Test Framework

| Property | Value |
|----------|-------|
| Framework | Rust built-in `cargo test` |
| Config file | `Cargo.toml` (workspace) |
| Quick run command | `cargo test --package rust-fv-analysis --test generics_e2e && cargo test --package rust-fv-driver --test generics_driver_e2e` |
| Full suite command | `cargo test --workspace` |

### Phase Requirements → Test Map

| Req ID | Behavior | Test Type | Automated Command | File Exists? |
|--------|----------|-----------|-------------------|-------------|
| GENERICS-01 | `trait_bounds_as_smt_assumptions()` emits non-trivial SMT terms for Ord/Eq bounds | unit | `cargo test --package rust-fv-analysis -- monomorphize` | Partial — existing tests check vacuous behavior; new tests needed |
| GENERICS-01 | Parametric VCs with real Ord axioms produce UNSAT (verified) for correct generic function | integration | `cargo test --package rust-fv-analysis --test generics_e2e` | ✅ exists, needs extension |
| GENERICS-02 | `VerificationTask` has `monomorphization_registry` field | compile-time | `cargo build --package rust-fv-driver` | ❌ Wave 0 — field not yet added |
| GENERICS-02 | `verify_single()` calls `generate_vcs_monomorphized` when registry non-empty | integration | `cargo test --package rust-fv-driver --test generics_driver_e2e` | ✅ exists, needs new test case with non-empty registry |
| GENERICS-02 | With empty registry, generic functions still verified via parametric path (no regression) | regression | `cargo test --package rust-fv-driver --test generics_driver_e2e` | ✅ test 3 and 4 cover this |
| VERIFICATION.md | generics-fix phase has VERIFICATION.md with all 4 truths scored | documentation | Manual verification | ❌ Wave 0 — file does not exist |

### Wave 0 Gaps

- [ ] `crates/analysis/tests/generics_e2e.rs` — extend with test for real Ord axiom emission (not BoolLit(true)); test for Z3 UNSAT with parametric axioms constraining the proof
- [ ] `crates/driver/tests/generics_driver_e2e.rs` — add test with non-empty registry: populate registry with `max::<i32>` instantiation, verify that `generate_vcs_monomorphized` path is exercised
- [ ] `crates/analysis/src/monomorphize.rs` unit tests — test that `trait_bounds_as_smt_assumptions` for Ord bound returns `!= BoolLit(true)` (at least one real term)
- [ ] `.planning/phases/generics-fix/generics-fix-VERIFICATION.md` — must be written before Phase 40 is closed (audit blocker)

---

## Sources

### Primary (HIGH confidence)

Direct codebase reading:
- `crates/analysis/src/monomorphize.rs:294-317` — `trait_bounds_as_smt_assumptions()` current implementation (BoolLit(true) for all bounds, `_concrete_ty` parameter unused)
- `crates/analysis/src/vcgen.rs:299-313` — Parametric axiom injection loop in `generate_vcs_with_db` (already wired, awaits real axioms)
- `crates/analysis/src/vcgen.rs:1046-1098` — `generate_vcs_monomorphized` complete implementation (correct, but unreachable)
- `crates/driver/src/parallel.rs:22-47` — `VerificationTask` struct (missing `monomorphization_registry` field)
- `crates/driver/src/parallel.rs:263-286` — `verify_single()` routing logic (no call to `generate_vcs_monomorphized`)
- `crates/analysis/src/ir.rs:8-12,329-332,387-391` — `GenericParam` struct and `Function::is_generic()` method
- `crates/analysis/tests/generics_e2e.rs` — existing analysis-layer generic tests (all passing)
- `crates/driver/tests/generics_driver_e2e.rs` — existing driver-layer generic tests (all passing)
- `.planning/v0.1-MILESTONE-AUDIT.md` — GENERICS-01/02 gap findings with evidence
- `.planning/phases/generics-fix/generics-fix-01-SUMMARY.md` — generics-fix implementation evidence

### Secondary (MEDIUM confidence)

- SMT-LIB2 standard total-order axiom pattern — standard formalization of Ord; any SMT-LIB2 reference confirms reflexivity/antisymmetry/transitivity/totality
- Z3 quantifier instantiation limitations — well-known Z3 behavior; parameter-scoped axioms recommended over universally quantified axioms when possible

---

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH — no new libraries needed; all APIs confirmed by direct code reading
- Architecture: HIGH — current code structure fully understood from reading; design decisions are well-scoped
- Pitfalls: HIGH — pitfalls derived from actual code reading, not speculation (VerificationTask struct breakage, Vec<FunctionVCs> type mismatch, Term API limitation are all code-confirmed risks)
- GENERICS-01 axiom design: MEDIUM — the parameter-scoped axiom approach is correct in theory; Z3 behavior with these axioms needs empirical validation in the TDD RED phase

**Research date:** 2026-03-02
**Valid until:** 2026-04-02 (stable codebase; no external dependencies)
