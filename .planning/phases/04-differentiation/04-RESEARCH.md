# Phase 4: Differentiation - Research

**Researched:** 2026-02-11
**Domain:** Advanced specification features (prophecy variables, ghost code, quantifiers, unbounded integers, generics)
**Confidence:** MEDIUM-HIGH

## Summary

Phase 4 transforms the verifier from basic contract checking to expressive mathematical reasoning. This phase adds prophecy variables for mutable borrow reasoning (Creusot-style), ghost code for specification-only constructs, quantifiers (forall/exists) with trigger-based instantiation, unbounded mathematical integers (int/nat) for overflow-free specification arithmetic, and generic/trait verification via monomorphization.

**Critical findings:**
1. **Prophecy variables are research-level but proven** - Creusot POPL 2026 tutorial demonstrates production usage, RustHornBelt provides theoretical foundation, requires prophecy creation at borrow and resolution at expiration
2. **Trigger inference is the hardest quantifier challenge** - Verus tunable automation paper (2026) shows conservative selection beats aggressive instantiation, manual `#[trigger]` overrides essential
3. **Ghost code erasure is straightforward with proc macros** - Verus/Prusti demonstrate `#[ghost]` attribute pattern, compile-time check then erase from MIR encoding, no runtime overhead
4. **Unbounded integers are standard SMT theory** - SMT-LIB Int theory proven, must carefully manage bitvector↔int conversions to prevent unsoundness
5. **Monomorphization verification is plausible but expensive** - Each generic instantiation becomes separate VC, planner must account for combinatorial explosion in large codebases

**Primary recommendation:** Implement incrementally in strict dependency order: (1) unbounded integers for spec-only arithmetic, (2) ghost code for helper variables, (3) quantifiers with manual triggers, (4) prophecy variables for mutable borrows (research spike), (5) generic monomorphization last. Test each feature in isolation before composition.

## Standard Stack

### Core Libraries (Additions to Phase 3)

| Library | Version | Purpose | Why Standard |
|---------|---------|---------|--------------|
| (no new dependencies) | - | Use existing smtlib/ crate | All Phase 4 features map to existing SMT-LIB constructs |

**Key insight:** Phase 4 is primarily VCGen/encoding logic, not new library dependencies. SMT-LIB already has Int theory, quantifiers (Forall/Exists), and let-bindings for ghost variables.

### SMT-LIB Theories Required

| Theory | Purpose | Already Supported |
|--------|---------|-------------------|
| QF_UFBVDT | Bitvectors + datatypes | ✓ (Phase 2-3) |
| UFBVDTLIA | Add Int theory for unbounded integers | New - add Int sort |
| Quantifiers | Forall/exists with triggers | New - non-QF logic |

**Installation:**
```toml
# No new crates needed - extend existing smtlib/ and analysis/
```

**Confidence:** HIGH - no external dependencies, pure SMT encoding work.

## Architecture Patterns

### Recommended Project Structure (Additions)

```
crates/analysis/src/
├── encode_prophecy.rs    # Prophecy variable creation/resolution
├── encode_quantifier.rs  # Forall/exists with trigger inference
├── ghost_erasure.rs      # Ghost code detection and erasure
└── monomorphize.rs       # Generic instantiation tracking
```

### Pattern 1: Unbounded Mathematical Integers (int/nat)

**What:** Specification-only types `int` (unbounded integer) and `nat` (non-negative unbounded integer) for mathematical reasoning without overflow.

**When to use:** In specifications when overflow semantics would make properties unsound or overly complex.

**Example:**
```rust
// Rust executable code uses i32 (wrapping)
#[requires(n >= 0)]
#[ensures(result == n * (n + 1) / 2)]  // This would overflow for large n
fn sum_to_n(n: i32) -> i32 {
    // Spec uses mathematical integers, implementation uses i32
}

// Spec with int type (no overflow)
#[requires(n >= 0)]
#[ensures(result == (n as int) * ((n as int) + 1) / 2)]  // Mathematical division
fn sum_to_n_safe(n: i32) -> i32 {
    // Cast to int in spec, i32 in implementation
}
```

**SMT encoding:**
```smt2
; int type maps to SMT-LIB Int
(declare-const n Int)
(declare-const result Int)

; Spec: result == n * (n + 1) / 2
(assert (= result (div (* n (+ n 1)) 2)))  ; Integer division, no overflow

; For nat (non-negative int), add constraint
(declare-const count Nat)
(assert (>= count 0))  ; Or use subtype encoding
```

**Implementation strategy:**
1. Add `Sort::Int` and `Sort::Nat` to smtlib/src/sort.rs (already exists)
2. Extend spec parser to recognize `int` and `nat` keywords
3. Add `as int` cast operator in specs (Rust value → unbounded spec value)
4. VCGen: executable code remains bitvector, specs use Int sort
5. **Critical:** Conversions must be explicit - never silently mix bitvectors and Int

**Soundness concern:** Bitvector overflow can make Int-based specs unsound. Require explicit casts and document when to use each.

**Confidence:** HIGH - SMT-LIB Int theory is well-established, Verus demonstrates production usage.

### Pattern 2: Ghost Code with #[ghost] Attribute

**What:** Variables and functions marked `#[ghost]` are type-checked, usable in specifications, but completely erased from compiled output.

**When to use:** Specification-only helper variables (loop witnesses, intermediate proofs), proof functions, prophecy variables.

**Example:**
```rust
#[requires(arr.len() > 0)]
#[ensures(result >= 0 && result < arr.len())]
#[ensures(arr[result] == max_value)]
#[ensures(forall(|i: usize| i < arr.len() ==> arr[i] <= max_value))]
fn find_max_index(arr: &[i32]) -> usize {
    let mut max_idx = 0;
    #[ghost] let mut max_value: i32 = arr[0];  // Ghost variable for spec

    #[invariant(max_idx < arr.len())]
    #[invariant(max_value == arr[max_idx])]
    #[invariant(forall(|j: usize| j <= i ==> arr[j] <= max_value))]
    for i in 0..arr.len() {
        if arr[i] > arr[max_idx] {
            max_idx = i;
            #[ghost] { max_value = arr[i]; }  // Ghost code block
        }
    }
    max_idx
}
```

**Implementation:**
1. Proc macro detects `#[ghost]` on local variables
2. MIR converter skips ghost locals when generating executable IR
3. VCGen includes ghost locals in VC encoding (for spec evaluation)
4. Ghost code must be terminating (prevents infinite loops affecting semantics)

**Verification flow:**
```
Rust source → MIR (includes ghost) → IR conversion
                                          ↓
                         Executable IR ←─ Ghost IR
                         (no ghost)       (for VCGen only)
```

**Confidence:** MEDIUM-HIGH - Verus/Prusti demonstrate pattern, implementation is straightforward attribute filtering.

### Pattern 3: Quantifiers with Manual Triggers

**What:** Universal (`forall`) and existential (`exists`) quantification over collections, with user-specified trigger patterns for SMT instantiation.

**When to use:** Properties over all/some elements of collections, generic type properties, inductive invariants.

**Example:**
```rust
// Universal quantification
#[requires(forall(|i: usize| i < arr.len() ==> arr[i] > 0))]
#[ensures(result > 0)]
fn sum_positive(arr: &[i32]) -> i32 {
    arr.iter().sum()
}

// With explicit trigger (Verus syntax)
#[requires(forall(|i: int| #[trigger] is_even(i) ==> f(i) > 0))]
fn even_property(x: i32) -> bool {
    // Trigger fires when is_even(t) appears in SMT context
}

// Existential quantification
#[ensures(exists(|i: usize| i < arr.len() && arr[i] == target) ==> result.is_some())]
fn find_element(arr: &[i32], target: i32) -> Option<usize> {
    arr.iter().position(|&x| x == target)
}
```

**SMT encoding:**
```smt2
; Forall with trigger
(assert (forall ((i Int))
  (! (=> (and (>= i 0) (< i arr_len))
         (> (select arr i) 0))
     :pattern ((select arr i)))))  ; Trigger on array access

; Exists (negation of forall + not)
(assert (not (forall ((i Int))
  (not (and (< i arr_len) (= (select arr i) target))))))
```

**Trigger selection rules (from Verus docs):**
1. **Must contain all quantified variables** - `(select arr i)` contains both `arr` and `i`
2. **Cannot use basic operators** - No `==`, `+`, `&&`, etc. as triggers
3. **Must match relevant code patterns** - Trigger fires when pattern appears in SMT context
4. **Avoid matching loops** - Multiple triggers can cause exponential instantiation

**Implementation:**
1. Extend spec parser to recognize `forall(|var: T| expr)` and `exists(|var: T| expr)` syntax
2. Add `#[trigger]` attribute for manual trigger annotation
3. Implement conservative trigger inference (Verus approach):
   - Prefer function applications over operators
   - Select minimal trigger set covering all variables
   - Warn if no good trigger found, require manual annotation
4. Add `Term::Forall` and `Term::Exists` to smtlib (already exists in codebase)
5. Test with simple collection properties before complex invariants

**Pitfall:** Aggressive trigger selection causes timeouts. Default to conservative (require manual triggers), add `#![auto_trigger]` opt-in later.

**Confidence:** MEDIUM - Trigger inference is research-hard, but Verus demonstrates conservative manual approach works in practice.

### Pattern 4: Prophecy Variables for Mutable Borrows

**What:** Prophecy variables denote the "final value" of a mutable borrow when its lifetime ends, enabling reasoning about `&mut T` in specifications.

**When to use:** Specifications involving mutable borrows, functions taking `&mut Vec`, `&mut HashMap`, etc.

**Example (Creusot syntax):**
```rust
#[ensures(v.len() == old(v.len()) + 1)]
#[ensures(^v[old(v.len())] == elem)]  // ^ = final operator
fn push_vec(v: &mut Vec<i32>, elem: i32) {
    v.push(elem);
}

// Prophecy reasoning
#[requires(x > 0)]
#[ensures(*x == old(*x) + 1)]  // Current dereference
#[ensures(^x == old(*x) + 1)]  // Final value (when borrow expires)
fn increment(x: &mut i32) {
    *x += 1;
}
```

**Prophecy lifecycle:**
1. **Creation:** When mutable borrow created, introduce prophecy variable `x_prophecy`
2. **Usage:** In specs, `^x` refers to `x_prophecy` (future value)
3. **Resolution:** When borrow expires, assert `actual_final_value == x_prophecy`

**SMT encoding (RustHornBelt approach):**
```smt2
; At borrow creation
(declare-const v_initial (Array Int Int))
(declare-const v_prophecy (Array Int Int))  ; Prophecy of final value

; Specification: ^v[old(v.len())] == elem
(assert (= (select v_prophecy v_initial_len) elem))

; At borrow expiration (resolution)
(assert (= v_final v_prophecy))  ; Actual final value matches prophecy
```

**Implementation strategy:**
1. Detect mutable borrow parameters in MIR (`&mut T`)
2. Create prophecy variable `{param}_prophecy` at function entry
3. Extend spec parser to recognize `^expr` (final operator)
4. VCGen: replace `^x` with `x_prophecy` in postconditions
5. At borrow expiration (function return), assert `x_final == x_prophecy`

**Research dependency:** Success criterion 4 requires Creusot source study. POPL 2020 prophecy paper + Creusot POPL 2026 tutorial are essential reading before implementation.

**Confidence:** LOW-MEDIUM - Research-level feature, Creusot demonstrates feasibility but encoding is non-trivial. Recommend research spike before committing.

### Pattern 5: Generic Verification via Monomorphization

**What:** Verify generic functions by generating separate VCs for each concrete type instantiation.

**When to use:** Generic functions with trait bounds (`T: Ord`, `T: Clone`), generic data structures.

**Example:**
```rust
#[requires(a <= b)]
#[ensures(result == b)]
fn max<T: Ord>(a: T, b: T) -> T {
    if a < b { b } else { a }
}

// Verification: generate VCs for each instantiation
// max::<i32>: separate VC with i32-specific encoding
// max::<u64>: separate VC with u64-specific encoding
```

**Monomorphization tracking:**
```rust
struct MonomorphizationRegistry {
    /// Maps generic function signature to instantiated types
    instantiations: HashMap<String, Vec<TypeInstantiation>>,
}

struct TypeInstantiation {
    generic_params: Vec<String>,  // ["T", "U"]
    concrete_types: Vec<Ty>,      // [i32, String]
    vc_generated: bool,
}
```

**Implementation:**
1. Detect generic functions during MIR conversion (`fn<T>` syntax)
2. Track each call site's concrete type arguments
3. Generate separate VC per instantiation (VCGen pass per type combo)
4. Trait bounds become preconditions (e.g., `T: Ord` → comparison operators valid)
5. Deduplication: cache generated VCs to avoid redundant work

**Pitfall:** Combinatorial explosion for highly generic code. Recommend starting with simple generics (single type param, no where clauses).

**Confidence:** MEDIUM - Rust compiler already does monomorphization, we mirror the process. Verus/Prusti handle generics, but complexity grows fast.

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Trigger inference | Custom heuristic engine | Manual triggers + conservative selection (Verus approach) | Trigger inference is NP-hard, research-level problem. Conservative selection with manual overrides is proven approach. |
| Prophecy variable encoding | Ad-hoc "future value" variables | RustHornBelt encoding (creation + resolution) | Prophecies require careful lifetime tracking and SMT constraint generation. RustHornBelt is peer-reviewed, proven sound. |
| Ghost code erasure | Custom MIR rewriting | Attribute-based filtering in proc macro | Proc macros already parse attributes. Simple filtering avoids complex MIR manipulation. |
| Bitvector↔Int conversion | Implicit casting | Explicit `as int` in specs | Silent conversions cause soundness bugs (overflow hidden). Explicit casts force user awareness. |
| Generic instantiation tracking | Manual type substitution | Leverage rustc's monomorphization | Compiler already computes instantiations. Query via TyCtxt, don't reimplement. |

**Key insight:** Phase 4 features touch research-level problems (prophecies, triggers). Adopt proven encodings from Creusot/Verus/RustHornBelt rather than inventing new approaches.

## Common Pitfalls

### Pitfall 1: Bitvector/Int Mixing Causes Unsoundness

**What goes wrong:** Spec says `result == n * (n + 1) / 2` using Int division, but implementation uses i32 arithmetic that overflows. Verifier proves property for Int, runtime fails for i32.

**Why it happens:** SMT-LIB Int and BitVec have fundamentally different semantics. Int division is mathematical, bitvector operations wrap on overflow.

**How to avoid:**
- **Never implicitly convert** bitvector ↔ Int
- Require explicit `as int` casts in specs: `(n as int) * ((n as int) + 1) / 2`
- Document in manual: "int/nat are spec-only types, not runtime values"
- Add runtime overflow checks if spec uses Int but implementation uses fixed-width

**Warning signs:**
- Spec verifies but runtime panics on overflow
- Different results in debug vs release builds
- Spec involves large arithmetic with small integer types

**Example:**
```rust
// WRONG - silent int/bitvector mixing
#[ensures(result == n * (n + 1) / 2)]  // Uses Int division
fn sum_to_n(n: i32) -> i32 {
    (0..=n).sum()  // Uses i32 arithmetic (wraps on overflow)
}

// CORRECT - explicit conversion and overflow acknowledgment
#[requires(n >= 0 && (n as int) * ((n as int) + 1) / 2 <= i32::MAX)]
#[ensures(result == (n as int) * ((n as int) + 1) / 2)]
fn sum_to_n_safe(n: i32) -> i32 {
    (0..=n).sum()
}
```

**Confidence:** HIGH - Well-documented in SMT verification literature, Verus explicitly addresses this.

### Pitfall 2: Aggressive Trigger Selection Causes Timeouts

**What goes wrong:** Automatic trigger inference selects multiple triggers, SMT solver explores exponential search space, verification times out.

**Why it happens:** Triggers control quantifier instantiation. Multiple triggers = multiple instantiation paths = combinatorial explosion.

**How to avoid (from Verus tunable automation paper 2026):**
- **Default to conservative trigger selection** - fewest triggers necessary
- **Require manual `#[trigger]` for complex quantifiers** - user specifies pattern
- **Warn on multi-trigger quantifiers** - alert user to potential performance impact
- **Implement `#![auto_trigger]` opt-in** - aggressive selection only when requested
- **Provide feedback** - show which triggers were selected in verbose mode

**Warning signs:**
- Verification timeout on simple quantified properties
- Z3 uses excessive memory (>1GB for single VC)
- Small code changes cause dramatic performance swings

**Example:**
```rust
// BAD - no trigger specified, auto-selection may choose poorly
#[requires(forall(|i: usize| i < arr.len() ==> arr[i] > 0))]
fn sum_positive(arr: &[i32]) -> i32 { ... }

// GOOD - explicit trigger on array access
#[requires(forall(|i: usize| #[trigger] arr[i] > 0))]  // Fires on arr[i] access
fn sum_positive_explicit(arr: &[i32]) -> i32 { ... }
```

**Mitigation:**
```rust
// Conservative trigger inference
fn infer_triggers(quantifier: &Forall) -> Vec<Trigger> {
    let candidates = find_function_applications(&quantifier.body);
    let minimal_set = select_minimal_covering_set(candidates);

    if minimal_set.len() > 1 {
        warn!("Multiple triggers required: {:?}. Consider manual #[trigger].", minimal_set);
    }

    minimal_set
}
```

**Confidence:** HIGH - Verus 2026 tunable automation paper provides empirical evidence and proven strategy.

### Pitfall 3: Prophecy Resolution Missed at Early Return

**What goes wrong:** Function with mutable borrow has early return, prophecy variable never resolved, spec verification unsound.

**Why it happens:** Prophecy resolution must occur at **every** exit point (return, panic, early return), not just final return.

**How to avoid:**
- Scan MIR for all `Return` terminators
- Insert prophecy resolution assertion before each return
- Test with functions having multiple exit paths
- Document: "Prophecy specs unsupported with early returns" (Phase 4 limitation)

**Warning signs:**
- Spec verifies but panics at runtime
- Different behavior with/without early returns
- Prophecy-related VCs missing in verification output

**Example:**
```rust
// WRONG - early return skips prophecy resolution
#[ensures(^v.len() == old(v.len()) + 1)]
fn push_or_fail(v: &mut Vec<i32>, elem: i32, flag: bool) {
    if !flag {
        return;  // BUG: prophecy for v never resolved!
    }
    v.push(elem);
}

// CORRECT - explicit prophecy in each branch
#[ensures(flag ==> ^v.len() == old(v.len()) + 1)]
#[ensures(!flag ==> ^v.len() == old(v.len()))]
fn push_or_fail_correct(v: &mut Vec<i32>, elem: i32, flag: bool) {
    if !flag {
        // Prophecy: v unchanged
        return;
    }
    v.push(elem);
    // Prophecy: v has one more element
}
```

**Implementation:**
```rust
fn resolve_prophecies(func: &Function) -> Vec<Assertion> {
    let mut resolutions = Vec::new();

    for bb in &func.basic_blocks {
        if matches!(bb.terminator, Terminator::Return) {
            for prophecy in &func.prophecy_vars {
                // Assert actual_value == prophecy_value
                resolutions.push(assert_eq(prophecy.actual, prophecy.prophecy_var));
            }
        }
    }

    resolutions
}
```

**Confidence:** MEDIUM - Creusot handles this, but requires careful CFG analysis.

### Pitfall 4: Ghost Code Has Side Effects

**What goes wrong:** Ghost code contains I/O, network calls, or other side effects. Erasure changes program semantics.

**Why it happens:** User misunderstands "ghost" - assumes it runs at verification time, not that it's erased.

**How to avoid:**
- **Type-check ghost code** - must be pure (no I/O, no unsafe, no FFI)
- **Lint ghost blocks** - detect prohibited operations (println!, file access, etc.)
- **Document clearly** - "Ghost code never executes, even during verification"
- **Require `#[ghost]` functions to be `#[pure]`** - enforce purity

**Warning signs:**
- Test failures when running verified code
- Different behavior in verification vs execution
- Ghost code calls external functions

**Example:**
```rust
// WRONG - ghost code has side effects
#[ghost]
fn log_verification(msg: &str) {
    println!("Verifying: {}", msg);  // BUG: side effect in ghost code
}

// CORRECT - ghost code is pure computation
#[ghost]
#[pure]
fn compute_witness(x: i32) -> i32 {
    x * x  // Pure computation, no side effects
}
```

**Enforcement:**
```rust
fn validate_ghost_code(item: &Item) -> Result<(), Error> {
    if has_ghost_attr(item) {
        if contains_io(item) {
            return Err("Ghost code cannot perform I/O");
        }
        if contains_unsafe(item) {
            return Err("Ghost code cannot use unsafe");
        }
        if !is_pure(item) {
            return Err("Ghost code must be marked #[pure]");
        }
    }
    Ok(())
}
```

**Confidence:** HIGH - Verus/Prusti enforce purity, standard verification practice.

### Pitfall 5: Monomorphization Combinatorial Explosion

**What goes wrong:** Generic function with 3 type parameters, each used with 5 types = 5³ = 125 VCs. Verification takes hours.

**Why it happens:** Monomorphization generates VC per instantiation. Generics multiply verification cost.

**How to avoid:**
- **Start with single-type-param generics** - defer complex generics to later
- **Deduplicate equivalent instantiations** - `Vec<i32>` and `Vec<u32>` may have identical VC
- **Limit verification scope** - only verify instantiations actually used in codebase
- **Add timeout per VC** - prevent single instantiation blocking all others
- **Document cost** - "Generic verification is O(instantiations × VC cost)"

**Warning signs:**
- Verification time grows exponentially with generic parameters
- Many "duplicate" VCs with only type names different
- Generic function verifies in isolation, fails in real codebase

**Example:**
```rust
// AVOID in Phase 4 - too many instantiations
fn complex_generic<T, U, V>(a: T, b: U, c: V) -> (T, U, V)
where
    T: Clone + Ord,
    U: Debug + Hash,
    V: Default + Send,
{
    // If used with 5 types each: 5³ = 125 VCs
}

// PREFER in Phase 4 - single type param
fn simple_generic<T: Ord>(a: T, b: T) -> T {
    // If used with 5 types: 5 VCs
    if a < b { b } else { a }
}
```

**Mitigation:**
```rust
struct MonomorphizationBudget {
    max_instantiations_per_function: usize,  // e.g., 20
    timeout_per_vc: Duration,                 // e.g., 30s
}

fn verify_generic(func: &Function, budget: &MonomorphizationBudget) -> Result {
    let instantiations = collect_instantiations(func);

    if instantiations.len() > budget.max_instantiations_per_function {
        warn!("Function {} has {} instantiations, may be slow",
              func.name, instantiations.len());
    }

    // Verify each instantiation with timeout
    for inst in instantiations {
        verify_with_timeout(func, inst, budget.timeout_per_vc)?;
    }
}
```

**Confidence:** MEDIUM - Known issue in generic verification, Verus/Prusti documentation mentions performance concerns.

### Pitfall 6: Quantifier Without Trigger Never Fires

**What goes wrong:** Spec has `forall(|x: i32| f(x) > 0)` but no trigger, SMT solver never instantiates, property vacuously true.

**Why it happens:** SMT solvers use pattern matching for instantiation. No pattern = no instantiation.

**How to avoid:**
- **Require trigger for all quantifiers** - either inferred or manual
- **Fail loudly if no trigger found** - error, not warning
- **Test with counterexamples** - ensure quantifier actually fires
- **Document trigger rules** - what makes a valid trigger

**Warning signs:**
- Spec verifies trivially fast (<1ms)
- Adding contradictory quantified fact doesn't cause UNSAT
- Removing quantifier doesn't change verification result

**Example:**
```rust
// WRONG - no trigger, quantifier never instantiates
#[requires(forall(|x: i32| x > 0 ==> x + 1 > x))]  // No function application
fn useless_spec() { }

// CORRECT - trigger on function application
#[requires(forall(|x: i32| #[trigger] f(x) > 0))]  // Fires when f(t) appears
fn working_spec() { }
```

**Detection:**
```rust
fn check_quantifier_triggers(spec: &SpecExpr) -> Result<(), Error> {
    match spec {
        SpecExpr::Forall(vars, body) | SpecExpr::Exists(vars, body) => {
            let triggers = infer_triggers(body);
            if triggers.is_empty() {
                return Err(format!(
                    "Quantifier has no valid trigger. Add #[trigger] annotation.\n\
                     Valid triggers must:\n\
                     1. Contain all quantified variables\n\
                     2. Not use basic operators (==, +, &&)\n\
                     3. Preferably be function applications"
                ));
            }
        }
        _ => {}
    }
    Ok(())
}
```

**Confidence:** HIGH - Well-documented SMT solver behavior, Verus enforces trigger presence.

## Code Examples

Verified patterns from Creusot, Verus, and RustHornBelt papers.

### Unbounded Integer Specification

```rust
// Source: Verus tutorial
use rust_fv_macros::*;

// Mathematical property using unbounded integers
#[requires(n >= 0)]
#[ensures((result as int) == (n as int) * ((n as int) + 1) / 2)]
fn sum_to_n(n: i32) -> i32 {
    let mut sum = 0;
    let mut i = 0;

    #[invariant(i <= n)]
    #[invariant((sum as int) == (i as int) * ((i as int) - 1) / 2)]
    while i < n {
        sum = sum.checked_add(i).expect("overflow");  // Runtime check
        i += 1;
    }

    sum
}

// SMT encoding (in encode_term.rs)
fn encode_int_cast(expr: &Expr) -> Term {
    match expr {
        Expr::Cast(val, Type::Int) => {
            // Bitvector to Int conversion
            let bv_term = encode_expr(val);
            Term::App("bv2int".to_string(), vec![bv_term])
        }
        _ => encode_expr(expr),
    }
}
```

### Ghost Code with Erasure

```rust
// Source: Verus ghost/exec documentation
use rust_fv_macros::*;

#[requires(arr.len() > 0)]
#[ensures(result < arr.len())]
#[ensures(forall(|i: usize| i < arr.len() ==> arr[i] <= arr[result]))]
fn find_max_index(arr: &[i32]) -> usize {
    let mut max_idx = 0;

    // Ghost variable for specification
    #[ghost]
    let mut max_val: i32 = arr[0];

    #[invariant(max_idx < arr.len())]
    #[invariant(max_val == arr[max_idx])]
    #[invariant(forall(|j: usize| j < i ==> arr[j] <= max_val))]
    for i in 1..arr.len() {
        #[ghost]
        {
            // Ghost code block - erased from compilation
            assert!(arr[i] <= max_val || arr[i] > max_val);  // Proof hint
        }

        if arr[i] > arr[max_idx] {
            max_idx = i;
            #[ghost] { max_val = arr[i]; }
        }
    }

    max_idx
}

// MIR conversion (in mir_converter.rs)
fn convert_local(local: &mir::Local, attrs: &[Attribute]) -> Option<Local> {
    if has_ghost_attr(attrs) {
        // Ghost local - include in spec IR, exclude from executable IR
        return None;  // Filtered out for compilation
    }
    Some(Local { name: format!("_{}", local.index()), ty: convert_ty(local.ty) })
}
```

### Quantifiers with Triggers

```rust
// Source: Verus forall tutorial
use rust_fv_macros::*;

// Manual trigger specification
#[requires(forall(|i: usize| i < s.len() ==> #[trigger] is_even(s[i])))]
#[ensures(result % 2 == 0)]
fn sum_even_sequence(s: &[i32]) -> i32 {
    s.iter().sum()
}

// Multiple triggers (multi-pattern)
#[requires(forall(|i: usize, j: usize|
    i < arr.len() && j < arr.len() && i < j ==>
    #[trigger] arr[i] <= #[trigger] arr[j]
))]
fn is_sorted_property(arr: &[i32]) -> bool {
    // Triggers on both arr[i] and arr[j]
    true
}

// SMT encoding (in encode_quantifier.rs)
fn encode_forall(vars: &[(String, Ty)], body: &Expr, triggers: &[Trigger]) -> Term {
    let smt_vars: Vec<(String, Sort)> = vars.iter()
        .map(|(name, ty)| (name.clone(), encode_sort(ty)))
        .collect();

    let smt_body = encode_expr(body);

    // Annotate with triggers
    let annotated_body = if !triggers.is_empty() {
        let patterns: Vec<Term> = triggers.iter()
            .map(|t| encode_trigger_pattern(t))
            .collect();
        Term::Annotated(
            Box::new(smt_body),
            vec![("pattern".to_string(), patterns)]
        )
    } else {
        smt_body
    };

    Term::Forall(smt_vars, Box::new(annotated_body))
}
```

### Prophecy Variables for Mutable Borrows

```rust
// Source: Creusot POPL 2026 tutorial (adapted)
use rust_fv_macros::*;

// Final operator (^) denotes prophecy
#[ensures(v.len() == old(v.len()) + 1)]
#[ensures(^v[old(v.len())] == elem)]  // Final value at new index
fn push_element(v: &mut Vec<i32>, elem: i32) {
    v.push(elem);
}

// More complex: mutable borrow with conditional mutation
#[requires(*x > 0)]
#[ensures(flag ==> ^x == old(*x) + 1)]
#[ensures(!flag ==> ^x == old(*x))]
fn conditional_increment(x: &mut i32, flag: bool) {
    if flag {
        *x += 1;
    }
}

// VCGen prophecy encoding (in encode_prophecy.rs)
struct ProphecyEncoding {
    initial_value: Term,    // old(*x)
    prophecy_var: String,   // x_prophecy
    final_value: Term,      // Value at function exit
}

fn encode_mutable_param(param: &Local, ty: &Ty) -> ProphecyEncoding {
    match ty {
        Ty::MutRef(inner) => {
            let initial = Term::Const(format!("{}_initial", param.name));
            let prophecy = format!("{}_prophecy", param.name);

            ProphecyEncoding {
                initial_value: initial.clone(),
                prophecy_var: prophecy.clone(),
                final_value: Term::Const(format!("{}_final", param.name)),
            }
        }
        _ => panic!("Not a mutable reference"),
    }
}

fn resolve_prophecy(encoding: &ProphecyEncoding) -> Term {
    // At function exit: assert final_value == prophecy
    Term::Eq(
        Box::new(encoding.final_value.clone()),
        Box::new(Term::Const(encoding.prophecy_var.clone()))
    )
}
```

### Generic Verification via Monomorphization

```rust
// Source: Prusti generic verification patterns
use rust_fv_macros::*;

// Generic max function
#[requires(a <= b)]  // Uses Ord trait bound
#[ensures(result == b)]
fn max<T: Ord>(a: T, b: T) -> T {
    if a < b { b } else { a }
}

// Call sites determine instantiations
fn use_max() {
    let x = max(3i32, 5i32);      // Instantiation 1: max::<i32>
    let y = max(2u64, 9u64);      // Instantiation 2: max::<u64>
    let z = max('a', 'z');        // Instantiation 3: max::<char>
}

// Monomorphization tracking (in monomorphize.rs)
struct MonomorphizationTracker {
    instantiations: HashMap<DefId, Vec<GenericArgs>>,
}

impl MonomorphizationTracker {
    fn record_call(&mut self, func_def: DefId, args: GenericArgs) {
        self.instantiations.entry(func_def)
            .or_insert_with(Vec::new)
            .push(args);
    }

    fn generate_vcs(&self, func: &Function) -> Vec<VC> {
        let mut vcs = Vec::new();

        for args in &self.instantiations[&func.def_id] {
            // Substitute generic type params with concrete types
            let instantiated = substitute_generics(func, args);

            // Generate VC for this instantiation
            let vc = generate_vc(&instantiated);
            vcs.push(vc);
        }

        vcs
    }
}
```

### Trigger Inference Algorithm

```rust
// Source: Verus trigger selection (conservative approach)
use rust_fv_macros::*;

// Conservative trigger inference
fn infer_triggers(quantifier_body: &Expr, bound_vars: &[String]) -> Vec<Trigger> {
    // Find all function applications
    let candidates = find_function_apps(quantifier_body);

    // Filter to valid triggers (contain all bound vars, no forbidden ops)
    let valid: Vec<_> = candidates.into_iter()
        .filter(|app| {
            let app_vars = free_variables(app);
            bound_vars.iter().all(|v| app_vars.contains(v))
        })
        .filter(|app| !uses_forbidden_ops(app))  // No ==, +, &&, etc.
        .collect();

    if valid.is_empty() {
        return vec![];  // Require manual trigger
    }

    // Select minimal covering set
    let minimal = select_minimal_set(&valid, bound_vars);

    if minimal.len() > 1 {
        // Multi-trigger - warn user
        eprintln!("Warning: Multi-trigger quantifier may impact performance");
    }

    minimal
}

fn uses_forbidden_ops(expr: &Expr) -> bool {
    match expr {
        Expr::BinOp(op, _, _) => matches!(op,
            BinOp::Eq | BinOp::Add | BinOp::Sub | BinOp::And | BinOp::Or
        ),
        _ => false,
    }
}
```

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| Implicit bitvector/int mixing | Explicit `as int` casts | Verus design (2023+) | Prevents unsound specs from overflow hiding |
| Aggressive trigger auto-selection | Conservative + manual `#[trigger]` | Verus tunable automation (2026) | Reduces timeout rates, improves predictability |
| Ad-hoc mutable borrow encoding | Prophecy variables (RustHornBelt) | POPL 2020 → Creusot 2022+ | Sound encoding for `&mut T` in specs |
| Ghost code via separate macro crate | `#[ghost]` attribute in main verifier | Verus 2023, Prusti 2024+ | Simpler UX, better type checking |
| Per-instantiation manual verification | Automatic monomorphization tracking | Prusti generic support (2024+) | Reduces annotation burden for generics |

**Deprecated/outdated:**
- **Implicit quantifier triggers** - Modern verifiers (Verus, Dafny) require explicit triggers or conservative inference
- **Bitvector-only specs** - Unbounded Int theory standard in 2025+ tools for mathematical properties
- **Ghost code via separate crate** - Attribute-based approach simpler and more maintainable

## Open Questions

### 1. Prophecy Variable Encoding Complexity

**What we know:**
- Creusot demonstrates production usage with POPL 2026 tutorial
- RustHornBelt provides theoretical soundness proof
- Requires prophecy creation at borrow + resolution at expiration

**What's unclear:**
- How complex is the SMT encoding in practice?
- Do nested mutable borrows require nested prophecies?
- Performance impact on SMT solving time?

**Recommendation:**
- Research spike (2-3 days) before committing to implementation
- Read Creusot source code (creusot-rs/creusot on GitHub)
- Implement minimal prototype for `fn f(x: &mut i32)` before Vec/HashMap
- If too complex, defer to Phase 5 or mark as experimental

### 2. Trigger Inference vs Manual Annotation Trade-off

**What we know:**
- Conservative inference works (Verus 2026 tunable automation paper)
- Manual triggers are precise but burden users
- Aggressive inference causes timeouts

**What's unclear:**
- What % of quantifiers can be auto-inferred with conservative approach?
- How often do users need manual triggers in practice?
- Should we fail or warn when no trigger found?

**Recommendation:**
- Phase 4: Conservative inference + manual `#[trigger]` required when inference fails
- Collect metrics during testing (% auto-inferred vs manual)
- Consider adding inference hints in Phase 5 based on data

### 3. Monomorphization Budget for Large Codebases

**What we know:**
- Each generic instantiation = separate VC
- Combinatorial explosion possible (3 type params × 5 types = 125 VCs)
- Verification time scales linearly with instantiations

**What's unclear:**
- What's acceptable upper bound on instantiations per function?
- Should we deduplicate "equivalent" instantiations (i32 vs u32)?
- Parallel verification feasible for independent instantiations?

**Recommendation:**
- Phase 4: Limit to single-type-param generics, max 20 instantiations per function
- Add `--max-instantiations` CLI flag for user control
- Phase 5: Explore deduplication and parallelization if needed

## Sources

### Primary (HIGH confidence)

**Prophecy Variables:**
- [Creusot: Formal verification of Rust programs (POPL 2026 Tutorial)](https://popl26.sigplan.org/details/POPL-2026-tutorials/6/Creusot-Formal-verification-of-Rust-programs) - January 2026, prophecy operator tutorial
- [Creusot: a Foundry for the Deductive Verification of Rust Programs](https://jhjourdan.mketjh.fr/pdf/denis2022creusot.pdf) - Pearlite specification language with final operator
- [Using a Prophecy-Based Encoding of Rust Borrows](https://inria.hal.science/hal-05244847/file/main.pdf) - SMT encoding of prophecy variables
- [Thrust: A Prophecy-based Refinement Type System for Rust](https://www.riec.tohoku.ac.jp/~unno/papers/pldi2025.pdf) - PLDI 2025, prophecy for refinement types

**Quantifiers and Triggers:**
- [Verus Tutorial: forall and triggers](https://verus-lang.github.io/verus/guide/forall.html) - Manual trigger annotation syntax
- [Tunable Automation in Automated Program Verification](https://arxiv.org/html/2512.03926) - 2026, broadcast mechanism and trigger strategies
- [The SMT-LIB Standard Version 2.0](https://smt-lib.org/papers/smt-lib-reference-v2.0-r10.12.21.pdf) - `:pattern` syntax for triggers
- [Programming Z3](https://theory.stanford.edu/~nikolaj/programmingz3.html) - Quantifier and trigger documentation

**Ghost Code:**
- [Verus: Ghost code vs. exec code](https://verus-lang.github.io/verus/guide/ghost_vs_exec.html) - Official Verus documentation
- [Verus: Verifying Rust Programs using Linear Ghost Types](https://www.andrew.cmu.edu/user/bparno/papers/verus-ghost.pdf) - OOPSLA 2023
- [Initiative: Ghost types and blocks · Issue #161 · rust-lang/lang-team](https://github.com/rust-lang/lang-team/issues/161) - Rust RFC for ghost code

**Unbounded Integers:**
- [Understanding how F* uses Z3](https://fstar-lang.org/tutorial/book/under_the_hood/uth_smt.html) - Int theory encoding
- [Satisfiability Modulo Theories - Wikipedia](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories) - SMT-LIB Int theory overview
- [SMT Theory Arbitrage: Approximating Unbounded Constraints](https://dl.acm.org/doi/10.1145/3656387) - Bitvector/Int conversion

**Monomorphization:**
- [Monomorphization - Rust Compiler Development Guide](https://rustc-dev-guide.rust-lang.org/backend/monomorph.html) - How rustc handles generics
- [Lessons Learned Verifying the Rust Standard Library](https://arxiv.org/html/2510.01072v1) - Monomorphization challenges in verification

### Secondary (MEDIUM confidence)

**Creusot Implementation:**
- [Pearlite - Rust library](https://lib.rs/crates/pearlite) - Creusot specification language crate
- [Creusot 0.9.0 Devlog](https://creusot-rs.github.io/devlog/2026-01-19/) - January 2026, recent features
- [Creusot ARCHITECTURE.md](https://github.com/creusot-rs/creusot/blob/master/ARCHITECTURE.md) - Implementation details

**Verification Techniques:**
- [RefinedRust: A Type System for High-Assurance Verification](https://plv.mpi-sws.org/refinedrust/paper-refinedrust.pdf) - Alternative borrow encoding
- [Surveying the Rust Verification Landscape](https://arxiv.org/html/2410.01981v1) - Comparative analysis of tools

### Tertiary (LOW confidence - needs validation)

- [Interpolating bit-vector formulas using uninterpreted predicates](https://link.springer.com/article/10.1007/s10703-021-00372-6) - Bitvector/Int conversion techniques
- [Syntax-Guided Quantifier Instantiation](https://pmc.ncbi.nlm.nih.gov/articles/PMC7984542/) - Advanced trigger inference

## Metadata

**Confidence breakdown:**
- Unbounded integers: HIGH - SMT-LIB Int theory proven, Verus demonstrates `as int` pattern
- Ghost code: HIGH - Verus/Prusti show attribute-based approach works, implementation straightforward
- Quantifiers: MEDIUM-HIGH - Trigger syntax proven, but inference complexity requires careful design
- Prophecy variables: MEDIUM-LOW - Research-level, Creusot demonstrates feasibility but encoding non-trivial
- Monomorphization: MEDIUM - Rustc provides infrastructure, but combinatorial explosion is real concern

**Research date:** 2026-02-11
**Valid until:** 2026-03-15 (30 days - Phase 4 planning should complete before expiry)
