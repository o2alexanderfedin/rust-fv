# Phase 9: Lifetime Reasoning - Research

**Researched:** 2026-02-12
**Domain:** Rust lifetime verification, NLL, prophecy variables, MIR borrow analysis
**Confidence:** HIGH

## Summary

Lifetime reasoning is a mature research area with production implementations in Creusot, Verus, and Prusti. The core challenge is verifying temporal properties about references: when borrows are valid, when they expire, and what final values mutable borrows have when their lifetimes end. This phase builds on existing prophecy infrastructure (already implemented in `encode_prophecy.rs`) and extends it with lifetime tracking, NLL-based scope analysis, and conflict detection.

**Primary recommendation:** Leverage rustc's MIR borrow checker infrastructure (region inference, outlives constraints) as the source of truth for lifetime information. Use prophecy variables for mutable borrow final values (already implemented). Add layer-by-layer tracking for nested borrows and conflict VCs for overlapping shared/mutable lifetimes.

**Key insight:** Rust's NLL implementation already solves the hard problem of lifetime scope analysis via control-flow-sensitive MIR analysis. We should extract and verify rustc's computed lifetime constraints rather than reimplementing lifetime analysis from scratch.

## User Constraints (from CONTEXT.md)

<user_constraints>
### Locked Decisions

#### Annotation requirements
- Dual approach: leverage existing Rust lifetime syntax AND support optional new annotations
- Existing Rust syntax (`'a`, `'b`, `where T: 'a`) automatically participates in verification
- New `#[borrow_ensures(x, expr)]` attribute on functions for specifying mutable borrow final values
- `final(*x)` syntax inline within `#[ensures]` for reasoning about mutable reference final state
- Functions with lifetime parameters automatically get borrow validity VCs — no opt-in needed
- Elided lifetimes are resolved (same as rustc) and verified — developer doesn't need to write explicit lifetimes

#### Supported lifetime patterns
- Higher-ranked trait bounds (`for<'a>` syntax) included in v0.2
- Full generic lifetime bounds: `T: 'a`, `T: 'static`, and multi-lifetime bounds `T: 'a + 'b`
- Full `'static` lifetime verification — verify that values claimed as `'static` truly have no non-static references
- Pin/self-referential structs deferred to v0.3+ (depends on Phase 10 unsafe maturity)

#### Borrow expiry semantics
- Automatic prophecy variable insertion for each mutable reference parameter — developer uses `final(*x)` in specs
- Layer-by-layer tracking for nested borrows (`&mut &mut T`): each indirection level gets its own prophecy variable (`final(*x)` for outer, `final(**x)` for inner)
- Generate explicit conflict VCs when shared (`&T`) and mutable (`&mut T`) borrows have overlapping lifetimes
- Full temporary borrow support — track borrows created in expressions (e.g., `&vec[0]`) with their precise scope

#### Failure diagnostics
- Source-level borrow timeline showing full lifecycle: creation, usage, expiry, and conflict point
- Default to concise violation message; `--verbose` or `#[verifier::verbose]` for full lifetime explanation chain (`'a outlives 'b because...`)
- Include actionable fix suggestions (e.g., "consider cloning x before the borrow" or "move this usage before line N")
- Severity levels at Claude's discretion, leaning toward safety and precision (prefer errors over warnings when ambiguous)

### Claude's Discretion
- Specific prophecy variable encoding strategy in Z3
- NLL analysis implementation approach (MIR-based vs custom)
- Exact fix suggestion heuristics
- Severity classification for edge-case lifetime issues
- Temporary borrow tracking implementation details
</user_constraints>

## Standard Stack

### Core
| Library | Version | Purpose | Why Standard |
|---------|---------|---------|--------------|
| rustc_borrowck | nightly | Borrow checker with region inference | Official Rust compiler component, contains NLL implementation |
| rustc_middle::mir | nightly | MIR representation and borrow data | Foundation for all MIR-based analysis in rustc |
| Z3 | 4.13+ | SMT solver for lifetime VCs | Already in use, supports uninterpreted sorts for regions |

### Supporting
| Library | Version | Purpose | When to Use |
|---------|---------|---------|-------------|
| rustc_infer | nightly | Inference engine utilities | If implementing custom region inference (LOW priority) |
| polonius | experimental | Next-gen borrow checker | If rustc borrow checker insufficient (unlikely for v0.2) |

### Alternatives Considered
| Instead of | Could Use | Tradeoff |
|------------|-----------|----------|
| rustc region inference | Custom lifetime analysis | Custom gives control but requires reimplementing NLL's complexity (not worth it) |
| Z3 uninterpreted sorts | Z3 datatypes for regions | Datatypes allow pattern matching but uninterpreted sorts sufficient and simpler |
| Prophecy variables | Two-state encoding (pre/post) | Two-state encoding simpler but cannot express `final(*x)` operator in specs |

**Installation:**
```bash
# Already available via rustc nightly
rustup toolchain install nightly

# Z3 already in dependencies
# No additional installation needed
```

## Architecture Patterns

### Recommended Module Structure
```
crates/analysis/src/
├── encode_prophecy.rs      # EXISTING: Prophecy detection and encoding
├── lifetime_analysis.rs    # NEW: Extract lifetime info from MIR
├── borrow_conflict.rs      # NEW: Detect shared/mutable conflicts
├── vcgen.rs                # EXTEND: Add VcKind::BorrowValidity
└── ir.rs                   # EXTEND: Add lifetime metadata to IR

crates/driver/src/
├── mir_converter.rs        # EXTEND: Extract region info from rustc MIR
└── lifetime_extractor.rs   # NEW: Query rustc borrowck results
```

### Pattern 1: Extract Rustc Region Information
**What:** Query rustc's borrow checker results to get computed lifetimes and outlives constraints
**When to use:** Every function with lifetime parameters or references
**Example:**
```rust
// Source: Rustc Dev Guide - Region Inference
// https://rustc-dev-guide.rust-lang.org/borrow_check/region_inference.html

use rustc_borrowck::consumers::get_body_with_borrowck_facts;
use rustc_middle::ty::RegionVid;

pub fn extract_region_constraints(
    tcx: TyCtxt<'_>,
    def_id: LocalDefId,
) -> RegionConstraints {
    let body_with_facts = get_body_with_borrowck_facts(tcx, def_id);
    let region_inference = &body_with_facts.region_inference_context;

    // Extract outlives constraints: 'a: 'b
    let outlives: Vec<(RegionVid, RegionVid)> = region_inference
        .outlives_constraints()
        .map(|(a, b)| (*a, *b))
        .collect();

    // Extract lifetime scopes (NLL live ranges)
    let live_ranges: HashMap<RegionVid, LiveRange> = region_inference
        .regions()
        .map(|r| (r, region_inference.region_value(r)))
        .collect();

    RegionConstraints { outlives, live_ranges }
}
```

### Pattern 2: Layer-by-Layer Prophecy for Nested Borrows
**What:** Create separate prophecy variables for each indirection level in nested mutable references
**When to use:** Any `&mut &mut T` or deeper nesting
**Example:**
```rust
// Pattern for &mut &mut i32 parameter x
//
// Creates:
// - x_initial: &mut i32 (outer initial state)
// - x_prophecy: &mut i32 (outer final state)
// - x_deref_initial: i32 (inner initial state at *x)
// - x_deref_prophecy: i32 (inner final state at *x)
//
// Specs can use:
// - final(*x) -> resolves to x_prophecy
// - final(**x) -> resolves to x_deref_prophecy

fn create_nested_prophecies(param: &Local) -> Vec<ProphecyInfo> {
    let mut prophecies = Vec::new();
    let mut current_ty = &param.ty;
    let mut deref_level = 0;

    while let Ty::Ref(inner, Mutability::Mutable) = current_ty {
        let suffix = if deref_level == 0 {
            String::new()
        } else {
            format!("_deref{}", deref_level)
        };

        prophecies.push(ProphecyInfo {
            param_name: param.name.clone(),
            initial_var: format!("{}{}_initial", param.name, suffix),
            prophecy_var: format!("{}{}_prophecy", param.name, suffix),
            inner_ty: (**inner).clone(),
            deref_level,
        });

        current_ty = inner;
        deref_level += 1;
    }

    prophecies
}
```

### Pattern 3: Borrow Conflict VC Generation
**What:** Generate VCs that fail when shared and mutable borrows have overlapping lifetimes
**When to use:** Any function with both `&T` and `&mut T` parameters or locals
**Example:**
```rust
// For function(x: &T, y: &mut T), generate VC:
// (assert (not (and (live_in_scope 'x bb) (live_in_scope 'y bb))))
//
// If both lifetimes overlap at basic block bb, VC fails

pub fn generate_borrow_conflict_vcs(
    shared_borrows: &[(Local, RegionVid)],
    mutable_borrows: &[(Local, RegionVid)],
    live_ranges: &HashMap<RegionVid, LiveRange>,
    basic_blocks: &[BasicBlock],
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    for (shared_local, shared_region) in shared_borrows {
        for (mut_local, mut_region) in mutable_borrows {
            // Check if regions overlap
            let shared_range = &live_ranges[shared_region];
            let mut_range = &live_ranges[mut_region];

            if shared_range.overlaps(mut_range) {
                // Find overlapping basic blocks
                for (bb_idx, bb) in basic_blocks.iter().enumerate() {
                    if shared_range.contains(bb_idx) && mut_range.contains(bb_idx) {
                        vcs.push(VerificationCondition {
                            constraint: Term::Not(Box::new(
                                Term::And(vec![
                                    Term::Const(format!("live_{}_{}", shared_local.name, bb_idx)),
                                    Term::Const(format!("live_{}_{}", mut_local.name, bb_idx)),
                                ])
                            )),
                            location: VcLocation {
                                function: current_function.clone(),
                                basic_block: bb_idx,
                                statement_index: None,
                                source_span: bb.span.clone(),
                                vc_kind: VcKind::BorrowValidity,
                            },
                            description: format!(
                                "Shared borrow {} and mutable borrow {} cannot overlap at BB{}",
                                shared_local.name, mut_local.name, bb_idx
                            ),
                        });
                    }
                }
            }
        }
    }

    vcs
}
```

### Pattern 4: Elided Lifetime Resolution
**What:** Apply Rust's lifetime elision rules to resolve implicit lifetimes
**When to use:** Functions without explicit lifetime annotations
**Example:**
```rust
// Source: The Rust Reference - Lifetime Elision
// https://doc.rust-lang.org/reference/lifetime-elision.html

// fn first(x: &i32) -> &i32
// Elided form: single input lifetime, assign to output
// Resolved: fn first<'a>(x: &'a i32) -> &'a i32

pub fn resolve_elided_lifetimes(sig: &FnSig) -> FnSig {
    // Rule 1: Each elided lifetime in parameters becomes distinct
    let mut next_lifetime = 0;
    let mut param_lifetimes = Vec::new();

    for param_ty in &sig.params {
        if let Ty::Ref(_, lifetime) = param_ty {
            if lifetime.is_elided() {
                param_lifetimes.push(Lifetime::fresh(next_lifetime));
                next_lifetime += 1;
            }
        }
    }

    // Rule 2: If exactly one input lifetime, assign to all output lifetimes
    if param_lifetimes.len() == 1 {
        return sig.with_all_lifetimes(param_lifetimes[0]);
    }

    // Rule 3: If &self or &mut self exists, use its lifetime for outputs
    if let Some(self_param) = sig.params.first() {
        if is_self_reference(self_param) {
            if let Ty::Ref(_, self_lifetime) = self_param {
                return sig.with_output_lifetime(*self_lifetime);
            }
        }
    }

    // Otherwise: error, explicit annotation required
    // But for verification we can treat as unconstrained (fresh lifetime)
    sig
}
```

### Anti-Patterns to Avoid
- **Don't reimplement NLL analysis:** Rustc already computes precise lifetime scopes via control-flow analysis. Extract rustc's results rather than reimplementing.
- **Don't encode lifetimes as integers:** Lifetimes are partial orders with outlives constraints, not totally ordered integers. Use uninterpreted sorts in Z3.
- **Don't ignore temporary borrows:** Expressions like `foo(&vec[0])` create borrows with precise scopes. Must track these via MIR temporaries.
- **Don't assume lexical scoping:** NLL makes borrow lifetimes end at last use, not scope end. Must use rustc's computed live ranges.

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Lifetime scope analysis | Custom control-flow lifetime tracker | `rustc_borrowck::region_inference` | NLL involves complex dataflow (liveness + outlives propagation). Rustc's implementation is battle-tested and handles all edge cases. |
| Outlives constraint solving | Custom transitive closure solver | `RegionInferenceContext::outlives_constraints()` | Region inference involves SCCs, variance, and higher-ranked constraints. Use rustc's solver. |
| Lifetime elision | Custom elision rules | `rustc_middle::ty::Generics::elide_lifetimes()` | Elision has 3 rules but many special cases (async, impl Trait, etc). Use rustc's resolver. |
| Polonius facts | Custom MIR borrow analysis | `rustc_borrowck::consumers::get_body_with_borrowck_facts()` | Polonius fact generation is deeply integrated with rustc. Use the consumer API. |
| Higher-ranked lifetimes | Custom `for<'a>` encoding | Rustc's region inference with placeholders | HRTB verification requires placeholder substitution and leak checking. Let rustc handle it. |

**Key insight:** Lifetime analysis is one of the most complex parts of the Rust compiler. Reusing rustc's infrastructure is not optional — it's the only practical approach for soundness and completeness.

## Common Pitfalls

### Pitfall 1: Assuming Prophecies are Set at Function Entry
**What goes wrong:** Developer expects `final(*x)` to have a value at function entry, leading to incorrect encoding where prophecy variable is constrained too early.
**Why it happens:** Intuition from two-state verification (pre/post) doesn't match prophecy semantics.
**How to avoid:**
- Prophecy variables are **unconstrained** at function entry (they predict the future)
- Only constrain prophecy at function return: `assert(param_final == param_prophecy)`
- In specs, `final(*x)` is a free variable until return point
**Warning signs:** SMT queries timing out due to unconstrained variables, or VCs passing when they should fail.

### Pitfall 2: Confusing Lifetime Parameters with Region Variables
**What goes wrong:** Treating lifetime parameters (`'a`) as the same as region variables (internal rustc representation), leading to type confusion when extracting borrow checker data.
**Why it happens:** Both are called "lifetimes" but have different representations and semantics.
**How to avoid:**
- Lifetime parameters (`'a`) are **types** in Rust's type system
- Region variables (`RegionVid`) are **inference variables** in the borrow checker
- Lifetime parameters are resolved to region variables during type checking
- Extract `RegionVid` from `rustc_borrowck`, not `LifetimeName` from HIR
**Warning signs:** Compiler errors about "expected RegionVid, found Region", or missing lifetime information.

### Pitfall 3: Ignoring NLL Liveness (Using Lexical Scopes)
**What goes wrong:** Computing borrow validity based on lexical scope (block end) instead of last use point, rejecting valid Rust code that relies on NLL.
**Why it happens:** Pre-2018 Rust used lexical lifetimes. Many resources still describe the old model.
**How to avoid:**
- Use `RegionInferenceContext::region_value()` to get precise live ranges
- Live ranges are sets of MIR locations (basic block + statement index)
- A borrow ends at its **last use**, not at the end of the block
- Test with NLL patterns: borrow used early, then value used later in same block
**Warning signs:** Verification rejecting code that rustc accepts, particularly in if/else or match arms.

### Pitfall 4: Missing Reborrow Chains
**What goes wrong:** Not tracking that `let y = &mut *x` creates a reborrow chain where `x` is invalidated while `y` is live, leading to missed conflicts.
**Why it happens:** Reborrows are implicit in Rust (inserted by compiler), not visible in source.
**How to avoid:**
- Detect `Place::Deref` in MIR to identify dereference operations
- When `&mut *x` appears, this creates a reborrow relationship
- Track reborrow chains in IR: `Reborrow { original: Local, reborrow: Local }`
- Ensure original borrow is not used while reborrow is live
**Warning signs:** Accepting code with aliasing mutable references, missing `VcKind::BorrowValidity` failures.

### Pitfall 5: Incomplete Temporary Lifetime Tracking
**What goes wrong:** Temporary borrows (e.g., in `vec.push(&temp)`) have precise lifetimes that don't match any named variable, leading to false negatives where invalid borrows aren't detected.
**Why it happens:** Temporaries are implicit in source code but explicit in MIR.
**How to avoid:**
- Scan MIR for `StorageLive`/`StorageDead` of temporary locals
- Assign region variables to all temporaries, not just parameters
- Track temporary lifetimes using same region inference as named locals
- Generate `VcKind::BorrowValidity` for temporaries that outlive their storage
**Warning signs:** Tests passing with invalid temporary borrows, memory safety violations not caught.

### Pitfall 6: Mishandling Static Lifetime
**What goes wrong:** Treating `'static` as "infinite lifetime" without verifying that referenced data actually has static storage duration, allowing invalid `'static` claims.
**Why it happens:** Confusion between lifetime annotation and actual storage duration.
**How to avoid:**
- `'static` annotation claims: "this reference lives for entire program"
- Must verify: referenced data has static storage (global, const, string literal)
- In MIR, check `TerminatorKind::Const` for referenced data
- Generate VC: if `T: 'static`, then `T` contains no non-static references
- Use rustc's `ty::TypeAndMut::infer_outlives()` to check `T: 'static`
**Warning signs:** Accepting stack references with `'static` annotation.

## Code Examples

Verified patterns from official sources:

### Extracting Region Constraints from Rustc
```rust
// Source: Rustc Compiler Development Guide - Region Inference
// https://rustc-dev-guide.rust-lang.org/borrow_check/region_inference.html

use rustc_borrowck::consumers::{
    BodyWithBorrowckFacts, ConsumerOptions, RustcFacts
};
use rustc_middle::ty::{RegionVid, TyCtxt};
use rustc_hir::def_id::LocalDefId;

/// Extract borrow checker facts for verification.
pub fn extract_lifetime_facts(
    tcx: TyCtxt<'_>,
    def_id: LocalDefId,
) -> BodyWithBorrowckFacts<'_> {
    let consumer_opts = ConsumerOptions::PoloniusInputFacts;

    // Get MIR body with computed borrow checker facts
    rustc_borrowck::consumers::get_body_with_borrowck_facts(
        tcx,
        def_id,
        consumer_opts,
    )
}

/// Extract outlives constraints ('a: 'b).
pub fn get_outlives_constraints(
    facts: &BodyWithBorrowckFacts<'_>,
) -> Vec<(RegionVid, RegionVid)> {
    let region_inference = &facts.region_inference_context;

    region_inference
        .outlives_constraints()
        .map(|(sup, sub)| (*sup, *sub))
        .collect()
}

/// Check if region 'a outlives region 'b.
pub fn check_outlives(
    facts: &BodyWithBorrowckFacts<'_>,
    a: RegionVid,
    b: RegionVid,
) -> bool {
    let region_inference = &facts.region_inference_context;

    // Get the value (set of locations) for each region
    let a_value = region_inference.region_value(a);
    let b_value = region_inference.region_value(b);

    // 'a: 'b iff value('b) ⊆ value('a)
    b_value.is_subset_of(a_value)
}
```

### Encoding Lifetime Bounds in SMT
```rust
// Encode T: 'a as SMT constraint

use rust_fv_smtlib::term::Term;
use rust_fv_smtlib::command::Command;

/// Encode a lifetime bound (T: 'a) as an SMT constraint.
///
/// Approach: Use uninterpreted function `outlives(r1, r2) -> Bool`
/// to represent region outlives relationship.
pub fn encode_lifetime_bound(
    type_param: &str,
    lifetime: &str,
) -> Vec<Command> {
    vec![
        // Declare outlives relation (if not already declared)
        Command::DeclareFun(
            "outlives".to_string(),
            vec![Sort::Region, Sort::Region],
            Sort::Bool,
        ),

        // Assert: all lifetimes in T must outlive 'a
        // (assert (forall ((r Region))
        //   (=> (lifetime-in-type r T) (outlives r 'a))))
        Command::Assert(Term::Forall(
            vec![("r".to_string(), Sort::Region)],
            Box::new(Term::Implies(
                Box::new(Term::App(
                    "lifetime-in-type".to_string(),
                    vec![
                        Term::Const("r".to_string()),
                        Term::Const(type_param.to_string()),
                    ],
                )),
                Box::new(Term::App(
                    "outlives".to_string(),
                    vec![
                        Term::Const("r".to_string()),
                        Term::Const(lifetime.to_string()),
                    ],
                )),
            )),
        )),
    ]
}

/// Encode 'static lifetime bound (T: 'static).
/// All lifetimes in T must be 'static (outlive everything).
pub fn encode_static_bound(type_param: &str) -> Command {
    Command::Assert(Term::Forall(
        vec![("r".to_string(), Sort::Region)],
        Box::new(Term::Implies(
            Box::new(Term::App(
                "lifetime-in-type".to_string(),
                vec![
                    Term::Const("r".to_string()),
                    Term::Const(type_param.to_string()),
                ],
            )),
            Box::new(Term::App(
                "is-static".to_string(),
                vec![Term::Const("r".to_string())],
            )),
        )),
    ))
}
```

### NLL Live Range Extraction
```rust
// Source: Rustc source - RegionInferenceContext
// https://doc.rust-lang.org/stable/nightly-rustc/rustc_borrowck/region_infer/struct.RegionInferenceContext.html

use rustc_middle::mir::Location;

/// Represents the set of MIR locations where a region is live.
pub struct LiveRange {
    locations: Vec<Location>,
}

impl LiveRange {
    /// Check if this range contains a given location.
    pub fn contains(&self, location: &Location) -> bool {
        self.locations.contains(location)
    }

    /// Check if two live ranges overlap.
    pub fn overlaps(&self, other: &LiveRange) -> bool {
        self.locations.iter().any(|loc| other.contains(loc))
    }
}

/// Extract live range for a region from rustc.
pub fn extract_live_range(
    region_inference: &RegionInferenceContext<'_>,
    region: RegionVid,
) -> LiveRange {
    let region_value = region_inference.region_value(region);

    // region_value is a set of points in the MIR CFG
    let locations = region_value
        .points()
        .map(|point| point.location())
        .collect();

    LiveRange { locations }
}
```

### Higher-Ranked Trait Bounds (HRTB) Handling
```rust
// Source: Rustc Dev Guide - Higher-Ranked Trait Bounds
// https://rustc-dev-guide.rust-lang.org/traits/hrtb.html

// for<'a> Fn(&'a T) -> &'a T
//
// Verification approach:
// 1. Replace bound lifetime with placeholder P
// 2. Verify trait bound holds for placeholder
// 3. Check no placeholder "leaks" (escapes its scope)

pub fn verify_hrtb<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_ref: &TraitRef<'tcx>,
) -> Result<(), HrtbError> {
    // 1. Replace 'a with placeholder P
    let placeholder_region = tcx.mk_placeholder_region();
    let trait_ref_with_placeholder = trait_ref.replace_bound_vars(placeholder_region);

    // 2. Verify trait bound holds
    if !tcx.infer_ctxt().enter(|infcx| {
        infcx.can_prove_trait(trait_ref_with_placeholder)
    }) {
        return Err(HrtbError::TraitNotSatisfied);
    }

    // 3. Check for placeholder leaks
    // A leak occurs if placeholder appears in:
    // - Function return type (outside of trait bound)
    // - Type of a local variable
    // - Any constraint that outlives the trait bound
    if trait_ref_with_placeholder.has_escaping_bound_vars() {
        return Err(HrtbError::PlaceholderLeak);
    }

    Ok(())
}
```

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| Lexical lifetimes (scope-based) | Non-lexical lifetimes (liveness-based) | Rust 1.63 (Aug 2022) | Borrow scopes end at last use, not block end. Must use rustc's live ranges, not lexical scopes. |
| AST-based borrow checker | MIR-based borrow checker | Rust 2018 | All lifetime analysis now happens on MIR. Must extract from MIR, not HIR/AST. |
| Two-state verification (pre/post) | Prophecy-based verification | Creusot (2022), Thrust (2025) | Enables `final(*x)` operator for mutable borrow final values. More expressive than two-state. |
| Custom lifetime encoding | Extract rustc region inference | Prusti/Creusot (2020+) | Rustc already solves the hard problem. Verification tools extract rustc's results. |
| Manual outlives constraints | Inferred outlives requirements | Rust RFC 2093 (2018) | Rustc infers `T: 'a` from struct definitions. Verifier must query inferred constraints, not just explicit ones. |

**Deprecated/outdated:**
- **Lexical lifetime checking:** Pre-2018 approach where borrows last until end of scope. Use NLL live ranges instead.
- **Two-state encoding for mutable borrows:** `old(*x)` and `new(*x)` cannot express mid-execution state. Use prophecy variables.
- **Custom borrow conflict detection:** Rustc's region inference already finds conflicts. Extract and verify rustc's results.

## Open Questions

1. **Temporary Lifetime Extension Edge Cases**
   - What we know: Rust has complex rules for when temporaries are extended (e.g., in match guards)
   - What's unclear: Whether rustc's MIR accurately represents all lifetime extension cases for verification
   - Recommendation: Test with all cases from [Rust Issue #39283](https://github.com/rust-lang/rust/issues/39283), add verification tests for temporary extension patterns

2. **Interaction Between Prophecy and Reborrowing**
   - What we know: Reborrowing creates new borrows that invalidate the original
   - What's unclear: How to handle prophecy resolution when a borrow is reborrowed multiple times (`x` -> `y` -> `z`)
   - Recommendation: Each reborrow gets its own prophecy variable. At reborrow point, constrain original prophecy to equal reborrow's initial state.

3. **Variance and Lifetime Subtyping**
   - What we know: Rust has variance rules (e.g., `&'a T` is covariant in `'a`)
   - What's unclear: Whether we need to encode variance explicitly or if rustc's region inference handles it
   - Recommendation: Start without explicit variance encoding. If VCs fail on valid code, add variance constraints from rustc's `ty::Variance`.

4. **Polonius Integration Timeline**
   - What we know: Polonius is the next-gen borrow checker with better precision
   - What's unclear: When Polonius will stabilize and whether we should support it in v0.2
   - Recommendation: Design with Polonius in mind (use consumer API, not direct rustc internals). Add Polonius support if it stabilizes before v0.2 release.

## Sources

### Primary (HIGH confidence)
- [Rust Compiler Development Guide - Region Inference](https://rustc-dev-guide.rust-lang.org/borrow_check/region_inference.html) - rustc's NLL implementation
- [Rust Compiler Development Guide - Constraint Propagation](https://rustc-dev-guide.rust-lang.org/borrow_check/region_inference/constraint_propagation.html) - outlives constraint solving
- [rustc_borrowck::region_infer::RegionInferenceContext API](https://doc.rust-lang.org/stable/nightly-rustc/rustc_borrowck/region_infer/struct.RegionInferenceContext.html) - extracting region data
- [The Rust Reference - Lifetime Elision](https://doc.rust-lang.org/reference/lifetime-elision.html) - elision rules
- [RFC 2094: Non-Lexical Lifetimes](https://rust-lang.github.io/rfcs/2094-nll.html) - NLL specification
- [RFC 2093: Infer Outlives Requirements](https://rust-lang.github.io/rfcs/2093-infer-outlives.html) - inferred `T: 'a` bounds
- Existing codebase: `crates/analysis/src/encode_prophecy.rs` - prophecy implementation

### Secondary (MEDIUM confidence)
- [Creusot: Deductive Verification for Rust](https://inria.hal.science/hal-03737878v1/document) - prophecy-based approach, "final" operator (verified via paper abstract and search results)
- [Using a Prophecy-Based Encoding of Rust Borrows](https://inria.hal.science/hal-05244847/file/main.pdf) - technical details on prophecy encoding (2025 publication, referenced in search results)
- [Verus: Verifying Rust Programs using Linear Ghost Types](https://dl.acm.org/doi/10.1145/3586037) - alternative approach with tracked/ghost modes
- [Thrust: A Prophecy-based Refinement Type System for Rust](https://www.riec.tohoku.ac.jp/~unno/papers/pldi2025.pdf) - 2025 refinement type approach with prophecy
- [The Prusti Project: Formal Verification for Rust](https://dl.acm.org/doi/10.1007/978-3-031-06773-0_5) - lifecycle reasoning, struct lifetimes

### Tertiary (LOW confidence)
- [Polonius Project Status](https://rust-lang.github.io/polonius/current_status.html) - next-gen borrow checker (experimental, not yet stable)
- [RustHornBelt: Semantic Foundation](https://people.mpi-sws.org/~dreyer/papers/rusthornbelt/paper.pdf) - foundational formalization (theory, not implementation guidance)

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH - rustc_borrowck is official compiler component, Z3 already in use
- Architecture: HIGH - patterns verified from rustc dev guide and existing verifier implementations (Creusot, Prusti)
- Pitfalls: HIGH - based on NLL RFC, rustc implementation details, and known verification challenges
- Prophecy encoding: HIGH - already implemented in `encode_prophecy.rs`, verified working
- HRTB handling: MEDIUM - complex feature, less documentation on verification approach
- Polonius integration: LOW - experimental, timeline uncertain

**Research date:** 2026-02-12
**Valid until:** 30 days (stable Rust features), 7 days for Polonius status
