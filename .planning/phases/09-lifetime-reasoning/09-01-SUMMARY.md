---
phase: 09-lifetime-reasoning
plan: 01
subsystem: lifetime-analysis
tags: [ir, lifetime, borrow, prophecy, vcgen, diagnostics]
dependency_graph:
  requires: [phase-08-trait-objects]
  provides: [lifetime-ir-types, lifetime-analysis-module, nested-prophecies, borrow-validity-vcs]
  affects: [ir, vcgen, encode-prophecy, diagnostics]
tech_stack:
  added: [lifetime-analysis-module]
  patterns: [transitive-closure, reborrow-chain-detection, nested-prophecy-encoding]
key_files:
  created:
    - crates/analysis/src/lifetime_analysis.rs
  modified:
    - crates/analysis/src/ir.rs
    - crates/analysis/src/vcgen.rs
    - crates/analysis/src/encode_sort.rs
    - crates/analysis/src/encode_prophecy.rs
    - crates/analysis/src/lib.rs
    - crates/driver/src/callbacks.rs
    - crates/driver/src/diagnostics.rs
decisions:
  - "LifetimeParam, OutlivesConstraint, BorrowInfo, ReborrowChain as core lifetime IR types"
  - "Transitive closure for outlives resolution (fixpoint iteration)"
  - "Reborrow chain detection groups borrows with source_local into chains"
  - "ProphecyInfo.deref_level tracks nested mutable borrow layers (0 for direct, 1+ for nested)"
  - "Nested prophecy naming: _prophecy (level 0), _deref_prophecy (level 1), _deref{N}_prophecy (level N>1)"
  - "VcKind::BorrowValidity for borrow-specific verification diagnostics"
  - "region_sort() returns Sort::Uninterpreted(\"Region\") for lifetime encoding"
  - "compute_live_ranges uses conservative approximation; precise MIR-based ranges deferred to driver integration"
metrics:
  duration_minutes: 14
  completed_date: "2026-02-13"
  tasks_completed: 2
  files_created: 1
  files_modified: 32
  tests_added: 40
  loc_added: ~2116
---

# Phase 09 Plan 01: Lifetime IR and Analysis Infrastructure Summary

Lifetime IR types and analysis infrastructure with nested prophecy encoding for borrow validity verification.

## What Was Built

### Lifetime IR Types (ir.rs)

Added four core lifetime types between TraitImpl and ClosureInfo:

1. **LifetimeParam**: Named lifetime parameters ('a, 'b, 'static) with is_static flag
2. **OutlivesConstraint**: Represents 'a: 'b constraints (longer outlives shorter)
3. **BorrowInfo**: Tracks borrow origin (local_name, region, mutability, deref_level, source_local)
4. **ReborrowChain**: Groups original borrow and reborrow sequence

Extended Function struct with four new fields:
- `lifetime_params: Vec<LifetimeParam>`
- `outlives_constraints: Vec<OutlivesConstraint>`
- `borrow_info: Vec<BorrowInfo>`
- `reborrow_chains: Vec<ReborrowChain>`

Updated 25 files with Function construction sites to include these fields (all initialized to empty vecs).

### Lifetime Analysis Module (lifetime_analysis.rs)

**LifetimeContext struct** manages all lifetime information for a function:
- `lifetimes: HashMap<String, LifetimeParam>` - lifetime name → param info
- `outlives: Vec<OutlivesConstraint>` - all outlives constraints
- `borrow_map: HashMap<String, BorrowInfo>` - local name → borrow info
- `reborrow_chains: Vec<ReborrowChain>` - all reborrow chains

**Key Functions:**
- `extract_lifetime_params(func) -> Vec<LifetimeParam>` - extracts from Function.lifetime_params
- `resolve_outlives(func) -> Vec<OutlivesConstraint>` - transitive closure (if 'a: 'b and 'b: 'c, add 'a: 'c)
- `detect_reborrow_chains(func) -> Vec<ReborrowChain>` - groups borrows with source_local into chains
- `build_lifetime_context(func) -> LifetimeContext` - orchestrates extraction/resolution/detection
- `check_static_validity(borrow, context) -> bool` - checks if borrow is 'static or outlives 'static
- `compute_live_ranges(func) -> HashMap<String, Vec<usize>>` - conservative approximation (borrow live 0..num_blocks)

**LifetimeContext Methods:**
- `add_lifetime(&mut self, param)`, `add_outlives(&mut self, constraint)`, `register_borrow(&mut self, info)`
- `get_borrow(&self, local_name) -> Option<&BorrowInfo>`, `get_lifetime(&self, name) -> Option<&LifetimeParam>`
- `outlives_constraints(&self) -> &[OutlivesConstraint]`
- `borrows_in_region(&self, region) -> Vec<&BorrowInfo>`, `mutable_borrows() -> Vec<&BorrowInfo>`, `shared_borrows() -> Vec<&BorrowInfo>`

### Nested Prophecy Encoding (encode_prophecy.rs)

**Extended ProphecyInfo** with `deref_level: u32` field:
- 0 for direct &mut T
- 1 for outer layer of &mut &mut T
- 2+ for deeper nesting

**New Functions:**
- `detect_nested_prophecies(func) -> Vec<ProphecyInfo>` - walks type structure for nested &mut references, creates one ProphecyInfo per layer
- `nested_prophecy_declarations(prophecies) -> Vec<Command>` - generates SMT DeclareConst for each level, asserts level 0 initial = param

**Naming Convention:**
- Level 0: `{param}_initial`, `{param}_prophecy`
- Level 1: `{param}_deref_initial`, `{param}_deref_prophecy`
- Level N (N>1): `{param}_deref{N}_initial`, `{param}_deref{N}_prophecy`

For &mut &mut i32 param `_1`:
- Level 0: `_1_initial = _1`, `_1_prophecy` declared
- Level 1: `_1_deref_initial`, `_1_deref_prophecy` declared

Updated `detect_prophecies` to set `deref_level: 0` for backward compatibility.

### VcKind::BorrowValidity (vcgen.rs, callbacks.rs, diagnostics.rs)

**Added VcKind::BorrowValidity variant** for borrow-specific VCs (shared/mutable conflict, use-after-expiry, reborrow validity).

**Driver Integration:**
- `vc_kind_to_string(&VcKind::BorrowValidity) -> "borrow_validity"` (callbacks.rs)
- `vc_kind_description(&VcKind::BorrowValidity) -> "borrow validity violation"` (diagnostics.rs)
- `suggest_fix(&VcKind::BorrowValidity)` - guidance on checking lifetimes, avoiding overlapping borrows, ensuring source validity
- `format_borrow_validity_help()` - explains borrow lifecycle and common validity violations
- `report_text_only` adds BorrowValidity block with help message

### Region Sort (encode_sort.rs)

**Added `region_sort() -> Sort`** helper:
- Returns `Sort::Uninterpreted("Region")`
- Provides consistent way to reference Region sort throughout verification pipeline
- Used for lifetime region encoding in SMT

## Tests Added

### Lifetime IR Types (8 tests in ir.rs)
- `test_lifetime_param_creation`, `test_lifetime_param_static`
- `test_outlives_constraint`
- `test_borrow_info_shared`, `test_borrow_info_mutable`, `test_borrow_info_reborrow`
- `test_reborrow_chain`
- `test_function_lifetime_fields`

### Lifetime Analysis Module (20 tests in lifetime_analysis.rs)
- **LifetimeContext (7 tests):** new, add_lifetime, add_outlives, register_borrow, borrows_in_region, mutable_borrows, shared_borrows
- **extract_lifetime_params (2 tests):** with lifetimes, empty
- **resolve_outlives (3 tests):** simple, transitive ('a: 'b + 'b: 'c → 'a: 'c), no duplicates
- **detect_reborrow_chains (3 tests):** none, single (B reborrows A), deep (C reborrows B reborrows A)
- **build_lifetime_context (1 test):** full orchestration
- **check_static_validity (3 tests):** is_static, outlives_static, not_static
- **compute_live_ranges (1 test):** basic conservative approximation

### Nested Prophecy Encoding (8 tests in encode_prophecy.rs)
- `test_detect_nested_prophecies_simple` - &mut i32 → 1 prophecy at level 0
- `test_detect_nested_prophecies_nested` - &mut &mut i32 → 2 prophecies (level 0, 1)
- `test_detect_nested_prophecies_triple` - &mut &mut &mut i32 → 3 prophecies (level 0, 1, 2)
- `test_detect_nested_prophecies_shared_no_prophecy` - &i32 → 0 prophecies
- `test_nested_prophecy_naming_level0`, `test_nested_prophecy_naming_level1` - naming convention
- `test_nested_prophecy_declarations` - verify DeclareConst/Assert command generation
- `test_prophecy_info_deref_level_default` - backward compatibility (detect_prophecies → deref_level=0)

### VcKind and Diagnostics (4 tests in callbacks.rs, diagnostics.rs)
- `test_region_sort` - encode_sort.rs
- `test_vc_kind_to_string_borrow_validity` - callbacks.rs
- `test_vc_kind_description_borrow_validity`, `test_suggest_fix_borrow_validity` - diagnostics.rs

## Deviations from Plan

None - plan executed exactly as written.

## Key Implementation Details

**Transitive Closure Algorithm:**
```rust
while changed {
    let current_len = constraints.len();
    // For all constraint pairs, if c1.shorter == c2.longer, add transitive
    for c1 in &constraints {
        for c2 in &constraints {
            if c1.shorter == c2.longer {
                let transitive = OutlivesConstraint { longer: c1.longer, shorter: c2.shorter };
                if !constraints.contains(&transitive) && !new_constraints.contains(&transitive) {
                    new_constraints.push(transitive);
                }
            }
        }
    }
    constraints.extend(new_constraints);
    changed = constraints.len() > current_len;
}
```

**Reborrow Chain Detection:**
- Build map: source → [reborrows]
- For each borrow with reborrows, trace chain until no more reborrows
- Returns `ReborrowChain { original, reborrows }` per chain root

**Nested Prophecy Detection:**
- Walk type structure: `while let Ty::Ref(inner, Mutability::Mutable) = current_ty`
- Create ProphecyInfo for each level with appropriate naming
- Level-specific initial/prophecy variable names

**Conservative Live Ranges:**
- Current implementation: borrow live from block 0 to last block
- Future: driver will provide precise MIR-based live ranges (per research: "extract rustc's results")

## Integration Points

**For Plan 02 (Borrow Conflict VCs):**
- Use `LifetimeContext.mutable_borrows()`, `shared_borrows()` to detect conflicts
- Use `outlives_constraints()` for lifetime ordering
- Use `reborrow_chains` to validate reborrow validity

**For Plan 03 (End-to-End Lifetime Verification):**
- Use `build_lifetime_context(func)` to populate all lifetime information
- Use `check_static_validity(borrow, context)` for static borrow checks
- Use `detect_nested_prophecies(func)` for nested &mut &mut T parameters
- Use `nested_prophecy_declarations(prophecies)` for SMT encoding

**For Driver Integration:**
- Populate Function.lifetime_params from HIR/MIR
- Populate Function.outlives_constraints from rustc borrow checker
- Populate Function.borrow_info from MIR borrow data
- Replace `compute_live_ranges` conservative approximation with rustc's precise NLL live ranges

## Self-Check: PASSED

All claimed artifacts verified:

**Created Files:**
- [x] crates/analysis/src/lifetime_analysis.rs

**Modified Files:**
- [x] crates/analysis/src/ir.rs (LifetimeParam, OutlivesConstraint, BorrowInfo, ReborrowChain, Function fields)
- [x] crates/analysis/src/vcgen.rs (VcKind::BorrowValidity)
- [x] crates/analysis/src/encode_sort.rs (region_sort)
- [x] crates/analysis/src/encode_prophecy.rs (ProphecyInfo.deref_level, detect_nested_prophecies, nested_prophecy_declarations)
- [x] crates/analysis/src/lib.rs (pub mod lifetime_analysis)
- [x] crates/driver/src/callbacks.rs (vc_kind_to_string BorrowValidity)
- [x] crates/driver/src/diagnostics.rs (vc_kind_description, suggest_fix, format_borrow_validity_help)

**Commits:**
- [x] b4a4c8a: feat(09-01): add lifetime IR types and VcKind::BorrowValidity
- [x] 634646d: feat(09-01): create lifetime_analysis module and extend encode_prophecy for nested borrows

**Test Counts:**
- [x] 40 new tests (8 IR + 20 lifetime_analysis + 8 encode_prophecy + 4 driver)
- [x] Total workspace tests: 848 (was 820 before Task 1, added 28 in Task 2)
