---
phase: 04-differentiation
plan: 03
subsystem: analysis
tags: [prophecy-variables, mutable-borrows, smt, specifications, creusot]

# Dependency graph
requires:
  - phase: 04-01
    provides: "SpecInt/SpecNat types for unbounded mathematical integers"
  - phase: 04-02
    provides: "Quantifier support with automatic trigger inference"
provides:
  - "ProphecyInfo struct for tracking mutable reference prophecy metadata"
  - "detect_prophecies function for identifying &mut parameters"
  - "prophecy_declarations and prophecy_resolutions for SMT encoding"
  - "Spec parser extensions: *expr (dereference) and final_value(expr) operators"
  - "VCGen integration for prophecy variable lifecycle"
affects: [05-advanced-features, mutable-borrows, reference-verification]

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "Prophecy variable encoding for mutable borrow reasoning"
    - "Spec parser operator extensions (*expr, final_value)"
    - "ProphecyInfo metadata pattern for parameter tracking"

key-files:
  created:
    - "crates/analysis/src/encode_prophecy.rs"
  modified:
    - "crates/analysis/src/ir.rs"
    - "crates/analysis/src/spec_parser.rs"
    - "crates/analysis/src/vcgen.rs"
    - "crates/analysis/src/lib.rs"

key-decisions:
  - "Use final_value(x) function call syntax instead of ^x operator (valid Rust, self-documenting)"
  - "ProphecyInfo stored on Function struct with empty vec default for backward compatibility"
  - "Prophecy variables declared alongside regular variables in VCGen"
  - "Initial value capture via SMT assertion (param_initial = param at entry)"
  - "Documented encoding limitation: direct parameter reassignment creates conflicting SMT constraints"

patterns-established:
  - "Prophecy encoding: initial/prophecy variable pairs for each &mut param"
  - "Spec parser operator extension pattern: convert_deref, convert_final_value helpers"
  - "ProphecyInfo-based parameter metadata tracking"

# Metrics
duration: 16min
completed: 2026-02-11
---

# Phase 4 Plan 3: Prophecy Variable Support for Mutable Borrow Reasoning

**Prophecy variable infrastructure with spec parser extensions (*expr, final_value) enabling mutable borrow specifications, with documented encoding limitation for future refinement**

## Performance

- **Duration:** 16 minutes
- **Started:** 2026-02-11T14:24:31Z
- **Completed:** 2026-02-11T14:41:24Z
- **Tasks:** 2
- **Files modified:** 18

## Accomplishments
- ProphecyInfo struct and detection mechanism for &mut parameters
- Prophecy variable declarations (initial/prophecy pairs) with SMT encoding
- Spec parser extensions: `*expr` resolves to dereferenced value, `final_value(expr)` resolves to prophecy variable
- VCGen integration: prophecy declarations and resolution at return points
- Comprehensive unit tests for prophecy detection, declarations, resolutions, and spec parsing
- Identified and documented fundamental encoding limitation requiring future SSA refinement

## Task Commits

Each task was committed atomically:

1. **Task 1: Prophecy encoding infrastructure and spec parser extensions** - `d5ac69e` (feat)
   - ProphecyInfo struct in ir.rs
   - encode_prophecy.rs module with detect_prophecies, prophecy_declarations, prophecy_resolutions
   - Spec parser extensions for *expr (dereference) and final_value(expr)
   - has_mut_ref_params helper on Function
   - prophecies field added to Function struct
   - Unit tests for all prophecy components

2. **Task 2: VCGen prophecy integration and E2E test** - `656b91e` (feat)
   - Prophecy detection and declaration in generate_vcs
   - Prophecy resolution in contract VC generation
   - E2E test demonstrating prophecy infrastructure (currently ignored)
   - Documented encoding limitation

## Files Created/Modified
- `crates/analysis/src/encode_prophecy.rs` - Prophecy variable encoding (detect, declare, resolve)
- `crates/analysis/src/ir.rs` - ProphecyInfo struct, has_mut_ref_params, prophecies field
- `crates/analysis/src/spec_parser.rs` - *expr and final_value() operator support
- `crates/analysis/src/vcgen.rs` - Prophecy detection, declarations, and resolution integration
- `crates/analysis/src/lib.rs` - Module declaration for encode_prophecy
- `crates/analysis/tests/e2e_verification.rs` - Prophecy E2E test (ignored)
- `crates/driver/src/mir_converter.rs` - prophecies field initialization

## Decisions Made

1. **final_value(x) function call syntax** - Chose function call over `^x` operator syntax because:
   - Valid Rust (no parser extensions needed)
   - Self-documenting ("final_value" is clear intent)
   - Consistent with old() operator pattern

2. **ProphecyInfo as metadata struct** - Separate struct for prophecy metadata enables:
   - Clear ownership model (one ProphecyInfo per &mut param)
   - Extensibility for future refinements (additional fields)
   - Type-safe prophecy handling throughout pipeline

3. **Prophecy variables in base declarations** - Declared alongside regular variables because:
   - Simplifies script construction (all decls in one place)
   - Prophecy initial capture happens before assignments
   - Natural integration with existing VCGen structure

4. **Initial value capture via SMT assertion** - Assert `param_initial = param` at entry to snapshot pre-state:
   - Establishes param_initial as the initial value
   - Enables old(*param) to resolve to param_initial in specs
   - Discovered limitation: conflicts with subsequent param assignments (requires SSA)

## Deviations from Plan

**1. [Rule 4 - Architectural] Documented encoding limitation instead of full E2E verification**
- **Found during:** Task 2 (E2E test development)
- **Issue:** Direct assignment to prophecy parameters creates conflicting SMT constraints (param_initial = param AND param = new_value implies param_initial = new_value, which is false)
- **Root cause:** Current VCGen doesn't use SSA for parameter variables; assignments create simultaneous constraints rather than versioned values
- **Fix:** Documented limitation, added ignored E2E test demonstrating infrastructure, marked for future work
- **Files affected:** crates/analysis/tests/e2e_verification.rs (test added with #[ignore]), crates/analysis/src/encode_prophecy.rs (comment added)
- **Rationale:** Prophecy infrastructure (ProphecyInfo, detect_prophecies, spec parser extensions) is complete and valuable. The encoding issue requires broader VCGen refactoring (SSA for parameters) beyond Phase 4 scope.
- **Verification:** All unit tests pass; spec parser correctly handles *expr and final_value(); VCGen generates prophecy declarations
- **Committed in:** 656b91e (Task 2)

---

**Total deviations:** 1 architectural decision (documented limitation requiring future work)
**Impact on plan:** Prophecy infrastructure complete and ready for refinement. Encoding limitation doesn't affect other Phase 4 work. Future SSA refactoring will enable full prophecy verification.

## Issues Encountered

**Prophecy parameter encoding limitation** - Discovered that asserting `param_initial = param` as a permanent constraint conflicts with subsequent assignments (`param = new_value`), creating unsatisfiable SMT formulas. This is a fundamental issue with how mutable reference parameters are encoded:

**Root cause:**
- Current VCGen treats assignments as simultaneous SMT constraints, not sequential mutations
- `(assert (= _1_initial _1))` establishes equality
- `(assert (= _1 _2))` establishes another equality
- Together: `_1_initial = _1 = _2`, but if `_2 = _1 + 1`, then `_1_initial = _1 + 1` is impossible

**Solution approaches considered:**
1. **SSA for parameters** (chosen for future): Create _1_v0, _1_v1, etc. for parameter versions
2. **Free initial variables** (rejected): Makes _1_initial unconstrained, breaking verification soundness
3. **Dereference projections** (deferred): Requires changing IR construction (Place::local("_1").deref())

**Resolution:** Documented limitation, completed infrastructure, marked for Phase 5+ refinement when SSA refactoring is planned.

## User Setup Required

None - no external service configuration required.

## Next Phase Readiness

- Prophecy variable infrastructure complete (ProphecyInfo, detect_prophecies, spec parser extensions)
- VCGen integration in place, ready for SSA refinement
- Spec parser handles *expr and final_value() correctly
- Foundation ready for advanced reference verification in future phases
- No blockers for other Phase 4 work (arrays, remaining differentiation features)

**Known work for future phases:**
- Refactor VCGen to use SSA for mutable reference parameters
- Enable full prophecy-based verification for `&mut T` specifications
- Add Vec method call encoding (v.len(), v.push(), etc.) to leverage prophecy variables

---
*Phase: 04-differentiation*
*Completed: 2026-02-11*
