# Codebase Concerns

**Analysis Date:** 2026-02-10

## Tech Debt

### Phase 1 Encoding Limitations

**Area:** Type encoding and cast handling

**Issue:** Aggregate types (tuples, structs, enums) are encoded as uninterpreted sorts with no semantic structure. This prevents any meaningful verification on composite data.

- **Files:** `crates/analysis/src/encode_sort.rs` (lines 19-21)
- **Impact:** Cannot verify properties of data structures; tuple and struct field access lose type information. Type casts treated as identity operations (line 188, `crates/analysis/src/vcgen.rs`).
- **Fix approach:** Phase 2 work - implement SMT datatype encoding with field/variant constructors and proper cast semantics

### Float Unsupported

**Area:** Floating-point arithmetic

**Issue:** Floating-point values are represented as uninterpreted constants (`FLOAT_UNSUPPORTED`), blocking any verification of float operations.

- **Files:** `crates/analysis/src/encode_term.rs` (lines 56-59)
- **Impact:** Any function using floats produces non-verifiable placeholder values
- **Fix approach:** Implement IEEE 754 floating-point encoding using SMT-LIB's `(_ FloatingPoint e s)` sort (infrastructure exists in `crates/smtlib/src/sort.rs`)

### Aggregate Construction and Discriminants Skipped

**Area:** Rvalue encoding

**Issue:** Aggregate construction and enum discriminants return `None` during encoding, silently losing semantic information.

- **Files:** `crates/analysis/src/vcgen.rs` (lines 191-198)
- **Impact:** Functions constructing tuples/structs/enums produce incomplete verification conditions; enum pattern matching cannot be verified
- **Fix approach:** Implement aggregate encoding using SMT datatype constructors

### Incomplete Specification Parser

**Area:** Specification expression parsing

**Issue:** `parse_simple_spec()` in `crates/analysis/src/vcgen.rs` (lines 429+) only handles basic comparisons and logical operators. Complex expressions, function calls, and quantifiers are not supported.

- **Files:** `crates/analysis/src/vcgen.rs` (lines 429-450)
- **Impact:** Preconditions/postconditions limited to simple inequalities; cannot express complex properties
- **Fix approach:** Extend parser to handle full expression syntax; integrate with actual specification language (Phase 2)

---

## Known Bugs

### Array Length Encoding Missing

**Issue:** Array length operations return `None` during rvalue encoding, losing semantic information about array bounds.

- **Symptoms:** Functions using `.len()` on arrays/slices cannot be fully verified
- **Files:** `crates/analysis/src/vcgen.rs` (lines 183-185)
- **Trigger:** Any code path accessing array length
- **Workaround:** None - just loses information silently

### Unused SSA Counter in Assignment Encoding

**Issue:** `_ssa_counter` parameter in `encode_assignment()` is declared but never used (line 155 in `crates/analysis/src/vcgen.rs`).

- **Symptoms:** False positives on multiple assignments to same variable - second assignment overwrites first in encoding
- **Files:** `crates/analysis/src/vcgen.rs` (line 155)
- **Trigger:** Functions with control flow where same variable is assigned in different paths
- **Workaround:** Rename variables or reorder basic blocks to avoid conflicts

---

## Security Considerations

### External Process Execution Without Validation

**Area:** Z3 solver invocation

**Risk:** Spawning Z3 subprocess with user-controlled timeout and extra arguments without proper shell escaping.

- **Files:** `crates/solver/src/solver.rs` (lines 69-75)
- **Current mitigation:** Arguments passed as Vec, not via shell - but extra_args could contain arbitrary strings if user supplies them
- **Recommendations:**
  - Validate extra_args whitelist (e.g., only allow `-v`, `-t`, specific options)
  - Document that this is for embedded use only, not CLI tool
  - Add tests with malicious argument injection

### No Contract Verification Without Solver

**Area:** Verification callback chain

**Risk:** If Z3 is not found, verification silently fails and reports "No verification conditions generated" (lines 97-100, `crates/driver/src/callbacks.rs`).

- **Files:** `crates/driver/src/callbacks.rs` (lines 94-100)
- **Current mitigation:** Error message printed to stderr
- **Recommendations:**
  - Make verification failure a hard error (exit 1)
  - Add `--allow-unverified` flag for CI scripts that want to continue
  - Test detection of missing Z3

---

## Performance Bottlenecks

### SMT-LIB Formatter Complexity

**Problem:** The formatter module is 1300+ lines (`crates/smtlib/src/formatter.rs`). Most of this is repetitive Display implementations for Term variants.

- **Files:** `crates/smtlib/src/formatter.rs` (complete file)
- **Cause:** SMT-LIB has ~50 term constructors, each needs formatting
- **Current impact:** Maintainability issue, not runtime (formatting is fast)
- **Improvement path:**
  - Macro-based code generation for term Display
  - Consider alternative: use a formatting trait that generates templates

### Parser Module Size

**Problem:** Parser is 533 lines, mixing SMT-LIB parsing with model extraction. Complex regex-based extraction of model values.

- **Files:** `crates/solver/src/parser.rs`
- **Cause:** No proper SMT-LIB2 parser library available (z3-sys doesn't expose it)
- **Current impact:** Fragile to Z3 output format changes
- **Improvement path:**
  - Consider lighter parsing (e.g., use nom or pest)
  - Add regression tests on actual Z3 output samples
  - Version pin Z3 to ensure format stability

### VCGen Walks All Basic Blocks Multiple Times

**Problem:** `collect_assignments_up_to()` walks basic blocks again for each VC generated. With N statements and M VCs, this is O(N*M).

- **Files:** `crates/analysis/src/vcgen.rs` (lines 125-148)
- **Cause:** Straightforward implementation without caching
- **Current impact:** Negligible for Phase 1 (small functions), but scales poorly
- **Improvement path:**
  - Cache assignments per block during initial walk
  - Precompute path conditions

---

## Fragile Areas

### Basic Block Terminator Conversion

**Area:** Control flow translation

**Files:** `crates/driver/src/mir_converter.rs` (line 82)

**Why fragile:** Falls back to `ir::Terminator::Unreachable` if terminator is missing. This masks rustc MIR generation bugs.

**Safe modification:**
  - Add explicit match on all terminator kinds
  - Panic with detailed error on unexpected terminator
  - Add test for each terminator variant

**Test coverage:**
  - `crates/analysis/tests/e2e_verification.rs` has 4 e2e tests covering basic control flow
  - No unit tests on mir_converter.rs itself
  - Missing: tests for Panic, Yield, GeneratorDrop, ThreadLocalInit

### Contract Extraction from HIR Attributes

**Area:** Macro-based specification parsing

**Files:** `crates/driver/src/callbacks.rs` (lines 92-92, calls extract_contracts)

**Why fragile:** Doc attribute format is a private contract between macro expansion and driver. Any change to macro breaks extraction.

**Safe modification:**
  - Document the format explicitly
  - Add round-trip tests: write spec → macro → extraction → verify format
  - Use structured attributes if rustc 1.90+ available

**Test coverage:**
  - `crates/macros/tests/basic.rs` tests that macros compile and don't break code
  - No tests verify extraction of contracts from expanded attributes

### Specification Expression Parsing

**Area:** Simple spec parser in vcgen

**Files:** `crates/analysis/src/vcgen.rs` (lines 429-450)

**Why fragile:** Hand-written recursive descent parser with no error recovery. Invalid specs silently return `None`.

**Safe modification:**
  - Return `Result<Term, ParseError>` instead of `Option<Term>`
  - Add detailed error messages with location info
  - Use parser combinator library (nom, pest)

**Test coverage:**
  - Basic success cases tested
  - No negative tests for malformed expressions

---

## Scaling Limits

### Single-function Verification Only

**Constraint:** Current design verifies one function at a time, no inter-procedural analysis.

- **Current capacity:** Handles functions with ~20-30 basic blocks (~100 lines)
- **Limit:** Hits solver timeout (configurable, default none) or memory limits
- **Scaling path:**
  - Add function summaries (precondition + postcondition, no body)
  - Implement bottom-up verification (verify callees first)
  - Cache verification results per function signature

### SMT-LIB Variable Naming

**Constraint:** All variables flattened into global namespace. Projections encoded as dotted names (`_1.0.1.deref[_2]`).

- **Current capacity:** Hundreds of variables, many with projections
- **Limit:** O(name_length) string operations, solver struggling with redundant variables
- **Scaling path:**
  - Use numeric variable indices with encoding table
  - Implement proper scoping in SMT
  - Compress projection chains (e.g., alias deeply nested paths)

### Bitvector Width Assumptions

**Constraint:** All bitvectors 64-bit or smaller for array indices; raw pointers always 64-bit.

- **Current capacity:** Standard x86/ARM architectures
- **Limit:** Fails on 128-bit systems or custom pointer widths
- **Scaling path:**
  - Query target architecture from rustc
  - Make pointer width configurable

---

## Dependencies at Risk

### Z3 as Hard Dependency

**Risk:** Project requires Z3 binary at runtime. No fallback solver implemented.

- **Impact:** Verification pipeline breaks if Z3 is missing, not installed, or version incompatible
- **Current mitigation:** Auto-detection with common paths + PATH lookup
- **Migration plan:**
  - Implement fallback to CVC5 (different SMT-LIB output format, needs parser changes)
  - Make solver pluggable trait (Z3Solver -> trait Solver + impl for each backend)
  - Support both Z3 and CVC5 as optional features

### rustc_driver Unstable API

**Risk:** `rustc_driver::Callbacks` and related types are nightly-only. Project targets Rust 1.85.0 (stable) but driver crate is nightly-only.

- **Impact:** Cannot use on stable Rust; breaks if rustc internals change (which they do frequently)
- **Current mitigation:** Feature-gated driver, can still build without it
- **Migration plan:**
  - Track rustc versions that work and document compatibility
  - Consider using rustc-plugin approach (if available in 1.85+)
  - Add CI matrix testing against multiple rustc versions

### Procedural Macro Attribute Format

**Risk:** Doc attributes are unstable; no guarantee format will be preserved.

- **Impact:** Macro expansion and HIR extraction could diverge
- **Current mitigation:** Round-trip tests
- **Migration plan:**
  - Migrate to `#![register_tool]` + custom attributes when stabilized
  - Add version check at compile time

---

## Missing Critical Features

### No Loop Invariants

**Problem:** Loops are unrolled by rustc MIR; no support for loop invariants or unbounded loops.

**Blocks:** Cannot verify any function with loops that don't unroll

**Affects:** Real-world code (most functions have loops)

**Timeline:** Phase 2 feature

### No Mutable Borrow Reasoning

**Problem:** References treated as transparent (see encode_sort.rs line 47). Mutable borrows not tracked.

**Blocks:** Cannot verify borrowing patterns or mutation safety

**Affects:** Any use of mutable references

**Timeline:** Phase 2 feature (requires prophecy operators)

### No Unsafe Code Support

**Problem:** `unsafe` blocks converted to IR same as safe code; no special handling of raw pointers, mem operations.

**Blocks:** Cannot verify unsafe code

**Affects:** Low-level code, FFI, systems programming

**Timeline:** Phase 3 feature

### No Recursive Function Support

**Problem:** Recursion would loop forever in VCGen. No function summaries or decreasing variants.

**Blocks:** Cannot verify recursive functions

**Affects:** Tree traversal, recursive algorithms

**Timeline:** Phase 2 feature (with function summaries)

---

## Test Coverage Gaps

### mir_converter.rs Untested

**What's not tested:** Direct conversion of rustc MIR to IR. Currently only tested end-to-end.

- **Files:** `crates/driver/src/mir_converter.rs`
- **Risk:** Bugs in MIR translation go undetected until user reports
- **Priority:** HIGH
- **Approach:** Unit test with synthetic MIR structures

### Contract Extraction Untested

**What's not tested:** Actual extraction of contracts from HIR attributes. Macro expansion tested, but not the driver-side extraction.

- **Files:** `crates/driver/src/callbacks.rs` (extract_contracts function)
- **Risk:** Changes to macro format could break extraction silently
- **Priority:** HIGH
- **Approach:** Integration test: compile code with macros, verify driver finds contracts

### Parser Error Cases Untested

**What's not tested:** Invalid SMT-LIB output, malformed models, missing `sat`/`unsat` in output.

- **Files:** `crates/solver/src/parser.rs`
- **Risk:** Parser panics or produces silent errors on unexpected Z3 output
- **Priority:** MEDIUM
- **Approach:** Fuzzing tests with Z3 output mutations

### Specification Parser Edge Cases

**What's not tested:** Complex expressions, nested operators, operator precedence, error cases.

- **Files:** `crates/analysis/src/vcgen.rs` (parse_simple_spec)
- **Risk:** Specs silently fail to parse, returning None, leading to under-verification
- **Priority:** MEDIUM
- **Approach:** Property-based testing of parser on expression grammar

### VCGen Completeness

**What's not tested:** Full function CFG coverage - does every code path get a VC? Are all operations checked?

- **Files:** `crates/analysis/src/vcgen.rs`
- **Risk:** VCs generated for only some paths, leading to undetected bugs
- **Priority:** MEDIUM
- **Approach:** Instrumented VCGen that tracks which IR statements produced VCs; verify all produce at least one

---

## Architectural Concerns

### Linear SSA Assumption

**Issue:** VCGen assumes linear execution (walk blocks in order), but MIR CFG can have arbitrary loop/branch structures.

**Impact:**
- Multiple assignments to same variable not properly tracked (SSA counter unused)
- Loop bodies visited multiple times, generating duplicate VCs
- Backward jumps not properly handled in assignment collection

**Fix:** Implement true SSA renaming or path-sensitive analysis

### No Handling of Unreachable Code

**Issue:** Unreachable blocks still generate VCs, potentially creating SAT problems from unreachable paths.

**Impact:** False negatives if unreachable code contains contradictions that hide real bugs

**Files:** `crates/analysis/src/vcgen.rs` (doesn't check block reachability)

**Fix:** Mark reachable blocks during initial walk; skip unreachable ones

### Monolithic Script Generation

**Issue:** All VCs for a function combined into few large SMT-LIB scripts (one per condition type). Each script re-encodes entire function semantics.

**Impact:** Large functions generate multi-MB scripts; solver struggles with size

**Files:** `crates/analysis/src/vcgen.rs` (base_script, collect_all_assignments)

**Fix:** Generate minimal scripts with only necessary context; use SMT-LIB includes or compose scripts

---

## Implementation Complexity

### smtlib/formatter.rs at 1300 Lines

**Observations:**
- Pure Display implementations
- Heavy duplication (each Term variant has similar formatting logic)
- No semantic validation

**Risk:** Hard to maintain, easy to introduce formatting bugs

**Improvement:** Extract common patterns into helper macros, consider code generation

### Type System Surface Area

**Observations:**
- `crates/analysis/src/ir.rs` defines 10+ type variants
- Each needs encoding, overflow checks, operand handling
- Floating-point, slices, raw pointers all have special cases

**Risk:** Easy to forget a variant; incomplete handling scattered across files

**Improvement:** Enum-based dispatch with exhaustiveness checking enabled

---

## Runtime Concerns

### No Timeout Handling for Individual VCs

**Issue:** Timeout is set at solver level, but if one large VC times out, the entire function fails.

- **Files:** `crates/solver/src/config.rs`, `crates/solver/src/solver.rs`
- **Impact:** Cannot distinguish "timed out" from "satisfiable" - both reported as Unknown
- **Fix:** Handle timeout separately; consider per-VC timeout or incremental checking

### Process Spawning Overhead

**Issue:** Each VC check spawns Z3 process. For a function with 20 statements, this is 20+ process starts.

- **Files:** `crates/solver/src/solver.rs` (Command::new)
- **Impact:** Verification can be slow even for small functions
- **Fix:** Consider Z3 server mode or in-process Z3 library (if available)

---

## Documentation Debt

### No VCGen Algorithm Documentation

**Files:** `crates/analysis/src/vcgen.rs`

**What's missing:**
- Formal specification of VC generation algorithm
- Explanation of why each VC is generated
- Proof sketch of soundness/completeness
- Examples of generated VCs

**Impact:** Hard for contributors to understand correctness or modify safely

### Missing Type Encoding Justification

**Files:** `crates/analysis/src/encode_sort.rs`, `crates/analysis/src/encode_term.rs`

**What's missing:**
- Why each Rust type maps to specific SMT sort
- Soundness argument for signed/unsigned bitvector operations
- Why references are transparent
- How overflow semantics match Rust semantics

---

## Summary of Priorities

**CRITICAL (blocks Phase 1 completion):**
- mir_converter.rs integration testing
- Contract extraction testing
- Z3 availability handling

**HIGH (Phase 2 blockers):**
- Aggregate type encoding
- Mutable borrow support
- Loop invariants
- Recursive function support

**MEDIUM (improve reliability):**
- SMT-LIB parser robustness
- Specification parser error handling
- Unreachable code detection
- SSA-based variable tracking

**LOW (code quality):**
- Formatter code generation
- Documentation
- Performance optimization (pre-Phase 3)

---

*Concerns audit: 2026-02-10*
