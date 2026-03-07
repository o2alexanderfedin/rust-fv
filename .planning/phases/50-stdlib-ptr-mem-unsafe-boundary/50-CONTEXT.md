# Phase 50: Stdlib Ptr/Mem & Unsafe Boundary - Context

**Gathered:** 2026-03-06
**Status:** Ready for planning

<domain>
## Phase Boundary

Provide zero-config stdlib contracts for low-level pointer and memory operations, model FFI extern "C" functions as opaque callees with user-provided contracts, encode transmute with size/alignment/validity VCs, track MaybeUninit initialization state, and document the async multi-threaded limitation with W080 diagnostic. Five requirements: COMPL-23, COMPL-24, COMPL-25, LANG-15, LANG-16.

</domain>

<decisions>
## Implementation Decisions

### Ptr Contract Scope (COMPL-23)
- Core 4 functions: `ptr::read`, `ptr::write`, `ptr::copy`, `ptr::copy_nonoverlapping` with alignment and validity VCs
- Extended coverage: also `ptr::swap`, `ptr::replace`, `ptr::drop_in_place`, `ptr::null`/`ptr::null_mut`
- Overlap detection for copy/copy_nonoverlapping: address range check using bitvector arithmetic — assert `!(src <= dst+count*size && dst <= src+count*size)` (not separation logic predicates)
- Zero-config activation: auto-loaded via StdlibContractRegistry like existing Vec/HashMap contracts — any call to ptr functions automatically gets safety VCs

### Mem Contract Scope (COMPL-24)
- `mem::swap`: postcondition `a_post == b_pre && b_post == a_pre`
- `mem::replace`: postcondition `result == old_val && place_post == new_val`
- `mem::forget`: modeled as no-drop (skip destructor VCs for the value)
- `mem::size_of` / `mem::align_of`: encoded as SMT integer constants — useful for transmute VCs and FFI layout checks
- Zero-config activation via StdlibContractRegistry

### FFI extern "C" Modeling (LANG-15)
- New V110 FFI-specific diagnostic: separate from V060 opaque callee — message: "extern function not modeled — add #[requires]/#[ensures]"
- User contracts on extern items: adding `#[requires]`/`#[ensures]` to `extern "C" fn` declarations silences V110 and contracts are used at call sites
- Basic `#[repr(C)]` layout verification: for structs passed to extern fns, verify size and alignment match C ABI expectations using `mem::size_of`/`mem::align_of` SMT constants
- Variadic extern functions: allow contracts on fixed args, ignore variadic portion; V110 still fires for the variadic part
- Detection: MIR-level foreign item detection (not string matching on ABI)

### Transmute Encoding (LANG-16)
- Three-tier VCs for `mem::transmute`:
  1. Size compatibility: `size_of::<Src>() == size_of::<Dst>()` (compile-time for concrete types, SMT for generics)
  2. Alignment compatibility: `align_of::<Dst>()` divides the source address
  3. Bit-pattern validity: destination type validity constraints on the reinterpreted bits
- Pointer-to-pointer transmutes: additional mutability safety check — `*const T` to `*mut T` checked for aliasing rule violations (precision over simplicity)
- Validity constraints scope: all types with niche — bool (0/1), char (valid Unicode scalar), NonZero* (non-zero), references (non-null+aligned), enum niche values (Option<NonNull> etc.), padding bytes
- Validity implemented via type-introspection of destination Ty to generate appropriate SMT assertions

### MaybeUninit Tracking (LANG-16)
- Approach chosen for safety, precision, and completeness: ghost bool per local `is_initialized: Bool` in SMT preamble (follows RefCell ghost state pattern from Phase 48)
- `MaybeUninit::uninit()` → `is_initialized = false`
- `MaybeUninit::write(val)` / `MaybeUninit::new(val)` → `is_initialized = true`
- `MaybeUninit::assume_init()` → asserts `is_initialized == true`; generates MemorySafety VC
- ADT DefId matching for MaybeUninit detection (same pattern as NonNull from Phase 49)

### Async Limitation Documentation (COMPL-25)
- W080 diagnostic fires when async fn spawns threads (tokio::spawn, std::thread::spawn, or similar) — sound trigger toward safety
- Plain async fns without thread spawning don't warn (avoids noise)
- Suppressible via `#[allow(verify::sequential_model)]` attribute on the async fn
- Documentation: W080 diagnostic message links to mdbook page explaining sequential polling assumption, implications, and when safe to ignore
- Verification continues under sequential model even when W080 fires — function still verifies, just with the limitation noted

### Claude's Discretion
- Exact SMT encoding for ptr overlap range checks (bitvector width, signed vs unsigned comparison)
- StdlibContractRegistry wiring details for new ptr/mem modules
- MIR-level foreign item detection implementation
- Type introspection depth for niche validity constraints
- mdbook page content and location
- Test fixture design for all five requirement areas
- Diagnostic message wording for V110 and W080

</decisions>

<code_context>
## Existing Code Insights

### Reusable Assets
- `StdlibContractRegistry` + `register_contract()`: Zero-config contract loading pattern used by Vec/HashMap/Option/Result/Iterator/From — extend with ptr/mem modules
- `stdlib_contracts/` directory: 11 existing contract modules — add `ptr.rs` and `mem.rs`
- V060/V061 opaque callee diagnostics (Phase 37): Pattern for uncontracted callees — V110 follows same structure
- AlignmentSafety VCs + `bvsmod` on 64-bit bitvectors (Phase 47): Reuse for transmute alignment checks
- `UnsafeOperation` enum in vcgen.rs: Existing unsafe operation detection — extend with TransmuteUnsafe, FfiCall
- Heap-as-array memory model (Phase 11): `ptr::copy_nonoverlapping` overlap VCs build on byte-addressable heap
- `needs_null_check()` in vcgen.rs: Controls null-check VC generation — reference for ptr VCs
- RefCell ghost state pattern (Phase 48): Per-local ghost boolean declarations in SMT preamble — reuse for MaybeUninit
- `CoroutineInfo` + async polling model (Phase 23): Integration point for W080 detection
- `mem::size_of`/`mem::align_of` can be modeled as SMT constants using existing Sort::int() (Phase 46)

### Established Patterns
- ADT DefId matching: Used for Option, Result, Vec, NonNull detection — same pattern for MaybeUninit
- VcKind-based diagnostics: Each safety property gets VcKind + diagnostic code (V060-V100 series) — continue with V110 for FFI, W080 for async
- Per-local ghost variables: ProphecyInfo and RefCellGhostState patterns — reuse for MaybeUninit init tracking
- Zero-config stdlib contracts: StdlibContractRegistry auto-loads contracts without user action

### Integration Points
- `stdlib_contracts/ptr.rs` (new): Contracts for ptr::read/write/copy/copy_nonoverlapping/swap/replace/drop_in_place/null
- `stdlib_contracts/mem.rs` (new): Contracts for mem::swap/replace/forget/size_of/align_of
- `vcgen.rs`: Transmute VC generation (size+alignment+validity), W080 async detection, FFI V110 diagnostics
- `ir.rs`: MaybeUninit ghost state tracking, possible Ty::MaybeUninit variant
- `mir_converter.rs`: Detect MaybeUninit ADT, foreign item calls, transmute intrinsic calls
- `diagnostics.rs`: Add V110 (FFI opaque callee), W080 (async sequential model)
- `callbacks.rs`: Wire new diagnostics to driver output
- `encode_term.rs`: Transmute encoding as bitwise reinterpretation with validity constraints
- `docs/` or mdbook: W080 documentation page

</code_context>

<specifics>
## Specific Ideas

- Overlap detection uses address range arithmetic, not separation logic — simpler and matches Rust's actual safety invariant
- V110 is FFI-specific (not reusing V060) — clearer diagnostic message for FFI context
- Variadic externs get contracts on fixed args only — pragmatic compromise
- Transmute validity covers ALL types with niche (bool, char, NonZero, references, enum niches, padding) — comprehensive
- MaybeUninit follows RefCell ghost state pattern (Phase 48) — consistent codebase approach
- W080 only fires on thread-spawning async fns (not all async fns) — avoids noise while maintaining safety
- W080 is suppressible via attribute — lets users acknowledge the limitation
- repr(C) layout verification uses mem::size_of/align_of as SMT constants — dual purpose with mem contracts
- Pointer-to-pointer transmutes get additional mutability safety checks — prioritizing precision and completeness

</specifics>

<deferred>
## Deferred Ideas

None — discussion stayed within phase scope

</deferred>

---

*Phase: 50-stdlib-ptr-mem-unsafe-boundary*
*Context gathered: 2026-03-06*
