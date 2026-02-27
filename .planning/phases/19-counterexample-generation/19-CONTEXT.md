# Phase 19: Counterexample Generation - Context

**Gathered:** 2026-02-19
**Status:** Ready for planning

<domain>
## Phase Boundary

When `cargo verify` finds a counterexample, transform the raw SMT model dump into a human-readable, Rust-typed counterexample with source locations — shown inline in the terminal via ariadne and emitted as structured JSON in `--output-format=json`. This phase is presentation and output-contract only; the SMT solver and VCGen are unchanged.

</domain>

<decisions>
## Implementation Decisions

### Variable Selection
- Show **all variables live at the point of failure** — not just spec-referenced ones; more context is better
- For variables reassigned during execution (SSA versions): show **both** the initial value and the value at failure, with labels distinguishing them (e.g., `(initial)` and `(at failure)`)
- **Ghost variables** (`#[ghost]`, spec-only vars) are **hidden** — they are spec-internal, showing them breaks abstraction for the developer
- **Loop induction variables** (e.g., `i`) are **always shown**, regardless of VC kind — the loop iteration where something went wrong is crucial context

### Complex Type Display
- **Structs**: Fully recursive expansion — show all nested fields with no depth truncation
- **Vecs/slices/arrays**: Show all elements up to 10; beyond 10, truncate with `... (N more)` message
- **Enums**: Use **Rust Debug format** — mirror what `{:?}` would print (`Some(42)`, `Ok(Point { x: 3 })`) — familiar to all Rust developers
- **Raw pointers** (`*const T`, `*mut T`): Show **symbolic address + pointee value** — `ptr@0x1 -> i32: 42` — both the abstract heap address and what it points to in the SMT model

### Ariadne Annotation Style
- Place counterexample labels **at each variable's use site** in the spec — secondary spans connecting value to its role in the failing spec
- **No cap** on inline labels — show all variables, even if there are many
- Label format: **`x: i32 = 5`** — Rust declaration syntax, reads like a let binding
- For variables with two values (initial + at-failure): use **two separate span labels** — one at the parameter declaration site labeled `(initial)`, one at the failing line labeled `(at failure)`

### JSON Schema Design
- Top-level structure: **structured with metadata**:
  ```json
  {
    "counterexample": {
      "variables": [...],
      "failing_location": { "file": "...", "line": N, "column": N },
      "vc_kind": "postcondition",
      "violated_spec": "result >= 0"
    }
  }
  ```
- Complex value representation: **both display string and raw typed tree**:
  ```json
  {
    "name": "p",
    "type": "Point",
    "display": "Point { x: 3, y: -1 }",
    "raw": { "kind": "struct", "fields": [{ "name": "x", "type": "i32", "value": 3 }, { "name": "y", "type": "i32", "value": -1 }] }
  }
  ```
- **Include `violated_spec`**: the text of the `#[ensures]`/`#[assert]` clause that failed — allows IDEs to display the violated property without parsing source
- Variables with two values: **single entry with `initial` and `at_failure` sub-objects**:
  ```json
  {
    "name": "x",
    "type": "i32",
    "initial": { "display": "5", "raw": 5 },
    "at_failure": { "display": "7", "raw": 7 }
  }
  ```

### Claude's Discretion
- Exact ariadne color scheme and label styling
- Ordering of variables within the counterexample (spec-referenced first vs alphabetical vs declaration order)
- How to handle `!Send`/non-`Debug` types that the SMT model has a value for but Rust can't represent as a string easily
- Whether to show a summary header line (e.g., `counterexample found:`) before the ariadne output

</decisions>

<specifics>
## Specific Ideas

- No specific UI references provided — standard Rust compiler diagnostic aesthetic (rustc/clippy style) is the target
- The JSON schema should be consumable by the VSCode extension built in Phase 16 without modification

</specifics>

<deferred>
## Deferred Ideas

None — discussion stayed within phase scope.

</deferred>

---

*Phase: 19-counterexample-generation*
*Context gathered: 2026-02-19*
