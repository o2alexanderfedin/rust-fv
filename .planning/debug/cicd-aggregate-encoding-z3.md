---
status: resolved
trigger: "CI failure: cicd-aggregate-encoding-z3-unsupported — aggregate_encoding tests fail in CI (Ubuntu/Linux) with ParseError("Unexpected solver output: unsupported") when using Z3 subprocess solver"
created: 2026-02-27T00:00:00Z
updated: 2026-02-27T12:00:00Z
---

## Current Focus

hypothesis: Ubuntu's apt z3 (4.8.x) does not support the QF_UFBVDT logic and prints "unsupported" to stdout, which parse_solver_output sees as the first line and returns ParseError("Unexpected solver output: unsupported")
test: Fix base_script() in vcgen.rs to use "ALL" instead of "QF_UFBVDT" when datatypes are present — ALL is universally supported in z3 4.6+
expecting: Tests pass in CI with Ubuntu's older z3
next_action: Apply fix in vcgen.rs line 1602: change "QF_UFBVDT" to "ALL"

## Symptoms

expected: aggregate_encoding tests pass in CI as they do locally
actual: Tests fail with: ParseError("Unexpected solver output: unsupported")
errors: "Z3 should not error on struct construction VC: ParseError(\"Unexpected solver output: unsupported\")"
reproduction: Push a version tag to GitHub, CI runs cargo test --workspace --all-features on ubuntu-latest
started: New CI workflow, first run

## Eliminated

- hypothesis: Test code logic error
  evidence: Tests pass locally on macOS z3 4.15.4
  timestamp: 2026-02-27T00:00:00Z

- hypothesis: SMT-LIB script is malformed
  evidence: Scripts are valid SMT-LIB2 accepted by local z3; issue is solely the set-logic command
  timestamp: 2026-02-27T00:00:00Z

## Evidence

- timestamp: 2026-02-27T00:00:00Z
  checked: CI workflow (.github/workflows/release.yml)
  found: Ubuntu installs z3 via `sudo apt-get install -y z3 libz3-dev`
  implication: Gets whatever version ubuntu-latest has packaged, typically z3 4.8.x

- timestamp: 2026-02-27T00:00:00Z
  checked: vcgen.rs base_script() function at line 1586-1620
  found: When datatypes present and no int usage, logic is "QF_UFBVDT"
  implication: QF_UFBVDT is not supported by z3 4.8.x — prints "unsupported" to stdout

- timestamp: 2026-02-27T00:00:00Z
  checked: parser.rs parse_solver_output() line 43-45
  found: Any first line that isn't sat/unsat/unknown/timeout → ParseError("Unexpected solver output: {first_line}")
  implication: z3's "unsupported" output becomes a ParseError

- timestamp: 2026-02-27T00:00:00Z
  checked: GitHub issue Z3Prover/z3#4754
  found: z3 4.8.9 prints "unsupported ; ignoring unsupported logic QF_UFDT" warning when QF_UFDT (and related DT logics) are used
  implication: QF_UFBVDT has same issue on Ubuntu apt z3 versions

- timestamp: 2026-02-27T00:00:00Z
  checked: vcgen.rs line 1594-1598
  found: When uses_int=true, logic is already "ALL" which is universally supported
  implication: Fix is to use "ALL" instead of "QF_UFBVDT" when datatypes are present

## Resolution

root_cause: Ubuntu apt z3 4.8.x does not support QF_UFBVDT logic. base_script() in vcgen.rs uses QF_UFBVDT when datatypes are present but no int types. z3 prints "unsupported" to stdout which parse_solver_output() treats as ParseError.
fix: |
  1. base_script(): changed QF_UFBVDT → ALL when datatypes or int theory present
  2. generate_index_bounds_vcs(): replaced manual SetLogic("QF_BV") + datatype_declarations with base_script() call
  3. Null-check VC: replaced manual SetLogic("QF_BV") + datatype_declarations with base_script() call
  4. Bounds-check VC: replaced manual SetLogic("QF_AUFBV") + datatype_declarations with base_script(uses_int=true)
  5. Updated base_script unit test to assert ALL instead of QF_UFBVDT
verification: cargo test --workspace --all-features — all 1202+ tests pass, 0 failed
files_changed:
  - crates/analysis/src/vcgen.rs
