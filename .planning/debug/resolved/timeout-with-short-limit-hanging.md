---
status: resolved
trigger: "timeout_with_short_limit hangs indefinitely in CI/CD"
created: 2026-02-27T00:00:00Z
updated: 2026-02-27T10:30:00Z
---

## Current Focus

hypothesis: The child process is moved into a background thread making it impossible to kill from the main thread when the OS timeout fires; Z3 process becomes an orphan running indefinitely on CI Ubuntu z3 4.8.x
test: Read solver.rs lines 92-139 (check_sat_raw OS-level timeout code)
expecting: Fix requires capturing child.id() before move, then killing by PID on timeout
next_action: Implement fix using child.id() + platform kill (SIGKILL on Unix, TerminateProcess on Windows)

## Symptoms

expected: test `timeout_with_short_limit` completes in a few seconds at most
actual: test hangs for 60+ seconds in CI/CD, blocking the entire test suite
errors: "test timeout_with_short_limit has been running for over 60 seconds" (GitHub Actions warning)
reproduction: Run in CI/CD on Ubuntu (z3 from apt). The test likely passes locally on macOS with newer z3.
started: Recurring — prior fix attempt in commit 5e2100d existed but was insufficient

## Eliminated

- hypothesis: z3 internal -t: flag reliably terminates z3 on all platforms
  evidence: Prior fix raised timeout 1ms->5000ms but it STILL hangs in CI. The -t: flag is a solver heuristic timeout, not a process kill. Ubuntu's older z3 4.8.x ignores -t: for QF_NIA problems.
  timestamp: 2026-02-27T00:05:00Z

- hypothesis: Increasing timeout_ms makes the problem go away
  evidence: Commit 5e2100d raised to 5000ms. Still hangs per CI logs (job-level 45-min timeout added as workaround, not fix).
  timestamp: 2026-02-27T00:05:00Z

- hypothesis: OS-level timeout via mpsc::channel is not implemented
  evidence: solver.rs lines 92-139 show OS-level timeout IS implemented, but the child is moved into the background thread so it cannot be killed from the main thread on timeout.
  timestamp: 2026-02-27T10:12:00Z

## Evidence

- timestamp: 2026-02-27T00:02:00Z
  checked: crates/solver/src/solver.rs check_sat_raw()
  found: Uses child.wait_with_output() which blocks indefinitely with no OS-level timeout
  implication: If Z3 process doesn't terminate, Rust hangs forever

- timestamp: 2026-02-27T00:03:00Z
  checked: crates/solver/src/config.rs SolverKind::timeout_arg()
  found: Z3 timeout is passed as -t:{ms} CLI flag — this is Z3's internal soft timeout
  implication: Z3 can ignore this flag on hard QF_NIA problems, especially on older versions

- timestamp: 2026-02-27T00:04:00Z
  checked: .github/workflows/ci.yml
  found: Ubuntu uses `apt-get install -y z3` (4.8.x, very old), macOS uses `brew install z3` (modern)
  implication: Ubuntu z3 4.8.x has poor timeout handling for QF_NIA; the subprocess never exits

- timestamp: 2026-02-27T00:05:00Z
  checked: git show 5e2100d
  found: Prior "fix" just raised the timeout value and added a job-level 45-minute timeout as a band-aid
  implication: Root cause (no OS-level timeout) was never fixed

- timestamp: 2026-02-27T10:10:00Z
  checked: solver.rs lines 92-139 (current code)
  found: OS-level timeout IS implemented via mpsc channel, BUT child is moved into background thread so it cannot be killed. Comment at line 127 literally says "We cannot kill child from here because it was moved into the thread."
  implication: Z3 process becomes orphan running indefinitely; background thread stays blocked; test returns Unknown but process leak persists and can cause CI timeouts on subsequent tests

- timestamp: 2026-02-27T10:15:00Z
  checked: Process::id() availability in std::process::Child
  found: child.id() returns the OS PID before the child is moved; can use std::process::Command::kill_on_drop or retain PID and call platform kill()
  implication: Fix: capture child.id() before moving child into thread; on timeout use libc::kill(pid, SIGKILL) on Unix or TerminateProcess on Windows

## Resolution

root_cause: In CliSolver::check_sat_raw(), the child process was moved into a background thread making it impossible to kill from the main thread when the OS-level timeout fired. Z3 4.8.x on Ubuntu CI ignores the -t: flag for QF_NIA, so the child ran indefinitely as an orphan. The background thread stayed blocked in wait_with_output() indefinitely. While the test could "return" (Unknown result), the leaked Z3 process and blocked thread accumulated in CI, eventually causing the 60s GitHub Actions test timeout to trigger on the test process.
fix: Capture child.id() before moving child into background thread. On OS timeout, call kill_process(child_pid) which sends SIGKILL on Unix / TerminateProcess on Windows. Then join the background thread (now fast since the process is dead). This guarantees no process or thread leaks.
verification: cargo test -p rust-fv-solver completed in 0.68s with 21/21 integration tests passing including timeout_with_short_limit (0.60s total). 212 unit tests also green. clippy: zero warnings.
files_changed:
  - crates/solver/src/solver.rs
  - crates/solver/Cargo.toml
  - Cargo.toml
