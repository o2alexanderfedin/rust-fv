# Git Hooks Documentation

This repository uses automated git hooks to enforce code quality and workflow standards.

## Installed Hooks

### Pre-commit Hook
**Location**: `.git/hooks/pre-commit`

**Checks**:
1. **Git Flow Enforcement**
   - Ensures commits only happen on valid branches (main, develop, feature/*, release/*, hotfix/*, support/*)
   - Rejects commits on arbitrary branches
   - Guides users to use git flow commands

2. **Rust Quality Checks** (when Cargo.toml exists and .rs files are staged)
   - **Formatting**: `cargo fmt --check` - ensures code follows Rust formatting standards
   - **Linting**: `cargo clippy` with `-D warnings` - catches common mistakes and anti-patterns
   - **Type Checking**: `cargo check` - verifies code compiles without errors

**Fixing Issues**:
```bash
# Fix formatting
cargo fmt

# Fix clippy warnings
cargo clippy --fix --allow-dirty

# See type errors
cargo check
```

### Pre-push Hook
**Location**: `.git/hooks/pre-push`

**Checks**:
1. **Test Suite Execution** (when Cargo.toml exists)
   - Runs full test suite: `cargo test --all-targets --all-features`
   - Prevents pushing code with failing tests

**Fixing Issues**:
```bash
# Run tests locally
cargo test

# Run specific test
cargo test test_name

# Run tests with output
cargo test -- --nocapture
```

## Why These Hooks?

### Benefits
- **Early Error Detection**: Catch issues before they reach CI/CD
- **Code Quality**: Enforce consistent formatting and best practices
- **Workflow Compliance**: Maintain git flow discipline
- **Fast Feedback**: Developers get immediate feedback on local machine

### Performance
- Hooks only run checks on staged files
- Formatting/linting are fast (<1s for small changes)
- Tests run before push, not on every commit
- Hooks skip checks if no Rust code exists yet

## Bypassing Hooks (Use Sparingly)

In rare cases where you need to bypass hooks:

```bash
# Skip pre-commit hook (not recommended)
git commit --no-verify

# Skip pre-push hook (not recommended)
git push --no-verify
```

**⚠️ Warning**: Bypassing hooks can introduce quality issues. Only use in emergencies.

## Customization

Hooks are located in `.git/hooks/` and can be modified as needed. However, `.git` is not tracked, so hook changes must be documented and shared manually.

Consider using a hook management tool like [pre-commit](https://pre-commit.com/) for team-wide hook distribution.

## Troubleshooting

### "cargo: command not found"
**Solution**: Install Rust toolchain: https://rustup.rs/

### "cargo fmt failed"
**Solution**: Run `cargo fmt` to auto-format code

### "clippy found warnings"
**Solution**: Run `cargo clippy --fix` or manually fix reported issues

### "tests are too slow"
**Solution**: Consider running subset of tests in pre-push, full suite in CI

## Related Configuration

- **rustfmt**: Configuration in `rustfmt.toml` or `.rustfmt.toml`
- **clippy**: Configuration in `Cargo.toml` under `[lints.clippy]`
- **git flow**: Initialized with default branch names (main, develop)

---

**Last Updated**: 2026-02-10
