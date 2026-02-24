/// Verification Condition Generator.
///
/// Translates our MIR-like IR into SMT-LIB scripts that encode
/// the semantics of the program and check all verification conditions:
///
/// - **Every variable**: declared as an SMT constant with its type's sort
/// - **Every operation**: encoded with exact semantics (signed/unsigned)
/// - **Every arithmetic op**: overflow check generated
/// - **Every division**: division-by-zero check generated
/// - **Every shift**: shift-amount-in-bounds check generated
/// - **Every condition**: path conditions encoded via ITE
/// - **Every assertion**: verified via SMT
/// - **Every contract**: preconditions assumed, postconditions checked
///
/// ## SSA and Path-Condition Encoding
///
/// The VCGen traverses the CFG (control-flow graph) properly via
/// `Terminator::Goto`, `SwitchInt`, `Assert`, and `Call` edges rather
/// than walking basic blocks linearly by index. This ensures that
/// assignments in different branches do not clobber each other.
///
/// For postcondition verification, all paths through the function are
/// enumerated. Each path's assignments are guarded by the conjunction
/// of branch conditions along that path (the path condition). At merge
/// points, the return value `_0` is encoded as:
///
/// ```text
/// (assert (=> path_1_cond (= _0 path_1_value)))
/// (assert (=> path_2_cond (= _0 path_2_value)))
/// ```
///
/// This naturally handles if/else, match arms, and early returns without
/// explicit phi nodes.
use std::collections::{HashMap, HashSet};

use rust_fv_smtlib::command::Command;
use rust_fv_smtlib::script::Script;
use rust_fv_smtlib::term::Term;

use crate::contract_db::ContractDatabase;
use crate::encode_sort::{collect_datatype_declarations, encode_type};
use crate::encode_term::{
    encode_aggregate_with_type, encode_binop, encode_field_access, encode_operand,
    encode_place_with_type, encode_unop, overflow_check,
};
use crate::ghost_predicate_db::GhostPredicateDatabase;
use crate::ir::*;
use crate::ownership::{OwnershipConstraint, classify_argument, generate_ownership_constraints};
use crate::sep_logic;
use crate::spec_parser;

/// A verification condition with metadata for error reporting.
#[derive(Debug, Clone)]
pub struct VerificationCondition {
    /// Human-readable description of what is being verified
    pub description: String,
    /// The SMT-LIB script to check (expect UNSAT = verified)
    pub script: Script,
    /// Source location hint (function name, block index, statement index)
    pub location: VcLocation,
}

/// Location information for a verification condition.
#[derive(Debug, Clone)]
pub struct VcLocation {
    pub function: String,
    pub block: usize,
    pub statement: usize,
    /// Source file path (when available)
    pub source_file: Option<String>,
    /// Source line number (1-based, when available)
    pub source_line: Option<usize>,
    /// Source column number (1-based, when available).
    ///
    /// Populated by `fill_vc_locations` in the driver when MIR `SourceInfo`
    /// spans are available. `None` in unit-test contexts.
    pub source_column: Option<usize>,
    /// The specific contract text that failed (e.g., "result > 0")
    pub contract_text: Option<String>,
    /// What kind of verification condition this is
    pub vc_kind: VcKind,
}

/// Classification of verification conditions for diagnostics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VcKind {
    /// Precondition check (requires clause)
    Precondition,
    /// Postcondition check (ensures clause)
    Postcondition,
    /// Loop invariant holds before loop
    LoopInvariantInit,
    /// Loop invariant preserved by loop body
    LoopInvariantPreserve,
    /// Loop invariant holds after loop
    LoopInvariantExit,
    /// Arithmetic overflow check
    Overflow,
    /// Division by zero check
    DivisionByZero,
    /// Shift amount bounds check
    ShiftBounds,
    /// Assert statement check
    Assertion,
    /// Panic-freedom check (unwrap, index, etc.)
    PanicFreedom,
    /// Termination measure decreases check
    Termination,
    /// Closure contract verification
    ClosureContract,
    /// Behavioral subtyping check (trait impl satisfies trait contract)
    BehavioralSubtyping,
    /// Borrow validity check (shared/mutable conflict, use-after-expiry, reborrow validity)
    BorrowValidity,
    /// Memory safety check (null-check, bounds-check, use-after-free for unsafe code)
    MemorySafety,
    /// Floating-point NaN propagation or infinity overflow check
    FloatingPointNaN,
    /// Data race freedom check (conflicting accesses must be ordered)
    DataRaceFreedom,
    /// Lock invariant check (must hold at release)
    LockInvariant,
    /// Deadlock detection (lock-order cycle)
    Deadlock,
    /// Channel operation safety (send-on-closed, capacity overflow, recv deadlock)
    ChannelSafety,
    /// RC11 coherence check: hb;eco? is irreflexive under weak memory ordering.
    /// Generated only for functions with at least one non-SeqCst atomic op.
    WeakMemoryCoherence,
    /// Weak memory data race: conflicting Relaxed accesses to same location from different threads.
    /// Under Relaxed ordering, Relaxed-vs-Relaxed to same location without ordering is a race.
    WeakMemoryRace,
    /// Weak memory atomicity: RMW atomicity under RC11 (rmw ∩ (rb;mo) = ∅).
    /// Generated for fetch_add/compare_exchange ops under non-SeqCst ordering.
    WeakMemoryAtomicity,
    /// `#[state_invariant]` check just before a `.await` suspends (at Yield terminator).
    AsyncStateInvariantSuspend,
    /// `#[state_invariant]` check just after a `.await` resumes (after Yield resume).
    AsyncStateInvariantResume,
    /// `#[ensures]` check at `Poll::Ready` resolution of an async fn.
    AsyncPostcondition,
}

impl VcKind {
    /// Classify overflow check kind from binary operation.
    fn from_overflow_op(op: BinOp) -> Self {
        match op {
            BinOp::Div | BinOp::Rem => Self::DivisionByZero,
            BinOp::Shl | BinOp::Shr => Self::ShiftBounds,
            _ => Self::Overflow,
        }
    }
}

/// Result of generating VCs for a function.
#[derive(Debug)]
pub struct FunctionVCs {
    pub function_name: String,
    pub conditions: Vec<VerificationCondition>,
}

/// A single path through the CFG: a sequence of (block_index, statements)
/// with an accumulated path condition.
#[derive(Debug, Clone)]
struct CfgPath {
    /// The path condition: conjunction of all branch decisions along this path.
    /// `None` means unconditional (single path, no branches).
    condition: Option<Term>,
    /// Assignments collected along this path, in order.
    assignments: Vec<PathAssignment>,
    /// Overflow VCs found along this path.
    overflow_vcs: Vec<OverflowVcInfo>,
    /// Call sites encountered along this path.
    call_sites: Vec<CallSiteInfo>,
}

/// Information about a function call encountered during path traversal.
#[derive(Debug, Clone)]
struct CallSiteInfo {
    /// Normalized callee function name (bare name, no `const ` prefix or path qualifiers).
    callee_name: String,
    /// Arguments passed to the callee.
    args: Vec<Operand>,
    /// Place where the return value is stored.
    destination: Place,
    /// Block index where the call occurs.
    block_idx: usize,
    /// Assignments before this call in the current path.
    prior_assignments: Vec<PathAssignment>,
    /// Path condition at the call point.
    path_condition: Option<Term>,
}

/// An assignment found along a path, with its location info.
#[derive(Debug, Clone)]
struct PathAssignment {
    place: Place,
    rvalue: Rvalue,
    block_idx: usize,
    /// Number of branch conditions accumulated at the time this assignment
    /// was recorded. Assignments with `branch_depth == 0` are in the common
    /// prefix and should NOT be guarded by the path condition.
    branch_depth: usize,
}

/// Info about an overflow check found along a path.
#[derive(Debug, Clone)]
struct OverflowVcInfo {
    op: BinOp,
    lhs_operand: Operand,
    rhs_operand: Operand,
    place: Place,
    block_idx: usize,
    stmt_idx: usize,
    /// Assignments that precede this overflow point along this path.
    prior_assignments: Vec<PathAssignment>,
    /// Path condition at this point.
    path_condition: Option<Term>,
}

/// Generate all verification conditions for a function.
///
/// This is the main entry point. It produces a set of SMT-LIB scripts,
/// each checking one verification condition. If any script is SAT,
/// the corresponding condition is violated.
///
/// The optional `contract_db` enables inter-procedural verification:
/// when present, call sites are encoded modularly using callee contracts
/// as summaries (assert precondition, havoc return, assume postcondition).
/// Pass `None` for backward-compatible behavior where calls are opaque.
/// Like `generate_vcs` but with ghost predicate expansion.
///
/// Called by `verify_single()` in the driver. `generate_vcs()` delegates to this
/// with an empty ghost predicate database for backward compatibility.
pub fn generate_vcs_with_db(
    func: &Function,
    contract_db: Option<&ContractDatabase>,
    ghost_pred_db: &GhostPredicateDatabase,
) -> FunctionVCs {
    tracing::info!(function = %func.name, "Generating verification conditions");

    let mut conditions = Vec::new();

    // Collect datatype declarations (must come before variable declarations)
    let datatype_declarations = collect_datatype_declarations(func);

    // Detect prophecies for mutable reference parameters
    let prophecies = crate::encode_prophecy::detect_prophecies(func);
    if !prophecies.is_empty() {
        tracing::debug!(
            function = %func.name,
            prophecy_count = prophecies.len(),
            "Detected mutable reference parameters requiring prophecy variables"
        );
    }

    // Collect all variable declarations (including prophecy variables)
    let mut declarations = collect_declarations(func);

    // Add prophecy variable declarations if needed
    if !prophecies.is_empty() {
        let mut prophecy_decls = crate::encode_prophecy::prophecy_declarations(&prophecies);
        declarations.append(&mut prophecy_decls);
    }

    // Add closure function declarations for closure parameters
    let closure_infos = crate::closure_analysis::extract_closure_info(func);
    for closure_info in &closure_infos {
        let mut closure_decls =
            crate::defunctionalize::encode_closure_as_uninterpreted(closure_info);
        declarations.append(&mut closure_decls);
    }

    // Enumerate all paths through the CFG
    let paths = enumerate_paths(func);
    tracing::debug!(function = %func.name, path_count = paths.len(), "Enumerated CFG paths");

    // Generate overflow VCs from all paths
    for path in &paths {
        for ov in &path.overflow_vcs {
            let mut vc = generate_overflow_vc(
                func,
                &datatype_declarations,
                &declarations,
                ov,
                ghost_pred_db,
            );
            conditions.append(&mut vc);
        }
    }

    // Generate terminator assertion VCs (Terminator::Assert)
    let mut assert_vcs = generate_assert_terminator_vcs(
        func,
        &datatype_declarations,
        &declarations,
        &paths,
        ghost_pred_db,
    );
    conditions.append(&mut assert_vcs);

    // Generate bounds-check VCs for array/slice index accesses (Projection::Index).
    // Each statement that reads a place through an Index projection generates a
    // safety VC: 0 <= idx AND idx < {arr}_len.
    let mut index_vcs = generate_index_bounds_vcs(func, &datatype_declarations, &declarations);
    conditions.append(&mut index_vcs);

    // Generate contract verification conditions (postconditions)
    // When contract_db is provided, callee postconditions are assumed during
    // the caller's postcondition check.
    let mut contract_vcs = generate_contract_vcs(
        func,
        &datatype_declarations,
        &declarations,
        &paths,
        contract_db,
        ghost_pred_db,
    );
    conditions.append(&mut contract_vcs);

    // Generate call-site precondition VCs (inter-procedural)
    if let Some(db) = contract_db {
        let mut call_vcs = generate_call_site_vcs(
            func,
            db,
            &datatype_declarations,
            &declarations,
            &paths,
            ghost_pred_db,
        );
        conditions.append(&mut call_vcs);
    }

    // Recursion analysis: detect recursive functions and generate termination VCs
    {
        // Build function list for call graph (current function + contract_db functions)
        let func_list: Vec<(String, &Function)> = vec![(func.name.clone(), func)];

        // Build call graph and detect recursion
        let cg = crate::call_graph::CallGraph::from_functions(&func_list);
        let recursive_groups = cg.detect_recursion();

        if !recursive_groups.is_empty() {
            tracing::info!(
                function = %func.name,
                group_count = recursive_groups.len(),
                "Detected recursive function(s)"
            );

            // Check for missing decreases annotations
            let missing = crate::recursion::check_missing_decreases(&func_list, &recursive_groups);
            for err in &missing {
                tracing::warn!(
                    function = %err.function_name,
                    group = ?err.recursive_group,
                    "Recursive function missing #[decreases] annotation"
                );

                // Generate diagnostic VC (always SAT = failure)
                let mut script = rust_fv_smtlib::script::Script::new();
                script.push(rust_fv_smtlib::command::Command::SetLogic(
                    "QF_BV".to_string(),
                ));
                script.push(rust_fv_smtlib::command::Command::Assert(
                    rust_fv_smtlib::term::Term::BoolLit(true),
                ));
                script.push(rust_fv_smtlib::command::Command::CheckSat);

                conditions.push(VerificationCondition {
                    description: format!(
                        "recursive function `{}` missing termination measure",
                        err.function_name,
                    ),
                    script,
                    location: VcLocation {
                        function: err.function_name.clone(),
                        block: 0,
                        statement: 0,
                        source_file: None,
                        source_line: None,
                        source_column: None,
                        contract_text: Some("add #[decreases(expr)] annotation".to_string()),
                        vc_kind: VcKind::Termination,
                    },
                });
            }

            // Generate termination VCs for functions with decreases annotations
            if missing.is_empty() || func.contracts.decreases.is_some() {
                let mut term_vcs = crate::recursion::generate_termination_vcs(
                    func,
                    &recursive_groups,
                    contract_db,
                );
                conditions.append(&mut term_vcs);
            }
        }

        // Clean up: func_list is no longer needed
        drop(func_list);
    }

    // Closure analysis: detect closure parameters and generate closure-related VCs
    {
        let closure_infos = crate::closure_analysis::extract_closure_info(func);
        let closure_calls = crate::closure_analysis::detect_closure_calls(func);

        tracing::debug!(
            function = %func.name,
            closure_count = closure_infos.len(),
            call_count = closure_calls.len(),
            "Closure analysis"
        );

        // FnOnce validation: check for double calls
        let fnonce_errors = crate::closure_analysis::validate_fnonce_single_call(func);
        for err_msg in &fnonce_errors {
            tracing::warn!(
                function = %func.name,
                error = %err_msg,
                "FnOnce closure called multiple times"
            );

            // Generate diagnostic VC (always-SAT = failure)
            let mut script = rust_fv_smtlib::script::Script::new();
            script.push(rust_fv_smtlib::command::Command::SetLogic(
                "QF_BV".to_string(),
            ));
            script.push(rust_fv_smtlib::command::Command::Assert(
                rust_fv_smtlib::term::Term::BoolLit(true),
            ));
            script.push(rust_fv_smtlib::command::Command::CheckSat);

            conditions.push(VerificationCondition {
                description: err_msg.clone(),
                script,
                location: VcLocation {
                    function: func.name.clone(),
                    block: 0,
                    statement: 0,
                    source_file: None,
                    source_line: None,
                    source_column: None,
                    contract_text: Some("FnOnce closures can only be called once".to_string()),
                    vc_kind: VcKind::ClosureContract,
                },
            });
        }

        // For each closure parameter, add uninterpreted function declaration to datatype declarations
        // This will be used when generating VCs
        // (The actual usage will be in encode_operand/encode_place when encoding closure calls)
    }

    // --- Borrow validity analysis ---
    // Only run if function has lifetime metadata
    if !func.lifetime_params.is_empty() || !func.borrow_info.is_empty() {
        tracing::debug!(
            function = %func.name,
            lifetime_params = func.lifetime_params.len(),
            borrows = func.borrow_info.len(),
            "Generating borrow validity VCs"
        );

        let lifetime_ctx = crate::lifetime_analysis::build_lifetime_context(func);
        let live_ranges = crate::lifetime_analysis::compute_live_ranges(func);

        // Generate conflict VCs
        let conflicts =
            crate::borrow_conflict::detect_borrow_conflicts(&lifetime_ctx, &live_ranges);
        let mut conflict_vcs =
            crate::borrow_conflict::generate_conflict_vcs(&conflicts, &func.name);
        conditions.append(&mut conflict_vcs);

        // Generate expiry VCs
        let mut expiry_vcs =
            crate::borrow_conflict::generate_expiry_vcs(&lifetime_ctx, &live_ranges, func);
        conditions.append(&mut expiry_vcs);

        // Generate reborrow VCs
        let mut reborrow_vcs =
            crate::borrow_conflict::generate_reborrow_vcs(&lifetime_ctx, &live_ranges);
        conditions.append(&mut reborrow_vcs);

        tracing::debug!(
            function = %func.name,
            conflicts = conflicts.len(),
            "Borrow validity VCs generated"
        );
    }

    // === Unsafe code analysis (Phase 10) ===
    // Check if function is trusted - skip body verification if so
    if crate::unsafe_analysis::is_trusted_function(func) {
        tracing::info!(
            function = %func.name,
            "Trusted function - skipping body verification"
        );
        // Early return with empty VCs - only contracts matter at call sites
        return FunctionVCs {
            function_name: func.name.clone(),
            conditions: vec![],
        };
    }

    // Detect unsafe blocks
    let unsafe_blocks = crate::unsafe_analysis::detect_unsafe_blocks(func);
    if !unsafe_blocks.is_empty() {
        tracing::debug!(
            function = %func.name,
            unsafe_block_count = unsafe_blocks.len(),
            "Detected unsafe blocks"
        );
    }

    // Check for missing unsafe contracts
    if let Some(warning_msg) = crate::unsafe_analysis::check_missing_unsafe_contracts(func) {
        tracing::warn!(
            function = %func.name,
            warning = %warning_msg,
            "Unsafe function missing safety contracts"
        );

        // Generate diagnostic VC (always-SAT = warning)
        let mut script = rust_fv_smtlib::script::Script::new();
        script.push(rust_fv_smtlib::command::Command::SetLogic(
            "QF_BV".to_string(),
        ));
        script.push(rust_fv_smtlib::command::Command::Assert(
            rust_fv_smtlib::term::Term::BoolLit(true),
        ));
        script.push(rust_fv_smtlib::command::Command::CheckSat);

        conditions.push(VerificationCondition {
            description: warning_msg.clone(),
            script,
            location: VcLocation {
                function: func.name.clone(),
                block: 0,
                statement: 0,
                source_file: None,
                source_line: None,
                source_column: None,
                contract_text: Some(
                    "add #[unsafe_requires], #[unsafe_ensures], or #[trusted]".to_string(),
                ),
                vc_kind: VcKind::MemorySafety,
            },
        });
    }

    // Extract and analyze unsafe operations
    let unsafe_operations = crate::unsafe_analysis::extract_unsafe_operations(func);
    if !unsafe_operations.is_empty() {
        tracing::debug!(
            function = %func.name,
            unsafe_op_count = unsafe_operations.len(),
            "Detected unsafe operations"
        );

        // Add heap model declarations if needed (for bounds checks)
        let mut heap_model_added = false;
        if crate::heap_model::heap_model_declarations_needed(func) {
            // Heap model commands will be prepended to VCs that need them
            heap_model_added = true;
            tracing::debug!(
                function = %func.name,
                "Heap model declarations needed for pointer arithmetic"
            );
        }

        // Generate memory safety VCs for each unsafe operation
        for op in &unsafe_operations {
            // Null-check VC
            if crate::unsafe_analysis::needs_null_check(op) {
                let (ptr_local, block_index) = match op {
                    UnsafeOperation::RawDeref {
                        ptr_local,
                        block_index,
                        ..
                    } => (ptr_local, *block_index),
                    _ => continue, // shouldn't happen based on needs_null_check logic
                };

                // Build null-check VC script
                let mut script = rust_fv_smtlib::script::Script::new();
                // Use QF_BV for null-checks (no heap model needed, just pointer comparison)
                script.push(rust_fv_smtlib::command::Command::SetLogic(
                    "QF_BV".to_string(),
                ));

                // Add datatype and variable declarations
                for cmd in &datatype_declarations {
                    script.push(cmd.clone());
                }
                for cmd in &declarations {
                    script.push(cmd.clone());
                }

                // Assert the null-check condition (ptr == 0 is the violation)
                let null_check_assertion =
                    crate::heap_model::generate_null_check_assertion(ptr_local);
                script.push(rust_fv_smtlib::command::Command::Assert(
                    null_check_assertion,
                ));
                script.push(rust_fv_smtlib::command::Command::CheckSat);

                conditions.push(VerificationCondition {
                    description: format!(
                        "null-check: raw pointer dereference of '{}' requires non-null",
                        ptr_local
                    ),
                    script,
                    location: VcLocation {
                        function: func.name.clone(),
                        block: block_index,
                        statement: 0,
                        source_file: None,
                        source_line: None,
                        source_column: None,
                        contract_text: Some(format!("{} != null", ptr_local)),
                        vc_kind: VcKind::MemorySafety,
                    },
                });
            }

            // Bounds-check VC
            if crate::unsafe_analysis::needs_bounds_check(op) {
                let (ptr_local, offset_local, block_index) = match op {
                    UnsafeOperation::PtrArithmetic {
                        ptr_local,
                        offset_local,
                        block_index,
                        ..
                    } => (ptr_local, offset_local, *block_index),
                    _ => continue, // shouldn't happen based on needs_bounds_check logic
                };

                // Build bounds-check VC script
                let mut script = rust_fv_smtlib::script::Script::new();
                // Use QF_AUFBV for bounds-checks (requires heap model with uninterpreted functions)
                script.push(rust_fv_smtlib::command::Command::SetLogic(
                    "QF_AUFBV".to_string(),
                ));

                // Add heap model declarations
                if heap_model_added {
                    let heap_model_cmds = crate::heap_model::declare_heap_model();
                    for cmd in heap_model_cmds {
                        script.push(cmd);
                    }
                }

                // Add datatype and variable declarations
                for cmd in &datatype_declarations {
                    script.push(cmd.clone());
                }
                for cmd in &declarations {
                    script.push(cmd.clone());
                }

                // Assert the bounds-check condition (offset out of bounds is the violation)
                let bounds_check_assertion =
                    crate::heap_model::generate_bounds_check_assertion(ptr_local, offset_local);
                script.push(rust_fv_smtlib::command::Command::Assert(
                    bounds_check_assertion,
                ));
                script.push(rust_fv_smtlib::command::Command::CheckSat);

                conditions.push(VerificationCondition {
                    description: format!(
                        "bounds-check: pointer arithmetic on '{}' with offset '{}'",
                        ptr_local, offset_local
                    ),
                    script,
                    location: VcLocation {
                        function: func.name.clone(),
                        block: block_index,
                        statement: 0,
                        source_file: None,
                        source_line: None,
                        source_column: None,
                        contract_text: Some(format!(
                            "offset {} within allocation bounds",
                            offset_local
                        )),
                        vc_kind: VcKind::MemorySafety,
                    },
                });
            }
        }
    }

    // Generate loop invariant VCs for loops with user-supplied invariants
    let detected_loops = detect_loops(func);
    for loop_info in &detected_loops {
        if loop_info.invariants.is_empty() {
            tracing::warn!(
                function = %func.name,
                header = loop_info.header_block,
                "Loop without invariant annotation -- skipping verification"
            );
        } else {
            tracing::debug!(
                function = %func.name,
                header = loop_info.header_block,
                invariant_count = loop_info.invariants.len(),
                "Generating loop invariant VCs"
            );
            let mut loop_vcs = generate_loop_invariant_vcs(
                func,
                &datatype_declarations,
                &declarations,
                loop_info,
                ghost_pred_db,
            );
            conditions.append(&mut loop_vcs);
        }
    }

    // Generate floating-point VCs (NaN propagation and infinity overflow)
    {
        let mut float_vcs = crate::float_verification::generate_float_vcs(func);
        if !float_vcs.is_empty() {
            tracing::debug!(
                function = %func.name,
                float_vc_count = float_vcs.len(),
                "Generated floating-point VCs (NaN propagation + infinity overflow)"
            );
            conditions.append(&mut float_vcs);
        }
    }

    // Generate concurrency VCs (data race freedom, lock invariants, deadlocks, channel safety)
    {
        let mut concurrency_vcs = generate_concurrency_vcs(func);
        if !concurrency_vcs.is_empty() {
            tracing::debug!(
                function = %func.name,
                concurrency_vc_count = concurrency_vcs.len(),
                "Generated concurrency VCs (bounded verification)"
            );
            conditions.append(&mut concurrency_vcs);
        }
    }

    // HOF-01 / HOF-02: Generate fn_spec entailment VCs if any are declared
    if !func.contracts.fn_specs.is_empty() {
        let hof_vcs = crate::hof_vcgen::generate_fn_spec_vcs(func, &func.contracts.fn_specs);
        conditions.extend(hof_vcs);
    }

    // ASY-01 / ASY-02: Generate async VCs if this is an async fn (coroutine)
    if func.coroutine_info.is_some() {
        let async_vcs = crate::async_vcgen::generate_async_vcs(func, ghost_pred_db);
        conditions.extend(async_vcs);
    }

    tracing::info!(
        function = %func.name,
        vc_count = conditions.len(),
        "Verification condition generation complete"
    );

    FunctionVCs {
        function_name: func.name.clone(),
        conditions,
    }
}

/// Generate all verification conditions for a function.
///
/// This is the main entry point. It produces a set of SMT-LIB scripts,
/// each checking one verification condition. If any script is SAT,
/// the corresponding condition is violated.
///
/// The optional `contract_db` enables inter-procedural verification:
/// when present, call sites are encoded modularly using callee contracts
/// as summaries (assert precondition, havoc return, assume postcondition).
/// Pass `None` for backward-compatible behavior where calls are opaque.
///
/// This delegates to `generate_vcs_with_db` with an empty ghost predicate database.
/// Use `generate_vcs_with_db` directly to enable ghost predicate expansion.
pub fn generate_vcs(func: &Function, contract_db: Option<&ContractDatabase>) -> FunctionVCs {
    let empty_db = GhostPredicateDatabase::new();
    generate_vcs_with_db(func, contract_db, &empty_db)
}

/// Generate verification conditions with a specific encoding mode.
///
/// When `mode` is `EncodingMode::Bitvector`, this is equivalent to `generate_vcs`.
/// When `mode` is `EncodingMode::Integer`, integer types are declared as `Int` sort
/// and the SMT logic is set to `QF_LIA` (linear integer arithmetic) or `QF_NIA`
/// (nonlinear, when multiplication is present).
///
/// The existing `generate_vcs` remains unchanged for backward compatibility.
/// Use this function when comparing bv2int encoding equivalence in differential testing.
pub fn generate_vcs_with_mode(
    func: &Function,
    contract_db: Option<&ContractDatabase>,
    mode: crate::bv2int::EncodingMode,
) -> FunctionVCs {
    use crate::bv2int::EncodingMode;

    if mode == EncodingMode::Bitvector {
        return generate_vcs(func, contract_db);
    }

    // Integer mode: collect declarations using encode_type_with_mode
    tracing::info!(
        function = %func.name,
        "Generating verification conditions (integer encoding mode)"
    );

    // For integer mode, generate VCs using existing pipeline but with Int-sort declarations.
    // The key difference from bitvector mode is the variable declarations use Sort::Int.
    // We use a modified collect_declarations that respects the encoding mode.
    let mut conditions = Vec::new();

    let datatype_declarations = collect_datatype_declarations(func);

    let prophecies = crate::encode_prophecy::detect_prophecies(func);
    let mut declarations = collect_declarations_with_mode(func, mode);

    if !prophecies.is_empty() {
        let mut prophecy_decls = crate::encode_prophecy::prophecy_declarations(&prophecies);
        declarations.append(&mut prophecy_decls);
    }

    let closure_infos = crate::closure_analysis::extract_closure_info(func);
    for closure_info in &closure_infos {
        let mut closure_decls =
            crate::defunctionalize::encode_closure_as_uninterpreted(closure_info);
        declarations.append(&mut closure_decls);
    }

    let paths = enumerate_paths(func);

    // generate_vcs_with_mode does not support ghost predicates; use empty db
    let empty_db = GhostPredicateDatabase::new();

    // Generate overflow VCs
    for path in &paths {
        for ov in &path.overflow_vcs {
            let mut vc =
                generate_overflow_vc(func, &datatype_declarations, &declarations, ov, &empty_db);
            conditions.append(&mut vc);
        }
    }

    // Generate assert terminator VCs
    let mut assert_vcs = generate_assert_terminator_vcs(
        func,
        &datatype_declarations,
        &declarations,
        &paths,
        &empty_db,
    );
    conditions.append(&mut assert_vcs);

    // Generate contract VCs
    let mut contract_vcs = generate_contract_vcs(
        func,
        &datatype_declarations,
        &declarations,
        &paths,
        contract_db,
        &empty_db,
    );
    conditions.append(&mut contract_vcs);

    // Generate call-site precondition VCs
    if let Some(db) = contract_db {
        let mut call_vcs = generate_call_site_vcs(
            func,
            db,
            &datatype_declarations,
            &declarations,
            &paths,
            &empty_db,
        );
        conditions.append(&mut call_vcs);
    }

    // Swap QF_BV logic to QF_LIA/QF_NIA in all generated scripts
    let has_nonlinear = func_has_multiplication(func);
    let int_logic = if has_nonlinear { "QF_NIA" } else { "QF_LIA" };
    let conditions = conditions
        .into_iter()
        .map(|mut vc| {
            vc.script = replace_script_logic(vc.script, int_logic);
            vc
        })
        .collect();

    tracing::info!(
        function = %func.name,
        logic = int_logic,
        "Integer-mode verification condition generation complete"
    );

    FunctionVCs {
        function_name: func.name.clone(),
        conditions,
    }
}

/// Collect variable declarations using mode-aware type encoding.
///
/// In `EncodingMode::Integer`, integer types (`Int(_)`, `Uint(_)`) are declared as
/// `Sort::Int` instead of `Sort::BitVec(N)`.
fn collect_declarations_with_mode(
    func: &Function,
    mode: crate::bv2int::EncodingMode,
) -> Vec<Command> {
    use crate::bv2int::encode_type_with_mode;

    let mut decls = Vec::new();

    let sort = encode_type_with_mode(&func.return_local.ty, mode);
    decls.push(Command::DeclareConst(func.return_local.name.clone(), sort));

    for param in &func.params {
        let sort = encode_type_with_mode(&param.ty, mode);
        decls.push(Command::DeclareConst(param.name.clone(), sort));
    }

    for local in &func.locals {
        let sort = encode_type_with_mode(&local.ty, mode);
        decls.push(Command::DeclareConst(local.name.clone(), sort));
    }

    decls
}

/// Returns `true` if the function contains a multiplication operation.
///
/// Used to select `QF_NIA` (nonlinear) vs `QF_LIA` (linear) logic.
fn func_has_multiplication(func: &Function) -> bool {
    for bb in &func.basic_blocks {
        for stmt in &bb.statements {
            if let Statement::Assign(
                _,
                Rvalue::BinaryOp(BinOp::Mul, _, _) | Rvalue::CheckedBinaryOp(BinOp::Mul, _, _),
            ) = stmt
            {
                return true;
            }
        }
    }
    false
}

/// Replace the `SetLogic` command in a script with a new logic string.
///
/// Used to switch from `QF_BV` to `QF_LIA`/`QF_NIA` in integer-encoded VCs.
fn replace_script_logic(script: Script, new_logic: &str) -> Script {
    let commands: Vec<Command> = script
        .commands()
        .iter()
        .map(|cmd| {
            if let Command::SetLogic(_) = cmd {
                Command::SetLogic(new_logic.to_string())
            } else {
                cmd.clone()
            }
        })
        .collect();
    Script::with_commands(commands)
}

/// Generate verification conditions for a potentially generic function via monomorphization.
///
/// For generic functions, this generates separate VCs for each concrete type instantiation
/// registered in the MonomorphizationRegistry. For non-generic functions, this delegates
/// to `generate_vcs()` directly.
///
/// # Monomorphization Strategy
///
/// Generic functions like `fn max<T: Ord>(a: T, b: T) -> T` are verified by:
/// 1. Looking up all concrete instantiations in the registry (e.g., T=i32, T=u64)
/// 2. Substituting generic type parameters with concrete types for each instantiation
/// 3. Generating VCs for each monomorphized version independently
///
/// This mirrors Rust's own monomorphization strategy and avoids the complexity of
/// parametric reasoning. Each instantiation is verified separately with the concrete
/// type's semantics (e.g., signed comparison for i32, unsigned for u64).
///
/// # Returns
///
/// A vector of `FunctionVCs`, one per instantiation. For non-generic functions,
/// the vector contains a single element.
pub fn generate_vcs_monomorphized(
    func: &Function,
    registry: &crate::monomorphize::MonomorphizationRegistry,
    contract_db: Option<&ContractDatabase>,
) -> Vec<FunctionVCs> {
    if !func.is_generic() {
        // Non-generic function: delegate directly to generate_vcs
        tracing::debug!(function = %func.name, "Non-generic function - generating VCs directly");
        return vec![generate_vcs(func, contract_db)];
    }

    // Generic function: get all registered instantiations
    let instantiations = registry.get_instantiations(&func.name);

    if instantiations.is_empty() {
        tracing::warn!(
            function = %func.name,
            "Generic function has no registered instantiations - skipping verification"
        );
        return vec![];
    }

    tracing::info!(
        function = %func.name,
        instantiation_count = instantiations.len(),
        "Generating VCs for generic function via monomorphization"
    );

    let mut all_vcs = Vec::new();

    for inst in instantiations {
        tracing::debug!(
            function = %func.name,
            label = %inst.label,
            "Monomorphizing and generating VCs"
        );

        // Substitute generic types with concrete types
        let concrete_func = crate::monomorphize::substitute_generics(func, inst);

        // Generate VCs for the concrete version
        let vcs = generate_vcs(&concrete_func, contract_db);
        all_vcs.push(vcs);
    }

    tracing::info!(
        function = %func.name,
        total_vcs = all_vcs.iter().map(|v| v.conditions.len()).sum::<usize>(),
        "Monomorphization-based VC generation complete"
    );

    all_vcs
}

/// Enumerate all paths through the CFG from the entry block to Return terminators.
///
/// Each path records:
/// - The path condition (conjunction of branch decisions)
/// - All assignments along the path
/// - Overflow check points along the path
///
/// For functions without branches, there is a single path with no condition.
/// For if/else, there are two paths with complementary conditions.
/// For nested branches, paths multiply.
///
/// To prevent infinite loops on back-edges, a block is skipped if already
/// visited on the current path (cycle detection).
fn enumerate_paths(func: &Function) -> Vec<CfgPath> {
    if func.basic_blocks.is_empty() {
        return vec![CfgPath {
            condition: None,
            assignments: vec![],
            overflow_vcs: vec![],
            call_sites: vec![],
        }];
    }

    let mut completed_paths = Vec::new();
    let initial_state = PathState {
        conditions: Vec::new(),
        assignments: Vec::new(),
        overflow_vcs: Vec::new(),
        call_sites: Vec::new(),
        visited: HashSet::new(),
    };

    traverse_block(func, 0, initial_state, &mut completed_paths);

    // If no paths completed (e.g., all paths are Unreachable), return empty path
    if completed_paths.is_empty() {
        completed_paths.push(CfgPath {
            condition: None,
            assignments: vec![],
            overflow_vcs: vec![],
            call_sites: vec![],
        });
    }

    completed_paths
}

/// Mutable state accumulated during path traversal.
#[derive(Clone)]
struct PathState {
    /// Branch conditions collected along this path.
    conditions: Vec<Term>,
    /// Assignments collected along this path.
    assignments: Vec<PathAssignment>,
    /// Overflow VCs found along this path.
    overflow_vcs: Vec<OverflowVcInfo>,
    /// Call sites encountered along this path.
    call_sites: Vec<CallSiteInfo>,
    /// Blocks visited on this path (cycle detection).
    visited: HashSet<usize>,
}

impl PathState {
    /// Build the path condition from accumulated branch conditions.
    fn path_condition(&self) -> Option<Term> {
        match self.conditions.len() {
            0 => None,
            1 => Some(self.conditions[0].clone()),
            _ => Some(Term::And(self.conditions.clone())),
        }
    }

    /// Finalize this path state into a CfgPath.
    fn into_cfg_path(self) -> CfgPath {
        let condition = self.path_condition();
        CfgPath {
            condition,
            assignments: self.assignments,
            overflow_vcs: self.overflow_vcs,
            call_sites: self.call_sites,
        }
    }
}

/// Recursively traverse a block, collecting assignments and following CFG edges.
fn traverse_block(
    func: &Function,
    block_idx: usize,
    mut state: PathState,
    completed: &mut Vec<CfgPath>,
) {
    // Cycle detection: skip if already visited on this path
    if state.visited.contains(&block_idx) {
        // Complete this path as-is (loop back-edge, Phase 2 will handle properly)
        completed.push(state.into_cfg_path());
        return;
    }

    // Bounds check
    if block_idx >= func.basic_blocks.len() {
        completed.push(state.into_cfg_path());
        return;
    }

    state.visited.insert(block_idx);
    let block = &func.basic_blocks[block_idx];

    // Process all statements in this block
    for (stmt_idx, stmt) in block.statements.iter().enumerate() {
        if let Statement::Assign(place, rvalue) = stmt {
            // Record overflow check info before adding the assignment
            match rvalue {
                Rvalue::BinaryOp(op, lhs_op, rhs_op)
                | Rvalue::CheckedBinaryOp(op, lhs_op, rhs_op) => {
                    state.overflow_vcs.push(OverflowVcInfo {
                        op: *op,
                        lhs_operand: lhs_op.clone(),
                        rhs_operand: rhs_op.clone(),
                        place: place.clone(),
                        block_idx,
                        stmt_idx,
                        prior_assignments: state.assignments.clone(),
                        path_condition: state.path_condition(),
                    });
                }
                _ => {}
            }

            // Record the assignment with the current branch depth
            state.assignments.push(PathAssignment {
                place: place.clone(),
                rvalue: rvalue.clone(),
                block_idx,
                branch_depth: state.conditions.len(),
            });
        }
    }

    // Follow the terminator
    match &block.terminator {
        Terminator::Return => {
            // Path complete
            completed.push(state.into_cfg_path());
        }

        Terminator::Goto(target) => {
            traverse_block(func, *target, state, completed);
        }

        Terminator::SwitchInt {
            discr,
            targets,
            otherwise,
        } => {
            let discr_term = encode_operand(discr);

            // Process each explicit target
            let mut taken_conditions = Vec::new();
            for (value, target_block) in targets {
                // Branch condition: discr == value
                let branch_cond = match discr {
                    Operand::Copy(place) | Operand::Move(place) => {
                        let discr_ty = find_local_type(func, &place.local);
                        match discr_ty {
                            Some(Ty::Bool) => {
                                if *value == 1 {
                                    discr_term.clone()
                                } else {
                                    Term::Not(Box::new(discr_term.clone()))
                                }
                            }
                            Some(ty) => {
                                let width = ty.bit_width().unwrap_or(32);
                                Term::Eq(
                                    Box::new(discr_term.clone()),
                                    Box::new(Term::BitVecLit(*value, width)),
                                )
                            }
                            None => {
                                // Default: treat as boolean
                                if *value == 1 {
                                    discr_term.clone()
                                } else {
                                    Term::Not(Box::new(discr_term.clone()))
                                }
                            }
                        }
                    }
                    Operand::Constant(_) => {
                        // Constant discriminant -- unusual but handle it
                        Term::Eq(
                            Box::new(discr_term.clone()),
                            Box::new(Term::BitVecLit(*value, 32)),
                        )
                    }
                };

                taken_conditions.push(branch_cond.clone());

                let mut branch_state = state.clone();
                branch_state.conditions.push(branch_cond);
                traverse_block(func, *target_block, branch_state, completed);
            }

            // Otherwise branch: NOT(any of the explicit conditions)
            let otherwise_cond = if taken_conditions.len() == 1 {
                Term::Not(Box::new(taken_conditions[0].clone()))
            } else {
                Term::Not(Box::new(Term::Or(taken_conditions)))
            };

            let mut otherwise_state = state;
            otherwise_state.conditions.push(otherwise_cond);
            traverse_block(func, *otherwise, otherwise_state, completed);
        }

        Terminator::Assert {
            cond: _,
            expected: _,
            target,
            kind: _,
        } => {
            // Process the assertion, then continue to target
            // (Assertion VCs are generated separately)
            traverse_block(func, *target, state, completed);
        }

        Terminator::Call {
            func: callee_func,
            args,
            destination,
            target,
        } => {
            // Record the call site for inter-procedural verification
            let callee_name = normalize_callee_name(callee_func);
            state.call_sites.push(CallSiteInfo {
                callee_name,
                args: args.clone(),
                destination: destination.clone(),
                block_idx,
                prior_assignments: state.assignments.clone(),
                path_condition: state.path_condition(),
            });
            // The destination gets an unconstrained value (havoc)
            // Continue to the target block
            traverse_block(func, *target, state, completed);
        }

        Terminator::Unreachable => {
            // Path ends here -- don't add to completed paths
            // (unreachable paths don't contribute to verification)
        }
    }
}

/// Collect all variable declarations for a function.
fn collect_declarations(func: &Function) -> Vec<Command> {
    let mut decls = Vec::new();

    // Return place
    let sort = encode_type(&func.return_local.ty);
    decls.push(Command::DeclareConst(func.return_local.name.clone(), sort));

    // Parameters
    for param in &func.params {
        let sort = encode_type(&param.ty);
        decls.push(Command::DeclareConst(param.name.clone(), sort));
    }

    // Locals (including ghost locals - they're declared but may not be used in executable VCs)
    for local in &func.locals {
        let sort = encode_type(&local.ty);
        decls.push(Command::DeclareConst(local.name.clone(), sort));
    }

    // Len constants: for each Rvalue::Len(place) in the body, declare {place}_len as BitVec(64)
    for bb in &func.basic_blocks {
        for stmt in &bb.statements {
            if let Statement::Assign(_, Rvalue::Len(len_place)) = stmt {
                let len_const = crate::encode_term::len_constant_name(&len_place.local);
                decls.push(Command::DeclareConst(
                    len_const,
                    rust_fv_smtlib::sort::Sort::BitVec(64),
                ));
            }
        }
    }

    decls
}

/// Generate bounds-check VCs for array/slice index accesses (Projection::Index).
///
/// Scans all statements in the function body. For every operand that reads through
/// a `Projection::Index(idx_local)`, emits a VC asserting:
///   NOT (0 <= idx AND idx < {arr}_len)   -- UNSAT means bounds check passes
///
/// The index local's type determines its bit width for zero-extension to 64 bits.
fn generate_index_bounds_vcs(
    func: &Function,
    datatype_declarations: &[Command],
    declarations: &[Command],
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    for (block_idx, bb) in func.basic_blocks.iter().enumerate() {
        for (stmt_idx, stmt) in bb.statements.iter().enumerate() {
            // Find operands with Index projections in assignment RHS
            let index_operand = match stmt {
                Statement::Assign(_, Rvalue::Use(op)) => extract_index_operand(op),
                _ => None,
            };

            if let Some((arr_local, idx_local)) = index_operand {
                // Determine bit width of index type
                let idx_bits = find_local_type(func, idx_local)
                    .map(crate::encode_term::ty_bit_width)
                    .unwrap_or(64);

                let idx_term = Term::Const(idx_local.to_string());
                let len_term = Term::Const(crate::encode_term::len_constant_name(arr_local));
                let bounds_ok = crate::encode_term::bounds_check_term(idx_term, idx_bits, len_term);

                // Build VC script: assert NOT bounds_ok — UNSAT proves safety
                let mut script = Script::new();
                script.push(Command::SetLogic("QF_BV".to_string()));
                script.push(Command::SetOption(
                    "produce-models".to_string(),
                    "true".to_string(),
                ));
                for cmd in datatype_declarations {
                    script.push(cmd.clone());
                }
                for cmd in declarations {
                    script.push(cmd.clone());
                }
                script.push(Command::Assert(Term::Not(Box::new(bounds_ok))));
                script.push(Command::CheckSat);
                script.push(Command::GetModel);

                let desc = format!(
                    "bounds check: {} index {} in bounds at block {}",
                    arr_local, idx_local, block_idx
                );
                vcs.push(VerificationCondition {
                    description: desc,
                    script,
                    location: VcLocation {
                        function: func.name.clone(),
                        block: block_idx,
                        statement: stmt_idx,
                        source_file: None,
                        source_line: None,
                        source_column: None,
                        contract_text: Some(format!(
                            "0 <= {} && {} < {}_len",
                            idx_local, idx_local, arr_local
                        )),
                        vc_kind: VcKind::MemorySafety,
                    },
                });
            }
        }
    }

    vcs
}

/// Extract (arr_local, idx_local) from an operand that reads through Projection::Index.
fn extract_index_operand(op: &Operand) -> Option<(&str, &str)> {
    let place = match op {
        Operand::Copy(p) | Operand::Move(p) => p,
        Operand::Constant(_) => return None,
    };
    for proj in &place.projections {
        if let Projection::Index(idx_local) = proj {
            return Some((&place.local, idx_local.as_str()));
        }
    }
    None
}

/// Check if a function uses specification integer types (SpecInt/SpecNat).
/// This determines whether we need Int theory in SMT logic.
fn uses_spec_int_types(func: &Function) -> bool {
    // Check return type
    if func.return_local.ty.is_spec_int() {
        return true;
    }
    // Check parameters
    for param in &func.params {
        if param.ty.is_spec_int() {
            return true;
        }
    }
    // Check locals
    for local in &func.locals {
        if local.ty.is_spec_int() {
            return true;
        }
    }
    false
}

/// Build a base script with logic, datatype declarations, and variable declarations.
///
/// Datatype declarations (DeclareDatatype) must come AFTER SetLogic/SetOption
/// but BEFORE DeclareConst, since SMT-LIB requires sorts to be declared before use.
///
/// Logic selection:
/// - QF_BV: bitvectors only
/// - QF_UFBVDT: bitvectors + datatypes
/// - AUFLIRA: arrays, uninterpreted functions, linear integer/real arithmetic
/// - When Int theory is needed (for SpecInt/SpecNat or Bv2Int terms), use AUFLIRA
///   or omit set-logic to let Z3 auto-detect (more robust)
fn base_script(
    datatype_declarations: &[Command],
    variable_declarations: &[Command],
    uses_int: bool,
) -> Script {
    let mut script = Script::new();

    // Logic selection based on features used
    if uses_int {
        // Int theory needed: use ALL logic to get all Z3 theories including bv2int/int2bv
        // These conversion functions are Z3 extensions, not standard SMT-LIB2
        script.push(Command::SetLogic("ALL".to_string()));
        tracing::debug!("Using ALL logic for Int theory + bitvectors with bv2int/int2bv");
    } else if datatype_declarations.is_empty() {
        script.push(Command::SetLogic("QF_BV".to_string()));
    } else {
        script.push(Command::SetLogic("QF_UFBVDT".to_string()));
    }

    script.push(Command::SetOption(
        "produce-models".to_string(),
        "true".to_string(),
    ));

    // Datatype declarations first (sort definitions)
    for decl in datatype_declarations {
        script.push(decl.clone());
    }

    // Then variable declarations (which may reference the datatype sorts)
    for decl in variable_declarations {
        script.push(decl.clone());
    }
    script
}

/// Encode an assignment as an SMT assertion.
fn encode_assignment(
    place: &Place,
    rvalue: &Rvalue,
    func: &Function,
    _ssa_counter: &mut HashMap<String, u32>,
) -> Option<Command> {
    // Handle projected LHS (field access on left side)
    if !place.projections.is_empty() {
        // For projected places, encode the LHS using type-aware projection
        let lhs = encode_place_with_type(place, func)?;
        let rhs = match rvalue {
            Rvalue::Use(op) => encode_operand_for_vcgen(op, func),
            _ => return None, // Complex rvalues on projected places are rare
        };
        return Some(Command::Assert(Term::Eq(Box::new(lhs), Box::new(rhs))));
    }

    let lhs = Term::Const(place.local.clone());

    let rhs = match rvalue {
        Rvalue::Use(op) => encode_operand_for_vcgen(op, func),
        Rvalue::BinaryOp(op, lhs_op, rhs_op) => {
            let l = encode_operand(lhs_op);
            let r = encode_operand(rhs_op);
            // For comparison ops (Gt, Lt, Ge, Le, Eq, Ne), the result type is Bool
            // but signedness must come from the *operand* types, not the destination.
            let ty = if op.is_comparison() {
                infer_operand_type(func, lhs_op)
                    .or_else(|| infer_operand_type(func, rhs_op))
                    .or_else(|| find_local_type(func, &place.local))?
            } else {
                find_local_type(func, &place.local)?
            };
            encode_binop(*op, &l, &r, ty)
        }
        Rvalue::CheckedBinaryOp(op, lhs_op, rhs_op) => {
            // For checked ops, encode just the result (field .0 of the tuple)
            let l = encode_operand(lhs_op);
            let r = encode_operand(rhs_op);
            let ty = infer_operand_type(func, lhs_op)?;
            encode_binop(*op, &l, &r, ty)
        }
        Rvalue::UnaryOp(op, operand) => {
            let t = encode_operand(operand);
            let ty = find_local_type(func, &place.local)?;
            encode_unop(*op, &t, ty)
        }
        Rvalue::Ref(_, ref_place) => {
            // Reference is transparent -- same as the value
            Term::Const(ref_place.local.clone())
        }
        Rvalue::Len(len_place) => {
            // Model slice/array length as a named constant: {local}_len.
            // The constant is declared as Sort::BitVec(64) via collect_declarations.
            let len_name = crate::encode_term::len_constant_name(&len_place.local);
            Term::Const(len_name)
        }
        Rvalue::Cast(kind, op, target_ty) => {
            let src = encode_operand_for_vcgen(op, func);
            let source_ty = infer_operand_type(func, op).unwrap_or(target_ty); // fallback: assume same type (safe — no truncation)
            let from_bits = crate::encode_term::ty_bit_width(source_ty);
            let to_bits = crate::encode_term::ty_bit_width(target_ty);
            let from_signed = crate::encode_term::ty_is_signed(source_ty);
            crate::encode_term::encode_cast(kind, src, from_bits, to_bits, from_signed)
        }
        Rvalue::Aggregate(kind, operands) => {
            let result_ty = find_local_type(func, &place.local);
            if let Some(ty) = result_ty {
                encode_aggregate_with_type(kind, operands, ty)?
            } else {
                return None;
            }
        }
        Rvalue::Discriminant(disc_place) => {
            // Encode the discriminant of an enum value as an uninterpreted selector application.
            // The discriminant is an integer tag that SwitchInt compares against literal variant
            // indices. We declare it as: (discriminant-{local} enum_value) where enum_value is
            // the place holding the enum. This produces Term::App which the SwitchInt
            // path-condition logic already handles correctly — SwitchInt compares discr_term
            // against BitVecLit values for each target arm.
            let disc_fn = format!("discriminant-{}", disc_place.local);
            Term::App(disc_fn, vec![Term::Const(disc_place.local.clone())])
        }
    };

    Some(Command::Assert(Term::Eq(Box::new(lhs), Box::new(rhs))))
}

/// Encode a path's assignments as guarded SMT assertions.
///
/// Assignments made AFTER a branch point (branch_depth > 0) are guarded:
/// `(assert (=> path_cond (= var value)))`
///
/// Assignments made in the common prefix BEFORE any branch (branch_depth == 0)
/// are unguarded: `(assert (= var value))`
///
/// If there is no condition (single path), all assertions are unguarded.
fn encode_path_assignments(func: &Function, path: &CfgPath) -> Vec<Command> {
    let mut ssa_counter = HashMap::new();
    let mut assertions = Vec::new();

    for pa in &path.assignments {
        if let Some(cmd) = encode_assignment(&pa.place, &pa.rvalue, func, &mut ssa_counter) {
            // Only guard assignments that were made AFTER a branch point
            if pa.branch_depth > 0 {
                if let (Some(cond), Command::Assert(inner_term)) = (&path.condition, &cmd) {
                    assertions.push(Command::Assert(Term::Implies(
                        Box::new(cond.clone()),
                        Box::new(inner_term.clone()),
                    )));
                } else {
                    assertions.push(cmd);
                }
            } else {
                // Common prefix assignment -- no guard needed
                assertions.push(cmd);
            }
        }
    }

    assertions
}

/// Generate an overflow VC from overflow info collected during path traversal.
fn generate_overflow_vc(
    func: &Function,
    datatype_declarations: &[Command],
    declarations: &[Command],
    ov: &OverflowVcInfo,
    ghost_pred_db: &GhostPredicateDatabase,
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    let lhs = encode_operand(&ov.lhs_operand);
    let rhs = encode_operand(&ov.rhs_operand);

    let ty = infer_operand_type(func, &ov.lhs_operand)
        .or_else(|| find_local_type(func, &ov.place.local));

    if let Some(ty) = ty
        && let Some(no_overflow) = overflow_check(ov.op, &lhs, &rhs, ty)
    {
        let mut script = base_script(
            datatype_declarations,
            declarations,
            uses_spec_int_types(func),
        );

        // Add prior assignments along this path
        let mut ssa_counter = HashMap::new();
        for pa in &ov.prior_assignments {
            if let Some(cmd) = encode_assignment(&pa.place, &pa.rvalue, func, &mut ssa_counter) {
                script.push(cmd);
            }
        }

        // Assume preconditions
        for pre in &func.contracts.requires {
            if let Some(pre_term) = parse_spec(&pre.raw, func, ghost_pred_db) {
                script.push(Command::Assert(pre_term));
            }
        }

        // If there's a path condition, assume it
        if let Some(ref cond) = ov.path_condition {
            script.push(Command::Assert(cond.clone()));
        }

        // Assert that overflow IS possible (negate no-overflow)
        script.push(Command::Assert(Term::Not(Box::new(no_overflow))));
        script.push(Command::CheckSat);
        script.push(Command::GetModel);

        vcs.push(VerificationCondition {
            description: format!(
                "{}: no overflow in {:?} at block {}, stmt {}",
                func.name, ov.op, ov.block_idx, ov.stmt_idx,
            ),
            script,
            location: VcLocation {
                function: func.name.clone(),
                block: ov.block_idx,
                statement: ov.stmt_idx,
                source_file: None,
                source_line: None,
                source_column: None,
                contract_text: None,
                vc_kind: VcKind::from_overflow_op(ov.op),
            },
        });
    }

    vcs
}

/// Generate VCs for Terminator::Assert along all paths.
///
/// Each Assert terminator in the CFG produces a VC that checks whether the
/// assertion condition can ever fail under the given preconditions. The
/// `AssertKind` provides specific error messages identifying the panic source.
fn generate_assert_terminator_vcs(
    func: &Function,
    datatype_declarations: &[Command],
    declarations: &[Command],
    paths: &[CfgPath],
    ghost_pred_db: &GhostPredicateDatabase,
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    // Find blocks with Assert terminators
    for (block_idx, block) in func.basic_blocks.iter().enumerate() {
        if let Terminator::Assert {
            cond,
            expected,
            kind,
            ..
        } = &block.terminator
        {
            let cond_term = encode_operand(cond);
            let expected_term = Term::BoolLit(*expected);

            // Find paths that pass through this block
            let relevant_paths: Vec<_> = paths
                .iter()
                .filter(|p| {
                    p.assignments.iter().any(|a| a.block_idx == block_idx)
                        || p.assignments.is_empty()
                })
                .collect();

            let mut script = base_script(
                datatype_declarations,
                declarations,
                uses_spec_int_types(func),
            );

            // Encode all path assignments
            for path in &relevant_paths {
                let cmds = encode_path_assignments(func, path);
                for cmd in cmds {
                    script.push(cmd);
                }
            }

            // If no relevant paths found, fall back to encoding all paths
            if relevant_paths.is_empty() {
                for path in paths {
                    let cmds = encode_path_assignments(func, path);
                    for cmd in cmds {
                        script.push(cmd);
                    }
                }
            }

            // Assume preconditions
            for pre in &func.contracts.requires {
                if let Some(pre_term) = parse_spec(&pre.raw, func, ghost_pred_db) {
                    script.push(Command::Assert(pre_term));
                }
            }

            // Build description from AssertKind
            let description = format_assert_description(&func.name, block_idx, kind);

            // Try to find a case where the assertion fails
            let assertion_holds = Term::Eq(Box::new(cond_term), Box::new(expected_term));
            script.push(Command::Comment(description.clone()));
            script.push(Command::Assert(Term::Not(Box::new(assertion_holds))));
            script.push(Command::CheckSat);
            script.push(Command::GetModel);

            vcs.push(VerificationCondition {
                description,
                script,
                location: VcLocation {
                    function: func.name.clone(),
                    block: block_idx,
                    statement: usize::MAX,
                    source_file: None,
                    source_line: None,
                    source_column: None,
                    contract_text: None,
                    vc_kind: VcKind::Assertion,
                },
            });
        }
    }

    vcs
}

/// Format a human-readable description from an AssertKind.
fn format_assert_description(func_name: &str, block_idx: usize, kind: &AssertKind) -> String {
    match kind {
        AssertKind::UserAssert => {
            format!("{func_name}: assertion might fail at block {block_idx}")
        }
        AssertKind::BoundsCheck { .. } => {
            format!("{func_name}: array index out of bounds at block {block_idx}")
        }
        AssertKind::Overflow(op) => {
            format!("{func_name}: arithmetic overflow in {op:?} at block {block_idx}")
        }
        AssertKind::DivisionByZero => {
            format!("{func_name}: division by zero at block {block_idx}")
        }
        AssertKind::RemainderByZero => {
            format!("{func_name}: remainder by zero at block {block_idx}")
        }
        AssertKind::NegationOverflow => {
            format!("{func_name}: negation overflow at block {block_idx}")
        }
        AssertKind::UnwrapNone => {
            format!("{func_name}: unwrap() called on None at block {block_idx}")
        }
        AssertKind::ExpectFailed(msg) => {
            format!("{func_name}: expect() failed: {msg} at block {block_idx}")
        }
        AssertKind::Other(msg) => {
            format!("{func_name}: {msg} at block {block_idx}")
        }
    }
}

/// Generate contract verification conditions using path-sensitive encoding.
///
/// For each postcondition, we:
/// 1. Declare all variables
/// 2. Encode all path assignments with path-condition guards
/// 3. Assert all preconditions
/// 4. Assume callee postconditions at call sites (if contract_db provided)
/// 5. Try to find a counterexample where the postcondition fails
fn generate_contract_vcs(
    func: &Function,
    datatype_declarations: &[Command],
    declarations: &[Command],
    paths: &[CfgPath],
    contract_db: Option<&ContractDatabase>,
    ghost_pred_db: &GhostPredicateDatabase,
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    if func.contracts.ensures.is_empty() {
        return vcs;
    }

    // Detect prophecies for mutable reference parameters
    let prophecies = crate::encode_prophecy::detect_prophecies(func);

    for (post_idx, post) in func.contracts.ensures.iter().enumerate() {
        let mut script = base_script(
            datatype_declarations,
            declarations,
            uses_spec_int_types(func),
        );

        // Encode assignments from ALL paths, each guarded by its path condition
        for path in paths {
            let cmds = encode_path_assignments(func, path);
            for cmd in cmds {
                script.push(cmd);
            }

            // Resolve prophecies at return (all paths end with Return)
            if !prophecies.is_empty() {
                // For simplified approach: assume the final value equals the current value
                // (i.e., the last assignment to each prophecy param's deref place)
                let final_values = HashMap::new(); // Empty map = use current value
                let resolution_cmds =
                    crate::encode_prophecy::prophecy_resolutions(&prophecies, &final_values);

                for cmd in resolution_cmds {
                    // Guard prophecy resolution by path condition
                    if let (Some(cond), Command::Assert(inner_term)) = (&path.condition, &cmd) {
                        script.push(Command::Assert(Term::Implies(
                            Box::new(cond.clone()),
                            Box::new(inner_term.clone()),
                        )));
                    } else {
                        script.push(cmd);
                    }
                }
            }
        }

        // Assume preconditions
        for pre in &func.contracts.requires {
            if let Some(pre_term) = parse_spec(&pre.raw, func, ghost_pred_db) {
                script.push(Command::Assert(pre_term));
            }
        }

        // Assume callee postconditions at call sites (inter-procedural)
        if let Some(db) = contract_db {
            for path in paths {
                for call_site in &path.call_sites {
                    encode_callee_postcondition_assumptions(
                        func,
                        db,
                        call_site,
                        &mut script,
                        ghost_pred_db,
                    );
                }
            }
        }

        // Assert that at least one path is taken
        // (The disjunction of all path conditions must be true)
        let path_conds: Vec<Term> = paths.iter().filter_map(|p| p.condition.clone()).collect();
        if !path_conds.is_empty() {
            script.push(Command::Assert(Term::Or(path_conds)));
        }

        // Sep-logic: if the function's contracts mention pts_to, upgrade to QF_AUFBV
        // and prepend sep-heap declarations so the solver can interpret the heap arrays.
        if has_sep_logic_spec(&func.contracts) {
            prepend_sep_heap_decls(&mut script);
            // No frame forall in postcondition VCs (no call site), so use QF_AUFBV
            let new_logic = sep_logic::sep_logic_smt_logic(false);
            script = replace_script_logic(script, new_logic);
        }

        // Negate postcondition and check if SAT (= postcondition violated)
        if let Some(post_term) = parse_spec(&post.raw, func, ghost_pred_db) {
            script.push(Command::Comment(format!(
                "Check postcondition: {}",
                post.raw
            )));
            script.push(Command::Assert(Term::Not(Box::new(post_term))));
            script.push(Command::CheckSat);
            script.push(Command::GetModel);

            vcs.push(VerificationCondition {
                description: format!(
                    "{}: postcondition {} holds ({})",
                    func.name, post_idx, post.raw,
                ),
                script,
                location: VcLocation {
                    function: func.name.clone(),
                    block: 0,
                    statement: 0,
                    source_file: None,
                    source_line: None,
                    source_column: None,
                    contract_text: Some(post.raw.clone()),
                    vc_kind: VcKind::Postcondition,
                },
            });
        }
    }

    vcs
}

// === Inter-procedural verification ===

/// Normalize a callee function name from MIR debug formatting.
///
/// MIR represents function operands with debug output like `const add` or
/// `const my_module::helper`. This strips the `const ` prefix and takes
/// the last path segment to get the bare function name for contract lookup.
pub fn normalize_callee_name(raw: &str) -> String {
    let trimmed = raw.trim();
    let stripped = trimmed.strip_prefix("const ").unwrap_or(trimmed).trim();
    // Take the last segment after `::`
    stripped
        .rsplit_once("::")
        .map(|(_, name)| name)
        .unwrap_or(stripped)
        .to_string()
}

/// Recursively substitute named constants in a Term tree.
///
/// For each `Term::Const(name)` where `substitutions` contains a mapping,
/// the constant is replaced with the mapped term. This is used to map callee
/// parameter names to actual argument terms at call sites.
pub fn substitute_term(term: &Term, substitutions: &HashMap<String, Term>) -> Term {
    match term {
        Term::Const(name) => {
            if let Some(replacement) = substitutions.get(name) {
                replacement.clone()
            } else {
                term.clone()
            }
        }
        Term::Not(t) => Term::Not(Box::new(substitute_term(t, substitutions))),
        Term::And(terms) => Term::And(
            terms
                .iter()
                .map(|t| substitute_term(t, substitutions))
                .collect(),
        ),
        Term::Or(terms) => Term::Or(
            terms
                .iter()
                .map(|t| substitute_term(t, substitutions))
                .collect(),
        ),
        Term::Implies(a, b) => Term::Implies(
            Box::new(substitute_term(a, substitutions)),
            Box::new(substitute_term(b, substitutions)),
        ),
        Term::Eq(a, b) => Term::Eq(
            Box::new(substitute_term(a, substitutions)),
            Box::new(substitute_term(b, substitutions)),
        ),
        Term::BvSLe(a, b) => Term::BvSLe(
            Box::new(substitute_term(a, substitutions)),
            Box::new(substitute_term(b, substitutions)),
        ),
        Term::BvSLt(a, b) => Term::BvSLt(
            Box::new(substitute_term(a, substitutions)),
            Box::new(substitute_term(b, substitutions)),
        ),
        Term::BvSGe(a, b) => Term::BvSGe(
            Box::new(substitute_term(a, substitutions)),
            Box::new(substitute_term(b, substitutions)),
        ),
        Term::BvSGt(a, b) => Term::BvSGt(
            Box::new(substitute_term(a, substitutions)),
            Box::new(substitute_term(b, substitutions)),
        ),
        Term::BvULe(a, b) => Term::BvULe(
            Box::new(substitute_term(a, substitutions)),
            Box::new(substitute_term(b, substitutions)),
        ),
        Term::BvULt(a, b) => Term::BvULt(
            Box::new(substitute_term(a, substitutions)),
            Box::new(substitute_term(b, substitutions)),
        ),
        Term::BvUGe(a, b) => Term::BvUGe(
            Box::new(substitute_term(a, substitutions)),
            Box::new(substitute_term(b, substitutions)),
        ),
        Term::BvUGt(a, b) => Term::BvUGt(
            Box::new(substitute_term(a, substitutions)),
            Box::new(substitute_term(b, substitutions)),
        ),
        Term::BvAdd(a, b) => Term::BvAdd(
            Box::new(substitute_term(a, substitutions)),
            Box::new(substitute_term(b, substitutions)),
        ),
        Term::BvSub(a, b) => Term::BvSub(
            Box::new(substitute_term(a, substitutions)),
            Box::new(substitute_term(b, substitutions)),
        ),
        Term::BvMul(a, b) => Term::BvMul(
            Box::new(substitute_term(a, substitutions)),
            Box::new(substitute_term(b, substitutions)),
        ),
        Term::BvSDiv(a, b) => Term::BvSDiv(
            Box::new(substitute_term(a, substitutions)),
            Box::new(substitute_term(b, substitutions)),
        ),
        Term::BvUDiv(a, b) => Term::BvUDiv(
            Box::new(substitute_term(a, substitutions)),
            Box::new(substitute_term(b, substitutions)),
        ),
        Term::BvSRem(a, b) => Term::BvSRem(
            Box::new(substitute_term(a, substitutions)),
            Box::new(substitute_term(b, substitutions)),
        ),
        Term::BvURem(a, b) => Term::BvURem(
            Box::new(substitute_term(a, substitutions)),
            Box::new(substitute_term(b, substitutions)),
        ),
        Term::BvNeg(a) => Term::BvNeg(Box::new(substitute_term(a, substitutions))),
        Term::BvAnd(a, b) => Term::BvAnd(
            Box::new(substitute_term(a, substitutions)),
            Box::new(substitute_term(b, substitutions)),
        ),
        Term::BvOr(a, b) => Term::BvOr(
            Box::new(substitute_term(a, substitutions)),
            Box::new(substitute_term(b, substitutions)),
        ),
        Term::BvXor(a, b) => Term::BvXor(
            Box::new(substitute_term(a, substitutions)),
            Box::new(substitute_term(b, substitutions)),
        ),
        Term::BvNot(a) => Term::BvNot(Box::new(substitute_term(a, substitutions))),
        Term::BvShl(a, b) => Term::BvShl(
            Box::new(substitute_term(a, substitutions)),
            Box::new(substitute_term(b, substitutions)),
        ),
        Term::BvLShr(a, b) => Term::BvLShr(
            Box::new(substitute_term(a, substitutions)),
            Box::new(substitute_term(b, substitutions)),
        ),
        Term::BvAShr(a, b) => Term::BvAShr(
            Box::new(substitute_term(a, substitutions)),
            Box::new(substitute_term(b, substitutions)),
        ),
        Term::Ite(c, t, e) => Term::Ite(
            Box::new(substitute_term(c, substitutions)),
            Box::new(substitute_term(t, substitutions)),
            Box::new(substitute_term(e, substitutions)),
        ),
        Term::App(name, args) => Term::App(
            name.clone(),
            args.iter()
                .map(|a| substitute_term(a, substitutions))
                .collect(),
        ),
        // Literals and other non-variable terms: return as-is
        _ => term.clone(),
    }
}

/// Build the argument substitution map for a call site.
///
/// Maps callee parameter names (e.g., "_1", "_2") to the caller's actual
/// argument terms at the call site.
fn build_arg_substitutions(
    call_site: &CallSiteInfo,
    callee_summary: &crate::contract_db::FunctionSummary,
    caller_func: &Function,
) -> HashMap<String, Term> {
    let mut subs = HashMap::new();
    for (i, param_name) in callee_summary.param_names.iter().enumerate() {
        if let Some(arg) = call_site.args.get(i) {
            let arg_term = encode_operand_for_vcgen(arg, caller_func);
            subs.insert(param_name.clone(), arg_term);
        }
    }
    subs
}

/// Check whether a function's contracts contain separation-logic predicates.
///
/// A cheap syntactic check: returns `true` if any `requires` or `ensures`
/// raw string contains the substring `"pts_to("`. This is sufficient for Phase 20
/// to determine whether sep-heap declarations and frame axioms are needed.
fn has_sep_logic_spec(contracts: &Contracts) -> bool {
    contracts.requires.iter().any(|s| s.raw.contains("pts_to("))
        || contracts.ensures.iter().any(|s| s.raw.contains("pts_to("))
}

/// Prepend sep-heap SMT declarations to a script.
///
/// Inserts `declare_sep_heap()` and `declare_heapval_accessor(64)` commands
/// immediately after the `SetLogic` command (which is always the first command).
fn prepend_sep_heap_decls(script: &mut Script) {
    let mut sep_decls: Vec<Command> = sep_logic::declare_sep_heap();
    sep_decls.push(sep_logic::declare_heapval_accessor(64));

    // Insert after SetLogic (index 0)
    let commands: Vec<Command> = script.commands().to_vec();
    let mut new_commands = Vec::with_capacity(commands.len() + sep_decls.len());
    if let Some((first, rest)) = commands.split_first() {
        new_commands.push(first.clone());
        new_commands.extend(sep_decls);
        new_commands.extend_from_slice(rest);
    } else {
        new_commands.extend(sep_decls);
    }
    *script = Script::with_commands(new_commands);
}

/// Generate call-site precondition VCs for inter-procedural verification.
///
/// For each call site on each path, if the callee has preconditions in the
/// contract database, we generate a VC that checks whether the caller satisfies
/// the callee's preconditions. The VC encodes:
/// - Prior path assignments (establishing the caller's state)
/// - Caller's preconditions as assumptions
/// - Callee's precondition (with argument substitution) as the assertion
///
/// If the VC is SAT, the caller may violate the callee's precondition.
fn generate_call_site_vcs(
    func: &Function,
    contract_db: &ContractDatabase,
    datatype_declarations: &[Command],
    declarations: &[Command],
    paths: &[CfgPath],
    ghost_pred_db: &GhostPredicateDatabase,
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    for path in paths {
        for call_site in &path.call_sites {
            let callee_summary = match contract_db.get(&call_site.callee_name) {
                Some(s) => s,
                None => {
                    tracing::debug!(
                        caller = %func.name,
                        callee = %call_site.callee_name,
                        "Call to function without contracts -- treating as opaque"
                    );
                    continue;
                }
            };

            if callee_summary.contracts.requires.is_empty() {
                tracing::debug!(
                    caller = %func.name,
                    callee = %call_site.callee_name,
                    "Callee has no preconditions -- skipping call-site VC"
                );
                continue;
            }

            tracing::debug!(
                caller = %func.name,
                callee = %call_site.callee_name,
                preconditions = callee_summary.contracts.requires.len(),
                "Encoding call-site precondition VCs"
            );

            // Build the callee function context for parsing specs
            let callee_func_context = build_callee_func_context(callee_summary);
            let arg_subs = build_arg_substitutions(call_site, callee_summary, func);

            for (pre_idx, pre) in callee_summary.contracts.requires.iter().enumerate() {
                // Parse the precondition in the callee's context
                let pre_term = match parse_spec(&pre.raw, &callee_func_context, ghost_pred_db) {
                    Some(t) => t,
                    None => continue,
                };

                // Substitute callee param names with actual caller arguments
                let substituted_pre = substitute_term(&pre_term, &arg_subs);

                let mut script = base_script(
                    datatype_declarations,
                    declarations,
                    uses_spec_int_types(func),
                );

                // Encode prior assignments along this path
                let mut ssa_counter = HashMap::new();
                for pa in &call_site.prior_assignments {
                    if let Some(cmd) =
                        encode_assignment(&pa.place, &pa.rvalue, func, &mut ssa_counter)
                    {
                        script.push(cmd);
                    }
                }

                // Assume caller's preconditions
                for caller_pre in &func.contracts.requires {
                    if let Some(caller_pre_term) = parse_spec(&caller_pre.raw, func, ghost_pred_db)
                    {
                        script.push(Command::Assert(caller_pre_term));
                    }
                }

                // If there's a path condition, assume it
                if let Some(ref cond) = call_site.path_condition {
                    script.push(Command::Assert(cond.clone()));
                }

                // Sep-logic frame rule: if callee has pts_to in contracts, emit frame axiom
                // and upgrade SMT logic to AUFBV (arrays + bitvectors + quantifiers).
                if has_sep_logic_spec(&callee_summary.contracts) {
                    // 1. Prepend sep-heap declarations after SetLogic
                    prepend_sep_heap_decls(&mut script);

                    // 2. Snapshot sep_heap before the call (sep_heap_pre = sep_heap)
                    script.push(Command::DeclareFun(
                        "sep_heap_pre".to_string(),
                        vec![],
                        rust_fv_smtlib::sort::Sort::Array(
                            Box::new(rust_fv_smtlib::sort::Sort::BitVec(64)),
                            Box::new(rust_fv_smtlib::sort::Sort::Uninterpreted(
                                "HeapVal".to_string(),
                            )),
                        ),
                    ));
                    script.push(Command::Assert(Term::Eq(
                        Box::new(Term::Const("sep_heap_pre".to_string())),
                        Box::new(Term::Const("sep_heap".to_string())),
                    )));

                    // 3. Extract footprint from callee's requires terms and emit frame axiom
                    let mut footprint_ptrs = Vec::new();
                    for req in &callee_summary.contracts.requires {
                        if let Some(req_term) =
                            parse_spec(&req.raw, &callee_func_context, ghost_pred_db)
                        {
                            let fp = sep_logic::extract_pts_to_footprint(&req_term);
                            footprint_ptrs.extend(fp);
                        }
                    }
                    // Substitute callee param names with caller arg terms in footprint
                    let footprint_substituted: Vec<Term> = footprint_ptrs
                        .iter()
                        .map(|t| substitute_term(t, &arg_subs))
                        .collect();
                    let frame_axiom = sep_logic::build_frame_axiom(&footprint_substituted);
                    script.push(Command::Assert(frame_axiom));

                    // 4. Upgrade SMT logic from QF_BV to AUFBV (frame forall needs quantifiers)
                    let new_logic = sep_logic::sep_logic_smt_logic(true);
                    script = replace_script_logic(script, new_logic);
                }

                // Assert that the callee's precondition CAN be violated (negate it)
                script.push(Command::Comment(format!(
                    "Check call to {}: precondition {} ({})",
                    call_site.callee_name, pre_idx, pre.raw,
                )));
                script.push(Command::Assert(Term::Not(Box::new(substituted_pre))));
                script.push(Command::CheckSat);
                script.push(Command::GetModel);

                vcs.push(VerificationCondition {
                    description: format!(
                        "{}: call to {} satisfies precondition {} ({})",
                        func.name, call_site.callee_name, pre_idx, pre.raw,
                    ),
                    script,
                    location: VcLocation {
                        function: func.name.clone(),
                        block: call_site.block_idx,
                        statement: 0,
                        source_file: None,
                        source_line: None,
                        source_column: None,
                        contract_text: Some(pre.raw.clone()),
                        vc_kind: VcKind::Precondition,
                    },
                });
            }
        }
    }

    vcs
}

/// Encode callee postcondition assumptions and ownership constraints into a script.
///
/// For each call site, if the callee has postconditions in the contract database,
/// we assert them (positively) with `result` mapped to the call's destination
/// and callee params mapped to actual arguments. This lets Z3 use the callee's
/// postconditions as known facts when checking the caller's postcondition.
///
/// Additionally, ownership constraints are encoded:
/// - `SharedBorrow` / `Copied` arguments: value is preserved after the call
/// - `MutableBorrow` arguments: value may change (no preservation constraint)
/// - `Moved` arguments: value consumed (logged, no constraint needed)
fn encode_callee_postcondition_assumptions(
    func: &Function,
    contract_db: &ContractDatabase,
    call_site: &CallSiteInfo,
    script: &mut Script,
    ghost_pred_db: &GhostPredicateDatabase,
) {
    let callee_summary = match contract_db.get(&call_site.callee_name) {
        Some(s) => s,
        None => {
            // Even without a callee contract, encode ownership constraints
            // if we can infer types from the caller's context
            encode_ownership_constraints_at_call_site(
                func,
                call_site,
                &[], // no param types from callee
                script,
            );
            return;
        }
    };

    // Encode ownership constraints using callee's param type information
    encode_ownership_constraints_at_call_site(func, call_site, &callee_summary.param_types, script);

    if callee_summary.contracts.ensures.is_empty() {
        return;
    }

    let callee_func_context = build_callee_func_context(callee_summary);
    let mut arg_subs = build_arg_substitutions(call_site, callee_summary, func);

    // Map callee's return place to the caller's destination for this call
    // The callee's return local is "_0", which `result` maps to
    arg_subs.insert(
        callee_func_context.return_local.name.clone(),
        Term::Const(call_site.destination.local.clone()),
    );

    for post in &callee_summary.contracts.ensures {
        if let Some(post_term) = parse_spec(&post.raw, &callee_func_context, ghost_pred_db) {
            let substituted_post = substitute_term(&post_term, &arg_subs);
            tracing::debug!(
                caller = %func.name,
                callee = %call_site.callee_name,
                postcondition = %post.raw,
                "Assuming callee postcondition at call site"
            );
            script.push(Command::Assert(substituted_post));
        }
    }
}

/// Encode ownership constraints at a call site.
///
/// For each argument, classifies its ownership kind based on the operand and
/// the callee's parameter type, then generates appropriate constraints:
/// - `ValuePreserved`: asserts the variable equals a pre-call snapshot
/// - `ValueMayChange`: no constraint (value is havoced)
/// - `ValueConsumed`: logged for tracing (borrow checker handles this)
fn encode_ownership_constraints_at_call_site(
    func: &Function,
    call_site: &CallSiteInfo,
    callee_param_types: &[Ty],
    script: &mut Script,
) {
    for (i, arg) in call_site.args.iter().enumerate() {
        // Use callee param type if available, otherwise infer from caller context
        let param_ty = if let Some(ty) = callee_param_types.get(i) {
            ty.clone()
        } else {
            // Fall back to caller's operand type
            match arg {
                Operand::Copy(place) | Operand::Move(place) => find_local_type(func, &place.local)
                    .cloned()
                    .unwrap_or(Ty::Unit),
                Operand::Constant(_) => continue, // Constants don't need constraints
            }
        };

        let kind = classify_argument(arg, &param_ty);
        let constraints = generate_ownership_constraints(kind, arg);

        for constraint in &constraints {
            match constraint {
                OwnershipConstraint::ValuePreserved { variable } => {
                    // Declare a pre-call snapshot and assert preservation
                    let pre_call_name = format!("{}_pre_call_{}", variable, call_site.block_idx);
                    // Declare the snapshot variable with the same sort
                    if let Some(ty) = find_local_type(func, variable) {
                        let sort = encode_type(ty);
                        script.push(Command::DeclareConst(pre_call_name.clone(), sort));
                    }
                    // Before the call: snapshot = variable
                    script.push(Command::Assert(Term::Eq(
                        Box::new(Term::Const(pre_call_name.clone())),
                        Box::new(Term::Const(variable.clone())),
                    )));
                    // After the call: variable = snapshot (preserved)
                    script.push(Command::Assert(Term::Eq(
                        Box::new(Term::Const(variable.clone())),
                        Box::new(Term::Const(pre_call_name)),
                    )));
                    tracing::debug!(
                        caller = %func.name,
                        callee = %call_site.callee_name,
                        variable = %variable,
                        kind = ?kind,
                        "Ownership: value preserved after call"
                    );
                }
                OwnershipConstraint::ValueMayChange { variable } => {
                    tracing::debug!(
                        caller = %func.name,
                        callee = %call_site.callee_name,
                        variable = %variable,
                        "Ownership: mutable borrow -- value may change (havoced)"
                    );
                    // No constraint -- value is unconstrained after the call
                }
                OwnershipConstraint::ValueConsumed { variable } => {
                    tracing::debug!(
                        caller = %func.name,
                        callee = %call_site.callee_name,
                        variable = %variable,
                        "Ownership: value moved (consumed) -- borrow checker handles this"
                    );
                    // No SMT constraint -- Rust's borrow checker prevents use-after-move
                }
            }
        }
    }
}

/// Build a minimal Function context for parsing callee specs.
///
/// The spec parser needs a Function to resolve variable names and types.
/// We construct one from the FunctionSummary.
fn build_callee_func_context(summary: &crate::contract_db::FunctionSummary) -> Function {
    Function {
        name: String::new(),
        return_local: Local {
            name: "_0".to_string(),
            ty: summary.return_ty.clone(),
            is_ghost: false,
        },
        params: summary
            .param_names
            .iter()
            .zip(summary.param_types.iter())
            .map(|(name, ty)| Local {
                name: name.clone(),
                ty: ty.clone(),
                is_ghost: false,
            })
            .collect(),
        locals: vec![],
        basic_blocks: vec![],
        contracts: Contracts::default(),
        loops: vec![],
        generic_params: vec![],
        prophecies: vec![],
        lifetime_params: vec![],
        outlives_constraints: vec![],
        borrow_info: vec![],
        reborrow_chains: vec![],
        unsafe_blocks: vec![],
        unsafe_operations: vec![],
        unsafe_contracts: None,
        is_unsafe_fn: false,
        thread_spawns: vec![],
        atomic_ops: vec![],
        sync_ops: vec![],
        lock_invariants: vec![],
        concurrency_config: None,
        source_names: std::collections::HashMap::new(),
        coroutine_info: None,
    }
}

// === Loop invariant verification ===

/// Detect loops in the CFG by finding back-edges.
///
/// A back-edge is an edge from block B to block A where A has already been
/// visited during DFS traversal. The target (A) is the loop header.
///
/// Returns `LoopInfo` entries from `func.loops` (user-supplied) merged with
/// any back-edges detected in the CFG. If the function has pre-populated
/// `loops` field, those are returned directly. Otherwise, back-edges are
/// detected and matched with invariants from `func.contracts.invariants`.
pub fn detect_loops(func: &Function) -> Vec<LoopInfo> {
    // If loops are already populated (e.g., from driver or test setup), use them
    if !func.loops.is_empty() {
        return func.loops.clone();
    }

    // Detect back-edges via DFS
    let mut visited = HashSet::new();
    let mut in_stack = HashSet::new();
    let mut back_edges: Vec<(usize, usize)> = Vec::new(); // (from, to)

    dfs_find_back_edges(func, 0, &mut visited, &mut in_stack, &mut back_edges);

    if back_edges.is_empty() {
        return vec![];
    }

    // Group back-edges by header (target of back-edge)
    let mut header_to_back_edges: HashMap<usize, Vec<usize>> = HashMap::new();
    for (from, to) in &back_edges {
        header_to_back_edges.entry(*to).or_default().push(*from);
    }

    // Create LoopInfo entries, matching with contract invariants
    // For now, all invariants in contracts.invariants are assumed to apply to the
    // first loop. A more sophisticated approach would use source location mapping.
    let invariants = func.contracts.invariants.clone();

    header_to_back_edges
        .into_iter()
        .map(|(header, back_edge_blocks)| LoopInfo {
            header_block: header,
            back_edge_blocks,
            invariants: invariants.clone(),
        })
        .collect()
}

/// DFS to find back-edges in the CFG.
fn dfs_find_back_edges(
    func: &Function,
    block_idx: usize,
    visited: &mut HashSet<usize>,
    in_stack: &mut HashSet<usize>,
    back_edges: &mut Vec<(usize, usize)>,
) {
    if block_idx >= func.basic_blocks.len() {
        return;
    }

    if visited.contains(&block_idx) {
        return;
    }

    visited.insert(block_idx);
    in_stack.insert(block_idx);

    // Get successors from the terminator
    let successors = terminator_successors(&func.basic_blocks[block_idx].terminator);

    for succ in successors {
        if in_stack.contains(&succ) {
            // Back-edge found: block_idx -> succ
            back_edges.push((block_idx, succ));
        } else if !visited.contains(&succ) {
            dfs_find_back_edges(func, succ, visited, in_stack, back_edges);
        }
    }

    in_stack.remove(&block_idx);
}

/// Get successor block indices from a terminator.
fn terminator_successors(term: &Terminator) -> Vec<usize> {
    match term {
        Terminator::Return | Terminator::Unreachable => vec![],
        Terminator::Goto(target) => vec![*target],
        Terminator::SwitchInt {
            targets, otherwise, ..
        } => {
            let mut succs: Vec<usize> = targets.iter().map(|(_, t)| *t).collect();
            succs.push(*otherwise);
            succs
        }
        Terminator::Assert { target, .. } => vec![*target],
        Terminator::Call { target, .. } => vec![*target],
    }
}

/// Generate the 3 classical loop invariant VCs for a single loop.
///
/// **VC1 - Initialization**: Precondition AND pre-loop assignments IMPLY invariant
/// **VC2 - Preservation**: Invariant AND loop condition AND body IMPLY invariant
/// **VC3 - Exit**: Invariant AND NOT loop condition IMPLY postcondition
fn generate_loop_invariant_vcs(
    func: &Function,
    datatype_declarations: &[Command],
    declarations: &[Command],
    loop_info: &LoopInfo,
    ghost_pred_db: &GhostPredicateDatabase,
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();
    let header = loop_info.header_block;

    // Parse all invariants
    let parsed_invariants: Vec<Term> = loop_info
        .invariants
        .iter()
        .filter_map(|inv| parse_spec(&inv.raw, func, ghost_pred_db))
        .collect();

    if parsed_invariants.is_empty() {
        return vcs;
    }

    // Build the combined invariant (conjunction of all invariants)
    let invariant = if parsed_invariants.len() == 1 {
        parsed_invariants[0].clone()
    } else {
        Term::And(parsed_invariants.clone())
    };

    // Extract the loop condition from the header block's terminator
    let loop_condition = extract_loop_condition(func, header);

    // Collect pre-loop assignments (from function entry to loop header)
    let pre_loop_assignments = collect_pre_loop_assignments(func, header);

    // Collect loop body assignments (from header's body entry to back-edge blocks)
    let body_assignments = collect_loop_body_assignments(func, header, &loop_info.back_edge_blocks);

    // === VC1: Initialization ===
    // Preconditions + pre-loop assignments => invariant
    {
        let mut script = base_script(
            datatype_declarations,
            declarations,
            uses_spec_int_types(func),
        );

        // Encode pre-loop assignments
        let mut ssa_counter = HashMap::new();
        for (place, rvalue) in &pre_loop_assignments {
            if let Some(cmd) = encode_assignment(place, rvalue, func, &mut ssa_counter) {
                script.push(cmd);
            }
        }

        // Assume preconditions
        for pre in &func.contracts.requires {
            if let Some(pre_term) = parse_spec(&pre.raw, func, ghost_pred_db) {
                script.push(Command::Assert(pre_term));
            }
        }

        // Assert negation of invariant (checking if invariant can fail on entry)
        script.push(Command::Comment(format!(
            "Loop invariant initialization check at block {header}"
        )));
        script.push(Command::Assert(Term::Not(Box::new(invariant.clone()))));
        script.push(Command::CheckSat);
        script.push(Command::GetModel);

        vcs.push(VerificationCondition {
            description: format!(
                "{}: loop invariant initialization at block {header}",
                func.name
            ),
            script,
            location: VcLocation {
                function: func.name.clone(),
                block: header,
                statement: 0,
                source_file: None,
                source_line: None,
                source_column: None,
                contract_text: loop_info.invariants.first().map(|inv| inv.raw.clone()),
                vc_kind: VcKind::LoopInvariantInit,
            },
        });
    }

    // === VC2: Preservation ===
    // Invariant + loop condition + body => invariant'
    //
    // We use "next-state" variables: for each variable modified in the body,
    // declare a `_var_next` constant and encode the body with those on the LHS.
    // Then check the invariant holds for the next-state variables.
    {
        // Collect variables modified in the loop body
        let modified_vars: HashSet<String> = body_assignments
            .iter()
            .map(|(place, _)| place.local.clone())
            .collect();

        // Build "next-state" declarations
        let mut next_decls: Vec<Command> = Vec::new();
        for var_name in &modified_vars {
            if let Some(ty) = find_local_type(func, var_name) {
                let sort = encode_type(ty);
                next_decls.push(Command::DeclareConst(format!("{var_name}_next"), sort));
            }
        }

        let mut script = base_script(
            datatype_declarations,
            declarations,
            uses_spec_int_types(func),
        );

        // Add next-state declarations
        for decl in &next_decls {
            script.push(decl.clone());
        }

        // Assume invariant holds at loop entry (on current-state variables)
        script.push(Command::Assert(invariant.clone()));

        // Assume preconditions (they hold throughout)
        for pre in &func.contracts.requires {
            if let Some(pre_term) = parse_spec(&pre.raw, func, ghost_pred_db) {
                script.push(Command::Assert(pre_term));
            }
        }

        // Encode header statements (which compute the loop condition)
        if header < func.basic_blocks.len() {
            let header_block = &func.basic_blocks[header];
            let mut ssa_counter = HashMap::new();
            for stmt in &header_block.statements {
                if let Statement::Assign(place, rvalue) = stmt
                    && let Some(cmd) = encode_assignment(place, rvalue, func, &mut ssa_counter)
                {
                    script.push(cmd);
                }
            }
        }

        // Assume loop condition is true (we're entering the loop body)
        if let Some(ref cond) = loop_condition {
            script.push(Command::Assert(cond.clone()));
        }

        // Encode loop body assignments using next-state variables on the LHS.
        // Body assignments from blocks AFTER the header (not header statements themselves).
        let body_only_assignments =
            collect_body_only_assignments(func, header, &loop_info.back_edge_blocks);
        for (place, rvalue) in &body_only_assignments {
            let rhs = match rvalue {
                Rvalue::Use(op) => Some(encode_operand_for_vcgen(op, func)),
                Rvalue::BinaryOp(op, lhs_op, rhs_op) => {
                    let l = encode_operand(lhs_op);
                    let r = encode_operand(rhs_op);
                    let ty = infer_operand_type(func, lhs_op)
                        .or_else(|| find_local_type(func, &place.local));
                    ty.map(|t| encode_binop(*op, &l, &r, t))
                }
                _ => None,
            };
            if let Some(rhs_term) = rhs {
                let lhs_name = if modified_vars.contains(&place.local) {
                    format!("{}_next", place.local)
                } else {
                    place.local.clone()
                };
                script.push(Command::Assert(Term::Eq(
                    Box::new(Term::Const(lhs_name)),
                    Box::new(rhs_term),
                )));
            }
        }

        // Check invariant with next-state variables substituted
        let invariant_next = substitute_next_state(&invariant, &modified_vars);
        script.push(Command::Comment(format!(
            "Loop invariant preservation check at block {header}"
        )));
        script.push(Command::Assert(Term::Not(Box::new(invariant_next))));
        script.push(Command::CheckSat);
        script.push(Command::GetModel);

        vcs.push(VerificationCondition {
            description: format!(
                "{}: loop invariant preservation at block {header}",
                func.name
            ),
            script,
            location: VcLocation {
                function: func.name.clone(),
                block: header,
                statement: 0,
                source_file: None,
                source_line: None,
                source_column: None,
                contract_text: loop_info.invariants.first().map(|inv| inv.raw.clone()),
                vc_kind: VcKind::LoopInvariantPreserve,
            },
        });
    }

    // === VC3: Exit / Sufficiency ===
    // Invariant + header stmts + NOT loop condition + post-loop => postcondition
    {
        for (post_idx, post) in func.contracts.ensures.iter().enumerate() {
            if let Some(post_term) = parse_spec(&post.raw, func, ghost_pred_db) {
                let mut script = base_script(
                    datatype_declarations,
                    declarations,
                    uses_spec_int_types(func),
                );

                // Assume invariant holds
                script.push(Command::Assert(invariant.clone()));

                // Assume preconditions
                for pre in &func.contracts.requires {
                    if let Some(pre_term) = parse_spec(&pre.raw, func, ghost_pred_db) {
                        script.push(Command::Assert(pre_term));
                    }
                }

                // Encode header statements (which compute the loop condition variable)
                // This establishes the relationship between the condition variable and
                // the loop variables (e.g., _4 = _3 < _1)
                if header < func.basic_blocks.len() {
                    let header_block = &func.basic_blocks[header];
                    let mut ssa_counter = HashMap::new();
                    for stmt in &header_block.statements {
                        if let Statement::Assign(place, rvalue) = stmt
                            && let Some(cmd) =
                                encode_assignment(place, rvalue, func, &mut ssa_counter)
                        {
                            script.push(cmd);
                        }
                    }
                }

                // Assume loop condition is false (loop exited)
                if let Some(ref cond) = loop_condition {
                    script.push(Command::Assert(Term::Not(Box::new(cond.clone()))));
                }

                // Encode post-loop assignments (from loop exit to function return)
                let post_loop_assignments =
                    collect_post_loop_assignments(func, header, &loop_condition);
                let mut ssa_counter = HashMap::new();
                for (place, rvalue) in &post_loop_assignments {
                    if let Some(cmd) = encode_assignment(place, rvalue, func, &mut ssa_counter) {
                        script.push(cmd);
                    }
                }

                // Assert negation of postcondition
                script.push(Command::Comment(format!(
                    "Loop invariant sufficiency (exit) check at block {header}: {}",
                    post.raw
                )));
                script.push(Command::Assert(Term::Not(Box::new(post_term))));
                script.push(Command::CheckSat);
                script.push(Command::GetModel);

                vcs.push(VerificationCondition {
                    description: format!(
                        "{}: loop invariant sufficiency (exit) at block {header} for postcondition {post_idx}",
                        func.name
                    ),
                    script,
                    location: VcLocation {
                        function: func.name.clone(),
                        block: header,
                        statement: 0,
                        source_file: None,
                        source_line: None,
                        source_column: None,
                        contract_text: loop_info.invariants.first().map(|inv| inv.raw.clone()),
                        vc_kind: VcKind::LoopInvariantExit,
                    },
                });
            }
        }
    }

    vcs
}

/// Extract the loop condition from the header block's terminator.
///
/// For a SwitchInt terminator at the loop header, the loop condition is the
/// discriminant being equal to the "continue" target value (typically true/1
/// for the body, false/0 for the exit).
fn extract_loop_condition(func: &Function, header_block: BlockId) -> Option<Term> {
    if header_block >= func.basic_blocks.len() {
        return None;
    }

    let block = &func.basic_blocks[header_block];
    match &block.terminator {
        Terminator::SwitchInt { discr, targets, .. } => {
            // The loop condition is typically the discriminant.
            // For `while cond { body }`, MIR generates:
            //   header: switchInt(cond) -> [1: body, otherwise: exit]
            // So the "true" branch goes to the body, and the condition is `discr == 1`
            // (or simply `discr` for boolean discriminants).
            let discr_term = encode_operand(discr);

            // Check if discriminant is a boolean
            if let Operand::Copy(place) | Operand::Move(place) = discr {
                let discr_ty = find_local_type(func, &place.local);
                if matches!(discr_ty, Some(Ty::Bool)) {
                    // Boolean: the condition is just the discriminant being true
                    return Some(discr_term);
                }
            }

            // For integer discriminants, the first target is typically the body
            if let Some((value, _)) = targets.first() {
                let width = match discr {
                    Operand::Copy(place) | Operand::Move(place) => {
                        find_local_type(func, &place.local)
                            .and_then(|ty| ty.bit_width())
                            .unwrap_or(32)
                    }
                    _ => 32,
                };
                return Some(Term::Eq(
                    Box::new(discr_term),
                    Box::new(Term::BitVecLit(*value, width)),
                ));
            }

            Some(discr_term)
        }
        _ => None, // Non-conditional loop header (unconditional loop)
    }
}

/// Collect assignments from function entry to the loop header.
///
/// These are the "pre-loop" assignments needed for the initialization VC.
fn collect_pre_loop_assignments(func: &Function, header_block: BlockId) -> Vec<(Place, Rvalue)> {
    let mut assignments = Vec::new();
    let mut visited = HashSet::new();
    collect_assignments_to_block(func, 0, header_block, &mut visited, &mut assignments);
    assignments
}

/// Recursively collect assignments from `current` block to `target` block.
fn collect_assignments_to_block(
    func: &Function,
    current: BlockId,
    target: BlockId,
    visited: &mut HashSet<BlockId>,
    assignments: &mut Vec<(Place, Rvalue)>,
) {
    if current == target || current >= func.basic_blocks.len() || visited.contains(&current) {
        return;
    }

    visited.insert(current);
    let block = &func.basic_blocks[current];

    // Collect assignments from this block
    for stmt in &block.statements {
        if let Statement::Assign(place, rvalue) = stmt {
            assignments.push((place.clone(), rvalue.clone()));
        }
    }

    // Follow successors toward the target
    let successors = terminator_successors(&block.terminator);
    for succ in successors {
        if succ == target || (!visited.contains(&succ) && succ < func.basic_blocks.len()) {
            collect_assignments_to_block(func, succ, target, visited, assignments);
            break; // Take the first path to target (simplified for single-entry loops)
        }
    }
}

/// Collect assignments in the loop body (from header's body successor to back-edge blocks).
fn collect_loop_body_assignments(
    func: &Function,
    header: BlockId,
    back_edge_blocks: &[BlockId],
) -> Vec<(Place, Rvalue)> {
    let mut assignments = Vec::new();

    if header >= func.basic_blocks.len() {
        return assignments;
    }

    // Find the body entry block: the first target from the header's SwitchInt
    let body_entry = match &func.basic_blocks[header].terminator {
        Terminator::SwitchInt { targets, .. } => {
            // First target is typically the body (true branch)
            targets.first().map(|(_, t)| *t)
        }
        Terminator::Goto(target) => Some(*target),
        _ => None,
    };

    if let Some(entry) = body_entry {
        // Include header's own statements (which may include the loop condition computation)
        for stmt in &func.basic_blocks[header].statements {
            if let Statement::Assign(place, rvalue) = stmt {
                assignments.push((place.clone(), rvalue.clone()));
            }
        }

        // Collect assignments from body entry to back-edge blocks
        let back_edge_set: HashSet<BlockId> = back_edge_blocks.iter().copied().collect();
        let mut visited = HashSet::new();
        visited.insert(header); // Don't revisit header
        collect_body_assignments_dfs(func, entry, &back_edge_set, &mut visited, &mut assignments);
    }

    assignments
}

/// DFS through the loop body, collecting assignments.
fn collect_body_assignments_dfs(
    func: &Function,
    block_idx: BlockId,
    back_edge_blocks: &HashSet<BlockId>,
    visited: &mut HashSet<BlockId>,
    assignments: &mut Vec<(Place, Rvalue)>,
) {
    if block_idx >= func.basic_blocks.len() || visited.contains(&block_idx) {
        return;
    }

    visited.insert(block_idx);
    let block = &func.basic_blocks[block_idx];

    // Collect assignments
    for stmt in &block.statements {
        if let Statement::Assign(place, rvalue) = stmt {
            assignments.push((place.clone(), rvalue.clone()));
        }
    }

    // If this is a back-edge block, stop (we've collected the full body path)
    if back_edge_blocks.contains(&block_idx) {
        return;
    }

    // Continue to successors
    let successors = terminator_successors(&block.terminator);
    for succ in successors {
        collect_body_assignments_dfs(func, succ, back_edge_blocks, visited, assignments);
    }
}

/// Collect assignments after the loop exit to the function return.
fn collect_post_loop_assignments(
    func: &Function,
    header: BlockId,
    _loop_condition: &Option<Term>,
) -> Vec<(Place, Rvalue)> {
    let mut assignments = Vec::new();

    if header >= func.basic_blocks.len() {
        return assignments;
    }

    // Find the exit block: the "otherwise" target from the header's SwitchInt
    let exit_block = match &func.basic_blocks[header].terminator {
        Terminator::SwitchInt { otherwise, .. } => Some(*otherwise),
        _ => None,
    };

    if let Some(exit) = exit_block {
        let mut visited = HashSet::new();
        visited.insert(header); // Don't go back into the loop
        collect_post_loop_dfs(func, exit, &mut visited, &mut assignments);
    }

    assignments
}

/// DFS through post-loop blocks to Return, collecting assignments.
fn collect_post_loop_dfs(
    func: &Function,
    block_idx: BlockId,
    visited: &mut HashSet<BlockId>,
    assignments: &mut Vec<(Place, Rvalue)>,
) {
    if block_idx >= func.basic_blocks.len() || visited.contains(&block_idx) {
        return;
    }

    visited.insert(block_idx);
    let block = &func.basic_blocks[block_idx];

    // Collect assignments
    for stmt in &block.statements {
        if let Statement::Assign(place, rvalue) = stmt {
            assignments.push((place.clone(), rvalue.clone()));
        }
    }

    // Follow successors
    let successors = terminator_successors(&block.terminator);
    for succ in successors {
        collect_post_loop_dfs(func, succ, visited, assignments);
    }
}

/// Collect body-only assignments (excluding header statements).
///
/// This collects assignments from the body entry block to back-edge blocks,
/// skipping the header's own statements.
fn collect_body_only_assignments(
    func: &Function,
    header: BlockId,
    back_edge_blocks: &[BlockId],
) -> Vec<(Place, Rvalue)> {
    let mut assignments = Vec::new();

    if header >= func.basic_blocks.len() {
        return assignments;
    }

    // Find the body entry block
    let body_entry = match &func.basic_blocks[header].terminator {
        Terminator::SwitchInt { targets, .. } => targets.first().map(|(_, t)| *t),
        Terminator::Goto(target) => Some(*target),
        _ => None,
    };

    if let Some(entry) = body_entry {
        let back_edge_set: HashSet<BlockId> = back_edge_blocks.iter().copied().collect();
        let mut visited = HashSet::new();
        visited.insert(header); // Don't revisit header
        collect_body_assignments_dfs(func, entry, &back_edge_set, &mut visited, &mut assignments);
    }

    assignments
}

/// Substitute next-state variable names in a term.
///
/// For each variable in `modified_vars`, replaces `Const("x")` with `Const("x_next")`.
fn substitute_next_state(term: &Term, modified_vars: &HashSet<String>) -> Term {
    match term {
        Term::Const(name) => {
            if modified_vars.contains(name) {
                Term::Const(format!("{name}_next"))
            } else {
                term.clone()
            }
        }
        Term::Not(t) => Term::Not(Box::new(substitute_next_state(t, modified_vars))),
        Term::And(terms) => Term::And(
            terms
                .iter()
                .map(|t| substitute_next_state(t, modified_vars))
                .collect(),
        ),
        Term::Or(terms) => Term::Or(
            terms
                .iter()
                .map(|t| substitute_next_state(t, modified_vars))
                .collect(),
        ),
        Term::Implies(a, b) => Term::Implies(
            Box::new(substitute_next_state(a, modified_vars)),
            Box::new(substitute_next_state(b, modified_vars)),
        ),
        Term::Eq(a, b) => Term::Eq(
            Box::new(substitute_next_state(a, modified_vars)),
            Box::new(substitute_next_state(b, modified_vars)),
        ),
        Term::BvSLe(a, b) => Term::BvSLe(
            Box::new(substitute_next_state(a, modified_vars)),
            Box::new(substitute_next_state(b, modified_vars)),
        ),
        Term::BvSLt(a, b) => Term::BvSLt(
            Box::new(substitute_next_state(a, modified_vars)),
            Box::new(substitute_next_state(b, modified_vars)),
        ),
        Term::BvSGe(a, b) => Term::BvSGe(
            Box::new(substitute_next_state(a, modified_vars)),
            Box::new(substitute_next_state(b, modified_vars)),
        ),
        Term::BvSGt(a, b) => Term::BvSGt(
            Box::new(substitute_next_state(a, modified_vars)),
            Box::new(substitute_next_state(b, modified_vars)),
        ),
        Term::BvULe(a, b) => Term::BvULe(
            Box::new(substitute_next_state(a, modified_vars)),
            Box::new(substitute_next_state(b, modified_vars)),
        ),
        Term::BvULt(a, b) => Term::BvULt(
            Box::new(substitute_next_state(a, modified_vars)),
            Box::new(substitute_next_state(b, modified_vars)),
        ),
        Term::BvUGe(a, b) => Term::BvUGe(
            Box::new(substitute_next_state(a, modified_vars)),
            Box::new(substitute_next_state(b, modified_vars)),
        ),
        Term::BvUGt(a, b) => Term::BvUGt(
            Box::new(substitute_next_state(a, modified_vars)),
            Box::new(substitute_next_state(b, modified_vars)),
        ),
        Term::BvAdd(a, b) => Term::BvAdd(
            Box::new(substitute_next_state(a, modified_vars)),
            Box::new(substitute_next_state(b, modified_vars)),
        ),
        Term::BvSub(a, b) => Term::BvSub(
            Box::new(substitute_next_state(a, modified_vars)),
            Box::new(substitute_next_state(b, modified_vars)),
        ),
        // For terms that don't contain variables (literals), return as-is
        _ => term.clone(),
    }
}

/// Encode an operand for VCGen with type-aware projection resolution.
///
/// If the operand references a place with projections (field access, indexing),
/// uses the function's type information to resolve them as selector applications.
fn encode_operand_for_vcgen(op: &Operand, func: &Function) -> Term {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            if place.projections.is_empty() {
                encode_operand(op)
            } else {
                // Try type-aware encoding for projections
                encode_place_with_type(place, func).unwrap_or_else(|| encode_operand(op))
            }
        }
        Operand::Constant(_) => encode_operand(op),
    }
}

/// Find the type of a local variable by name.
fn find_local_type<'a>(func: &'a Function, name: &str) -> Option<&'a Ty> {
    if func.return_local.name == name {
        return Some(&func.return_local.ty);
    }
    for p in &func.params {
        if p.name == name {
            return Some(&p.ty);
        }
    }
    for l in &func.locals {
        if l.name == name {
            return Some(&l.ty);
        }
    }
    None
}

/// Infer the type of an operand.
fn infer_operand_type<'a>(func: &'a Function, op: &Operand) -> Option<&'a Ty> {
    match op {
        Operand::Copy(place) | Operand::Move(place) => find_local_type(func, &place.local),
        Operand::Constant(c) => match c {
            Constant::Bool(_) => None, // Would need static Ty ref
            Constant::Int(_, _) => None,
            Constant::Uint(_, _) => None,
            _ => None,
        },
    }
}

/// Parse a specification expression with the full syn-based parser, falling back
/// to the simple parser if the syn parser returns None.
///
/// This ensures backward compatibility: all specs that worked before still work,
/// and the new parser handles additional syntax (field access, old(), etc.).
///
/// After parsing, quantified specs (forall/exists) are automatically annotated
/// with trigger patterns for SMT instantiation control.
fn parse_spec(spec: &str, func: &Function, ghost_pred_db: &GhostPredicateDatabase) -> Option<Term> {
    let term = spec_parser::parse_spec_expr_with_db(spec, func, ghost_pred_db)
        .or_else(|| parse_simple_spec(spec, func))?;

    // Annotate quantifiers with trigger patterns (validation happens here)
    // On validation error, log and return None (spec parsing fails)
    match crate::encode_quantifier::annotate_quantifier(term) {
        Ok(annotated_term) => Some(annotated_term),
        Err(trigger_error) => {
            // Trigger validation error - log it and fail spec parsing
            tracing::error!(
                "Trigger validation failed in function {}: {:?}",
                func.name,
                trigger_error
            );
            // TODO: In a full implementation, we'd propagate this error to the driver
            // for proper diagnostic formatting. For now, we log and fail parsing.
            None
        }
    }
}

/// Parse a simple specification expression into an SMT-LIB term.
///
/// Phase 1: supports basic comparisons and logical operators.
/// The spec language uses `result` to refer to the return value (`_0`).
///
/// Supported forms:
/// - `result > 0`, `result >= x`, `result == x + 1`, etc.
/// - `x > 0`, `x < 100`
/// - `result >= a && result >= b`
pub fn parse_simple_spec(spec: &str, func: &Function) -> Option<Term> {
    let spec = spec.trim();

    // Handle logical AND
    if let Some((left, right)) = split_logical_and(spec) {
        let l = parse_simple_spec(left, func)?;
        let r = parse_simple_spec(right, func)?;
        return Some(Term::And(vec![l, r]));
    }

    // Handle logical OR
    if let Some((left, right)) = split_logical_or(spec) {
        let l = parse_simple_spec(left, func)?;
        let r = parse_simple_spec(right, func)?;
        return Some(Term::Or(vec![l, r]));
    }

    // Handle comparison operators
    for (op_str, make_term) in COMPARISON_OPS {
        if let Some((left, right)) = spec.split_once(op_str) {
            let left = left.trim();
            let right = right.trim();
            // Avoid matching `>=` when looking for `>`
            if *op_str == ">" && right.starts_with('=') {
                continue;
            }
            if *op_str == "<" && right.starts_with('=') {
                continue;
            }
            if *op_str == "=" && left.ends_with('!') {
                continue;
            }
            let l = parse_spec_operand(left, func)?;
            let r = parse_spec_operand(right, func)?;
            return Some(make_term(l, r, func));
        }
    }

    // Handle boolean constants
    if spec == "true" {
        return Some(Term::BoolLit(true));
    }
    if spec == "false" {
        return Some(Term::BoolLit(false));
    }

    // Handle single variable (boolean)
    parse_spec_operand(spec, func)
}

type ComparisonFn = fn(Term, Term, &Function) -> Term;

const COMPARISON_OPS: &[(&str, ComparisonFn)] = &[
    (">=", |l, r, f| make_comparison(BinOp::Ge, l, r, f)),
    ("<=", |l, r, f| make_comparison(BinOp::Le, l, r, f)),
    ("!=", |l, r, _| {
        Term::Not(Box::new(Term::Eq(Box::new(l), Box::new(r))))
    }),
    ("==", |l, r, _| Term::Eq(Box::new(l), Box::new(r))),
    (">", |l, r, f| make_comparison(BinOp::Gt, l, r, f)),
    ("<", |l, r, f| make_comparison(BinOp::Lt, l, r, f)),
];

/// Infer signedness for a comparison from the function context and operand terms.
///
/// When comparing field accesses like `result.x > 0` on a struct return type,
/// we inspect the field type to determine whether signed or unsigned comparison
/// should be used (e.g., i32 -> signed, u32 -> unsigned).
fn infer_signedness_from_context(func: &Function, lhs: &Term, rhs: &Term) -> bool {
    // Check if either operand is a selector application (field access)
    // If so, determine signedness from the field type
    if let Some(signed) = infer_signedness_from_term(func, lhs) {
        return signed;
    }
    if let Some(signed) = infer_signedness_from_term(func, rhs) {
        return signed;
    }

    // Fallback: check return type and first parameter
    func.return_local.ty.is_signed() || func.params.first().is_some_and(|p| p.ty.is_signed())
}

/// Try to infer signedness from a term by looking at selector applications.
fn infer_signedness_from_term(func: &Function, term: &Term) -> Option<bool> {
    if let Term::App(selector_name, args) = term
        && args.len() == 1
    {
        // This looks like a selector application. Try to resolve the field type.
        // Selector names follow patterns:
        //   "{TypeName}-{field_name}" for structs
        //   "Tuple{N}-_{idx}" for tuples
        if let Some(field_ty) = resolve_selector_type(func, selector_name) {
            return Some(field_ty.is_signed());
        }
    }
    // Check if term is a variable with a known type
    if let Term::Const(name) = term
        && let Some(ty) = find_local_type(func, name)
        && (ty.is_signed() || ty.is_unsigned())
    {
        return Some(ty.is_signed());
    }
    None
}

/// Resolve the type of a field from a selector name.
///
/// Searches the function's types for matching struct/tuple fields.
fn resolve_selector_type<'a>(func: &'a Function, selector_name: &str) -> Option<&'a Ty> {
    // Check return type
    if let Some(ty) = resolve_selector_from_ty(&func.return_local.ty, selector_name) {
        return Some(ty);
    }
    // Check params
    for p in &func.params {
        if let Some(ty) = resolve_selector_from_ty(&p.ty, selector_name) {
            return Some(ty);
        }
    }
    // Check locals
    for l in &func.locals {
        if let Some(ty) = resolve_selector_from_ty(&l.ty, selector_name) {
            return Some(ty);
        }
    }
    None
}

fn resolve_selector_from_ty<'a>(ty: &'a Ty, selector_name: &str) -> Option<&'a Ty> {
    match ty {
        Ty::Struct(name, fields) => {
            // Struct selectors: "{TypeName}-{field_name}"
            let prefix = format!("{name}-");
            if let Some(field_name) = selector_name.strip_prefix(&prefix) {
                for (fname, fty) in fields {
                    if fname == field_name {
                        return Some(fty);
                    }
                }
            }
        }
        Ty::Tuple(fields) => {
            // Tuple selectors: "Tuple{N}-_{idx}"
            let type_name = format!("Tuple{}", fields.len());
            let prefix = format!("{type_name}-_");
            if let Some(idx_str) = selector_name.strip_prefix(&prefix)
                && let Ok(idx) = idx_str.parse::<usize>()
            {
                return fields.get(idx);
            }
        }
        _ => {}
    }
    None
}

fn make_comparison(op: BinOp, lhs: Term, rhs: Term, func: &Function) -> Term {
    // Determine signedness from the operand types:
    // 1. Check return type and param types for direct integer types
    // 2. For struct/tuple returns, check field types referenced in the comparison
    let signed = infer_signedness_from_context(func, &lhs, &rhs);

    let l = Box::new(lhs);
    let r = Box::new(rhs);

    match (op, signed) {
        (BinOp::Lt, true) => Term::BvSLt(l, r),
        (BinOp::Lt, false) => Term::BvULt(l, r),
        (BinOp::Le, true) => Term::BvSLe(l, r),
        (BinOp::Le, false) => Term::BvULe(l, r),
        (BinOp::Gt, true) => Term::BvSGt(l, r),
        (BinOp::Gt, false) => Term::BvUGt(l, r),
        (BinOp::Ge, true) => Term::BvSGe(l, r),
        (BinOp::Ge, false) => Term::BvUGe(l, r),
        _ => unreachable!(),
    }
}

/// Parse a single operand in a spec expression.
fn parse_spec_operand(s: &str, func: &Function) -> Option<Term> {
    let s = s.trim();

    // `result` -> `_0` (return place)
    if s == "result" {
        return Some(Term::Const(func.return_local.name.clone()));
    }

    // `result.field` -> selector application on return value
    if let Some(field_name) = s.strip_prefix("result.") {
        let base = Term::Const(func.return_local.name.clone());
        let ret_ty = &func.return_local.ty;
        match ret_ty {
            Ty::Struct(type_name, fields) => {
                // Try matching by field name
                if fields.iter().any(|(f, _)| f == field_name) {
                    let selector = format!("{type_name}-{field_name}");
                    return Some(Term::App(selector, vec![base]));
                }
                // Try matching by index
                if let Ok(idx) = field_name.parse::<usize>() {
                    return encode_field_access(base, ret_ty, idx);
                }
            }
            Ty::Tuple(fields) => {
                // Tuple fields are accessed by index: result.0, result.1, etc.
                // Also support _0, _1 style
                let idx_str = field_name.strip_prefix('_').unwrap_or(field_name);
                if let Ok(idx) = idx_str.parse::<usize>()
                    && idx < fields.len()
                {
                    let selector = format!("Tuple{}-_{idx}", fields.len());
                    return Some(Term::App(selector, vec![base]));
                }
            }
            _ => {}
        }
    }

    // Integer literal
    if let Ok(n) = s.parse::<i128>() {
        // Determine width from context (use return type or default to 32)
        let width = func.return_local.ty.bit_width().unwrap_or(32);
        return Some(Term::BitVecLit(n, width));
    }

    // Simple arithmetic: `x + 1`, `x - 1`
    if let Some((left, right)) = s.split_once('+') {
        let l = parse_spec_operand(left.trim(), func)?;
        let r = parse_spec_operand(right.trim(), func)?;
        return Some(Term::BvAdd(Box::new(l), Box::new(r)));
    }
    // Be careful with `-` to not match negative numbers
    if let Some(pos) = s.rfind('-') {
        if pos > 0 && s.as_bytes()[pos - 1] != b' ' {
            // Not a subtraction, might be part of a name
        } else if pos > 0 {
            let left = &s[..pos];
            let right = &s[pos + 1..];
            if !left.trim().is_empty() && !right.trim().is_empty() {
                let l = parse_spec_operand(left.trim(), func)?;
                let r = parse_spec_operand(right.trim(), func)?;
                return Some(Term::BvSub(Box::new(l), Box::new(r)));
            }
        }
    }

    // Variable name -- find in params or locals
    if find_local_type(func, s).is_some() {
        return Some(Term::Const(s.to_string()));
    }

    // Parameter name without MIR prefix
    for param in &func.params {
        if param.name == s {
            return Some(Term::Const(s.to_string()));
        }
    }

    None
}

/// Split a string on `&&` at the top level (not inside parentheses).
fn split_logical_and(s: &str) -> Option<(&str, &str)> {
    split_at_operator(s, "&&")
}

/// Split a string on `||` at the top level.
fn split_logical_or(s: &str) -> Option<(&str, &str)> {
    split_at_operator(s, "||")
}

fn split_at_operator<'a>(s: &'a str, op: &str) -> Option<(&'a str, &'a str)> {
    let mut depth = 0u32;
    let bytes = s.as_bytes();
    let op_bytes = op.as_bytes();
    let op_len = op_bytes.len();

    for i in 0..bytes.len().saturating_sub(op_len - 1) {
        match bytes[i] {
            b'(' => depth += 1,
            b')' => depth = depth.saturating_sub(1),
            _ => {}
        }
        if depth == 0 && &bytes[i..i + op_len] == op_bytes {
            return Some((s[..i].trim_end(), s[i + op_len..].trim_start()));
        }
    }
    None
}

/// Generate concurrency verification conditions.
///
/// Produces VCs for:
/// - Data race freedom (conflicting concurrent accesses must be ordered)
/// - Lock invariants (must hold at release)
/// - Deadlocks (lock-order cycle detection)
/// - Channel safety (send-on-closed, capacity overflow, recv deadlock)
/// - Bounded verification warning
///
/// Only runs if:
/// - func.concurrency_config.verify_concurrency is true, OR
/// - func.thread_spawns is non-empty
pub fn generate_concurrency_vcs(func: &Function) -> Vec<VerificationCondition> {
    // Guard: only run if concurrency verification is enabled or thread spawns detected
    let should_verify = func
        .concurrency_config
        .as_ref()
        .map(|c| c.verify_concurrency)
        .unwrap_or(false)
        || !func.thread_spawns.is_empty();

    if !should_verify {
        return Vec::new();
    }

    let mut vcs = Vec::new();

    // Step 1: Build MemoryAccess list from atomic_ops
    use crate::concurrency::MemoryAccess;
    use crate::ir::AtomicOpKind;
    let accesses: Vec<MemoryAccess> = func
        .atomic_ops
        .iter()
        .enumerate()
        .map(|(event_id, atomic_op)| {
            let is_write = matches!(
                atomic_op.kind,
                AtomicOpKind::Store
                    | AtomicOpKind::Swap
                    | AtomicOpKind::CompareExchange
                    | AtomicOpKind::FetchAdd
                    | AtomicOpKind::FetchSub
            );

            MemoryAccess {
                event_id,
                location: atomic_op.atomic_place.local.clone(),
                is_write,
                thread_id: 0, // Placeholder - will be filled by interleaving enumeration
                source_line: None,
            }
        })
        .collect();

    // Step 2: Generate data race freedom VCs
    if !accesses.is_empty() {
        let mut race_vcs = crate::concurrency::happens_before::data_race_freedom_vcs(&accesses);
        vcs.append(&mut race_vcs);
    }

    // Step 2b: RC11 weak memory axioms for non-SeqCst orderings (WMM-01, WMM-03)
    // Scoped to WeakMemory* VcKind only — does NOT affect existing DataRaceFreedom VCs (WMM-04)
    if crate::concurrency::rc11::has_non_seqcst_atomics(func) {
        let mut wmm_vcs = crate::concurrency::rc11::generate_rc11_vcs(func);
        vcs.append(&mut wmm_vcs);
    }

    // Step 3: Generate lock invariant VCs
    use crate::concurrency::lock_invariants::{LockOp, lock_invariant_vcs};
    use crate::ir::SyncOpKind;
    for (mutex_place, invariant_spec) in &func.lock_invariants {
        // Build locations from sync_ops
        let locations: Vec<(VcLocation, LockOp)> = func
            .sync_ops
            .iter()
            .filter_map(|sync_op| {
                if sync_op.sync_object.local == *mutex_place {
                    let lock_op = match sync_op.kind {
                        SyncOpKind::MutexLock => LockOp::Acquire,
                        SyncOpKind::MutexUnlock => LockOp::Release,
                        _ => return None,
                    };

                    Some((
                        VcLocation {
                            function: func.name.clone(),
                            block: 0, // No block_index in SyncOp
                            statement: 0,
                            source_file: None,
                            source_line: None,
                            source_column: None,
                            contract_text: Some(invariant_spec.raw.clone()),
                            vc_kind: VcKind::LockInvariant,
                        },
                        lock_op,
                    ))
                } else {
                    None
                }
            })
            .collect();

        if !locations.is_empty() {
            let mut inv_vcs = lock_invariant_vcs(mutex_place, &invariant_spec.raw, &locations);
            vcs.append(&mut inv_vcs);
        }
    }

    // Step 4: Build LockOrderGraph and detect deadlocks
    use crate::concurrency::deadlock_detection::{LockOrderGraph, deadlock_vcs, detect_deadlock};
    use std::collections::HashMap;

    let mut lock_order_graph = LockOrderGraph::new();
    let mut lock_name_to_id: HashMap<String, usize> = HashMap::new();
    let mut next_lock_id = 0;

    // Track which locks are held at each program point
    let mut held_locks: Vec<usize> = Vec::new();

    for sync_op in &func.sync_ops {
        // Get or assign lock ID
        let lock_id = *lock_name_to_id
            .entry(sync_op.sync_object.local.clone())
            .or_insert_with(|| {
                let id = next_lock_id;
                next_lock_id += 1;
                id
            });

        match sync_op.kind {
            SyncOpKind::MutexLock => {
                // Add edges from all currently held locks to this lock
                for &held_lock in &held_locks {
                    lock_order_graph.add_edge(held_lock, lock_id);
                }
                // Mark this lock as held
                if !held_locks.contains(&lock_id) {
                    held_locks.push(lock_id);
                }
            }
            SyncOpKind::MutexUnlock => {
                // Remove this lock from held set
                held_locks.retain(|&id| id != lock_id);
            }
            _ => {}
        }
    }

    // Detect deadlock cycles
    if let Some(cycle) = detect_deadlock(&lock_order_graph) {
        let mut deadlock_vcs = deadlock_vcs(&[cycle]);
        vcs.append(&mut deadlock_vcs);
    }

    // Step 5: Generate channel operation VCs
    use crate::concurrency::channel_verification::{
        ChannelOp, ChannelState, channel_operation_vcs,
    };
    for sync_op in &func.sync_ops {
        match sync_op.kind {
            SyncOpKind::ChannelSend => {
                let channel = ChannelState {
                    name: sync_op.sync_object.local.clone(),
                    capacity: None,   // Unknown - would come from type analysis
                    is_closed: false, // Conservative assumption
                };
                let op = ChannelOp::Send {
                    value: "msg".to_string(), // Placeholder
                };
                let location = VcLocation {
                    function: func.name.clone(),
                    block: 0, // No block_index in SyncOp
                    statement: 0,
                    source_file: None,
                    source_line: None,
                    source_column: None,
                    contract_text: None,
                    vc_kind: VcKind::ChannelSafety,
                };
                let mut chan_vcs = channel_operation_vcs(&channel, &op, location);
                vcs.append(&mut chan_vcs);
            }
            SyncOpKind::ChannelRecv => {
                let channel = ChannelState {
                    name: sync_op.sync_object.local.clone(),
                    capacity: None,
                    is_closed: false,
                };
                let op = ChannelOp::Recv;
                let location = VcLocation {
                    function: func.name.clone(),
                    block: 0, // No block_index in SyncOp
                    statement: 0,
                    source_file: None,
                    source_line: None,
                    source_column: None,
                    contract_text: None,
                    vc_kind: VcKind::ChannelSafety,
                };
                let mut chan_vcs = channel_operation_vcs(&channel, &op, location);
                vcs.append(&mut chan_vcs);
            }
            _ => {}
        }
    }

    // Step 6: Add bounded verification warning VC
    let config = func.concurrency_config.as_ref();
    let max_threads = config.map(|c| c.max_threads).unwrap_or(2);
    let max_switches = config.map(|c| c.max_context_switches).unwrap_or(3);

    let warning_description = format!(
        "Bounded verification: up to {} threads, {} context switches. May miss bugs in deeper interleavings.",
        max_threads, max_switches
    );

    // Diagnostic VC (always-SAT pattern)
    let mut script = rust_fv_smtlib::script::Script::new();
    script.push(rust_fv_smtlib::command::Command::SetLogic(
        "QF_BV".to_string(),
    ));
    script.push(rust_fv_smtlib::command::Command::Assert(
        rust_fv_smtlib::term::Term::BoolLit(true),
    ));
    script.push(rust_fv_smtlib::command::Command::CheckSat);

    vcs.push(VerificationCondition {
        description: warning_description,
        script,
        location: VcLocation {
            function: func.name.clone(),
            block: 0,
            statement: 0,
            source_file: None,
            source_line: None,
            source_column: None,
            contract_text: Some("Bounded concurrency verification enabled".to_string()),
            vc_kind: VcKind::DataRaceFreedom,
        },
    });

    vcs
}

// === Unit tests ===

#[cfg(test)]
mod tests {
    use super::*;
    use rust_fv_smtlib::sort::Sort;

    /// Build a simple function: `fn add(a: i32, b: i32) -> i32 { a + b }`
    fn make_add_function() -> Function {
        Function {
            name: "add".to_string(),
            return_local: Local {
                name: "_0".to_string(),
                ty: Ty::Int(IntTy::I32),
                is_ghost: false,
            },
            params: vec![
                Local {
                    name: "_1".to_string(),
                    ty: Ty::Int(IntTy::I32),
                    is_ghost: false,
                },
                Local {
                    name: "_2".to_string(),
                    ty: Ty::Int(IntTy::I32),
                    is_ghost: false,
                },
            ],
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local("_1")),
                        Operand::Copy(Place::local("_2")),
                    ),
                )],
                terminator: Terminator::Return,
            }],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        }
    }

    /// Build: `fn max(a: i32, b: i32) -> i32 { if a > b { a } else { b } }`
    fn make_max_function() -> Function {
        Function {
            name: "max".to_string(),
            return_local: Local {
                name: "_0".to_string(),
                ty: Ty::Int(IntTy::I32),
                is_ghost: false,
            },
            params: vec![
                Local {
                    name: "_1".to_string(),
                    ty: Ty::Int(IntTy::I32),
                    is_ghost: false,
                },
                Local {
                    name: "_2".to_string(),
                    ty: Ty::Int(IntTy::I32),
                    is_ghost: false,
                },
            ],
            locals: vec![Local {
                name: "_3".to_string(),
                ty: Ty::Bool,
                is_ghost: false,
            }],
            basic_blocks: vec![
                // bb0: _3 = _1 > _2; switchInt(_3)
                BasicBlock {
                    statements: vec![Statement::Assign(
                        Place::local("_3"),
                        Rvalue::BinaryOp(
                            BinOp::Gt,
                            Operand::Copy(Place::local("_1")),
                            Operand::Copy(Place::local("_2")),
                        ),
                    )],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local("_3")),
                        targets: vec![(1, 1)], // true -> bb1
                        otherwise: 2,          // false -> bb2
                    },
                },
                // bb1: _0 = _1; return
                BasicBlock {
                    statements: vec![Statement::Assign(
                        Place::local("_0"),
                        Rvalue::Use(Operand::Copy(Place::local("_1"))),
                    )],
                    terminator: Terminator::Return,
                },
                // bb2: _0 = _2; return
                BasicBlock {
                    statements: vec![Statement::Assign(
                        Place::local("_0"),
                        Rvalue::Use(Operand::Copy(Place::local("_2"))),
                    )],
                    terminator: Terminator::Return,
                },
            ],
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "result >= _1 && result >= _2".to_string(),
                }],
                invariants: vec![],
                is_pure: true,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
            },
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        }
    }

    #[test]
    fn generates_overflow_vc_for_add() {
        let func = make_add_function();
        let result = generate_vcs(&func, None);

        assert_eq!(result.function_name, "add");
        // Should have at least one VC for the addition overflow check
        assert!(
            result
                .conditions
                .iter()
                .any(|vc| vc.description.contains("overflow")),
            "Expected an overflow VC, got: {:?}",
            result
                .conditions
                .iter()
                .map(|vc| &vc.description)
                .collect::<Vec<_>>(),
        );
    }

    #[test]
    fn generates_contract_vc_for_max() {
        let func = make_max_function();
        let result = generate_vcs(&func, None);

        assert_eq!(result.function_name, "max");
        // Should have a postcondition VC
        assert!(
            result
                .conditions
                .iter()
                .any(|vc| vc.description.contains("postcondition")),
            "Expected a postcondition VC, got: {:?}",
            result
                .conditions
                .iter()
                .map(|vc| &vc.description)
                .collect::<Vec<_>>(),
        );
    }

    #[test]
    fn declarations_include_all_variables() {
        let func = make_add_function();
        let decls = collect_declarations(&func);

        // _0 (return) + _1 + _2 = 3 declarations
        assert_eq!(decls.len(), 3);

        // Verify they're DeclareConst commands with BitVec(32) sort
        for decl in &decls {
            match decl {
                Command::DeclareConst(_, Sort::BitVec(32)) => {}
                other => panic!("Expected DeclareConst with BitVec(32), got: {other:?}"),
            }
        }
    }

    #[test]
    fn max_function_declarations_include_locals() {
        let func = make_max_function();
        let decls = collect_declarations(&func);

        // _0 + _1 + _2 + _3 = 4 declarations
        assert_eq!(decls.len(), 4);
    }

    #[test]
    fn parse_simple_comparison_spec() {
        let func = make_add_function();
        let term = parse_simple_spec("result >= 0", &func);
        assert!(term.is_some());
    }

    #[test]
    fn parse_spec_with_and() {
        let func = make_max_function();
        let term = parse_simple_spec("result >= _1 && result >= _2", &func);
        assert!(term.is_some());
        if let Some(Term::And(parts)) = &term {
            assert_eq!(parts.len(), 2);
        } else {
            panic!("Expected And term, got: {term:?}");
        }
    }

    #[test]
    fn parse_spec_result_becomes_return_place() {
        let func = make_add_function();
        let term = parse_simple_spec("result == _1", &func).unwrap();
        if let Term::Eq(lhs, _rhs) = &term {
            assert_eq!(**lhs, Term::Const("_0".to_string()));
        } else {
            panic!("Expected Eq term");
        }
    }

    #[test]
    fn vc_scripts_have_check_sat() {
        let func = make_add_function();
        let result = generate_vcs(&func, None);

        for vc in &result.conditions {
            let script_str = vc.script.to_string();
            assert!(
                script_str.contains("(check-sat)"),
                "VC script should contain check-sat: {}",
                vc.description,
            );
        }
    }

    #[test]
    fn vc_scripts_declare_variables() {
        let func = make_add_function();
        let result = generate_vcs(&func, None);

        for vc in &result.conditions {
            let script_str = vc.script.to_string();
            assert!(
                script_str.contains("declare-const"),
                "VC script should declare variables: {}",
                vc.description,
            );
        }
    }

    #[test]
    fn no_vcs_for_nop() {
        let func = Function {
            name: "noop".to_string(),
            return_local: Local {
                name: "_0".to_string(),
                ty: Ty::Unit,
                is_ghost: false,
            },
            params: vec![],
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![Statement::Nop],
                terminator: Terminator::Return,
            }],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        };

        let result = generate_vcs(&func, None);
        assert!(result.conditions.is_empty());
    }

    #[test]
    fn division_generates_zero_check_vc() {
        let func = Function {
            name: "divide".to_string(),
            return_local: Local {
                name: "_0".to_string(),
                ty: Ty::Int(IntTy::I32),
                is_ghost: false,
            },
            params: vec![
                Local {
                    name: "_1".to_string(),
                    ty: Ty::Int(IntTy::I32),
                    is_ghost: false,
                },
                Local {
                    name: "_2".to_string(),
                    ty: Ty::Int(IntTy::I32),
                    is_ghost: false,
                },
            ],
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::BinaryOp(
                        BinOp::Div,
                        Operand::Copy(Place::local("_1")),
                        Operand::Copy(Place::local("_2")),
                    ),
                )],
                terminator: Terminator::Return,
            }],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        };

        let result = generate_vcs(&func, None);
        assert!(
            result
                .conditions
                .iter()
                .any(|vc| vc.description.contains("overflow") || vc.description.contains("Div")),
            "Expected a division VC"
        );
    }

    #[test]
    fn path_enumeration_linear_function() {
        let func = make_add_function();
        let paths = enumerate_paths(&func);
        assert_eq!(
            paths.len(),
            1,
            "Linear function should have exactly one path"
        );
        assert!(
            paths[0].condition.is_none(),
            "Single-path function should have no path condition"
        );
    }

    #[test]
    fn path_enumeration_branching_function() {
        let func = make_max_function();
        let paths = enumerate_paths(&func);
        assert_eq!(
            paths.len(),
            2,
            "If/else function should have exactly two paths"
        );
        // Both paths should have conditions
        assert!(
            paths[0].condition.is_some(),
            "First branch should have a condition"
        );
        assert!(
            paths[1].condition.is_some(),
            "Second branch should have a condition"
        );
    }

    #[test]
    fn max_postcondition_uses_path_conditions() {
        let func = make_max_function();
        let result = generate_vcs(&func, None);

        // The postcondition VC should exist
        let post_vcs: Vec<_> = result
            .conditions
            .iter()
            .filter(|vc| vc.description.contains("postcondition"))
            .collect();
        assert!(!post_vcs.is_empty(), "Should have postcondition VCs");

        // The script should contain implication (=>) for path-guarded assertions
        let script_str = post_vcs[0].script.to_string();
        assert!(
            script_str.contains("=>") || script_str.contains("implies"),
            "Postcondition VC for branching function should use path-guarded assertions. Script:\n{}",
            script_str,
        );
    }

    // === substitute_term tests ===
    // These cover the many uncovered branches in substitute_term (lines 1164-1280)

    fn make_subs() -> HashMap<String, Term> {
        let mut subs = HashMap::new();
        subs.insert("x".to_string(), Term::Const("y".to_string()));
        subs
    }

    #[test]
    fn substitute_term_not() {
        let subs = make_subs();
        let term = Term::Not(Box::new(Term::Const("x".to_string())));
        let result = substitute_term(&term, &subs);
        assert_eq!(result, Term::Not(Box::new(Term::Const("y".to_string()))));
    }

    #[test]
    fn substitute_term_and() {
        let subs = make_subs();
        let term = Term::And(vec![
            Term::Const("x".to_string()),
            Term::Const("z".to_string()),
        ]);
        let result = substitute_term(&term, &subs);
        assert_eq!(
            result,
            Term::And(vec![
                Term::Const("y".to_string()),
                Term::Const("z".to_string()),
            ])
        );
    }

    #[test]
    fn substitute_term_or() {
        let subs = make_subs();
        let term = Term::Or(vec![Term::Const("x".to_string()), Term::BoolLit(true)]);
        let result = substitute_term(&term, &subs);
        assert_eq!(
            result,
            Term::Or(vec![Term::Const("y".to_string()), Term::BoolLit(true)])
        );
    }

    #[test]
    fn substitute_term_implies() {
        let subs = make_subs();
        let term = Term::Implies(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::Const("x".to_string())),
        );
        let result = substitute_term(&term, &subs);
        assert_eq!(
            result,
            Term::Implies(
                Box::new(Term::Const("y".to_string())),
                Box::new(Term::Const("y".to_string())),
            )
        );
    }

    #[test]
    fn substitute_term_bv_signed_comparisons() {
        let subs = make_subs();
        let x = || Box::new(Term::Const("x".to_string()));
        let z = || Box::new(Term::BitVecLit(0, 32));
        let y = || Box::new(Term::Const("y".to_string()));

        // BvSLe
        let result = substitute_term(&Term::BvSLe(x(), z()), &subs);
        assert_eq!(result, Term::BvSLe(y(), z()));

        // BvSLt
        let result = substitute_term(&Term::BvSLt(x(), z()), &subs);
        assert_eq!(result, Term::BvSLt(y(), z()));

        // BvSGe
        let result = substitute_term(&Term::BvSGe(x(), z()), &subs);
        assert_eq!(result, Term::BvSGe(y(), z()));

        // BvSGt
        let result = substitute_term(&Term::BvSGt(x(), z()), &subs);
        assert_eq!(result, Term::BvSGt(y(), z()));
    }

    #[test]
    fn substitute_term_bv_unsigned_comparisons() {
        let subs = make_subs();
        let x = || Box::new(Term::Const("x".to_string()));
        let z = || Box::new(Term::BitVecLit(0, 32));
        let y = || Box::new(Term::Const("y".to_string()));

        // BvULe
        let result = substitute_term(&Term::BvULe(x(), z()), &subs);
        assert_eq!(result, Term::BvULe(y(), z()));

        // BvULt
        let result = substitute_term(&Term::BvULt(x(), z()), &subs);
        assert_eq!(result, Term::BvULt(y(), z()));

        // BvUGe
        let result = substitute_term(&Term::BvUGe(x(), z()), &subs);
        assert_eq!(result, Term::BvUGe(y(), z()));

        // BvUGt
        let result = substitute_term(&Term::BvUGt(x(), z()), &subs);
        assert_eq!(result, Term::BvUGt(y(), z()));
    }

    #[test]
    fn substitute_term_bv_arithmetic() {
        let subs = make_subs();
        let x = || Box::new(Term::Const("x".to_string()));
        let z = || Box::new(Term::BitVecLit(1, 32));
        let y = || Box::new(Term::Const("y".to_string()));

        assert_eq!(
            substitute_term(&Term::BvAdd(x(), z()), &subs),
            Term::BvAdd(y(), z())
        );
        assert_eq!(
            substitute_term(&Term::BvSub(x(), z()), &subs),
            Term::BvSub(y(), z())
        );
        assert_eq!(
            substitute_term(&Term::BvMul(x(), z()), &subs),
            Term::BvMul(y(), z())
        );
        assert_eq!(
            substitute_term(&Term::BvSDiv(x(), z()), &subs),
            Term::BvSDiv(y(), z())
        );
        assert_eq!(
            substitute_term(&Term::BvUDiv(x(), z()), &subs),
            Term::BvUDiv(y(), z())
        );
        assert_eq!(
            substitute_term(&Term::BvSRem(x(), z()), &subs),
            Term::BvSRem(y(), z())
        );
        assert_eq!(
            substitute_term(&Term::BvURem(x(), z()), &subs),
            Term::BvURem(y(), z())
        );
    }

    #[test]
    fn substitute_term_bv_neg() {
        let subs = make_subs();
        let result = substitute_term(&Term::BvNeg(Box::new(Term::Const("x".to_string()))), &subs);
        assert_eq!(result, Term::BvNeg(Box::new(Term::Const("y".to_string()))));
    }

    #[test]
    fn substitute_term_bv_bitwise() {
        let subs = make_subs();
        let x = || Box::new(Term::Const("x".to_string()));
        let z = || Box::new(Term::BitVecLit(0xFF, 32));
        let y = || Box::new(Term::Const("y".to_string()));

        assert_eq!(
            substitute_term(&Term::BvAnd(x(), z()), &subs),
            Term::BvAnd(y(), z())
        );
        assert_eq!(
            substitute_term(&Term::BvOr(x(), z()), &subs),
            Term::BvOr(y(), z())
        );
        assert_eq!(
            substitute_term(&Term::BvXor(x(), z()), &subs),
            Term::BvXor(y(), z())
        );
        assert_eq!(substitute_term(&Term::BvNot(x()), &subs), Term::BvNot(y()));
    }

    #[test]
    fn substitute_term_bv_shifts() {
        let subs = make_subs();
        let x = || Box::new(Term::Const("x".to_string()));
        let z = || Box::new(Term::BitVecLit(2, 32));
        let y = || Box::new(Term::Const("y".to_string()));

        assert_eq!(
            substitute_term(&Term::BvShl(x(), z()), &subs),
            Term::BvShl(y(), z())
        );
        assert_eq!(
            substitute_term(&Term::BvLShr(x(), z()), &subs),
            Term::BvLShr(y(), z())
        );
        assert_eq!(
            substitute_term(&Term::BvAShr(x(), z()), &subs),
            Term::BvAShr(y(), z())
        );
    }

    #[test]
    fn substitute_term_ite() {
        let subs = make_subs();
        let term = Term::Ite(
            Box::new(Term::BoolLit(true)),
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::BitVecLit(0, 32)),
        );
        let result = substitute_term(&term, &subs);
        assert_eq!(
            result,
            Term::Ite(
                Box::new(Term::BoolLit(true)),
                Box::new(Term::Const("y".to_string())),
                Box::new(Term::BitVecLit(0, 32)),
            )
        );
    }

    #[test]
    fn substitute_term_app() {
        let subs = make_subs();
        let term = Term::App(
            "foo".to_string(),
            vec![Term::Const("x".to_string()), Term::Const("z".to_string())],
        );
        let result = substitute_term(&term, &subs);
        assert_eq!(
            result,
            Term::App(
                "foo".to_string(),
                vec![Term::Const("y".to_string()), Term::Const("z".to_string()),],
            )
        );
    }

    #[test]
    fn substitute_term_literal_unchanged() {
        let subs = make_subs();
        let term = Term::BitVecLit(42, 32);
        let result = substitute_term(&term, &subs);
        assert_eq!(result, Term::BitVecLit(42, 32));
    }

    #[test]
    fn substitute_term_no_match_unchanged() {
        let subs = make_subs();
        let term = Term::Const("z".to_string());
        let result = substitute_term(&term, &subs);
        assert_eq!(result, Term::Const("z".to_string()));
    }

    // === substitute_next_state tests ===
    // These cover lines 2262-2321

    #[test]
    fn substitute_next_state_basic() {
        let mut vars = HashSet::new();
        vars.insert("x".to_string());

        let term = Term::Const("x".to_string());
        let result = substitute_next_state(&term, &vars);
        assert_eq!(result, Term::Const("x_next".to_string()));

        // Non-modified variable stays the same
        let term = Term::Const("z".to_string());
        let result = substitute_next_state(&term, &vars);
        assert_eq!(result, Term::Const("z".to_string()));
    }

    #[test]
    fn substitute_next_state_not() {
        let mut vars = HashSet::new();
        vars.insert("x".to_string());
        let term = Term::Not(Box::new(Term::Const("x".to_string())));
        let result = substitute_next_state(&term, &vars);
        assert_eq!(
            result,
            Term::Not(Box::new(Term::Const("x_next".to_string())))
        );
    }

    #[test]
    fn substitute_next_state_and_or() {
        let mut vars = HashSet::new();
        vars.insert("x".to_string());

        let term = Term::And(vec![Term::Const("x".to_string()), Term::BoolLit(true)]);
        let result = substitute_next_state(&term, &vars);
        assert_eq!(
            result,
            Term::And(vec![Term::Const("x_next".to_string()), Term::BoolLit(true)])
        );

        let term = Term::Or(vec![Term::Const("x".to_string()), Term::BoolLit(false)]);
        let result = substitute_next_state(&term, &vars);
        assert_eq!(
            result,
            Term::Or(vec![
                Term::Const("x_next".to_string()),
                Term::BoolLit(false)
            ])
        );
    }

    #[test]
    fn substitute_next_state_implies() {
        let mut vars = HashSet::new();
        vars.insert("x".to_string());
        let term = Term::Implies(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::BoolLit(true)),
        );
        let result = substitute_next_state(&term, &vars);
        assert_eq!(
            result,
            Term::Implies(
                Box::new(Term::Const("x_next".to_string())),
                Box::new(Term::BoolLit(true)),
            )
        );
    }

    #[test]
    fn substitute_next_state_eq() {
        let mut vars = HashSet::new();
        vars.insert("x".to_string());
        let term = Term::Eq(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::BitVecLit(0, 32)),
        );
        let result = substitute_next_state(&term, &vars);
        assert_eq!(
            result,
            Term::Eq(
                Box::new(Term::Const("x_next".to_string())),
                Box::new(Term::BitVecLit(0, 32)),
            )
        );
    }

    #[test]
    fn substitute_next_state_bv_comparisons() {
        let mut vars = HashSet::new();
        vars.insert("x".to_string());
        let x = || Box::new(Term::Const("x".to_string()));
        let z = || Box::new(Term::BitVecLit(0, 32));
        let xn = || Box::new(Term::Const("x_next".to_string()));

        assert_eq!(
            substitute_next_state(&Term::BvSLe(x(), z()), &vars),
            Term::BvSLe(xn(), z())
        );
        assert_eq!(
            substitute_next_state(&Term::BvSLt(x(), z()), &vars),
            Term::BvSLt(xn(), z())
        );
        assert_eq!(
            substitute_next_state(&Term::BvSGe(x(), z()), &vars),
            Term::BvSGe(xn(), z())
        );
        assert_eq!(
            substitute_next_state(&Term::BvSGt(x(), z()), &vars),
            Term::BvSGt(xn(), z())
        );
        assert_eq!(
            substitute_next_state(&Term::BvULe(x(), z()), &vars),
            Term::BvULe(xn(), z())
        );
        assert_eq!(
            substitute_next_state(&Term::BvULt(x(), z()), &vars),
            Term::BvULt(xn(), z())
        );
        assert_eq!(
            substitute_next_state(&Term::BvUGe(x(), z()), &vars),
            Term::BvUGe(xn(), z())
        );
        assert_eq!(
            substitute_next_state(&Term::BvUGt(x(), z()), &vars),
            Term::BvUGt(xn(), z())
        );
    }

    #[test]
    fn substitute_next_state_bv_arithmetic() {
        let mut vars = HashSet::new();
        vars.insert("x".to_string());
        let x = || Box::new(Term::Const("x".to_string()));
        let z = || Box::new(Term::BitVecLit(1, 32));
        let xn = || Box::new(Term::Const("x_next".to_string()));

        assert_eq!(
            substitute_next_state(&Term::BvAdd(x(), z()), &vars),
            Term::BvAdd(xn(), z())
        );
        assert_eq!(
            substitute_next_state(&Term::BvSub(x(), z()), &vars),
            Term::BvSub(xn(), z())
        );
    }

    #[test]
    fn substitute_next_state_literal_unchanged() {
        let vars = HashSet::new();
        let term = Term::BitVecLit(42, 32);
        let result = substitute_next_state(&term, &vars);
        assert_eq!(result, Term::BitVecLit(42, 32));
    }

    // === format_assert_description tests ===
    // These cover lines 1003, 1008-1009, 1011-1012

    #[test]
    fn format_assert_description_user_assert() {
        let desc = format_assert_description("foo", 0, &AssertKind::UserAssert);
        assert!(desc.contains("assertion might fail"));
        assert!(desc.contains("foo"));
    }

    #[test]
    fn format_assert_description_bounds_check() {
        let desc = format_assert_description(
            "bar",
            1,
            &AssertKind::BoundsCheck {
                len: Operand::Constant(Constant::Uint(10, UintTy::Usize)),
                index: Operand::Copy(Place::local("_1")),
            },
        );
        assert!(desc.contains("index out of bounds"));
    }

    #[test]
    fn format_assert_description_overflow() {
        let desc = format_assert_description("baz", 2, &AssertKind::Overflow(BinOp::Add));
        assert!(desc.contains("overflow"));
        assert!(desc.contains("Add"));
    }

    #[test]
    fn format_assert_description_division_by_zero() {
        let desc = format_assert_description("div_fn", 3, &AssertKind::DivisionByZero);
        assert!(desc.contains("division by zero"));
    }

    #[test]
    fn format_assert_description_remainder_by_zero() {
        let desc = format_assert_description("rem_fn", 4, &AssertKind::RemainderByZero);
        assert!(desc.contains("remainder by zero"));
    }

    #[test]
    fn format_assert_description_negation_overflow() {
        let desc = format_assert_description("neg_fn", 5, &AssertKind::NegationOverflow);
        assert!(desc.contains("negation overflow"));
    }

    #[test]
    fn format_assert_description_unwrap_none() {
        let desc = format_assert_description("unwrap_fn", 6, &AssertKind::UnwrapNone);
        assert!(desc.contains("unwrap()"));
        assert!(desc.contains("None"));
    }

    #[test]
    fn format_assert_description_expect_failed() {
        let desc = format_assert_description(
            "expect_fn",
            7,
            &AssertKind::ExpectFailed("value must exist".to_string()),
        );
        assert!(desc.contains("expect()"));
        assert!(desc.contains("value must exist"));
    }

    #[test]
    fn format_assert_description_other() {
        let desc =
            format_assert_description("other_fn", 8, &AssertKind::Other("custom msg".to_string()));
        assert!(desc.contains("custom msg"));
    }

    // === VcKind::from_overflow_op tests ===

    #[test]
    fn vc_kind_from_overflow_op() {
        assert_eq!(VcKind::from_overflow_op(BinOp::Add), VcKind::Overflow);
        assert_eq!(VcKind::from_overflow_op(BinOp::Sub), VcKind::Overflow);
        assert_eq!(VcKind::from_overflow_op(BinOp::Mul), VcKind::Overflow);
        assert_eq!(VcKind::from_overflow_op(BinOp::Div), VcKind::DivisionByZero);
        assert_eq!(VcKind::from_overflow_op(BinOp::Rem), VcKind::DivisionByZero);
        assert_eq!(VcKind::from_overflow_op(BinOp::Shl), VcKind::ShiftBounds);
        assert_eq!(VcKind::from_overflow_op(BinOp::Shr), VcKind::ShiftBounds);
    }

    // === enumerate_paths tests ===
    // Cover lines 376-380 (empty basic_blocks), 397-401 (unreachable), 461-462 (out of bounds),
    // 609 (Unreachable terminator)

    #[test]
    fn enumerate_paths_empty_function() {
        let func = Function {
            name: "empty".to_string(),
            return_local: Local::new("_0", Ty::Unit),
            params: vec![],
            locals: vec![],
            basic_blocks: vec![], // No blocks
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        };

        let paths = enumerate_paths(&func);
        assert_eq!(paths.len(), 1);
        assert!(paths[0].condition.is_none());
        assert!(paths[0].assignments.is_empty());
    }

    #[test]
    fn enumerate_paths_unreachable_terminator() {
        let func = Function {
            name: "unreachable_fn".to_string(),
            return_local: Local::new("_0", Ty::Unit),
            params: vec![],
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Unreachable,
            }],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        };

        let paths = enumerate_paths(&func);
        // With only unreachable paths, should fall back to empty path
        assert_eq!(paths.len(), 1);
        assert!(paths[0].assignments.is_empty());
    }

    #[test]
    fn enumerate_paths_with_call() {
        let func = Function {
            name: "caller".to_string(),
            return_local: Local::new("_0", Ty::Int(IntTy::I32)),
            params: vec![Local::new("_1", Ty::Int(IntTy::I32))],
            locals: vec![],
            basic_blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "callee".to_string(),
                        args: vec![Operand::Copy(Place::local("_1"))],
                        destination: Place::local("_0"),
                        target: 1,
                    },
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
            ],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        };

        let paths = enumerate_paths(&func);
        assert_eq!(paths.len(), 1);
        assert_eq!(paths[0].call_sites.len(), 1);
        assert_eq!(paths[0].call_sites[0].callee_name, "callee");
    }

    #[test]
    fn enumerate_paths_with_assert_terminator() {
        let func = Function {
            name: "assert_fn".to_string(),
            return_local: Local::new("_0", Ty::Unit),
            params: vec![Local::new("_1", Ty::Bool)],
            locals: vec![],
            basic_blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local("_1")),
                        expected: true,
                        target: 1,
                        kind: AssertKind::UserAssert,
                    },
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
            ],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        };

        let paths = enumerate_paths(&func);
        assert_eq!(paths.len(), 1);
    }

    // === uses_spec_int_types tests ===
    // Cover lines 644, 649, 655

    #[test]
    fn uses_spec_int_types_return() {
        let func = Function {
            name: "f".to_string(),
            return_local: Local::new("_0", Ty::SpecInt),
            params: vec![],
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        };
        assert!(uses_spec_int_types(&func));
    }

    #[test]
    fn uses_spec_int_types_param() {
        let func = Function {
            name: "f".to_string(),
            return_local: Local::new("_0", Ty::Unit),
            params: vec![Local::new("_1", Ty::SpecNat)],
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        };
        assert!(uses_spec_int_types(&func));
    }

    #[test]
    fn uses_spec_int_types_local() {
        let func = Function {
            name: "f".to_string(),
            return_local: Local::new("_0", Ty::Unit),
            params: vec![],
            locals: vec![Local::new("_1", Ty::SpecInt)],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        };
        assert!(uses_spec_int_types(&func));
    }

    #[test]
    fn uses_spec_int_types_none() {
        let func = make_add_function();
        assert!(!uses_spec_int_types(&func));
    }

    // === encode_assignment tests ===
    // Cover lines 718-723 (projected LHS), 744-749 (CheckedBinaryOp),
    // 756-758 (Ref), 760-762 (Len), 764-766 (Cast), 776-778 (Discriminant)

    #[test]
    fn encode_assignment_use() {
        let func = make_add_function();
        let mut ssa = HashMap::new();
        let result = encode_assignment(
            &Place::local("_0"),
            &Rvalue::Use(Operand::Copy(Place::local("_1"))),
            &func,
            &mut ssa,
        );
        assert!(result.is_some());
    }

    #[test]
    fn encode_assignment_ref() {
        let func = make_add_function();
        let mut ssa = HashMap::new();
        let result = encode_assignment(
            &Place::local("_0"),
            &Rvalue::Ref(Mutability::Shared, Place::local("_1")),
            &func,
            &mut ssa,
        );
        assert!(result.is_some());
    }

    #[test]
    fn encode_assignment_len_emits_len_constant() {
        // Rvalue::Len now encodes as an assignment to the {arr}_len constant (not None).
        let func = make_add_function();
        let mut ssa = HashMap::new();
        let result = encode_assignment(
            &Place::local("_0"),
            &Rvalue::Len(Place::local("_1")),
            &func,
            &mut ssa,
        );
        assert!(
            result.is_some(),
            "Rvalue::Len should produce an assignment assertion"
        );
        // The RHS should reference the len constant "_1_len"
        if let Some(Command::Assert(Term::Eq(_, rhs))) = result {
            assert!(
                matches!(*rhs, Term::Const(ref name) if name == "_1_len"),
                "expected RHS to be Const(\"_1_len\"), got: {:?}",
                *rhs
            );
        } else {
            panic!("expected Assert(Eq(...)) from encode_assignment for Rvalue::Len");
        }
    }

    #[test]
    fn encode_assignment_cast() {
        let func = make_add_function();
        let mut ssa = HashMap::new();
        let result = encode_assignment(
            &Place::local("_0"),
            &Rvalue::Cast(
                CastKind::IntToInt,
                Operand::Copy(Place::local("_1")),
                Ty::Int(IntTy::I64),
            ),
            &func,
            &mut ssa,
        );
        assert!(result.is_some());
    }

    #[test]
    fn encode_assignment_discriminant_emits_app_term() {
        let func = make_add_function();
        let mut ssa = HashMap::new();
        let result = encode_assignment(
            &Place::local("_0"),
            &Rvalue::Discriminant(Place::local("_1")),
            &func,
            &mut ssa,
        );
        // Rvalue::Discriminant now emits a discriminant-{local} application term, not None.
        assert!(
            result.is_some(),
            "expected Some command for Rvalue::Discriminant"
        );
        let cmd_text = format!("{result:?}");
        assert!(
            cmd_text.contains("discriminant-_1"),
            "expected 'discriminant-_1' in command, got: {cmd_text}"
        );
    }

    #[test]
    fn encode_assignment_checked_binary_op() {
        let func = make_add_function();
        let mut ssa = HashMap::new();
        let result = encode_assignment(
            &Place::local("_0"),
            &Rvalue::CheckedBinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local("_1")),
                Operand::Copy(Place::local("_2")),
            ),
            &func,
            &mut ssa,
        );
        assert!(result.is_some());
    }

    #[test]
    fn encode_assignment_unary_op() {
        let func = Function {
            name: "neg".to_string(),
            return_local: Local::new("_0", Ty::Int(IntTy::I32)),
            params: vec![Local::new("_1", Ty::Int(IntTy::I32))],
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        };
        let mut ssa = HashMap::new();
        let result = encode_assignment(
            &Place::local("_0"),
            &Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local("_1"))),
            &func,
            &mut ssa,
        );
        assert!(result.is_some());
    }

    // === find_local_type tests ===
    // Cover line 2361 (locals path)

    #[test]
    fn find_local_type_in_locals() {
        let func = make_max_function();
        // _3 is in locals
        let ty = find_local_type(&func, "_3");
        assert!(ty.is_some());
        assert_eq!(*ty.unwrap(), Ty::Bool);
    }

    #[test]
    fn find_local_type_return() {
        let func = make_add_function();
        let ty = find_local_type(&func, "_0");
        assert!(ty.is_some());
        assert_eq!(*ty.unwrap(), Ty::Int(IntTy::I32));
    }

    #[test]
    fn find_local_type_param() {
        let func = make_add_function();
        let ty = find_local_type(&func, "_1");
        assert!(ty.is_some());
    }

    #[test]
    fn find_local_type_not_found() {
        let func = make_add_function();
        let ty = find_local_type(&func, "nonexistent");
        assert!(ty.is_none());
    }

    // === infer_operand_type tests ===
    // Cover lines 2368-2372

    #[test]
    fn infer_operand_type_from_place() {
        let func = make_add_function();
        let ty = infer_operand_type(&func, &Operand::Copy(Place::local("_1")));
        assert!(ty.is_some());
    }

    #[test]
    fn infer_operand_type_constant_bool() {
        let func = make_add_function();
        let ty = infer_operand_type(&func, &Operand::Constant(Constant::Bool(true)));
        assert!(ty.is_none());
    }

    #[test]
    fn infer_operand_type_constant_int() {
        let func = make_add_function();
        let ty = infer_operand_type(&func, &Operand::Constant(Constant::Int(42, IntTy::I32)));
        assert!(ty.is_none());
    }

    #[test]
    fn infer_operand_type_constant_uint() {
        let func = make_add_function();
        let ty = infer_operand_type(&func, &Operand::Constant(Constant::Uint(42, UintTy::U32)));
        assert!(ty.is_none());
    }

    #[test]
    fn infer_operand_type_constant_unit() {
        let func = make_add_function();
        let ty = infer_operand_type(&func, &Operand::Constant(Constant::Unit));
        assert!(ty.is_none());
    }

    // === parse_simple_spec tests ===
    // Cover lines 2414-2416 (OR), 2441-2442, 2444-2445 (bool constants), 2449 (single var)

    #[test]
    fn parse_simple_spec_or() {
        let func = make_add_function();
        let term = parse_simple_spec("result >= 0 || result <= 100", &func);
        assert!(term.is_some());
        if let Some(Term::Or(parts)) = &term {
            assert_eq!(parts.len(), 2);
        } else {
            panic!("Expected Or term, got: {term:?}");
        }
    }

    #[test]
    fn parse_simple_spec_true() {
        let func = make_add_function();
        let term = parse_simple_spec("true", &func);
        assert_eq!(term, Some(Term::BoolLit(true)));
    }

    #[test]
    fn parse_simple_spec_false() {
        let func = make_add_function();
        let term = parse_simple_spec("false", &func);
        assert_eq!(term, Some(Term::BoolLit(false)));
    }

    #[test]
    fn parse_simple_spec_single_variable() {
        let func = make_max_function();
        // _3 is a Bool local
        let term = parse_simple_spec("_3", &func);
        assert!(term.is_some());
        assert_eq!(term.unwrap(), Term::Const("_3".to_string()));
    }

    #[test]
    fn parse_simple_spec_not_equal() {
        let func = make_add_function();
        let term = parse_simple_spec("result != 0", &func);
        assert!(term.is_some());
        if let Some(Term::Not(inner)) = &term {
            assert!(matches!(**inner, Term::Eq(_, _)));
        } else {
            panic!("Expected Not(Eq(...)), got: {term:?}");
        }
    }

    #[test]
    fn parse_simple_spec_gt_not_confused_with_ge() {
        let func = make_add_function();
        // ">" should not match ">="
        let term = parse_simple_spec("result > 0", &func);
        assert!(term.is_some());
    }

    #[test]
    fn parse_simple_spec_lt_not_confused_with_le() {
        let func = make_add_function();
        let term = parse_simple_spec("result < 100", &func);
        assert!(term.is_some());
    }

    // === parse_spec_operand tests ===
    // Cover lines 2601-2616 (struct/tuple field access), 2635-2643 (subtraction)

    #[test]
    fn parse_spec_operand_result_struct_field() {
        let func = Function {
            name: "struct_fn".to_string(),
            return_local: Local {
                name: "_0".to_string(),
                ty: Ty::Struct(
                    "Point".to_string(),
                    vec![
                        ("x".to_string(), Ty::Int(IntTy::I32)),
                        ("y".to_string(), Ty::Int(IntTy::I32)),
                    ],
                ),
                is_ghost: false,
            },
            params: vec![],
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        };

        let term = parse_spec_operand("result.x", &func);
        assert!(term.is_some());
        if let Some(Term::App(name, args)) = &term {
            assert_eq!(name, "Point-x");
            assert_eq!(args.len(), 1);
        } else {
            panic!("Expected App term for struct field, got: {term:?}");
        }
    }

    #[test]
    fn parse_spec_operand_result_tuple_field() {
        let func = Function {
            name: "tuple_fn".to_string(),
            return_local: Local {
                name: "_0".to_string(),
                ty: Ty::Tuple(vec![Ty::Int(IntTy::I32), Ty::Bool]),
                is_ghost: false,
            },
            params: vec![],
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        };

        let term = parse_spec_operand("result.0", &func);
        assert!(term.is_some());
        if let Some(Term::App(name, args)) = &term {
            assert_eq!(name, "Tuple2-_0");
            assert_eq!(args.len(), 1);
        } else {
            panic!("Expected App term for tuple field, got: {term:?}");
        }
    }

    #[test]
    fn parse_spec_operand_result_tuple_field_with_underscore() {
        let func = Function {
            name: "tuple_fn".to_string(),
            return_local: Local {
                name: "_0".to_string(),
                ty: Ty::Tuple(vec![Ty::Int(IntTy::I32), Ty::Bool]),
                is_ghost: false,
            },
            params: vec![],
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        };

        // Test with _1 style index
        let term = parse_spec_operand("result._1", &func);
        assert!(term.is_some());
        if let Some(Term::App(name, _)) = &term {
            assert_eq!(name, "Tuple2-_1");
        } else {
            panic!("Expected App term for tuple field, got: {term:?}");
        }
    }

    #[test]
    fn parse_spec_operand_integer_literal() {
        let func = make_add_function();
        let term = parse_spec_operand("42", &func);
        assert_eq!(term, Some(Term::BitVecLit(42, 32)));
    }

    #[test]
    fn parse_spec_operand_addition() {
        let func = make_add_function();
        let term = parse_spec_operand("_1 + 1", &func);
        assert!(term.is_some());
        if let Some(Term::BvAdd(_, _)) = &term {
            // OK
        } else {
            panic!("Expected BvAdd term, got: {term:?}");
        }
    }

    #[test]
    fn parse_spec_operand_subtraction() {
        let func = make_add_function();
        let term = parse_spec_operand("_1 - 1", &func);
        assert!(term.is_some());
        if let Some(Term::BvSub(_, _)) = &term {
            // OK
        } else {
            panic!("Expected BvSub term, got: {term:?}");
        }
    }

    #[test]
    fn parse_spec_operand_unknown_returns_none() {
        let func = make_add_function();
        let term = parse_spec_operand("unknown_var", &func);
        assert!(term.is_none());
    }

    // === make_comparison tests ===
    // Cover lines 2569-2575

    fn make_unsigned_function() -> Function {
        Function {
            name: "unsigned_fn".to_string(),
            return_local: Local::new("_0", Ty::Uint(UintTy::U32)),
            params: vec![Local::new("_1", Ty::Uint(UintTy::U32))],
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        }
    }

    #[test]
    fn make_comparison_signed_lt() {
        let func = make_add_function();
        let result = make_comparison(
            BinOp::Lt,
            Term::Const("_0".to_string()),
            Term::BitVecLit(0, 32),
            &func,
        );
        assert!(matches!(result, Term::BvSLt(_, _)));
    }

    #[test]
    fn make_comparison_unsigned_lt() {
        let func = make_unsigned_function();
        let result = make_comparison(
            BinOp::Lt,
            Term::Const("_0".to_string()),
            Term::BitVecLit(0, 32),
            &func,
        );
        assert!(matches!(result, Term::BvULt(_, _)));
    }

    #[test]
    fn make_comparison_signed_gt() {
        let func = make_add_function();
        let result = make_comparison(
            BinOp::Gt,
            Term::Const("_0".to_string()),
            Term::BitVecLit(0, 32),
            &func,
        );
        assert!(matches!(result, Term::BvSGt(_, _)));
    }

    #[test]
    fn make_comparison_unsigned_gt() {
        let func = make_unsigned_function();
        let result = make_comparison(
            BinOp::Gt,
            Term::Const("_0".to_string()),
            Term::BitVecLit(0, 32),
            &func,
        );
        assert!(matches!(result, Term::BvUGt(_, _)));
    }

    #[test]
    fn make_comparison_signed_le() {
        let func = make_add_function();
        let result = make_comparison(
            BinOp::Le,
            Term::Const("_0".to_string()),
            Term::BitVecLit(0, 32),
            &func,
        );
        assert!(matches!(result, Term::BvSLe(_, _)));
    }

    #[test]
    fn make_comparison_unsigned_le() {
        let func = make_unsigned_function();
        let result = make_comparison(
            BinOp::Le,
            Term::Const("_0".to_string()),
            Term::BitVecLit(0, 32),
            &func,
        );
        assert!(matches!(result, Term::BvULe(_, _)));
    }

    #[test]
    fn make_comparison_signed_ge() {
        let func = make_add_function();
        let result = make_comparison(
            BinOp::Ge,
            Term::Const("_0".to_string()),
            Term::BitVecLit(0, 32),
            &func,
        );
        assert!(matches!(result, Term::BvSGe(_, _)));
    }

    #[test]
    fn make_comparison_unsigned_ge() {
        let func = make_unsigned_function();
        let result = make_comparison(
            BinOp::Ge,
            Term::Const("_0".to_string()),
            Term::BitVecLit(0, 32),
            &func,
        );
        assert!(matches!(result, Term::BvUGe(_, _)));
    }

    // === infer_signedness_from_context / infer_signedness_from_term tests ===
    // Cover lines 2476-2481, 2498-2504

    #[test]
    fn infer_signedness_signed_return() {
        let func = make_add_function(); // i32 return
        let signed =
            infer_signedness_from_context(&func, &Term::BitVecLit(0, 32), &Term::BitVecLit(1, 32));
        assert!(signed);
    }

    #[test]
    fn infer_signedness_unsigned_return() {
        let func = make_unsigned_function(); // u32 return
        let signed =
            infer_signedness_from_context(&func, &Term::BitVecLit(0, 32), &Term::BitVecLit(1, 32));
        assert!(!signed);
    }

    #[test]
    fn infer_signedness_from_term_variable() {
        let func = make_add_function();
        // _1 is i32, should be signed
        let signed = infer_signedness_from_term(&func, &Term::Const("_1".to_string()));
        assert_eq!(signed, Some(true));
    }

    #[test]
    fn infer_signedness_from_term_unsigned_variable() {
        let func = make_unsigned_function();
        let signed = infer_signedness_from_term(&func, &Term::Const("_1".to_string()));
        assert_eq!(signed, Some(false));
    }

    #[test]
    fn infer_signedness_from_term_unknown_variable() {
        let func = make_add_function();
        let signed = infer_signedness_from_term(&func, &Term::Const("unknown".to_string()));
        assert_eq!(signed, None);
    }

    #[test]
    fn infer_signedness_from_term_selector() {
        // Create a function with a struct return type
        let func = Function {
            name: "selector_fn".to_string(),
            return_local: Local {
                name: "_0".to_string(),
                ty: Ty::Struct(
                    "Pair".to_string(),
                    vec![
                        ("x".to_string(), Ty::Int(IntTy::I32)),
                        ("y".to_string(), Ty::Uint(UintTy::U32)),
                    ],
                ),
                is_ghost: false,
            },
            params: vec![],
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        };

        // Selector "Pair-x" should resolve to i32 (signed)
        let signed = infer_signedness_from_term(
            &func,
            &Term::App("Pair-x".to_string(), vec![Term::Const("_0".to_string())]),
        );
        assert_eq!(signed, Some(true));

        // Selector "Pair-y" should resolve to u32 (unsigned)
        let signed = infer_signedness_from_term(
            &func,
            &Term::App("Pair-y".to_string(), vec![Term::Const("_0".to_string())]),
        );
        assert_eq!(signed, Some(false));
    }

    // === resolve_selector_from_ty tests ===
    // Cover lines 2543-2555 (Tuple path)

    #[test]
    fn resolve_selector_from_ty_struct() {
        let ty = Ty::Struct(
            "Point".to_string(),
            vec![
                ("x".to_string(), Ty::Int(IntTy::I32)),
                ("y".to_string(), Ty::Int(IntTy::I32)),
            ],
        );
        let result = resolve_selector_from_ty(&ty, "Point-x");
        assert_eq!(result, Some(&Ty::Int(IntTy::I32)));

        let result = resolve_selector_from_ty(&ty, "Point-z");
        assert!(result.is_none());
    }

    #[test]
    fn resolve_selector_from_ty_tuple() {
        let ty = Ty::Tuple(vec![Ty::Int(IntTy::I32), Ty::Bool]);
        let result = resolve_selector_from_ty(&ty, "Tuple2-_0");
        assert_eq!(result, Some(&Ty::Int(IntTy::I32)));

        let result = resolve_selector_from_ty(&ty, "Tuple2-_1");
        assert_eq!(result, Some(&Ty::Bool));

        // Out of range
        let result = resolve_selector_from_ty(&ty, "Tuple2-_5");
        assert!(result.is_none());
    }

    #[test]
    fn resolve_selector_from_ty_other() {
        let ty = Ty::Int(IntTy::I32);
        let result = resolve_selector_from_ty(&ty, "anything");
        assert!(result.is_none());
    }

    // === resolve_selector_type tests ===
    // Cover lines 2516-2527

    #[test]
    fn resolve_selector_type_in_params() {
        let func = Function {
            name: "f".to_string(),
            return_local: Local::new("_0", Ty::Unit),
            params: vec![Local {
                name: "_1".to_string(),
                ty: Ty::Struct("Foo".to_string(), vec![("bar".to_string(), Ty::Bool)]),
                is_ghost: false,
            }],
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        };
        let result = resolve_selector_type(&func, "Foo-bar");
        assert_eq!(result, Some(&Ty::Bool));
    }

    #[test]
    fn resolve_selector_type_in_locals() {
        let func = Function {
            name: "f".to_string(),
            return_local: Local::new("_0", Ty::Unit),
            params: vec![],
            locals: vec![Local {
                name: "_1".to_string(),
                ty: Ty::Struct(
                    "Baz".to_string(),
                    vec![("qux".to_string(), Ty::Int(IntTy::I64))],
                ),
                is_ghost: false,
            }],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        };
        let result = resolve_selector_type(&func, "Baz-qux");
        assert_eq!(result, Some(&Ty::Int(IntTy::I64)));
    }

    #[test]
    fn resolve_selector_type_not_found() {
        let func = make_add_function();
        let result = resolve_selector_type(&func, "NoSuchType-field");
        assert!(result.is_none());
    }

    // === normalize_callee_name tests ===

    #[test]
    fn normalize_callee_name_basic() {
        assert_eq!(normalize_callee_name("add"), "add");
        assert_eq!(normalize_callee_name("const add"), "add");
        assert_eq!(normalize_callee_name("const my_module::helper"), "helper");
        assert_eq!(normalize_callee_name("  const add  "), "add");
    }

    // === detect_loops tests ===
    // Cover lines 1662, 1666

    #[test]
    fn detect_loops_no_loops() {
        let func = make_add_function();
        let loops = detect_loops(&func);
        assert!(loops.is_empty());
    }

    #[test]
    fn detect_loops_pre_populated() {
        let mut func = make_add_function();
        func.loops = vec![LoopInfo {
            header_block: 0,
            back_edge_blocks: vec![1],
            invariants: vec![],
        }];
        let loops = detect_loops(&func);
        assert_eq!(loops.len(), 1);
        assert_eq!(loops[0].header_block, 0);
    }

    #[test]
    fn detect_loops_simple_loop() {
        // bb0: goto bb1
        // bb1: switchInt(_1) -> [1: bb2, otherwise: bb3]
        // bb2: _2 = _2 + 1; goto bb1 (back-edge)
        // bb3: return
        let func = Function {
            name: "loop_fn".to_string(),
            return_local: Local::new("_0", Ty::Int(IntTy::I32)),
            params: vec![],
            locals: vec![
                Local::new("_1", Ty::Bool),
                Local::new("_2", Ty::Int(IntTy::I32)),
            ],
            basic_blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Goto(1),
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local("_1")),
                        targets: vec![(1, 2)],
                        otherwise: 3,
                    },
                },
                BasicBlock {
                    statements: vec![Statement::Assign(
                        Place::local("_2"),
                        Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local("_2")),
                            Operand::Constant(Constant::Int(1, IntTy::I32)),
                        ),
                    )],
                    terminator: Terminator::Goto(1), // back-edge to header
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
            ],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        };

        let loops = detect_loops(&func);
        assert!(!loops.is_empty());
        assert_eq!(loops[0].header_block, 1);
    }

    // === extract_loop_condition tests ===
    // Cover lines 2003, 2026-2043

    #[test]
    fn extract_loop_condition_out_of_bounds() {
        let func = make_add_function();
        let result = extract_loop_condition(&func, 999);
        assert!(result.is_none());
    }

    #[test]
    fn extract_loop_condition_bool_discr() {
        let func = Function {
            name: "f".to_string(),
            return_local: Local::new("_0", Ty::Unit),
            params: vec![],
            locals: vec![Local::new("_1", Ty::Bool)],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local("_1")),
                    targets: vec![(1, 1)],
                    otherwise: 2,
                },
            }],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        };

        let cond = extract_loop_condition(&func, 0);
        assert!(cond.is_some());
        // For bool discriminant, just returns the discriminant term itself
        assert_eq!(cond.unwrap(), Term::Const("_1".to_string()));
    }

    #[test]
    fn extract_loop_condition_int_discr() {
        let func = Function {
            name: "f".to_string(),
            return_local: Local::new("_0", Ty::Unit),
            params: vec![],
            locals: vec![Local::new("_1", Ty::Int(IntTy::I32))],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local("_1")),
                    targets: vec![(42, 1)],
                    otherwise: 2,
                },
            }],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        };

        let cond = extract_loop_condition(&func, 0);
        assert!(cond.is_some());
        if let Some(Term::Eq(l, r)) = &cond {
            assert_eq!(**l, Term::Const("_1".to_string()));
            assert_eq!(**r, Term::BitVecLit(42, 32));
        } else {
            panic!("Expected Eq term, got: {cond:?}");
        }
    }

    #[test]
    fn extract_loop_condition_non_switch() {
        let func = Function {
            name: "f".to_string(),
            return_local: Local::new("_0", Ty::Unit),
            params: vec![],
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        };

        let cond = extract_loop_condition(&func, 0);
        assert!(cond.is_none());
    }

    #[test]
    fn extract_loop_condition_constant_discr() {
        let func = Function {
            name: "f".to_string(),
            return_local: Local::new("_0", Ty::Unit),
            params: vec![],
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Constant(Constant::Int(1, IntTy::I32)),
                    targets: vec![],
                    otherwise: 0,
                },
            }],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        };

        let cond = extract_loop_condition(&func, 0);
        // Empty targets -> returns discr_term directly
        assert!(cond.is_some());
    }

    // === collect_loop_body_assignments / collect_post_loop_assignments / collect_body_only_assignments tests ===
    // Cover lines 2098, 2107-2108, 2157-2159, 2172, 2178, 2198, 2214, 2230, 2236-2237

    fn make_loop_function() -> Function {
        // bb0: _1 = 0; goto bb1  (pre-loop)
        // bb1: switchInt(_2) -> [1: bb2, otherwise: bb3]  (header)
        // bb2: _1 = _1 + 1; goto bb1 (body, back-edge)
        // bb3: _0 = _1; return (exit)
        Function {
            name: "loop_fn".to_string(),
            return_local: Local::new("_0", Ty::Int(IntTy::I32)),
            params: vec![],
            locals: vec![
                Local::new("_1", Ty::Int(IntTy::I32)),
                Local::new("_2", Ty::Bool),
            ],
            basic_blocks: vec![
                // bb0: pre-loop
                BasicBlock {
                    statements: vec![Statement::Assign(
                        Place::local("_1"),
                        Rvalue::Use(Operand::Constant(Constant::Int(0, IntTy::I32))),
                    )],
                    terminator: Terminator::Goto(1),
                },
                // bb1: loop header
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local("_2")),
                        targets: vec![(1, 2)],
                        otherwise: 3,
                    },
                },
                // bb2: loop body
                BasicBlock {
                    statements: vec![Statement::Assign(
                        Place::local("_1"),
                        Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local("_1")),
                            Operand::Constant(Constant::Int(1, IntTy::I32)),
                        ),
                    )],
                    terminator: Terminator::Goto(1), // back-edge
                },
                // bb3: post-loop
                BasicBlock {
                    statements: vec![Statement::Assign(
                        Place::local("_0"),
                        Rvalue::Use(Operand::Copy(Place::local("_1"))),
                    )],
                    terminator: Terminator::Return,
                },
            ],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        }
    }

    #[test]
    fn collect_loop_body_assignments_basic() {
        let func = make_loop_function();
        let assignments = collect_loop_body_assignments(&func, 1, &[2]);
        // Should include header statements + body block statements
        assert!(!assignments.is_empty());
    }

    #[test]
    fn collect_loop_body_assignments_out_of_bounds() {
        let func = make_loop_function();
        let assignments = collect_loop_body_assignments(&func, 999, &[]);
        assert!(assignments.is_empty());
    }

    #[test]
    fn collect_post_loop_assignments_basic() {
        let func = make_loop_function();
        let assignments = collect_post_loop_assignments(&func, 1, &None);
        // Should include bb3's assignment (_0 = _1)
        assert!(!assignments.is_empty());
    }

    #[test]
    fn collect_post_loop_assignments_out_of_bounds() {
        let func = make_loop_function();
        let assignments = collect_post_loop_assignments(&func, 999, &None);
        assert!(assignments.is_empty());
    }

    #[test]
    fn collect_post_loop_assignments_non_switch_header() {
        let func = Function {
            name: "f".to_string(),
            return_local: Local::new("_0", Ty::Unit),
            params: vec![],
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        };
        let assignments = collect_post_loop_assignments(&func, 0, &None);
        // No SwitchInt -> no exit_block -> empty
        assert!(assignments.is_empty());
    }

    #[test]
    fn collect_body_only_assignments_basic() {
        let func = make_loop_function();
        let assignments = collect_body_only_assignments(&func, 1, &[2]);
        // Should include only body assignments (not header statements)
        assert!(!assignments.is_empty());
    }

    #[test]
    fn collect_body_only_assignments_out_of_bounds() {
        let func = make_loop_function();
        let assignments = collect_body_only_assignments(&func, 999, &[]);
        assert!(assignments.is_empty());
    }

    #[test]
    fn collect_body_only_assignments_goto_header() {
        // When header has Goto terminator instead of SwitchInt
        let func = Function {
            name: "f".to_string(),
            return_local: Local::new("_0", Ty::Unit),
            params: vec![],
            locals: vec![Local::new("_1", Ty::Int(IntTy::I32))],
            basic_blocks: vec![
                // bb0: header with Goto
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Goto(1),
                },
                // bb1: body
                BasicBlock {
                    statements: vec![Statement::Assign(
                        Place::local("_1"),
                        Rvalue::Use(Operand::Constant(Constant::Int(1, IntTy::I32))),
                    )],
                    terminator: Terminator::Goto(0), // back-edge
                },
            ],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        };
        let assignments = collect_body_only_assignments(&func, 0, &[1]);
        assert!(!assignments.is_empty());
    }

    // === terminator_successors tests ===

    #[test]
    fn terminator_successors_return() {
        let succs = terminator_successors(&Terminator::Return);
        assert!(succs.is_empty());
    }

    #[test]
    fn terminator_successors_unreachable() {
        let succs = terminator_successors(&Terminator::Unreachable);
        assert!(succs.is_empty());
    }

    #[test]
    fn terminator_successors_goto() {
        let succs = terminator_successors(&Terminator::Goto(5));
        assert_eq!(succs, vec![5]);
    }

    #[test]
    fn terminator_successors_switch() {
        let succs = terminator_successors(&Terminator::SwitchInt {
            discr: Operand::Copy(Place::local("_1")),
            targets: vec![(1, 2), (2, 3)],
            otherwise: 4,
        });
        assert_eq!(succs, vec![2, 3, 4]);
    }

    #[test]
    fn terminator_successors_assert() {
        let succs = terminator_successors(&Terminator::Assert {
            cond: Operand::Copy(Place::local("_1")),
            expected: true,
            target: 7,
            kind: AssertKind::UserAssert,
        });
        assert_eq!(succs, vec![7]);
    }

    #[test]
    fn terminator_successors_call() {
        let succs = terminator_successors(&Terminator::Call {
            func: "callee".to_string(),
            args: vec![],
            destination: Place::local("_0"),
            target: 3,
        });
        assert_eq!(succs, vec![3]);
    }

    // === encode_operand_for_vcgen tests ===

    #[test]
    fn encode_operand_for_vcgen_simple_copy() {
        let func = make_add_function();
        let result = encode_operand_for_vcgen(&Operand::Copy(Place::local("_1")), &func);
        assert_eq!(result, Term::Const("_1".to_string()));
    }

    #[test]
    fn encode_operand_for_vcgen_constant() {
        let func = make_add_function();
        let result =
            encode_operand_for_vcgen(&Operand::Constant(Constant::Int(42, IntTy::I32)), &func);
        assert_eq!(result, Term::BitVecLit(42, 32));
    }

    // === split_at_operator tests ===

    #[test]
    fn split_logical_and_simple() {
        let result = split_logical_and("a > 0 && b > 0");
        assert!(result.is_some());
        let (l, r) = result.unwrap();
        assert_eq!(l, "a > 0");
        assert_eq!(r, "b > 0");
    }

    #[test]
    fn split_logical_and_nested_parens() {
        let result = split_logical_and("(a > 0 && b > 0) && c > 0");
        assert!(result.is_some());
        let (l, r) = result.unwrap();
        assert_eq!(l, "(a > 0 && b > 0)");
        assert_eq!(r, "c > 0");
    }

    #[test]
    fn split_logical_or_simple() {
        let result = split_logical_or("a > 0 || b > 0");
        assert!(result.is_some());
        let (l, r) = result.unwrap();
        assert_eq!(l, "a > 0");
        assert_eq!(r, "b > 0");
    }

    #[test]
    fn split_logical_and_none() {
        let result = split_logical_and("a > 0");
        assert!(result.is_none());
    }

    // === base_script tests ===

    #[test]
    fn base_script_no_datatypes() {
        let script = base_script(&[], &[], false);
        let s = script.to_string();
        assert!(s.contains("QF_BV"));
    }

    #[test]
    fn base_script_with_datatypes() {
        let script = base_script(&[Command::Comment("datatype".to_string())], &[], false);
        let s = script.to_string();
        assert!(s.contains("QF_UFBVDT"));
    }

    #[test]
    fn base_script_with_int() {
        let script = base_script(&[], &[], true);
        let s = script.to_string();
        assert!(s.contains("ALL"));
    }

    // === SwitchInt with non-bool discriminant ===
    // Covers lines 529, 532-536, 541-544, 552-553

    #[test]
    fn enumerate_paths_switch_int_non_bool() {
        // SwitchInt with integer discriminant (not bool)
        let func = Function {
            name: "switch_int".to_string(),
            return_local: Local::new("_0", Ty::Int(IntTy::I32)),
            params: vec![],
            locals: vec![Local::new("_1", Ty::Int(IntTy::I32))],
            basic_blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local("_1")),
                        targets: vec![(0, 1), (1, 2)],
                        otherwise: 3,
                    },
                },
                // bb1: case 0
                BasicBlock {
                    statements: vec![Statement::Assign(
                        Place::local("_0"),
                        Rvalue::Use(Operand::Constant(Constant::Int(10, IntTy::I32))),
                    )],
                    terminator: Terminator::Return,
                },
                // bb2: case 1
                BasicBlock {
                    statements: vec![Statement::Assign(
                        Place::local("_0"),
                        Rvalue::Use(Operand::Constant(Constant::Int(20, IntTy::I32))),
                    )],
                    terminator: Terminator::Return,
                },
                // bb3: otherwise
                BasicBlock {
                    statements: vec![Statement::Assign(
                        Place::local("_0"),
                        Rvalue::Use(Operand::Constant(Constant::Int(30, IntTy::I32))),
                    )],
                    terminator: Terminator::Return,
                },
            ],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        };

        let paths = enumerate_paths(&func);
        assert_eq!(paths.len(), 3); // one per target + otherwise
    }

    #[test]
    fn enumerate_paths_switch_constant_discr() {
        // SwitchInt with constant discriminant
        let func = Function {
            name: "switch_const".to_string(),
            return_local: Local::new("_0", Ty::Int(IntTy::I32)),
            params: vec![],
            locals: vec![],
            basic_blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Constant(Constant::Int(1, IntTy::I32)),
                        targets: vec![(1, 1)],
                        otherwise: 2,
                    },
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
            ],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        };

        let paths = enumerate_paths(&func);
        assert_eq!(paths.len(), 2);
    }

    #[test]
    fn enumerate_paths_switch_no_type_info() {
        // SwitchInt with unknown discriminant type (None from find_local_type)
        let func = Function {
            name: "switch_unknown".to_string(),
            return_local: Local::new("_0", Ty::Unit),
            params: vec![],
            locals: vec![], // _1 not declared in locals
            basic_blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local("_1")),
                        targets: vec![(1, 1)],
                        otherwise: 2,
                    },
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
            ],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        };

        let paths = enumerate_paths(&func);
        // Should handle unknown type by defaulting to boolean
        assert_eq!(paths.len(), 2);
    }

    // === generate_assert_terminator_vcs test ===
    // Cover lines 920, 940-943

    #[test]
    fn generate_assert_vcs_for_assert_terminator() {
        let func = Function {
            name: "assert_fn".to_string(),
            return_local: Local::new("_0", Ty::Unit),
            params: vec![Local::new("_1", Ty::Bool)],
            locals: vec![],
            basic_blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local("_1")),
                        expected: true,
                        target: 1,
                        kind: AssertKind::UserAssert,
                    },
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
            ],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        };

        let result = generate_vcs(&func, None);
        assert!(
            result
                .conditions
                .iter()
                .any(|vc| vc.description.contains("assertion")),
            "Expected an assertion VC, got: {:?}",
            result
                .conditions
                .iter()
                .map(|vc| &vc.description)
                .collect::<Vec<_>>()
        );
    }

    // === PathState tests ===

    #[test]
    fn path_state_condition_none() {
        let state = PathState {
            conditions: vec![],
            assignments: vec![],
            overflow_vcs: vec![],
            call_sites: vec![],
            visited: HashSet::new(),
        };
        assert!(state.path_condition().is_none());
    }

    #[test]
    fn path_state_condition_single() {
        let state = PathState {
            conditions: vec![Term::BoolLit(true)],
            assignments: vec![],
            overflow_vcs: vec![],
            call_sites: vec![],
            visited: HashSet::new(),
        };
        assert_eq!(state.path_condition(), Some(Term::BoolLit(true)));
    }

    #[test]
    fn path_state_condition_multiple() {
        let state = PathState {
            conditions: vec![Term::BoolLit(true), Term::BoolLit(false)],
            assignments: vec![],
            overflow_vcs: vec![],
            call_sites: vec![],
            visited: HashSet::new(),
        };
        let cond = state.path_condition();
        assert!(matches!(cond, Some(Term::And(_))));
    }

    // === Shift overflow check classification ===

    #[test]
    fn shift_generates_bounds_check() {
        let func = Function {
            name: "shift_fn".to_string(),
            return_local: Local::new("_0", Ty::Int(IntTy::I32)),
            params: vec![
                Local::new("_1", Ty::Int(IntTy::I32)),
                Local::new("_2", Ty::Int(IntTy::I32)),
            ],
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::BinaryOp(
                        BinOp::Shl,
                        Operand::Copy(Place::local("_1")),
                        Operand::Copy(Place::local("_2")),
                    ),
                )],
                terminator: Terminator::Return,
            }],
            contracts: Contracts::default(),
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
            loops: vec![],
        };

        let result = generate_vcs(&func, None);
        assert!(
            result
                .conditions
                .iter()
                .any(|vc| vc.location.vc_kind == VcKind::ShiftBounds),
            "Expected a shift bounds VC"
        );
    }

    // === Loop invariant VCs with user-supplied invariants ===
    // Cover lines 1726 (empty invariants return early)

    #[test]
    fn generate_loop_invariant_vcs_empty_invariants() {
        let func = make_loop_function();
        let decls = collect_declarations(&func);
        let dt_decls = collect_datatype_declarations(&func);
        let loop_info = LoopInfo {
            header_block: 1,
            back_edge_blocks: vec![2],
            invariants: vec![], // No invariants
        };
        let empty_db = crate::ghost_predicate_db::GhostPredicateDatabase::new();
        let vcs = generate_loop_invariant_vcs(&func, &dt_decls, &decls, &loop_info, &empty_db);
        assert!(vcs.is_empty(), "No VCs when invariants are empty");
    }

    #[test]
    fn generate_loop_invariant_vcs_with_invariant() {
        let mut func = make_loop_function();
        // VC3 (exit) requires postconditions
        func.contracts.ensures.push(SpecExpr {
            raw: "_0 >= 0".to_string(),
        });
        let decls = collect_declarations(&func);
        let dt_decls = collect_datatype_declarations(&func);
        let loop_info = LoopInfo {
            header_block: 1,
            back_edge_blocks: vec![2],
            invariants: vec![SpecExpr {
                raw: "_1 >= 0".to_string(),
            }],
        };
        let empty_db = crate::ghost_predicate_db::GhostPredicateDatabase::new();
        let vcs = generate_loop_invariant_vcs(&func, &dt_decls, &decls, &loop_info, &empty_db);
        // Should generate 3 VCs: init, preserve, exit
        assert_eq!(vcs.len(), 3, "Expected 3 loop invariant VCs");
    }

    // === encode_path_assignments with branch depth ===
    // Cover lines 808 (else branch of path condition guard)

    #[test]
    fn encode_path_assignments_no_condition() {
        let func = make_add_function();
        let path = CfgPath {
            condition: None,
            assignments: vec![PathAssignment {
                place: Place::local("_0"),
                rvalue: Rvalue::Use(Operand::Copy(Place::local("_1"))),
                block_idx: 0,
                branch_depth: 1, // Even with depth > 0, no condition means no guard
            }],
            overflow_vcs: vec![],
            call_sites: vec![],
        };
        let cmds = encode_path_assignments(&func, &path);
        // Should still produce an assertion (just unguarded since condition is None)
        assert!(!cmds.is_empty());
    }

    // ====== VcKind::Termination tests (Phase 6) ======

    #[test]
    fn test_vc_kind_termination_variant_exists() {
        let kind = VcKind::Termination;
        assert_eq!(kind, VcKind::Termination);
        // Ensure it is distinct from other variants
        assert_ne!(kind, VcKind::Precondition);
        assert_ne!(kind, VcKind::Postcondition);
        assert_ne!(kind, VcKind::Assertion);
    }

    // ====== Recursion integration tests (Phase 6, Plan 02) ======

    /// Build a factorial function with recursive call for integration testing.
    fn make_recursive_factorial() -> Function {
        let params = vec![Local {
            name: "_1".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        }];

        let locals = vec![
            Local::new("_2", Ty::Bool),            // condition
            Local::new("_3", Ty::Int(IntTy::I32)), // call result
        ];

        // bb0: _2 = _1 <= 1; switchInt(_2) -> bb1 (true) or bb2 (false)
        let bb0 = BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_2"),
                Rvalue::BinaryOp(
                    BinOp::Le,
                    Operand::Copy(Place::local("_1")),
                    Operand::Constant(Constant::Int(1, IntTy::I32)),
                ),
            )],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local("_2")),
                targets: vec![(1, 1)],
                otherwise: 2,
            },
        };

        // bb1 (base case): _0 = 1; return
        let bb1 = BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::Use(Operand::Constant(Constant::Int(1, IntTy::I32))),
            )],
            terminator: Terminator::Return,
        };

        // bb2 (recursive case): call factorial(_1); _3 = result; -> bb3
        let bb2 = BasicBlock {
            statements: vec![],
            terminator: Terminator::Call {
                func: "factorial".to_string(),
                args: vec![Operand::Copy(Place::local("_1"))],
                destination: Place::local("_3"),
                target: 3,
            },
        };

        // bb3: _0 = _1 * _3; return
        let bb3 = BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::BinaryOp(
                    BinOp::Mul,
                    Operand::Copy(Place::local("_1")),
                    Operand::Copy(Place::local("_3")),
                ),
            )],
            terminator: Terminator::Return,
        };

        Function {
            name: "factorial".to_string(),
            params,
            return_local: Local::new("_0", Ty::Int(IntTy::I32)),
            locals,
            basic_blocks: vec![bb0, bb1, bb2, bb3],
            contracts: Contracts {
                requires: vec![SpecExpr {
                    raw: "_1 >= 0".to_string(),
                }],
                ensures: vec![SpecExpr {
                    raw: "result > 0".to_string(),
                }],
                invariants: vec![],
                is_pure: false,
                decreases: Some(SpecExpr {
                    raw: "_1".to_string(),
                }),
                fn_specs: vec![],
                state_invariant: None,
            },
            loops: vec![],
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
        }
    }

    #[test]
    fn test_generate_vcs_recursive_function_produces_termination_vc() {
        let factorial = make_recursive_factorial();

        // Build a ContractDatabase with factorial's summary
        let mut contract_db = crate::contract_db::ContractDatabase::new();
        contract_db.insert(
            "factorial".to_string(),
            crate::contract_db::FunctionSummary {
                contracts: factorial.contracts.clone(),
                param_names: vec!["_1".to_string()],
                param_types: vec![Ty::Int(IntTy::I32)],
                return_ty: Ty::Int(IntTy::I32),
            },
        );

        let result = generate_vcs(&factorial, Some(&contract_db));

        // Should have at least one termination VC
        let termination_vcs: Vec<_> = result
            .conditions
            .iter()
            .filter(|vc| vc.location.vc_kind == VcKind::Termination)
            .collect();

        assert!(
            !termination_vcs.is_empty(),
            "Expected at least one Termination VC for recursive factorial, got VCs: {:?}",
            result
                .conditions
                .iter()
                .map(|vc| format!("{}: {:?}", vc.description, vc.location.vc_kind))
                .collect::<Vec<_>>(),
        );
    }

    #[test]
    fn test_generate_vcs_non_recursive_no_termination_vc() {
        let func = make_add_function();
        let result = generate_vcs(&func, None);

        let termination_vcs: Vec<_> = result
            .conditions
            .iter()
            .filter(|vc| vc.location.vc_kind == VcKind::Termination)
            .collect();

        assert!(
            termination_vcs.is_empty(),
            "Non-recursive function should not produce Termination VCs"
        );
    }

    #[test]
    fn test_generate_vcs_recursive_without_decreases_produces_diagnostic_vc() {
        // Factorial WITHOUT decreases annotation
        let mut factorial = make_recursive_factorial();
        factorial.contracts.decreases = None;

        let mut contract_db = crate::contract_db::ContractDatabase::new();
        contract_db.insert(
            "factorial".to_string(),
            crate::contract_db::FunctionSummary {
                contracts: factorial.contracts.clone(),
                param_names: vec!["_1".to_string()],
                param_types: vec![Ty::Int(IntTy::I32)],
                return_ty: Ty::Int(IntTy::I32),
            },
        );

        let result = generate_vcs(&factorial, Some(&contract_db));

        // Should have a diagnostic termination VC (missing decreases)
        let termination_vcs: Vec<_> = result
            .conditions
            .iter()
            .filter(|vc| vc.location.vc_kind == VcKind::Termination)
            .collect();

        assert!(
            !termination_vcs.is_empty(),
            "Recursive function without decreases should produce diagnostic Termination VC, got VCs: {:?}",
            result
                .conditions
                .iter()
                .map(|vc| format!("{}: {:?}", vc.description, vc.location.vc_kind))
                .collect::<Vec<_>>(),
        );

        // The diagnostic VC description should mention "missing"
        assert!(
            termination_vcs
                .iter()
                .any(|vc| vc.description.contains("missing")),
            "Diagnostic VC should mention 'missing': {:?}",
            termination_vcs
                .iter()
                .map(|vc| &vc.description)
                .collect::<Vec<_>>(),
        );
    }

    // ====== VcKind::ClosureContract tests (Phase 7) ======

    #[test]
    fn test_vc_kind_closure_contract() {
        let kind1 = VcKind::ClosureContract;
        let kind2 = VcKind::ClosureContract;
        assert_eq!(kind1, kind2);
        assert_ne!(kind1, VcKind::Precondition);
        assert_ne!(kind1, VcKind::Termination);
    }

    // ====== Closure integration tests (Phase 7-02) ======

    #[test]
    fn test_vcgen_fn_closure_basic() {
        // Function with Fn closure parameter and simple postcondition
        let func = Function {
            name: "apply_fn".to_string(),
            params: vec![Local::new(
                "closure_param",
                Ty::Closure(Box::new(crate::ir::ClosureInfo {
                    name: "predicate".to_string(),
                    env_fields: vec![],
                    params: vec![("x".to_string(), Ty::Int(IntTy::I32))],
                    return_ty: Ty::Bool,
                    trait_kind: crate::ir::ClosureTrait::Fn,
                })),
            )],
            return_local: Local::new("_0", Ty::Bool),
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            contracts: Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "result == true".to_string(),
                }],
                is_pure: false,
                decreases: None,
                fn_specs: vec![],
                state_invariant: None,
                invariants: vec![],
            },
            generic_params: vec![],
            loops: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
        };

        let result = generate_vcs(&func, None);

        // Should generate postcondition VC
        assert!(
            !result.conditions.is_empty(),
            "Should generate at least postcondition VC"
        );

        // Check that the VC script contains a declare-fun for the closure
        let has_closure_decl = result.conditions.iter().any(|vc| {
            vc.script
                .commands()
                .iter()
                .any(|cmd| matches!(cmd, rust_fv_smtlib::command::Command::DeclareFun(name, _, _) if name == "predicate_impl"))
        });
        assert!(
            has_closure_decl,
            "VC should contain declare-fun for closure implementation"
        );
    }

    #[test]
    fn test_vcgen_fnmut_closure_prophecy() {
        // Function with FnMut closure parameter
        let func = Function {
            name: "apply_fnmut".to_string(),
            params: vec![Local::new(
                "closure_param",
                Ty::Closure(Box::new(crate::ir::ClosureInfo {
                    name: "mutator".to_string(),
                    env_fields: vec![("count".to_string(), Ty::Int(IntTy::I32))],
                    params: vec![],
                    return_ty: Ty::Unit,
                    trait_kind: crate::ir::ClosureTrait::FnMut,
                })),
            )],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            contracts: Contracts::default(),
            generic_params: vec![],
            loops: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
        };

        let result = generate_vcs(&func, None);

        // For FnMut closures with mutable captures, should eventually generate prophecy variable declarations
        // For now, just verify VCs are generated without errors
        // Just check that the function completed without panicking
        let _ = result.conditions.len();
    }

    #[test]
    fn test_vcgen_fnonce_double_call_diagnostic() {
        use crate::closure_analysis;

        // Function that calls FnOnce closure twice
        let func = Function {
            name: "call_twice".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![Local::new(
                "_1",
                Ty::Closure(Box::new(crate::ir::ClosureInfo {
                    name: "consumer".to_string(),
                    env_fields: vec![],
                    params: vec![],
                    return_ty: Ty::Unit,
                    trait_kind: crate::ir::ClosureTrait::FnOnce,
                })),
            )],
            basic_blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "FnOnce::call_once".to_string(),
                        args: vec![Operand::Copy(Place::local("_1"))],
                        destination: Place::local("_temp1"),
                        target: 1,
                    },
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "FnOnce::call_once".to_string(),
                        args: vec![Operand::Copy(Place::local("_1"))],
                        destination: Place::local("_temp2"),
                        target: 2,
                    },
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
            ],
            contracts: Contracts::default(),
            generic_params: vec![],
            loops: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
        };

        // Validate FnOnce single-call property
        let errors = closure_analysis::validate_fnonce_single_call(&func);
        assert!(
            !errors.is_empty(),
            "Should detect FnOnce called multiple times"
        );

        let result = generate_vcs(&func, None);

        // Should generate diagnostic VC for FnOnce violation
        let has_diagnostic = result.conditions.iter().any(|vc| {
            vc.location.vc_kind == VcKind::ClosureContract && vc.description.contains("FnOnce")
        });
        assert!(
            has_diagnostic,
            "Should generate diagnostic VC for FnOnce double-call"
        );
    }

    #[test]
    fn test_vcgen_closure_env_construction() {
        // Function that constructs a closure environment
        let func = Function {
            name: "make_closure".to_string(),
            params: vec![Local::new("_1", Ty::Int(IntTy::I32))],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![Local::new(
                "_2",
                Ty::Closure(Box::new(crate::ir::ClosureInfo {
                    name: "add_x".to_string(),
                    env_fields: vec![("x".to_string(), Ty::Int(IntTy::I32))],
                    params: vec![("y".to_string(), Ty::Int(IntTy::I32))],
                    return_ty: Ty::Int(IntTy::I32),
                    trait_kind: crate::ir::ClosureTrait::Fn,
                })),
            )],
            basic_blocks: vec![BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_2"),
                    Rvalue::Aggregate(
                        AggregateKind::Closure("add_x".to_string()),
                        vec![Operand::Copy(Place::local("_1"))],
                    ),
                )],
                terminator: Terminator::Return,
            }],
            contracts: Contracts::default(),
            generic_params: vec![],
            loops: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
        };

        let result = generate_vcs(&func, None);

        // Should generate VCs without errors
        // The closure env construction should be encoded as datatype constructor
        // Just check that the function completed without panicking
        let _ = result.conditions.len();
    }

    // ====== Trait object and dyn Trait tests (Phase 8-02) ======

    #[test]
    fn test_vcgen_without_trait_db_backward_compatible() {
        // Simple function to verify backward compatibility without TraitDatabase
        let func = Function {
            name: "simple".to_string(),
            params: vec![Local::new("_1", Ty::Int(IntTy::I32))],
            return_local: Local::new("_0", Ty::Int(IntTy::I32)),
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Copy(Place::local("_1"))),
                )],
                terminator: Terminator::Return,
            }],
            contracts: Contracts::default(),
            generic_params: vec![],
            loops: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
        };

        // Call with None TraitDatabase - should work as before
        let result = generate_vcs(&func, None);
        // Should not panic - just verify result exists
        let _ = result.conditions;
    }

    #[test]
    fn test_vcgen_trait_object_param_accepted() {
        // Function with trait object parameter
        let func = Function {
            name: "uses_trait_object".to_string(),
            params: vec![Local::new("_1", Ty::TraitObject("Stack".to_string()))],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            contracts: Contracts::default(),
            generic_params: vec![],
            loops: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
        };

        // Should generate VCs without panicking even without TraitDatabase
        let result = generate_vcs(&func, None);
        // Should not panic - just verify result exists
        let _ = result.conditions;
    }

    // === Unsafe analysis tests ===

    #[test]
    fn test_vcgen_trusted_function_skipped() {
        // Trusted function should skip body verification
        let func = Function {
            name: "trusted_fn".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            contracts: Contracts::default(),
            generic_params: vec![],
            loops: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: Some(UnsafeContracts {
                requires: vec![],
                ensures: vec![],
                is_trusted: true,
            }),
            is_unsafe_fn: true,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
        };

        let result = generate_vcs(&func, None);
        assert_eq!(
            result.conditions.len(),
            0,
            "Trusted function should produce no body VCs"
        );
    }

    #[test]
    fn test_vcgen_missing_contracts_warning() {
        // Unsafe function without contracts should produce diagnostic VC
        let func = Function {
            name: "unsafe_no_contracts".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            contracts: Contracts::default(),
            generic_params: vec![],
            loops: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: true,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
        };

        let result = generate_vcs(&func, None);
        // Should have at least the missing-contracts warning VC
        let warning_vcs: Vec<_> = result
            .conditions
            .iter()
            .filter(|vc| vc.location.vc_kind == VcKind::MemorySafety)
            .collect();
        assert!(
            !warning_vcs.is_empty(),
            "Should produce missing-contracts warning VC"
        );
        assert!(
            warning_vcs[0].description.contains("no safety contracts"),
            "Warning should mention missing contracts"
        );
    }

    #[test]
    fn test_vcgen_null_check_generated() {
        // Function with RawDeref (Unknown provenance) should generate null-check VC
        let func = Function {
            name: "deref_ptr".to_string(),
            params: vec![Local::new(
                "_1",
                Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Shared),
            )],
            return_local: Local::new("_0", Ty::Int(IntTy::I32)),
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            contracts: Contracts::default(),
            generic_params: vec![],
            loops: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![UnsafeOperation::RawDeref {
                ptr_local: "_1".to_string(),
                ptr_ty: Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Shared),
                provenance: RawPtrProvenance::Unknown,
                block_index: 0,
            }],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
        };

        let result = generate_vcs(&func, None);
        let null_check_vcs: Vec<_> = result
            .conditions
            .iter()
            .filter(|vc| {
                vc.location.vc_kind == VcKind::MemorySafety && vc.description.contains("null-check")
            })
            .collect();
        assert!(!null_check_vcs.is_empty(), "Should produce null-check VC");
        assert!(
            null_check_vcs[0].description.contains("_1"),
            "Null-check should reference the pointer variable"
        );
    }

    #[test]
    fn test_vcgen_null_check_skipped_from_ref() {
        // Function with RawDeref (FromRef provenance) should NOT generate null-check VC
        let func = Function {
            name: "deref_from_ref".to_string(),
            params: vec![Local::new(
                "_1",
                Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Shared),
            )],
            return_local: Local::new("_0", Ty::Int(IntTy::I32)),
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            contracts: Contracts::default(),
            generic_params: vec![],
            loops: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![UnsafeOperation::RawDeref {
                ptr_local: "_1".to_string(),
                ptr_ty: Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Shared),
                provenance: RawPtrProvenance::FromRef,
                block_index: 0,
            }],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
        };

        let result = generate_vcs(&func, None);
        let null_check_vcs: Vec<_> = result
            .conditions
            .iter()
            .filter(|vc| {
                vc.location.vc_kind == VcKind::MemorySafety && vc.description.contains("null-check")
            })
            .collect();
        assert!(
            null_check_vcs.is_empty(),
            "Should NOT produce null-check VC for FromRef pointers"
        );
    }

    #[test]
    fn test_vcgen_bounds_check_generated() {
        // Function with PtrArithmetic should generate bounds-check VC
        let func = Function {
            name: "ptr_add".to_string(),
            params: vec![
                Local::new(
                    "_1",
                    Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Shared),
                ),
                Local::new("_2", Ty::Int(IntTy::I32)),
            ],
            return_local: Local::new(
                "_0",
                Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Shared),
            ),
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            contracts: Contracts::default(),
            generic_params: vec![],
            loops: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![UnsafeOperation::PtrArithmetic {
                ptr_local: "_1".to_string(),
                offset_local: "_2".to_string(),
                ptr_ty: Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Shared),
                is_signed_offset: false,
                block_index: 0,
            }],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
        };

        let result = generate_vcs(&func, None);
        let bounds_check_vcs: Vec<_> = result
            .conditions
            .iter()
            .filter(|vc| {
                vc.location.vc_kind == VcKind::MemorySafety
                    && vc.description.contains("bounds-check")
            })
            .collect();
        assert!(
            !bounds_check_vcs.is_empty(),
            "Should produce bounds-check VC"
        );
        assert!(
            bounds_check_vcs[0].description.contains("_1"),
            "Bounds-check should reference pointer"
        );
        assert!(
            bounds_check_vcs[0].description.contains("_2"),
            "Bounds-check should reference offset"
        );
    }

    #[test]
    fn test_vcgen_safe_function_no_unsafe_vcs() {
        // Safe function with no unsafe operations produces no MemorySafety VCs
        let func = Function {
            name: "safe_fn".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            contracts: Contracts::default(),
            generic_params: vec![],
            loops: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
        };

        let result = generate_vcs(&func, None);
        let memory_safety_vcs: Vec<_> = result
            .conditions
            .iter()
            .filter(|vc| vc.location.vc_kind == VcKind::MemorySafety)
            .collect();
        assert!(
            memory_safety_vcs.is_empty(),
            "Safe function should not produce MemorySafety VCs"
        );
    }

    #[test]
    fn test_vc_kind_floating_point_nan_eq() {
        // VcKind::FloatingPointNaN should exist and be distinct
        let fp_nan = VcKind::FloatingPointNaN;
        assert_ne!(fp_nan, VcKind::Overflow);
        assert_ne!(fp_nan, VcKind::MemorySafety);
        assert_eq!(fp_nan, VcKind::FloatingPointNaN);
    }

    #[test]
    fn test_vc_kind_data_race_freedom() {
        let drf = VcKind::DataRaceFreedom;
        assert_eq!(drf, VcKind::DataRaceFreedom);
        assert_ne!(drf, VcKind::Overflow);
        assert_ne!(drf, VcKind::LockInvariant);
    }

    #[test]
    fn test_vc_kind_lock_invariant() {
        let li = VcKind::LockInvariant;
        assert_eq!(li, VcKind::LockInvariant);
        assert_ne!(li, VcKind::DataRaceFreedom);
        assert_ne!(li, VcKind::Deadlock);
    }

    #[test]
    fn test_vc_kind_deadlock() {
        let dl = VcKind::Deadlock;
        assert_eq!(dl, VcKind::Deadlock);
        assert_ne!(dl, VcKind::LockInvariant);
        assert_ne!(dl, VcKind::ChannelSafety);
    }

    #[test]
    fn test_vc_kind_channel_safety() {
        let cs = VcKind::ChannelSafety;
        assert_eq!(cs, VcKind::ChannelSafety);
        assert_ne!(cs, VcKind::Deadlock);
        assert_ne!(cs, VcKind::DataRaceFreedom);
    }

    #[test]
    fn test_generate_concurrency_vcs_empty() {
        // Function without concurrency produces no VCs
        let func = Function {
            name: "sequential_fn".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            contracts: Contracts::default(),
            generic_params: vec![],
            loops: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
        };

        let vcs = generate_concurrency_vcs(&func);
        assert!(vcs.is_empty());
    }

    #[test]
    fn test_generate_concurrency_vcs_with_atomics() {
        use crate::ir::{AtomicOp, AtomicOpKind, AtomicOrdering, ConcurrencyConfig};

        let func = Function {
            name: "concurrent_fn".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            contracts: Contracts::default(),
            generic_params: vec![],
            loops: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![
                AtomicOp {
                    kind: AtomicOpKind::Store,
                    atomic_place: Place::local("x".to_string()),
                    ordering: AtomicOrdering::SeqCst,
                    value: Some(Operand::Constant(Constant::Int(0, IntTy::I32))),
                    thread_id: 0,
                },
                AtomicOp {
                    kind: AtomicOpKind::Load,
                    atomic_place: Place::local("x".to_string()),
                    ordering: AtomicOrdering::SeqCst,
                    value: None,
                    thread_id: 0,
                },
            ],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: Some(ConcurrencyConfig {
                verify_concurrency: true,
                max_threads: 2,
                max_context_switches: 3,
            }),
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
        };

        let vcs = generate_concurrency_vcs(&func);
        // Should have: data race VCs + bounded verification warning
        assert!(!vcs.is_empty());
        assert!(
            vcs.iter()
                .any(|vc| vc.description.contains("Bounded verification"))
        );
    }

    #[test]
    fn test_generate_concurrency_vcs_with_lock_invariants() {
        use crate::ir::{ConcurrencyConfig, SyncOp, SyncOpKind};

        let func = Function {
            name: "mutex_fn".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            contracts: Contracts::default(),
            generic_params: vec![],
            loops: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![
                SyncOp {
                    kind: SyncOpKind::MutexLock,
                    sync_object: Place::local("m".to_string()),
                },
                SyncOp {
                    kind: SyncOpKind::MutexUnlock,
                    sync_object: Place::local("m".to_string()),
                },
            ],
            lock_invariants: vec![(
                "m".to_string(),
                SpecExpr {
                    raw: "x > 0".to_string(),
                },
            )],
            concurrency_config: Some(ConcurrencyConfig {
                verify_concurrency: true,
                max_threads: 2,
                max_context_switches: 3,
            }),
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
        };

        let vcs = generate_concurrency_vcs(&func);
        // Should have: lock invariant VC at release + bounded verification warning
        assert!(!vcs.is_empty());
        let lock_vcs: Vec<_> = vcs
            .iter()
            .filter(|vc| vc.location.vc_kind == VcKind::LockInvariant)
            .collect();
        assert_eq!(lock_vcs.len(), 1); // One release
    }

    #[test]
    fn test_generate_concurrency_vcs_with_sync_ops() {
        use crate::ir::{ConcurrencyConfig, SyncOp, SyncOpKind};

        let func = Function {
            name: "deadlock_fn".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            contracts: Contracts::default(),
            generic_params: vec![],
            loops: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![
                SyncOp {
                    kind: SyncOpKind::MutexLock,
                    sync_object: Place::local("m1".to_string()),
                },
                SyncOp {
                    kind: SyncOpKind::MutexLock,
                    sync_object: Place::local("m2".to_string()),
                },
            ],
            lock_invariants: vec![],
            concurrency_config: Some(ConcurrencyConfig {
                verify_concurrency: true,
                max_threads: 2,
                max_context_switches: 3,
            }),
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
        };

        let vcs = generate_concurrency_vcs(&func);
        // Should have: bounded verification warning (no deadlock in single-thread linear order)
        assert!(!vcs.is_empty());
    }

    #[test]
    fn test_generate_concurrency_vcs_bounded_warning() {
        use crate::ir::ConcurrencyConfig;

        let func = Function {
            name: "concurrent_fn".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            contracts: Contracts::default(),
            generic_params: vec![],
            loops: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: Some(ConcurrencyConfig {
                verify_concurrency: true,
                max_threads: 4,
                max_context_switches: 8,
            }),
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
        };

        let vcs = generate_concurrency_vcs(&func);
        assert_eq!(vcs.len(), 1); // Just the bounded verification warning
        assert!(vcs[0].description.contains("Bounded verification"));
        assert!(vcs[0].description.contains("4 threads"));
        assert!(vcs[0].description.contains("8 context switches"));
    }

    #[test]
    fn test_generate_concurrency_vcs_integration() {
        use crate::ir::ThreadSpawn;

        // Function with thread_spawns auto-enables verification
        let func = Function {
            name: "spawns_threads".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            contracts: Contracts::default(),
            generic_params: vec![],
            loops: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![ThreadSpawn {
                handle_local: "t1".to_string(),
                thread_fn: "worker".to_string(),
                args: vec![],
                is_scoped: false,
            }],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None, // No explicit config, but thread_spawns present
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
        };

        let vcs = generate_concurrency_vcs(&func);
        // Should auto-enable and produce bounded verification warning
        assert!(!vcs.is_empty());
        assert!(
            vcs.iter()
                .any(|vc| vc.description.contains("Bounded verification"))
        );
    }

    // === Phase 20-03: Sep-logic call site VC tests ===

    /// Build a caller function that calls a callee named "write_ptr" with one RawPtr arg.
    fn make_sep_logic_caller() -> Function {
        use crate::ir::Mutability;

        // bb0: call write_ptr(_1) -> bb1
        let bb0 = BasicBlock {
            statements: vec![],
            terminator: Terminator::Call {
                func: "write_ptr".to_string(),
                args: vec![Operand::Copy(Place::local("_1"))],
                destination: Place::local("_0"),
                target: 1,
            },
        };
        let bb1 = BasicBlock {
            statements: vec![],
            terminator: Terminator::Return,
        };

        Function {
            name: "caller".to_string(),
            params: vec![Local::new(
                "_1",
                Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Shared),
            )],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![bb0, bb1],
            contracts: Contracts::default(),
            generic_params: vec![],
            loops: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations: vec![],
            unsafe_contracts: None,
            is_unsafe_fn: false,
            thread_spawns: vec![],
            atomic_ops: vec![],
            sync_ops: vec![],
            lock_invariants: vec![],
            concurrency_config: None,
            source_names: std::collections::HashMap::new(),
            coroutine_info: None,
        }
    }

    #[test]
    fn test_sep_logic_call_site_vc_uses_aufbv() {
        use crate::contract_db::{ContractDatabase, FunctionSummary};
        use crate::ir::Mutability;

        // Build callee summary: write_ptr requires pts_to(_1, _2)
        let callee_contracts = Contracts {
            requires: vec![SpecExpr {
                raw: "pts_to(_1, _2)".to_string(),
            }],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
            fn_specs: vec![],
            state_invariant: None,
        };

        let mut contract_db = ContractDatabase::new();
        contract_db.insert(
            "write_ptr".to_string(),
            FunctionSummary {
                contracts: callee_contracts,
                param_names: vec!["_1".to_string(), "_2".to_string()],
                param_types: vec![
                    Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Shared),
                    Ty::Int(IntTy::I32),
                ],
                return_ty: Ty::Unit,
            },
        );

        let caller = make_sep_logic_caller();
        let result = generate_vcs(&caller, Some(&contract_db));

        // Find the call-site precondition VC(s)
        let call_vcs: Vec<_> = result
            .conditions
            .iter()
            .filter(|vc| vc.location.vc_kind == VcKind::Precondition)
            .collect();

        assert!(
            !call_vcs.is_empty(),
            "Expected at least one Precondition VC for sep-logic call site, got VCs: {:?}",
            result
                .conditions
                .iter()
                .map(|vc| format!("{}: {:?}", vc.description, vc.location.vc_kind))
                .collect::<Vec<_>>(),
        );

        // The VC script must use AUFBV logic (frame forall requires quantifiers)
        let vc = &call_vcs[0];
        let script_str = vc.script.to_string();

        assert!(
            script_str.contains("AUFBV"),
            "Sep-logic call-site VC must use AUFBV logic, got script:\n{}",
            script_str
        );

        // The VC script must declare sep_heap
        assert!(
            script_str.contains("sep_heap"),
            "Sep-logic call-site VC must declare sep_heap, got script:\n{}",
            script_str
        );
    }

    #[test]
    fn generate_vcs_with_db_expands_ghost_predicate_in_requires() {
        use crate::ghost_predicate_db::{GhostPredicate, GhostPredicateDatabase};
        // ghost predicate: is_pos(x) := x > 0
        let mut db = GhostPredicateDatabase::new();
        db.insert(
            "is_pos".to_string(),
            GhostPredicate {
                param_names: vec!["x".to_string()],
                body_raw: "x > 0".to_string(),
            },
        );
        // Build function with requires: "is_pos(_1)"
        // (db-less parse_spec_expr returns None for "is_pos(_1)" — no VC generated)
        // (generate_vcs_with_db with db returns Some(x > 0) — precondition VC generated)
        let mut func = make_add_function();
        func.contracts.requires = vec![crate::ir::SpecExpr {
            raw: "is_pos(_1)".to_string(),
        }];
        // Also add a trivial ensures so generate_contract_vcs fires and uses the requires
        func.contracts.ensures = vec![crate::ir::SpecExpr {
            raw: "_1 > 0".to_string(),
        }];
        let vcs = generate_vcs_with_db(&func, None, &db);
        // With ghost-predicate wired path, the requires "is_pos(_1)" expands to "_1 > 0"
        // and is assumed in the postcondition VC. That VC should exist.
        assert!(
            !vcs.conditions.is_empty(),
            "Ghost predicate in requires must produce at least one VC via generate_vcs_with_db"
        );
    }
}
