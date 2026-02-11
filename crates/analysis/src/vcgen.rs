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
use crate::ir::*;
use crate::ownership::{OwnershipConstraint, classify_argument, generate_ownership_constraints};
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
pub fn generate_vcs(func: &Function, contract_db: Option<&ContractDatabase>) -> FunctionVCs {
    tracing::info!(function = %func.name, "Generating verification conditions");

    let mut conditions = Vec::new();

    // Collect datatype declarations (must come before variable declarations)
    let datatype_declarations = collect_datatype_declarations(func);

    // Collect all variable declarations
    let declarations = collect_declarations(func);

    // Enumerate all paths through the CFG
    let paths = enumerate_paths(func);
    tracing::debug!(function = %func.name, path_count = paths.len(), "Enumerated CFG paths");

    // Generate overflow VCs from all paths
    for path in &paths {
        for ov in &path.overflow_vcs {
            let mut vc = generate_overflow_vc(func, &datatype_declarations, &declarations, ov);
            conditions.append(&mut vc);
        }
    }

    // Generate terminator assertion VCs (Terminator::Assert)
    let mut assert_vcs =
        generate_assert_terminator_vcs(func, &datatype_declarations, &declarations, &paths);
    conditions.append(&mut assert_vcs);

    // Generate contract verification conditions (postconditions)
    // When contract_db is provided, callee postconditions are assumed during
    // the caller's postcondition check.
    let mut contract_vcs = generate_contract_vcs(
        func,
        &datatype_declarations,
        &declarations,
        &paths,
        contract_db,
    );
    conditions.append(&mut contract_vcs);

    // Generate call-site precondition VCs (inter-procedural)
    if let Some(db) = contract_db {
        let mut call_vcs =
            generate_call_site_vcs(func, db, &datatype_declarations, &declarations, &paths);
        conditions.append(&mut call_vcs);
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
            let mut loop_vcs =
                generate_loop_invariant_vcs(func, &datatype_declarations, &declarations, loop_info);
            conditions.append(&mut loop_vcs);
        }
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

    decls
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
        Rvalue::Len(_) => {
            // Array length -- represented as an uninterpreted constant for now
            return None;
        }
        Rvalue::Cast(_, op, _) => {
            // Phase 1: casts are identity (TODO: proper cast encoding)
            encode_operand(op)
        }
        Rvalue::Aggregate(kind, operands) => {
            let result_ty = find_local_type(func, &place.local);
            if let Some(ty) = result_ty {
                encode_aggregate_with_type(kind, operands, ty)?
            } else {
                return None;
            }
        }
        Rvalue::Discriminant(_) => {
            // Phase 1: skip discriminant
            return None;
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
            if let Some(pre_term) = parse_spec(&pre.raw, func) {
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
                if let Some(pre_term) = parse_spec(&pre.raw, func) {
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
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    if func.contracts.ensures.is_empty() {
        return vcs;
    }

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
        }

        // Assume preconditions
        for pre in &func.contracts.requires {
            if let Some(pre_term) = parse_spec(&pre.raw, func) {
                script.push(Command::Assert(pre_term));
            }
        }

        // Assume callee postconditions at call sites (inter-procedural)
        if let Some(db) = contract_db {
            for path in paths {
                for call_site in &path.call_sites {
                    encode_callee_postcondition_assumptions(func, db, call_site, &mut script);
                }
            }
        }

        // Assert that at least one path is taken
        // (The disjunction of all path conditions must be true)
        let path_conds: Vec<Term> = paths.iter().filter_map(|p| p.condition.clone()).collect();
        if !path_conds.is_empty() {
            script.push(Command::Assert(Term::Or(path_conds)));
        }

        // Negate postcondition and check if SAT (= postcondition violated)
        if let Some(post_term) = parse_spec(&post.raw, func) {
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
                let pre_term = match parse_spec(&pre.raw, &callee_func_context) {
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
                    if let Some(caller_pre_term) = parse_spec(&caller_pre.raw, func) {
                        script.push(Command::Assert(caller_pre_term));
                    }
                }

                // If there's a path condition, assume it
                if let Some(ref cond) = call_site.path_condition {
                    script.push(Command::Assert(cond.clone()));
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
        if let Some(post_term) = parse_spec(&post.raw, &callee_func_context) {
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
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();
    let header = loop_info.header_block;

    // Parse all invariants
    let parsed_invariants: Vec<Term> = loop_info
        .invariants
        .iter()
        .filter_map(|inv| parse_spec(&inv.raw, func))
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
            if let Some(pre_term) = parse_spec(&pre.raw, func) {
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
            if let Some(pre_term) = parse_spec(&pre.raw, func) {
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
            },
        });
    }

    // === VC3: Exit / Sufficiency ===
    // Invariant + header stmts + NOT loop condition + post-loop => postcondition
    {
        for (post_idx, post) in func.contracts.ensures.iter().enumerate() {
            if let Some(post_term) = parse_spec(&post.raw, func) {
                let mut script = base_script(
                    datatype_declarations,
                    declarations,
                    uses_spec_int_types(func),
                );

                // Assume invariant holds
                script.push(Command::Assert(invariant.clone()));

                // Assume preconditions
                for pre in &func.contracts.requires {
                    if let Some(pre_term) = parse_spec(&pre.raw, func) {
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
fn parse_spec(spec: &str, func: &Function) -> Option<Term> {
    let term =
        spec_parser::parse_spec_expr(spec, func).or_else(|| parse_simple_spec(spec, func))?;

    // Annotate quantifiers with trigger patterns
    Some(crate::encode_quantifier::annotate_quantifier(term))
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
            },
            generic_params: vec![],
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
}
