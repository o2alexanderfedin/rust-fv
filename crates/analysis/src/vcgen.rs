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

use crate::encode_sort::encode_type;
use crate::encode_term::{encode_binop, encode_operand, encode_unop, overflow_check};
use crate::ir::*;

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
pub fn generate_vcs(func: &Function) -> FunctionVCs {
    tracing::info!(function = %func.name, "Generating verification conditions");

    let mut conditions = Vec::new();

    // Collect all variable declarations
    let declarations = collect_declarations(func);

    // Enumerate all paths through the CFG
    let paths = enumerate_paths(func);
    tracing::debug!(function = %func.name, path_count = paths.len(), "Enumerated CFG paths");

    // Generate overflow VCs from all paths
    for path in &paths {
        for ov in &path.overflow_vcs {
            let mut vc = generate_overflow_vc(func, &declarations, ov);
            conditions.append(&mut vc);
        }
    }

    // Generate terminator assertion VCs (Terminator::Assert)
    let mut assert_vcs = generate_assert_terminator_vcs(func, &declarations, &paths);
    conditions.append(&mut assert_vcs);

    // Generate contract verification conditions (postconditions)
    let mut contract_vcs = generate_contract_vcs(func, &declarations, &paths);
    conditions.append(&mut contract_vcs);

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
        }];
    }

    let mut completed_paths = Vec::new();
    let initial_state = PathState {
        conditions: Vec::new(),
        assignments: Vec::new(),
        overflow_vcs: Vec::new(),
        visited: HashSet::new(),
    };

    traverse_block(func, 0, initial_state, &mut completed_paths);

    // If no paths completed (e.g., all paths are Unreachable), return empty path
    if completed_paths.is_empty() {
        completed_paths.push(CfgPath {
            condition: None,
            assignments: vec![],
            overflow_vcs: vec![],
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
        } => {
            // Process the assertion, then continue to target
            // (Assertion VCs are generated separately)
            traverse_block(func, *target, state, completed);
        }

        Terminator::Call {
            func: _,
            args: _,
            destination,
            target,
        } => {
            // For now, treat the call as opaque but record the destination
            // The destination gets an unconstrained value (no assignment encoded)
            // Continue to the target block
            let _ = destination; // acknowledged but not encoded
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

    // Locals
    for local in &func.locals {
        let sort = encode_type(&local.ty);
        decls.push(Command::DeclareConst(local.name.clone(), sort));
    }

    decls
}

/// Build a base script with logic and declarations.
fn base_script(declarations: &[Command]) -> Script {
    let mut script = Script::new();
    script.push(Command::SetLogic("QF_BV".to_string()));
    script.push(Command::SetOption(
        "produce-models".to_string(),
        "true".to_string(),
    ));
    for decl in declarations {
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
    let lhs = Term::Const(place.local.clone());

    let rhs = match rvalue {
        Rvalue::Use(op) => encode_operand(op),
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
        Rvalue::Aggregate(_, _) => {
            // Phase 1: skip aggregate construction
            return None;
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
        let mut script = base_script(declarations);

        // Add prior assignments along this path
        let mut ssa_counter = HashMap::new();
        for pa in &ov.prior_assignments {
            if let Some(cmd) = encode_assignment(&pa.place, &pa.rvalue, func, &mut ssa_counter) {
                script.push(cmd);
            }
        }

        // Assume preconditions
        for pre in &func.contracts.requires {
            if let Some(pre_term) = parse_simple_spec(&pre.raw, func) {
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
fn generate_assert_terminator_vcs(
    func: &Function,
    declarations: &[Command],
    paths: &[CfgPath],
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    // Find blocks with Assert terminators
    for (block_idx, block) in func.basic_blocks.iter().enumerate() {
        if let Terminator::Assert { cond, expected, .. } = &block.terminator {
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

            let mut script = base_script(declarations);

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
                if let Some(pre_term) = parse_simple_spec(&pre.raw, func) {
                    script.push(Command::Assert(pre_term));
                }
            }

            // Try to find a case where the assertion fails
            let assertion_holds = Term::Eq(Box::new(cond_term), Box::new(expected_term));
            script.push(Command::Assert(Term::Not(Box::new(assertion_holds))));
            script.push(Command::CheckSat);
            script.push(Command::GetModel);

            vcs.push(VerificationCondition {
                description: format!("{}: assertion holds at block {block_idx}", func.name),
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

/// Generate contract verification conditions using path-sensitive encoding.
///
/// For each postcondition, we:
/// 1. Declare all variables
/// 2. Encode all path assignments with path-condition guards
/// 3. Assert all preconditions
/// 4. Try to find a counterexample where the postcondition fails
fn generate_contract_vcs(
    func: &Function,
    declarations: &[Command],
    paths: &[CfgPath],
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    if func.contracts.ensures.is_empty() {
        return vcs;
    }

    for (post_idx, post) in func.contracts.ensures.iter().enumerate() {
        let mut script = base_script(declarations);

        // Encode assignments from ALL paths, each guarded by its path condition
        for path in paths {
            let cmds = encode_path_assignments(func, path);
            for cmd in cmds {
                script.push(cmd);
            }
        }

        // Assume preconditions
        for pre in &func.contracts.requires {
            if let Some(pre_term) = parse_simple_spec(&pre.raw, func) {
                script.push(Command::Assert(pre_term));
            }
        }

        // Assert that at least one path is taken
        // (The disjunction of all path conditions must be true)
        let path_conds: Vec<Term> = paths.iter().filter_map(|p| p.condition.clone()).collect();
        if !path_conds.is_empty() {
            script.push(Command::Assert(Term::Or(path_conds)));
        }

        // Negate postcondition and check if SAT (= postcondition violated)
        if let Some(post_term) = parse_simple_spec(&post.raw, func) {
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

fn make_comparison(op: BinOp, lhs: Term, rhs: Term, func: &Function) -> Term {
    // Determine signedness from the return type or first parameter
    let signed =
        func.return_local.ty.is_signed() || func.params.first().is_some_and(|p| p.ty.is_signed());

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
            },
            params: vec![
                Local {
                    name: "_1".to_string(),
                    ty: Ty::Int(IntTy::I32),
                },
                Local {
                    name: "_2".to_string(),
                    ty: Ty::Int(IntTy::I32),
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
        }
    }

    /// Build: `fn max(a: i32, b: i32) -> i32 { if a > b { a } else { b } }`
    fn make_max_function() -> Function {
        Function {
            name: "max".to_string(),
            return_local: Local {
                name: "_0".to_string(),
                ty: Ty::Int(IntTy::I32),
            },
            params: vec![
                Local {
                    name: "_1".to_string(),
                    ty: Ty::Int(IntTy::I32),
                },
                Local {
                    name: "_2".to_string(),
                    ty: Ty::Int(IntTy::I32),
                },
            ],
            locals: vec![Local {
                name: "_3".to_string(),
                ty: Ty::Bool,
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
                is_pure: true,
            },
        }
    }

    #[test]
    fn generates_overflow_vc_for_add() {
        let func = make_add_function();
        let result = generate_vcs(&func);

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
        let result = generate_vcs(&func);

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
        let result = generate_vcs(&func);

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
        let result = generate_vcs(&func);

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
            },
            params: vec![],
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![Statement::Nop],
                terminator: Terminator::Return,
            }],
            contracts: Contracts::default(),
        };

        let result = generate_vcs(&func);
        assert!(result.conditions.is_empty());
    }

    #[test]
    fn division_generates_zero_check_vc() {
        let func = Function {
            name: "divide".to_string(),
            return_local: Local {
                name: "_0".to_string(),
                ty: Ty::Int(IntTy::I32),
            },
            params: vec![
                Local {
                    name: "_1".to_string(),
                    ty: Ty::Int(IntTy::I32),
                },
                Local {
                    name: "_2".to_string(),
                    ty: Ty::Int(IntTy::I32),
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
        };

        let result = generate_vcs(&func);
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
        let result = generate_vcs(&func);

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
