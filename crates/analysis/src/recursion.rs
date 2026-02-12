//! Recursion analysis: termination checking and recursive function encoding.
//!
//! Provides three core capabilities:
//! 1. **Missing decreases detection**: Flag recursive functions without `#[decreases]`
//! 2. **Termination VC generation**: Prove decreases measure strictly decreases at each recursive call
//! 3. **Uninterpreted function encoding**: Encode recursive functions as SMT uninterpreted functions with axioms

use std::collections::HashMap;

use rust_fv_smtlib::command::Command;
use rust_fv_smtlib::script::Script;
use rust_fv_smtlib::sort::Sort;
use rust_fv_smtlib::term::Term;

use crate::call_graph::RecursiveGroup;
use crate::contract_db::ContractDatabase;
use crate::encode_sort::encode_type;
use crate::encode_term::encode_operand;
use crate::ir::*;
use crate::spec_parser;
use crate::vcgen::{VcKind, VcLocation, VerificationCondition};

/// Error indicating a recursive function is missing a `#[decreases]` annotation.
#[derive(Debug, Clone)]
pub struct MissingDecreasesError {
    /// Name of the function missing the annotation.
    pub function_name: String,
    /// Names of all functions in the recursive group (SCC).
    pub recursive_group: Vec<String>,
}

/// Check for recursive functions that are missing `#[decreases]` annotations.
///
/// For each recursive group, checks each function in the group. If a function
/// has no `contracts.decreases`, it is flagged as missing a termination measure.
pub fn check_missing_decreases(
    functions: &[(String, &Function)],
    recursive_groups: &[RecursiveGroup],
) -> Vec<MissingDecreasesError> {
    let func_map: HashMap<&str, &Function> =
        functions.iter().map(|(n, f)| (n.as_str(), *f)).collect();

    let mut errors = Vec::new();
    for group in recursive_groups {
        for func_name in &group.functions {
            if let Some(func) = func_map.get(func_name.as_str())
                && func.contracts.decreases.is_none()
            {
                errors.push(MissingDecreasesError {
                    function_name: func_name.clone(),
                    recursive_group: group.functions.clone(),
                });
            }
        }
    }
    errors
}

/// Generate termination verification conditions for a recursive function.
///
/// For each recursive call site in the function, generates a VC checking that
/// the decreases measure at the call site is strictly less than at function entry.
///
/// Returns empty Vec if:
/// - The function is not in any recursive group
/// - The function has no `#[decreases]` annotation (handled by `check_missing_decreases`)
pub fn generate_termination_vcs(
    func: &Function,
    recursive_groups: &[RecursiveGroup],
    _contract_db: Option<&ContractDatabase>,
) -> Vec<VerificationCondition> {
    // Check if this function is in any recursive group
    let group = recursive_groups.iter().find(|g| g.contains(&func.name));
    let group = match group {
        Some(g) => g,
        None => return Vec::new(),
    };

    // Check if the function has a decreases annotation
    let decreases = match &func.contracts.decreases {
        Some(d) => d,
        None => return Vec::new(),
    };

    // Parse the decreases expression to get the entry measure
    let entry_measure = match spec_parser::parse_spec_expr(&decreases.raw, func) {
        Some(term) => term,
        None => return Vec::new(),
    };

    let mut vcs = Vec::new();

    // Find recursive call sites: scan basic blocks for Call terminators
    // where the callee is in the same recursive group
    for (block_idx, bb) in func.basic_blocks.iter().enumerate() {
        if let Terminator::Call {
            func: callee_name,
            args,
            ..
        } = &bb.terminator
        {
            // Normalize callee name and check if it's in the recursive group
            let normalized = normalize_callee(callee_name);
            if !group.contains(&normalized) {
                continue;
            }

            // Build argument substitution: map formal parameter names to actual arguments
            let mut substitutions = HashMap::new();
            for (i, param) in func.params.iter().enumerate() {
                if let Some(arg) = args.get(i) {
                    substitutions.insert(param.name.clone(), encode_operand(arg));
                }
            }

            // Substitute into the decreases expression to get the call-site measure
            let call_measure = crate::vcgen::substitute_term(&entry_measure, &substitutions);

            // Build termination VC script
            let mut script = Script::new();
            script.push(Command::SetLogic("QF_BV".to_string()));
            script.push(Command::SetOption(
                "produce-models".to_string(),
                "true".to_string(),
            ));

            // Declare variables for function parameters
            for param in &func.params {
                let sort = encode_type(&param.ty);
                script.push(Command::DeclareConst(param.name.clone(), sort));
            }

            // Assume preconditions
            for pre in &func.contracts.requires {
                if let Some(pre_term) = spec_parser::parse_spec_expr(&pre.raw, func) {
                    script.push(Command::Assert(pre_term));
                }
            }

            // Assert NOT (call_measure < entry_measure)
            // If UNSAT: measure strictly decreases (good)
            // If SAT: counterexample shows non-decreasing case (bad)
            let measure_decreases = build_less_than(&call_measure, &entry_measure, func);
            script.push(Command::Comment(format!(
                "Termination: decreases measure at call to {} must be less than at entry",
                normalized
            )));
            script.push(Command::Assert(Term::Not(Box::new(measure_decreases))));
            script.push(Command::CheckSat);
            script.push(Command::GetModel);

            vcs.push(VerificationCondition {
                description: format!(
                    "{}: termination measure decreases at call to {} in block {}",
                    func.name, normalized, block_idx,
                ),
                script,
                location: VcLocation {
                    function: func.name.clone(),
                    block: block_idx,
                    statement: 0,
                    source_file: None,
                    source_line: None,
                    contract_text: Some(decreases.raw.clone()),
                    vc_kind: VcKind::Termination,
                },
            });
        }
    }

    vcs
}

/// Encode a recursive function as an uninterpreted SMT function with axioms.
///
/// Declares `(declare-fun {name}_uninterp ({param_sorts}...) {return_sort})`
/// and generates axioms for base and recursive cases by analyzing the function's
/// basic blocks.
///
/// Returns a list of SMT commands to add to any script that uses this function.
pub fn encode_recursive_function(func: &Function) -> Vec<Command> {
    let mut commands = Vec::new();

    let uninterp_name = format!("{}_uninterp", func.name);

    // Declare uninterpreted function
    let param_sorts: Vec<Sort> = func.params.iter().map(|p| encode_type(&p.ty)).collect();
    let return_sort = encode_type(&func.return_local.ty);

    commands.push(Command::DeclareFun(
        uninterp_name.clone(),
        param_sorts.clone(),
        return_sort.clone(),
    ));

    // Analyze basic blocks to generate axioms
    // We look for SwitchInt patterns to identify base vs recursive cases
    if func.basic_blocks.is_empty() {
        return commands;
    }

    // Simple pattern: first block has SwitchInt -> base case and recursive case
    let first_block = &func.basic_blocks[0];

    if let Terminator::SwitchInt {
        discr,
        targets,
        otherwise,
    } = &first_block.terminator
    {
        let discr_term = encode_operand(discr);

        // For each target: determine if it's a base case or recursive case
        for &(value, target_block) in targets {
            if target_block < func.basic_blocks.len() {
                let target_bb = &func.basic_blocks[target_block];
                let is_recursive = is_block_recursive(target_bb, &func.name);

                let branch_cond = build_switch_condition(&discr_term, value, func, discr);

                if !is_recursive {
                    // Base case: encode as axiom
                    if let Some(return_val) = extract_return_value(target_bb) {
                        let axiom = build_case_axiom(
                            &uninterp_name,
                            &func.params,
                            &param_sorts,
                            &branch_cond,
                            &return_val,
                        );
                        commands.push(Command::Assert(axiom));
                    }
                } else {
                    // Recursive case: encode with uninterpreted function call
                    if let Some(return_expr) =
                        extract_recursive_return(target_bb, &func.name, &uninterp_name, func)
                    {
                        let axiom = build_case_axiom(
                            &uninterp_name,
                            &func.params,
                            &param_sorts,
                            &Term::Not(Box::new(branch_cond.clone())),
                            &return_expr,
                        );
                        commands.push(Command::Assert(axiom));
                    }
                }
            }
        }

        // Handle the otherwise branch
        if *otherwise < func.basic_blocks.len() {
            let otherwise_bb = &func.basic_blocks[*otherwise];
            let is_recursive = is_block_recursive(otherwise_bb, &func.name);

            // Otherwise condition = negation of all explicit branch conditions
            let mut taken_conds = Vec::new();
            for &(value, _) in targets {
                taken_conds.push(build_switch_condition(&discr_term, value, func, discr));
            }
            let otherwise_cond = if taken_conds.len() == 1 {
                Term::Not(Box::new(taken_conds.into_iter().next().unwrap()))
            } else {
                Term::Not(Box::new(Term::Or(taken_conds)))
            };

            if !is_recursive {
                if let Some(return_val) = extract_return_value(otherwise_bb) {
                    let axiom = build_case_axiom(
                        &uninterp_name,
                        &func.params,
                        &param_sorts,
                        &otherwise_cond,
                        &return_val,
                    );
                    commands.push(Command::Assert(axiom));
                }
            } else {
                if let Some(return_expr) =
                    extract_recursive_return(otherwise_bb, &func.name, &uninterp_name, func)
                {
                    let axiom = build_case_axiom(
                        &uninterp_name,
                        &func.params,
                        &param_sorts,
                        &otherwise_cond,
                        &return_expr,
                    );
                    commands.push(Command::Assert(axiom));
                }
            }
        }
    }

    commands
}

// === Internal helpers ===

/// Normalize a callee function name (strip "const " prefix and path segments).
fn normalize_callee(raw: &str) -> String {
    let trimmed = raw.trim();
    let stripped = trimmed.strip_prefix("const ").unwrap_or(trimmed).trim();
    stripped
        .rsplit_once("::")
        .map(|(_, name)| name)
        .unwrap_or(stripped)
        .to_string()
}

/// Build a less-than comparison appropriate for the function's parameter types.
fn build_less_than(lhs: &Term, rhs: &Term, func: &Function) -> Term {
    // Determine if we should use signed or unsigned comparison
    // based on the first parameter type (decreases measure type)
    let is_signed = func
        .params
        .first()
        .map(|p| p.ty.is_signed())
        .unwrap_or(true);

    if is_signed {
        Term::BvSLt(Box::new(lhs.clone()), Box::new(rhs.clone()))
    } else {
        Term::BvULt(Box::new(lhs.clone()), Box::new(rhs.clone()))
    }
}

/// Build a switch condition: discr == value.
fn build_switch_condition(
    discr_term: &Term,
    value: i128,
    func: &Function,
    discr: &Operand,
) -> Term {
    match discr {
        Operand::Copy(place) | Operand::Move(place) => {
            let discr_ty = func
                .params
                .iter()
                .chain(func.locals.iter())
                .chain(std::iter::once(&func.return_local))
                .find(|l| l.name == place.local)
                .map(|l| &l.ty);

            match discr_ty {
                Some(Ty::Bool) => {
                    if value == 1 {
                        discr_term.clone()
                    } else {
                        Term::Not(Box::new(discr_term.clone()))
                    }
                }
                Some(ty) => {
                    let width = ty.bit_width().unwrap_or(32);
                    Term::Eq(
                        Box::new(discr_term.clone()),
                        Box::new(Term::BitVecLit(value, width)),
                    )
                }
                None => {
                    if value == 1 {
                        discr_term.clone()
                    } else {
                        Term::Not(Box::new(discr_term.clone()))
                    }
                }
            }
        }
        Operand::Constant(_) => Term::Eq(
            Box::new(discr_term.clone()),
            Box::new(Term::BitVecLit(value, 32)),
        ),
    }
}

/// Check if a basic block contains a recursive call to the given function.
fn is_block_recursive(bb: &BasicBlock, func_name: &str) -> bool {
    if let Terminator::Call { func, .. } = &bb.terminator {
        let normalized = normalize_callee(func);
        normalized == func_name
    } else {
        false
    }
}

/// Extract the return value from a base case block (block that assigns to _0 and returns).
fn extract_return_value(bb: &BasicBlock) -> Option<Term> {
    for stmt in &bb.statements {
        if let Statement::Assign(place, rvalue) = stmt
            && place.local == "_0"
        {
            return match rvalue {
                Rvalue::Use(op) => Some(encode_operand(op)),
                Rvalue::BinaryOp(op, lhs, rhs) => {
                    let l = encode_operand(lhs);
                    let r = encode_operand(rhs);
                    Some(encode_binop_term(*op, l, r))
                }
                _ => None,
            };
        }
    }
    None
}

/// Extract the return expression from a recursive case block,
/// replacing recursive calls with the uninterpreted function.
fn extract_recursive_return(
    bb: &BasicBlock,
    func_name: &str,
    uninterp_name: &str,
    func: &Function,
) -> Option<Term> {
    // Look for a call to the recursive function
    if let Terminator::Call {
        func: callee,
        args,
        destination,
        target,
    } = &bb.terminator
    {
        let normalized = normalize_callee(callee);
        if normalized == func_name {
            // Encode the call using the uninterpreted function
            let arg_terms: Vec<Term> = args.iter().map(encode_operand).collect();
            let call_result = Term::App(uninterp_name.to_string(), arg_terms);

            // Check the target block for how the result is used
            if *target < func.basic_blocks.len() {
                let target_bb = &func.basic_blocks[*target];
                // Look for _0 = expr using the destination
                for stmt in &target_bb.statements {
                    if let Statement::Assign(place, rvalue) = stmt
                        && place.local == "_0"
                    {
                        // Replace the destination with the call result
                        let mut subs = HashMap::new();
                        subs.insert(destination.local.clone(), call_result.clone());
                        return Some(substitute_in_rvalue(rvalue, &subs));
                    }
                }
            }

            // If the destination is _0 directly, the call result IS the return value
            if destination.local == "_0" {
                return Some(call_result);
            }
        }
    }
    None
}

/// Substitute named constants in an Rvalue.
fn substitute_in_rvalue(rvalue: &Rvalue, subs: &HashMap<String, Term>) -> Term {
    match rvalue {
        Rvalue::Use(op) => {
            let t = encode_operand(op);
            crate::vcgen::substitute_term(&t, subs)
        }
        Rvalue::BinaryOp(op, lhs, rhs) => {
            let l = encode_operand(lhs);
            let r = encode_operand(rhs);
            let l_sub = crate::vcgen::substitute_term(&l, subs);
            let r_sub = crate::vcgen::substitute_term(&r, subs);
            encode_binop_term(*op, l_sub, r_sub)
        }
        _ => Term::Const("unknown".to_string()),
    }
}

/// Encode a binary operation as a Term (using bitvector operations).
fn encode_binop_term(op: BinOp, lhs: Term, rhs: Term) -> Term {
    let l = Box::new(lhs);
    let r = Box::new(rhs);
    match op {
        BinOp::Add => Term::BvAdd(l, r),
        BinOp::Sub => Term::BvSub(l, r),
        BinOp::Mul => Term::BvMul(l, r),
        BinOp::Div => Term::BvSDiv(l, r),
        BinOp::Rem => Term::BvSRem(l, r),
        BinOp::Eq => Term::Eq(l, r),
        BinOp::Ne => Term::Not(Box::new(Term::Eq(l, r))),
        BinOp::Lt => Term::BvSLt(l, r),
        BinOp::Le => Term::BvSLe(l, r),
        BinOp::Gt => Term::BvSGt(l, r),
        BinOp::Ge => Term::BvSGe(l, r),
        BinOp::BitAnd => Term::BvAnd(l, r),
        BinOp::BitOr => Term::BvOr(l, r),
        BinOp::BitXor => Term::BvXor(l, r),
        BinOp::Shl => Term::BvShl(l, r),
        BinOp::Shr => Term::BvAShr(l, r),
    }
}

/// Build a universally quantified axiom for a function case.
///
/// `(assert (forall ((params...)) (=> condition (= (func params) value))))`
fn build_case_axiom(
    func_name: &str,
    params: &[Local],
    param_sorts: &[Sort],
    condition: &Term,
    return_value: &Term,
) -> Term {
    let bound_vars: Vec<(String, Sort)> = params
        .iter()
        .zip(param_sorts.iter())
        .map(|(p, s)| (p.name.clone(), s.clone()))
        .collect();

    let param_terms: Vec<Term> = params.iter().map(|p| Term::Const(p.name.clone())).collect();

    let func_app = Term::App(func_name.to_string(), param_terms);
    let equality = Term::Eq(Box::new(func_app), Box::new(return_value.clone()));
    let implication = Term::Implies(Box::new(condition.clone()), Box::new(equality));

    Term::Forall(bound_vars, Box::new(implication))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::call_graph::CallGraph;
    use crate::ir::{
        BasicBlock, Contracts, Function, IntTy, Local, Operand, Place, Rvalue, SpecExpr, Statement,
        Terminator, Ty,
    };

    /// Helper: create a minimal function with given basic blocks and contracts.
    fn make_function(
        name: &str,
        params: Vec<Local>,
        basic_blocks: Vec<BasicBlock>,
        contracts: Contracts,
    ) -> Function {
        Function {
            name: name.to_string(),
            params,
            return_local: Local::new("_0", Ty::Int(IntTy::I32)),
            locals: vec![],
            basic_blocks,
            contracts,
            loops: vec![],
            generic_params: vec![],
            prophecies: vec![],
        }
    }

    /// Helper: create a basic block with a Call terminator to the given function.
    fn call_block(
        callee: &str,
        args: Vec<Operand>,
        destination: Place,
        target: usize,
    ) -> BasicBlock {
        BasicBlock {
            statements: vec![],
            terminator: Terminator::Call {
                func: callee.to_string(),
                args,
                destination,
                target,
            },
        }
    }

    /// Helper: create a return block that assigns a value to _0.
    fn return_block_with_assign(rvalue: Rvalue) -> BasicBlock {
        BasicBlock {
            statements: vec![Statement::Assign(Place::local("_0"), rvalue)],
            terminator: Terminator::Return,
        }
    }

    /// Helper: build a factorial-like function with optional decreases and requires.
    fn make_factorial(decreases: Option<&str>, requires: Vec<&str>) -> Function {
        let params = vec![Local::new("_1", Ty::Int(IntTy::I32))];
        let contracts = Contracts {
            requires: requires
                .iter()
                .map(|r| SpecExpr { raw: r.to_string() })
                .collect(),
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: decreases.map(|d| SpecExpr { raw: d.to_string() }),
        };

        // bb0: branch on _1 <= 1
        // bb1 (base): _0 = 1; return
        // bb2 (recursive): call factorial(_1 - 1); jump to bb3
        // bb3: _0 = _1 * call_result; return
        let locals = vec![
            Local::new("_2", Ty::Bool),            // condition result
            Local::new("_3", Ty::Int(IntTy::I32)), // call result
        ];

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
                targets: vec![(1, 1)], // true -> bb1 (base case)
                otherwise: 2,          // false -> bb2 (recursive case)
            },
        };

        let bb1 =
            return_block_with_assign(Rvalue::Use(Operand::Constant(Constant::Int(1, IntTy::I32))));

        let bb2 = BasicBlock {
            statements: vec![],
            terminator: Terminator::Call {
                func: "factorial".to_string(),
                args: vec![Operand::Copy(Place::local("_1"))], // simplified: _1 instead of _1 - 1 for test structure
                destination: Place::local("_3"),
                target: 3,
            },
        };

        // For the actual recursive arg substitution test, we need the actual arg to be _1 - 1
        // but since encode_operand on Copy just gives Const("_1"), the substitution
        // in generate_termination_vcs maps _1 to the actual argument operand.
        // We use a simpler approach: the arg is Copy(_1) in the call, but the test
        // checks that the VC is generated with the right structure.

        let bb3 = return_block_with_assign(Rvalue::BinaryOp(
            BinOp::Mul,
            Operand::Copy(Place::local("_1")),
            Operand::Copy(Place::local("_3")),
        ));

        Function {
            name: "factorial".to_string(),
            params,
            return_local: Local::new("_0", Ty::Int(IntTy::I32)),
            locals,
            basic_blocks: vec![bb0, bb1, bb2, bb3],
            contracts,
            loops: vec![],
            generic_params: vec![],
            prophecies: vec![],
        }
    }

    /// Helper: build a fibonacci-like function with two recursive calls.
    fn make_fibonacci(decreases: Option<&str>) -> Function {
        let params = vec![Local::new("_1", Ty::Int(IntTy::I32))];
        let contracts = Contracts {
            decreases: decreases.map(|d| SpecExpr { raw: d.to_string() }),
            ..Default::default()
        };

        let locals = vec![
            Local::new("_2", Ty::Bool),
            Local::new("_3", Ty::Int(IntTy::I32)),
            Local::new("_4", Ty::Int(IntTy::I32)),
        ];

        // bb0: branch on _1 <= 1
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

        // bb1 (base): _0 = _1; return
        let bb1 = return_block_with_assign(Rvalue::Use(Operand::Copy(Place::local("_1"))));

        // bb2 (first recursive call): call fibonacci(_1); destination = _3; target = bb3
        let bb2 = BasicBlock {
            statements: vec![],
            terminator: Terminator::Call {
                func: "fibonacci".to_string(),
                args: vec![Operand::Copy(Place::local("_1"))],
                destination: Place::local("_3"),
                target: 3,
            },
        };

        // bb3 (second recursive call): call fibonacci(_1); destination = _4; target = bb4
        let bb3 = BasicBlock {
            statements: vec![],
            terminator: Terminator::Call {
                func: "fibonacci".to_string(),
                args: vec![Operand::Copy(Place::local("_1"))],
                destination: Place::local("_4"),
                target: 4,
            },
        };

        // bb4: _0 = _3 + _4; return
        let bb4 = return_block_with_assign(Rvalue::BinaryOp(
            BinOp::Add,
            Operand::Copy(Place::local("_3")),
            Operand::Copy(Place::local("_4")),
        ));

        Function {
            name: "fibonacci".to_string(),
            params,
            return_local: Local::new("_0", Ty::Int(IntTy::I32)),
            locals,
            basic_blocks: vec![bb0, bb1, bb2, bb3, bb4],
            contracts,
            loops: vec![],
            generic_params: vec![],
            prophecies: vec![],
        }
    }

    // ====== check_missing_decreases tests ======

    #[test]
    fn test_check_missing_decreases_flags_recursive_without_decreases() {
        let factorial = make_factorial(None, vec![]);
        let funcs = vec![("factorial".to_string(), &factorial)];
        let cg = CallGraph::from_functions(&funcs);
        let groups = cg.detect_recursion();

        let errors = check_missing_decreases(&funcs, &groups);
        assert_eq!(errors.len(), 1);
        assert_eq!(errors[0].function_name, "factorial");
    }

    #[test]
    fn test_check_missing_decreases_ok_with_decreases() {
        let factorial = make_factorial(Some("_1"), vec![]);
        let funcs = vec![("factorial".to_string(), &factorial)];
        let cg = CallGraph::from_functions(&funcs);
        let groups = cg.detect_recursion();

        let errors = check_missing_decreases(&funcs, &groups);
        assert_eq!(errors.len(), 0);
    }

    #[test]
    fn test_check_missing_decreases_mutual_both_missing() {
        // Build even and odd functions calling each other, both without decreases
        let even_params = vec![Local::new("_1", Ty::Int(IntTy::I32))];
        let even = make_function(
            "even",
            even_params,
            vec![
                call_block(
                    "odd",
                    vec![Operand::Copy(Place::local("_1"))],
                    Place::local("_0"),
                    1,
                ),
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
            ],
            Contracts::default(),
        );

        let odd_params = vec![Local::new("_1", Ty::Int(IntTy::I32))];
        let odd = make_function(
            "odd",
            odd_params,
            vec![
                call_block(
                    "even",
                    vec![Operand::Copy(Place::local("_1"))],
                    Place::local("_0"),
                    1,
                ),
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
            ],
            Contracts::default(),
        );

        let funcs = vec![("even".to_string(), &even), ("odd".to_string(), &odd)];
        let cg = CallGraph::from_functions(&funcs);
        let groups = cg.detect_recursion();

        let errors = check_missing_decreases(&funcs, &groups);
        assert_eq!(errors.len(), 2, "Both even and odd should be flagged");
    }

    // ====== generate_termination_vcs tests ======

    #[test]
    fn test_generate_termination_vcs_factorial() {
        let factorial = make_factorial(Some("_1"), vec!["_1 >= 0"]);

        let funcs = vec![("factorial".to_string(), &factorial)];
        let cg = CallGraph::from_functions(&funcs);
        let groups = cg.detect_recursion();

        let vcs = generate_termination_vcs(&factorial, &groups, None);

        // One recursive call site -> one termination VC
        assert_eq!(vcs.len(), 1, "Expected 1 termination VC, got {}", vcs.len());
        assert!(
            vcs[0].description.contains("termination"),
            "VC description should mention termination: {}",
            vcs[0].description
        );
        assert_eq!(vcs[0].location.vc_kind, VcKind::Termination);
    }

    #[test]
    fn test_generate_termination_vcs_two_recursive_calls() {
        let fibonacci = make_fibonacci(Some("_1"));

        let funcs = vec![("fibonacci".to_string(), &fibonacci)];
        let cg = CallGraph::from_functions(&funcs);
        let groups = cg.detect_recursion();

        let vcs = generate_termination_vcs(&fibonacci, &groups, None);

        // Two recursive call sites -> two termination VCs
        assert_eq!(
            vcs.len(),
            2,
            "Expected 2 termination VCs for fibonacci, got {}",
            vcs.len()
        );
        for vc in &vcs {
            assert_eq!(vc.location.vc_kind, VcKind::Termination);
        }
    }

    #[test]
    fn test_generate_termination_vcs_no_decreases_returns_empty() {
        let factorial = make_factorial(None, vec![]);

        let funcs = vec![("factorial".to_string(), &factorial)];
        let cg = CallGraph::from_functions(&funcs);
        let groups = cg.detect_recursion();

        let vcs = generate_termination_vcs(&factorial, &groups, None);
        assert!(
            vcs.is_empty(),
            "Should return empty when no decreases annotation"
        );
    }

    #[test]
    fn test_generate_termination_vcs_non_recursive_returns_empty() {
        // Non-recursive function with decreases annotation
        let params = vec![Local::new("_1", Ty::Int(IntTy::I32))];
        let contracts = Contracts {
            decreases: Some(SpecExpr {
                raw: "_1".to_string(),
            }),
            ..Default::default()
        };

        let func = make_function(
            "not_recursive",
            params,
            vec![return_block_with_assign(Rvalue::Use(Operand::Copy(
                Place::local("_1"),
            )))],
            contracts,
        );

        // No recursion detected
        let groups: Vec<RecursiveGroup> = vec![];
        let vcs = generate_termination_vcs(&func, &groups, None);
        assert!(
            vcs.is_empty(),
            "Should return empty for non-recursive function"
        );
    }
}
