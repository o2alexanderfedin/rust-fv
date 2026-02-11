use rustc_hir::def_id::LocalDefId;
/// Convert `rustc` MIR to our verification IR.
///
/// This is the thin translation layer between the compiler's internal
/// representation and our stable, testable IR. When `rustc` internals
/// change, only this module needs updating.
use rustc_middle::mir;
use rustc_middle::ty::{self, TyCtxt};

use rust_fv_analysis::ir;

/// Convert a rustc MIR body to our IR Function.
pub fn convert_mir(
    tcx: TyCtxt<'_>,
    local_def_id: LocalDefId,
    body: &mir::Body<'_>,
    contracts: ir::Contracts,
) -> ir::Function {
    let def_id = local_def_id.to_def_id();
    let name = tcx.def_path_str(def_id);

    // Convert return type (local _0)
    let return_ty = convert_ty(body.local_decls[mir::Local::ZERO].ty);
    let return_local = ir::Local {
        name: "_0".to_string(),
        ty: return_ty,
        is_ghost: false,
    };

    // Convert parameters
    let params: Vec<ir::Local> = body
        .args_iter()
        .map(|local| {
            let decl = &body.local_decls[local];
            ir::Local {
                name: format!("_{}", local.as_usize()),
                ty: convert_ty(decl.ty),
                is_ghost: false,
            }
        })
        .collect();

    // Convert other locals (temporaries)
    let locals: Vec<ir::Local> = body
        .vars_and_temps_iter()
        .map(|local| {
            let decl = &body.local_decls[local];
            ir::Local {
                name: format!("_{}", local.as_usize()),
                ty: convert_ty(decl.ty),
                is_ghost: false,
            }
        })
        .collect();

    // Convert basic blocks
    let basic_blocks: Vec<ir::BasicBlock> = body
        .basic_blocks
        .iter()
        .map(|bb| convert_basic_block(bb))
        .collect();

    ir::Function {
        name,
        params,
        return_local,
        locals,
        basic_blocks,
        contracts,
        loops: vec![],
        generic_params: vec![],
        prophecies: vec![],
    }
}

/// Convert a basic block.
fn convert_basic_block(bb: &mir::BasicBlockData<'_>) -> ir::BasicBlock {
    let statements: Vec<ir::Statement> = bb
        .statements
        .iter()
        .filter_map(|stmt| convert_statement(stmt))
        .collect();

    let terminator = bb
        .terminator
        .as_ref()
        .map(|t| convert_terminator(t))
        .unwrap_or(ir::Terminator::Unreachable);

    ir::BasicBlock {
        statements,
        terminator,
    }
}

/// Convert a MIR statement.
fn convert_statement(stmt: &mir::Statement<'_>) -> Option<ir::Statement> {
    match &stmt.kind {
        mir::StatementKind::Assign(box (place, rvalue)) => {
            let ir_place = convert_place(place);
            let ir_rvalue = convert_rvalue(rvalue)?;
            Some(ir::Statement::Assign(ir_place, ir_rvalue))
        }
        // Skip storage, retag, coverage, etc.
        _ => None,
    }
}

/// Convert a MIR terminator.
fn convert_terminator(term: &mir::Terminator<'_>) -> ir::Terminator {
    match &term.kind {
        mir::TerminatorKind::Return => ir::Terminator::Return,

        mir::TerminatorKind::Goto { target } => ir::Terminator::Goto(target.as_usize()),

        mir::TerminatorKind::SwitchInt { discr, targets } => {
            let ir_discr = convert_operand(discr);
            let ir_targets: Vec<(i128, ir::BlockId)> = targets
                .iter()
                .map(|(val, target)| (val as i128, target.as_usize()))
                .collect();
            let otherwise = targets.otherwise().as_usize();

            ir::Terminator::SwitchInt {
                discr: ir_discr,
                targets: ir_targets,
                otherwise,
            }
        }

        mir::TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            ..
        } => {
            let func_name = format!("{func:?}");
            let ir_args: Vec<ir::Operand> =
                args.iter().map(|arg| convert_operand(&arg.node)).collect();
            let ir_dest = convert_place(destination);
            let ir_target = target.map(|t| t.as_usize()).unwrap_or(0);

            ir::Terminator::Call {
                func: func_name,
                args: ir_args,
                destination: ir_dest,
                target: ir_target,
            }
        }

        mir::TerminatorKind::Assert {
            cond,
            expected,
            target,
            msg,
            ..
        } => {
            let kind = classify_assert_kind(msg);
            ir::Terminator::Assert {
                cond: convert_operand(cond),
                expected: *expected,
                target: target.as_usize(),
                kind,
            }
        }

        mir::TerminatorKind::Unreachable => ir::Terminator::Unreachable,

        // Drop, Resume, Abort, etc. → treat as goto or unreachable
        mir::TerminatorKind::Drop { target, .. } => ir::Terminator::Goto(target.as_usize()),

        _ => ir::Terminator::Unreachable,
    }
}

/// Convert an rvalue.
fn convert_rvalue(rvalue: &mir::Rvalue<'_>) -> Option<ir::Rvalue> {
    match rvalue {
        mir::Rvalue::Use(op) => Some(ir::Rvalue::Use(convert_operand(op))),

        mir::Rvalue::BinaryOp(op, box (lhs, rhs)) => {
            let ir_op = convert_binop(op);
            Some(ir::Rvalue::BinaryOp(
                ir_op,
                convert_operand(lhs),
                convert_operand(rhs),
            ))
        }

        mir::Rvalue::UnaryOp(op, operand) => {
            let ir_op = match op {
                mir::UnOp::Not => ir::UnOp::Not,
                mir::UnOp::Neg => ir::UnOp::Neg,
                _ => return None,
            };
            Some(ir::Rvalue::UnaryOp(ir_op, convert_operand(operand)))
        }

        mir::Rvalue::Ref(_, borrow_kind, place) => {
            let mutability = match borrow_kind {
                mir::BorrowKind::Mut { .. } => ir::Mutability::Mutable,
                _ => ir::Mutability::Shared,
            };
            Some(ir::Rvalue::Ref(mutability, convert_place(place)))
        }

        mir::Rvalue::Cast(_, op, ty) => {
            let ir_ty = convert_ty(*ty);
            Some(ir::Rvalue::Cast(
                ir::CastKind::IntToInt,
                convert_operand(op),
                ir_ty,
            ))
        }

        mir::Rvalue::Discriminant(place) => Some(ir::Rvalue::Discriminant(convert_place(place))),

        // Aggregate (tuples, structs, enums)
        mir::Rvalue::Aggregate(box kind, operands) => {
            let ir_kind = match kind {
                mir::AggregateKind::Tuple => ir::AggregateKind::Tuple,
                _ => return None, // Skip complex aggregates for Phase 1
            };
            let ir_ops: Vec<ir::Operand> = operands.iter().map(|op| convert_operand(op)).collect();
            Some(ir::Rvalue::Aggregate(ir_kind, ir_ops))
        }

        _ => None, // Skip other rvalues for Phase 1
    }
}

/// Convert an operand.
fn convert_operand(op: &mir::Operand<'_>) -> ir::Operand {
    match op {
        mir::Operand::Copy(place) => ir::Operand::Copy(convert_place(place)),
        mir::Operand::Move(place) => ir::Operand::Move(convert_place(place)),
        mir::Operand::Constant(constant) => ir::Operand::Constant(convert_constant(constant)),
        // RuntimeChecks operand added in nightly — treat as a constant placeholder
        _ => ir::Operand::Constant(ir::Constant::Bool(true)),
    }
}

/// Convert a place.
fn convert_place(place: &mir::Place<'_>) -> ir::Place {
    let local = format!("_{}", place.local.as_usize());
    let projections: Vec<ir::Projection> = place
        .projection
        .iter()
        .filter_map(|elem| match elem {
            mir::PlaceElem::Deref => Some(ir::Projection::Deref),
            mir::PlaceElem::Field(field, _) => Some(ir::Projection::Field(field.as_usize())),
            mir::PlaceElem::Index(local) => {
                Some(ir::Projection::Index(format!("_{}", local.as_usize())))
            }
            mir::PlaceElem::Downcast(_, variant) => {
                Some(ir::Projection::Downcast(variant.as_usize()))
            }
            _ => None,
        })
        .collect();

    ir::Place { local, projections }
}

/// Convert a constant.
fn convert_constant(constant: &mir::ConstOperand<'_>) -> ir::Constant {
    // Try to evaluate the constant
    match constant.const_ {
        mir::Const::Val(val, ty) => convert_const_val(val, ty),
        _ => ir::Constant::Str(format!("{:?}", constant.const_)),
    }
}

/// Convert a constant value.
fn convert_const_val(val: mir::ConstValue, ty: ty::Ty<'_>) -> ir::Constant {
    match val {
        mir::ConstValue::Scalar(scalar) => convert_scalar(scalar, ty),
        _ => ir::Constant::Str(format!("{val:?}")),
    }
}

/// Convert a scalar constant.
fn convert_scalar(scalar: mir::interpret::Scalar, ty: ty::Ty<'_>) -> ir::Constant {
    match ty.kind() {
        ty::TyKind::Bool => {
            let val = scalar.to_bool().unwrap();
            ir::Constant::Bool(val)
        }
        ty::TyKind::Int(int_ty) => {
            let ir_ty = convert_int_ty(int_ty);
            let bits = ir_ty.bit_width();
            let size = rustc_abi::Size::from_bits(u64::from(bits));
            ir::Constant::Int(scalar.to_int(size).unwrap(), ir_ty)
        }
        ty::TyKind::Uint(uint_ty) => {
            let ir_ty = convert_uint_ty(uint_ty);
            let bits = ir_ty.bit_width();
            let size = rustc_abi::Size::from_bits(u64::from(bits));
            ir::Constant::Uint(scalar.to_uint(size).unwrap(), ir_ty)
        }
        _ => ir::Constant::Str(format!("{scalar:?}")),
    }
}

/// Convert a rustc type to our IR type.
pub fn convert_ty(ty: ty::Ty<'_>) -> ir::Ty {
    match ty.kind() {
        ty::TyKind::Bool => ir::Ty::Bool,
        ty::TyKind::Int(int_ty) => ir::Ty::Int(convert_int_ty(int_ty)),
        ty::TyKind::Uint(uint_ty) => ir::Ty::Uint(convert_uint_ty(uint_ty)),
        ty::TyKind::Float(float_ty) => ir::Ty::Float(convert_float_ty(float_ty)),
        ty::TyKind::Char => ir::Ty::Char,
        ty::TyKind::Tuple(fields) if fields.is_empty() => ir::Ty::Unit,
        ty::TyKind::Tuple(fields) => ir::Ty::Tuple(fields.iter().map(|t| convert_ty(t)).collect()),
        ty::TyKind::Array(elem, _) => {
            ir::Ty::Array(Box::new(convert_ty(*elem)), 0) // size not needed for SMT
        }
        ty::TyKind::Slice(elem) => ir::Ty::Slice(Box::new(convert_ty(*elem))),
        ty::TyKind::Ref(_, inner, mutability) => {
            let m = match mutability {
                rustc_hir::Mutability::Mut => ir::Mutability::Mutable,
                rustc_hir::Mutability::Not => ir::Mutability::Shared,
            };
            ir::Ty::Ref(Box::new(convert_ty(*inner)), m)
        }
        ty::TyKind::RawPtr(inner, mutability) => {
            let m = match mutability {
                rustc_hir::Mutability::Mut => ir::Mutability::Mutable,
                rustc_hir::Mutability::Not => ir::Mutability::Shared,
            };
            ir::Ty::RawPtr(Box::new(convert_ty(*inner)), m)
        }
        ty::TyKind::Never => ir::Ty::Never,
        _ => ir::Ty::Named(format!("{ty:?}")),
    }
}

fn convert_int_ty(ty: &ty::IntTy) -> ir::IntTy {
    match ty {
        ty::IntTy::I8 => ir::IntTy::I8,
        ty::IntTy::I16 => ir::IntTy::I16,
        ty::IntTy::I32 => ir::IntTy::I32,
        ty::IntTy::I64 => ir::IntTy::I64,
        ty::IntTy::I128 => ir::IntTy::I128,
        ty::IntTy::Isize => ir::IntTy::Isize,
    }
}

fn convert_uint_ty(ty: &ty::UintTy) -> ir::UintTy {
    match ty {
        ty::UintTy::U8 => ir::UintTy::U8,
        ty::UintTy::U16 => ir::UintTy::U16,
        ty::UintTy::U32 => ir::UintTy::U32,
        ty::UintTy::U64 => ir::UintTy::U64,
        ty::UintTy::U128 => ir::UintTy::U128,
        ty::UintTy::Usize => ir::UintTy::Usize,
    }
}

fn convert_float_ty(ty: &ty::FloatTy) -> ir::FloatTy {
    match ty {
        ty::FloatTy::F16 | ty::FloatTy::F32 => ir::FloatTy::F32,
        ty::FloatTy::F64 | ty::FloatTy::F128 => ir::FloatTy::F64,
    }
}

/// Classify a MIR AssertKind into our IR AssertKind for specific error messages.
fn classify_assert_kind(msg: &mir::AssertKind<mir::Operand<'_>>) -> ir::AssertKind {
    match msg {
        mir::AssertKind::BoundsCheck { len, index } => ir::AssertKind::BoundsCheck {
            len: convert_operand(len),
            index: convert_operand(index),
        },
        mir::AssertKind::Overflow(op, _, _) => ir::AssertKind::Overflow(convert_binop(op)),
        mir::AssertKind::OverflowNeg(_) => ir::AssertKind::NegationOverflow,
        mir::AssertKind::DivisionByZero(_) => ir::AssertKind::DivisionByZero,
        mir::AssertKind::RemainderByZero(_) => ir::AssertKind::RemainderByZero,
        _ => {
            // MisalignedPointerDereference, ResumedAfterReturn, ResumedAfterPanic, etc.
            ir::AssertKind::Other(format!("{msg:?}"))
        }
    }
}

fn convert_binop(op: &mir::BinOp) -> ir::BinOp {
    match op {
        mir::BinOp::Add | mir::BinOp::AddWithOverflow | mir::BinOp::AddUnchecked => ir::BinOp::Add,
        mir::BinOp::Sub | mir::BinOp::SubWithOverflow | mir::BinOp::SubUnchecked => ir::BinOp::Sub,
        mir::BinOp::Mul | mir::BinOp::MulWithOverflow | mir::BinOp::MulUnchecked => ir::BinOp::Mul,
        mir::BinOp::Div => ir::BinOp::Div,
        mir::BinOp::Rem => ir::BinOp::Rem,
        mir::BinOp::BitAnd => ir::BinOp::BitAnd,
        mir::BinOp::BitOr => ir::BinOp::BitOr,
        mir::BinOp::BitXor => ir::BinOp::BitXor,
        mir::BinOp::Shl | mir::BinOp::ShlUnchecked => ir::BinOp::Shl,
        mir::BinOp::Shr | mir::BinOp::ShrUnchecked => ir::BinOp::Shr,
        mir::BinOp::Eq => ir::BinOp::Eq,
        mir::BinOp::Ne => ir::BinOp::Ne,
        mir::BinOp::Lt => ir::BinOp::Lt,
        mir::BinOp::Le => ir::BinOp::Le,
        mir::BinOp::Gt => ir::BinOp::Gt,
        mir::BinOp::Ge => ir::BinOp::Ge,
        _ => ir::BinOp::Add, // fallback
    }
}
