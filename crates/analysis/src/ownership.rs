/// Ownership-aware reasoning for inter-procedural verification.
///
/// Rust's ownership system provides free information at call sites:
/// - **Moved** values cannot be used after the call (borrow checker enforces this)
/// - **Shared borrows** (`&T`) cannot be mutated by the callee -- value preserved
/// - **Mutable borrows** (`&mut T`) may be modified by the callee -- value havoced
/// - **Copied** values (Copy types) are unchanged after the call -- value preserved
///
/// This module classifies function call arguments by ownership kind and generates
/// constraints that the VCGen uses to tighten verification conditions.
use crate::ir::{Mutability, Operand, Ty};

/// How an argument is passed to a function call.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OwnershipKind {
    /// Value is moved into the callee (T, not behind a reference).
    /// After the call, the original variable is consumed -- cannot be used.
    Moved,
    /// Value is passed by shared reference (&T).
    /// After the call, the original value is guaranteed unchanged.
    SharedBorrow,
    /// Value is passed by mutable reference (&mut T).
    /// After the call, the original value may have been modified (havoced).
    MutableBorrow,
    /// Value is copied (Copy types like i32, bool).
    /// After the call, the original value is unchanged (it's a copy).
    Copied,
}

/// Constraint generated from ownership analysis at a call site.
#[derive(Debug, Clone)]
pub enum OwnershipConstraint {
    /// The argument's value is unchanged after the call.
    /// Encoded as: `(assert (= arg_after_call arg_before_call))`
    ValuePreserved { variable: String },
    /// The argument's value is consumed (moved). Any subsequent use is invalid.
    /// Rust's borrow checker already prevents this, but we log it for tracing.
    ValueConsumed { variable: String },
    /// The argument's target may be modified (havoced).
    /// Encoded by NOT adding a preservation constraint -- the referent
    /// of the mutable borrow remains unconstrained after the call.
    ValueMayChange { variable: String },
}

/// Classify how an argument is passed to a function call.
///
/// Classification priority:
/// 1. If `param_ty` is `Ty::Ref(_, Shared)` -> `SharedBorrow`
/// 2. If `param_ty` is `Ty::Ref(_, Mutable)` -> `MutableBorrow`
/// 3. If operand is `Operand::Copy(_)` -> `Copied`
/// 4. If operand is `Operand::Move(_)` -> `Moved`
/// 5. Default fallback: `Copied` (conservative, safe)
pub fn classify_argument(operand: &Operand, param_ty: &Ty) -> OwnershipKind {
    // Check parameter type first -- reference types take precedence
    if let Ty::Ref(_, Mutability::Shared) = param_ty {
        return OwnershipKind::SharedBorrow;
    }
    if let Ty::Ref(_, Mutability::Mutable) = param_ty {
        return OwnershipKind::MutableBorrow;
    }

    // Check operand kind
    match operand {
        Operand::Copy(_) => OwnershipKind::Copied,
        Operand::Move(_) => OwnershipKind::Moved,
        Operand::Constant(_) => OwnershipKind::Copied, // Constants are always copyable
    }
}

/// Generate ownership constraints for an argument at a call site.
///
/// Returns constraints based on the ownership classification:
/// - `Copied` / `SharedBorrow` -> `ValuePreserved` (value unchanged after call)
/// - `MutableBorrow` -> `ValueMayChange` (value may be modified)
/// - `Moved` -> `ValueConsumed` (value consumed, no constraint needed)
pub fn generate_ownership_constraints(
    kind: OwnershipKind,
    arg_operand: &Operand,
) -> Vec<OwnershipConstraint> {
    let variable = match arg_operand {
        Operand::Copy(place) | Operand::Move(place) => place.local.clone(),
        Operand::Constant(_) => return vec![], // Constants don't need constraints
    };

    match kind {
        OwnershipKind::Copied => vec![OwnershipConstraint::ValuePreserved { variable }],
        OwnershipKind::SharedBorrow => vec![OwnershipConstraint::ValuePreserved { variable }],
        OwnershipKind::MutableBorrow => vec![OwnershipConstraint::ValueMayChange { variable }],
        OwnershipKind::Moved => vec![OwnershipConstraint::ValueConsumed { variable }],
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{IntTy, Place};

    #[test]
    fn classify_copy_operand_non_ref_type() {
        let operand = Operand::Copy(Place::local("_1"));
        let ty = Ty::Int(IntTy::I32);
        assert_eq!(classify_argument(&operand, &ty), OwnershipKind::Copied);
    }

    #[test]
    fn classify_move_operand_non_ref_type() {
        let operand = Operand::Move(Place::local("_1"));
        let ty = Ty::Int(IntTy::I32);
        assert_eq!(classify_argument(&operand, &ty), OwnershipKind::Moved);
    }

    #[test]
    fn classify_shared_borrow_ref_type() {
        let operand = Operand::Copy(Place::local("_1"));
        let ty = Ty::Ref(Box::new(Ty::Int(IntTy::I32)), Mutability::Shared);
        assert_eq!(
            classify_argument(&operand, &ty),
            OwnershipKind::SharedBorrow
        );
    }

    #[test]
    fn classify_mutable_borrow_ref_type() {
        let operand = Operand::Copy(Place::local("_1"));
        let ty = Ty::Ref(Box::new(Ty::Int(IntTy::I32)), Mutability::Mutable);
        assert_eq!(
            classify_argument(&operand, &ty),
            OwnershipKind::MutableBorrow
        );
    }

    #[test]
    fn classify_constant_operand() {
        use crate::ir::Constant;
        let operand = Operand::Constant(Constant::Int(42, IntTy::I32));
        let ty = Ty::Int(IntTy::I32);
        assert_eq!(classify_argument(&operand, &ty), OwnershipKind::Copied);
    }

    #[test]
    fn classify_ref_type_overrides_operand_kind() {
        // Even with Operand::Move, a Ref type means borrow semantics
        let operand = Operand::Move(Place::local("_1"));
        let ty = Ty::Ref(Box::new(Ty::Int(IntTy::I32)), Mutability::Shared);
        assert_eq!(
            classify_argument(&operand, &ty),
            OwnershipKind::SharedBorrow
        );
    }

    #[test]
    fn generate_constraints_copied() {
        let operand = Operand::Copy(Place::local("_1"));
        let constraints = generate_ownership_constraints(OwnershipKind::Copied, &operand);
        assert_eq!(constraints.len(), 1);
        assert!(matches!(
            &constraints[0],
            OwnershipConstraint::ValuePreserved { variable } if variable == "_1"
        ));
    }

    #[test]
    fn generate_constraints_shared_borrow() {
        let operand = Operand::Copy(Place::local("_2"));
        let constraints = generate_ownership_constraints(OwnershipKind::SharedBorrow, &operand);
        assert_eq!(constraints.len(), 1);
        assert!(matches!(
            &constraints[0],
            OwnershipConstraint::ValuePreserved { variable } if variable == "_2"
        ));
    }

    #[test]
    fn generate_constraints_mutable_borrow() {
        let operand = Operand::Copy(Place::local("_3"));
        let constraints = generate_ownership_constraints(OwnershipKind::MutableBorrow, &operand);
        assert_eq!(constraints.len(), 1);
        assert!(matches!(
            &constraints[0],
            OwnershipConstraint::ValueMayChange { variable } if variable == "_3"
        ));
    }

    #[test]
    fn generate_constraints_moved() {
        let operand = Operand::Move(Place::local("_4"));
        let constraints = generate_ownership_constraints(OwnershipKind::Moved, &operand);
        assert_eq!(constraints.len(), 1);
        assert!(matches!(
            &constraints[0],
            OwnershipConstraint::ValueConsumed { variable } if variable == "_4"
        ));
    }

    #[test]
    fn generate_constraints_constant_no_constraints() {
        use crate::ir::Constant;
        let operand = Operand::Constant(Constant::Int(42, IntTy::I32));
        let constraints = generate_ownership_constraints(OwnershipKind::Copied, &operand);
        assert!(constraints.is_empty());
    }
}
