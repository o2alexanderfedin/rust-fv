//! Heap-as-array SMT encoding for raw pointer verification.
//!
//! This module implements a byte-addressable heap memory model using SMT array theory.
//! Provides null-check and bounds-check assertion generators for memory safety VCs.

use crate::ir::{Function, UnsafeOperation};
use rust_fv_smtlib::command::Command;
use rust_fv_smtlib::sort::Sort;
use rust_fv_smtlib::term::Term;

/// Declares the heap-as-array memory model in SMT-LIB.
///
/// Returns commands that declare:
/// - `heap`: byte-addressable memory (Array (_ BitVec 64) (_ BitVec 8))
/// - `allocated`: allocation validity predicate ((_ BitVec 64) -> Bool)
/// - `alloc_base`: allocation base address ((_ BitVec 64) -> (_ BitVec 64))
/// - `alloc_size`: allocation size ((_ BitVec 64) -> (_ BitVec 64))
/// - Axiom: null address (0) is not allocated
pub fn declare_heap_model() -> Vec<Command> {
    vec![
        // heap: ((_ BitVec 64) -> (_ BitVec 8)) - byte-addressable memory
        Command::DeclareFun("heap".to_string(), vec![Sort::BitVec(64)], Sort::BitVec(8)),
        // allocated: ((_ BitVec 64) -> Bool) - allocation validity predicate
        Command::DeclareFun("allocated".to_string(), vec![Sort::BitVec(64)], Sort::Bool),
        // alloc_base: ((_ BitVec 64) -> (_ BitVec 64)) - allocation base address
        Command::DeclareFun(
            "alloc_base".to_string(),
            vec![Sort::BitVec(64)],
            Sort::BitVec(64),
        ),
        // alloc_size: ((_ BitVec 64) -> (_ BitVec 64)) - allocation size
        Command::DeclareFun(
            "alloc_size".to_string(),
            vec![Sort::BitVec(64)],
            Sort::BitVec(64),
        ),
        // Axiom: null address (0) is not allocated
        Command::Assert(Term::Not(Box::new(Term::App(
            "allocated".to_string(),
            vec![Term::BitVecLit(0, 64)],
        )))),
    ]
}

/// Generates a null-check assertion term for a pointer.
///
/// Returns the "bad condition" (ptr == null) that should be asserted in the VC.
/// If the VC is SAT, the pointer can be null (violation found).
/// If the VC is UNSAT, the pointer is never null (property holds).
pub fn generate_null_check_assertion(ptr_name: &str) -> Term {
    Term::Eq(
        Box::new(Term::Const(ptr_name.to_string())),
        Box::new(Term::BitVecLit(0, 64)),
    )
}

/// Generates a bounds-check assertion term for pointer arithmetic.
///
/// Returns the assertion that the offset violates bounds.
/// Checks: effective_offset < allocation_size, where
/// effective_offset = (ptr - alloc_base(ptr)) + offset
///
/// If the VC is SAT, the offset can be out of bounds (violation found).
/// If the VC is UNSAT, the offset is always within bounds (property holds).
///
/// Note: The offset is zero-extended to 64 bits to match pointer width if needed.
pub fn generate_bounds_check_assertion(ptr_name: &str, offset_name: &str) -> Term {
    let ptr = Term::Const(ptr_name.to_string());
    let offset_raw = Term::Const(offset_name.to_string());

    // Zero-extend offset to 64 bits if it's 32 bits
    // In practice, offsets are typically i32/u32 (32-bit) but pointers are 64-bit
    // We use zero-extension for unsigned offsets, which is the common case
    let offset = Term::App("(_ zero_extend 32)".to_string(), vec![offset_raw]);

    // alloc_base(ptr)
    let base = Term::App("alloc_base".to_string(), vec![ptr.clone()]);

    // ptr - alloc_base(ptr)
    let base_offset = Term::BvSub(Box::new(ptr.clone()), Box::new(base));

    // (ptr - alloc_base(ptr)) + offset
    let effective_offset = Term::BvAdd(Box::new(base_offset), Box::new(offset));

    // alloc_size(ptr)
    let size = Term::App("alloc_size".to_string(), vec![ptr]);

    // effective_offset < alloc_size(ptr)
    let in_bounds = Term::BvULt(Box::new(effective_offset), Box::new(size));

    // NOT (effective_offset < alloc_size(ptr)) - the violation condition
    Term::Not(Box::new(in_bounds))
}

/// Returns true if the function requires heap model declarations.
///
/// Heap model is needed when the function has pointer arithmetic operations
/// (bounds checks require allocation metadata).
pub fn heap_model_declarations_needed(func: &Function) -> bool {
    func.unsafe_operations
        .iter()
        .any(|op| matches!(op, UnsafeOperation::PtrArithmetic { .. }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{
        BasicBlock, Contracts, Function, Local, Mutability, RawPtrProvenance, Ty, UnsafeOperation,
    };

    fn make_test_function(unsafe_operations: Vec<UnsafeOperation>) -> Function {
        Function {
            name: "test_fn".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Bool),
            locals: vec![],
            basic_blocks: vec![BasicBlock {
                statements: vec![],
                terminator: crate::ir::Terminator::Return,
            }],
            contracts: Contracts::default(),
            loops: vec![],
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
            unsafe_blocks: vec![],
            unsafe_operations,
            unsafe_contracts: None,
            is_unsafe_fn: false,
        }
    }

    #[test]
    fn test_declare_heap_model_count() {
        let commands = declare_heap_model();
        // Should have: heap, allocated, alloc_base, alloc_size declarations + null-not-allocated axiom
        assert_eq!(commands.len(), 5);
    }

    #[test]
    fn test_declare_heap_model_has_heap() {
        let commands = declare_heap_model();
        // First command should declare "heap" as an array
        match &commands[0] {
            Command::DeclareFun(name, param_sorts, return_sort) => {
                assert_eq!(name, "heap");
                assert_eq!(param_sorts.len(), 1);
                assert!(matches!(param_sorts[0], Sort::BitVec(64)));
                assert!(matches!(return_sort, Sort::BitVec(8)));
            }
            _ => panic!("Expected DeclareFun for heap"),
        }
    }

    #[test]
    fn test_declare_heap_model_has_allocated() {
        let commands = declare_heap_model();
        // Should have "allocated" function
        let has_allocated = commands.iter().any(|cmd| match cmd {
            Command::DeclareFun(name, _, _) => name == "allocated",
            _ => false,
        });
        assert!(has_allocated);
    }

    #[test]
    fn test_declare_heap_model_null_axiom() {
        let commands = declare_heap_model();
        // Last command should assert null is not allocated
        match &commands[4] {
            Command::Assert(term) => {
                // Should be (not (allocated #x0000000000000000))
                match term {
                    Term::Not(inner) => match &**inner {
                        Term::App(name, args) => {
                            assert_eq!(name, "allocated");
                            assert_eq!(args.len(), 1);
                            match &args[0] {
                                Term::BitVecLit(val, width) => {
                                    assert_eq!(*val, 0);
                                    assert_eq!(*width, 64);
                                }
                                _ => panic!("Expected BitVecLit for null address"),
                            }
                        }
                        _ => panic!("Expected App for allocated"),
                    },
                    _ => panic!("Expected Not for null axiom"),
                }
            }
            _ => panic!("Expected Assert for null axiom"),
        }
    }

    #[test]
    fn test_generate_null_check_assertion() {
        let term = generate_null_check_assertion("p");
        // Should be (= p #x0000000000000000)
        match term {
            Term::Eq(left, right) => match (*left, *right) {
                (Term::Const(name), Term::BitVecLit(val, width))
                | (Term::BitVecLit(val, width), Term::Const(name)) => {
                    assert_eq!(name, "p");
                    assert_eq!(val, 0);
                    assert_eq!(width, 64);
                }
                _ => panic!("Expected Const and BitVecLit"),
            },
            _ => panic!("Expected Eq term"),
        }
    }

    #[test]
    fn test_generate_bounds_check_assertion() {
        let term = generate_bounds_check_assertion("p", "off");
        // Should be (not (bvult (bvadd (bvsub p (alloc_base p)) (zero_extend off)) (alloc_size p)))
        match term {
            Term::Not(inner) => match *inner {
                Term::BvULt(effective_offset, size) => {
                    // Verify effective_offset structure
                    match *effective_offset {
                        Term::BvAdd(base_offset, offset_extended) => {
                            // base_offset should be (bvsub p (alloc_base p))
                            match *base_offset {
                                Term::BvSub(ptr, base_fn) => {
                                    assert!(matches!(*ptr, Term::Const(ref name) if name == "p"));
                                    match *base_fn {
                                        Term::App(name, args) => {
                                            assert_eq!(name, "alloc_base");
                                            assert_eq!(args.len(), 1);
                                        }
                                        _ => panic!("Expected App for alloc_base"),
                                    }
                                }
                                _ => panic!("Expected BvSub for base offset"),
                            }
                            // offset should be (zero_extend off)
                            match *offset_extended {
                                Term::App(name, args) => {
                                    assert_eq!(name, "(_ zero_extend 32)");
                                    assert_eq!(args.len(), 1);
                                    assert!(matches!(args[0], Term::Const(ref n) if n == "off"));
                                }
                                _ => panic!("Expected App for zero_extend"),
                            }
                        }
                        _ => panic!("Expected BvAdd for effective offset"),
                    }
                    // Verify size is (alloc_size p)
                    match *size {
                        Term::App(name, args) => {
                            assert_eq!(name, "alloc_size");
                            assert_eq!(args.len(), 1);
                        }
                        _ => panic!("Expected App for alloc_size"),
                    }
                }
                _ => panic!("Expected BvULt"),
            },
            _ => panic!("Expected Not"),
        }
    }

    #[test]
    fn test_heap_model_needed_with_arithmetic() {
        let op = UnsafeOperation::PtrArithmetic {
            ptr_local: "p".to_string(),
            offset_local: "off".to_string(),
            ptr_ty: Ty::RawPtr(Box::new(Ty::Int(crate::ir::IntTy::I32)), Mutability::Shared),
            is_signed_offset: false,
            block_index: 1,
        };
        let func = make_test_function(vec![op]);
        assert!(heap_model_declarations_needed(&func));
    }

    #[test]
    fn test_heap_model_needed_without_arithmetic() {
        let op = UnsafeOperation::RawDeref {
            ptr_local: "p".to_string(),
            ptr_ty: Ty::RawPtr(Box::new(Ty::Int(crate::ir::IntTy::I32)), Mutability::Shared),
            provenance: RawPtrProvenance::Unknown,
            block_index: 1,
        };
        let func = make_test_function(vec![op]);
        assert!(!heap_model_declarations_needed(&func));
    }
}
