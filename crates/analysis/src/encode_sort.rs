/// Encode Rust types as SMT-LIB sorts.
use rust_fv_smtlib::sort::Sort;

use crate::ir::{FloatTy, Ty};

/// Convert a Rust type to an SMT-LIB sort.
///
/// # Encoding Strategy
///
/// - `bool` → `Bool`
/// - `i8..i128, isize` → `(_ BitVec N)` (signed operations used)
/// - `u8..u128, usize` → `(_ BitVec N)` (unsigned operations used)
/// - `char` → `(_ BitVec 32)` (Unicode scalar value)
/// - `f32` → `(_ FloatingPoint 8 24)`
/// - `f64` → `(_ FloatingPoint 11 53)`
/// - `()` / `Never` → `Bool` (unit types represented as trivial)
/// - `[T; N]` → `(Array (_ BitVec 64) T_sort)` (index by bitvec)
/// - `&[T]` / `&T` → same as T (references are transparent for values)
/// - Tuples → uninterpreted sort (TODO: datatypes in Phase 2)
/// - Structs → uninterpreted sort (TODO: datatypes in Phase 2)
/// - Enums → uninterpreted sort (TODO: datatypes in Phase 2)
pub fn encode_type(ty: &Ty) -> Sort {
    match ty {
        Ty::Bool => Sort::Bool,

        Ty::Int(ity) => Sort::BitVec(ity.bit_width()),
        Ty::Uint(uty) => Sort::BitVec(uty.bit_width()),
        Ty::Char => Sort::BitVec(32),

        Ty::Float(fty) => encode_float(fty),

        Ty::Unit | Ty::Never => Sort::Bool,

        Ty::Array(elem_ty, _) => {
            let idx_sort = Sort::BitVec(64);
            let elem_sort = encode_type(elem_ty);
            Sort::Array(Box::new(idx_sort), Box::new(elem_sort))
        }

        Ty::Slice(elem_ty) => {
            let idx_sort = Sort::BitVec(64);
            let elem_sort = encode_type(elem_ty);
            Sort::Array(Box::new(idx_sort), Box::new(elem_sort))
        }

        // References are transparent: encode the pointee type
        Ty::Ref(inner, _) => encode_type(inner),

        // Raw pointers treated as bitvectors (addresses)
        Ty::RawPtr(_, _) => Sort::BitVec(64),

        Ty::Tuple(fields) if fields.is_empty() => Sort::Bool,
        Ty::Tuple(_) => Sort::Uninterpreted("Tuple".to_string()),

        Ty::Struct(name, _) => Sort::Uninterpreted(name.clone()),
        Ty::Enum(name, _) => Sort::Uninterpreted(name.clone()),
        Ty::Named(name) => Sort::Uninterpreted(name.clone()),
    }
}

fn encode_float(fty: &FloatTy) -> Sort {
    match fty {
        FloatTy::F32 => Sort::Float(8, 24),
        FloatTy::F64 => Sort::Float(11, 53),
    }
}

/// Get the bit width used for a type in SMT encoding.
pub fn type_bit_width(ty: &Ty) -> Option<u32> {
    match ty {
        Ty::Bool => Some(1),
        Ty::Int(ity) => Some(ity.bit_width()),
        Ty::Uint(uty) => Some(uty.bit_width()),
        Ty::Char => Some(32),
        _ => None,
    }
}

/// Determine if a type should use signed bitvector operations.
pub fn is_signed_type(ty: &Ty) -> bool {
    matches!(ty, Ty::Int(_))
}

// === Unit tests ===

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{IntTy, UintTy};
    use rust_fv_smtlib::sort::Sort;

    #[test]
    fn bool_encodes_to_bool() {
        assert_eq!(encode_type(&Ty::Bool), Sort::Bool);
    }

    #[test]
    fn i32_encodes_to_bv32() {
        assert_eq!(encode_type(&Ty::Int(IntTy::I32)), Sort::BitVec(32));
    }

    #[test]
    fn u64_encodes_to_bv64() {
        assert_eq!(encode_type(&Ty::Uint(UintTy::U64)), Sort::BitVec(64));
    }

    #[test]
    fn i8_encodes_to_bv8() {
        assert_eq!(encode_type(&Ty::Int(IntTy::I8)), Sort::BitVec(8));
    }

    #[test]
    fn i128_encodes_to_bv128() {
        assert_eq!(encode_type(&Ty::Int(IntTy::I128)), Sort::BitVec(128));
    }

    #[test]
    fn char_encodes_to_bv32() {
        assert_eq!(encode_type(&Ty::Char), Sort::BitVec(32));
    }

    #[test]
    fn f32_encodes_to_fp8_24() {
        assert_eq!(encode_type(&Ty::Float(FloatTy::F32)), Sort::Float(8, 24));
    }

    #[test]
    fn f64_encodes_to_fp11_53() {
        assert_eq!(encode_type(&Ty::Float(FloatTy::F64)), Sort::Float(11, 53));
    }

    #[test]
    fn unit_encodes_to_bool() {
        assert_eq!(encode_type(&Ty::Unit), Sort::Bool);
    }

    #[test]
    fn never_encodes_to_bool() {
        assert_eq!(encode_type(&Ty::Never), Sort::Bool);
    }

    #[test]
    fn array_i32_encodes_to_array_bv64_bv32() {
        let ty = Ty::Array(Box::new(Ty::Int(IntTy::I32)), 10);
        let expected = Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(32)));
        assert_eq!(encode_type(&ty), expected);
    }

    #[test]
    fn slice_u8_encodes_to_array_bv64_bv8() {
        let ty = Ty::Slice(Box::new(Ty::Uint(UintTy::U8)));
        let expected = Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8)));
        assert_eq!(encode_type(&ty), expected);
    }

    #[test]
    fn ref_is_transparent() {
        use crate::ir::Mutability;
        let inner = Ty::Int(IntTy::I32);
        let ref_ty = Ty::Ref(Box::new(inner.clone()), Mutability::Shared);
        assert_eq!(encode_type(&ref_ty), encode_type(&inner));
    }

    #[test]
    fn raw_ptr_encodes_to_bv64() {
        use crate::ir::Mutability;
        let ty = Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Shared);
        assert_eq!(encode_type(&ty), Sort::BitVec(64));
    }

    #[test]
    fn struct_encodes_to_uninterpreted() {
        let ty = Ty::Struct("Vec".to_string(), vec![]);
        assert_eq!(encode_type(&ty), Sort::Uninterpreted("Vec".to_string()));
    }

    #[test]
    fn signed_type_detection() {
        assert!(is_signed_type(&Ty::Int(IntTy::I32)));
        assert!(!is_signed_type(&Ty::Uint(UintTy::U32)));
        assert!(!is_signed_type(&Ty::Bool));
    }
}
