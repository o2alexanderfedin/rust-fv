/// Our own MIR-like intermediate representation.
///
/// This mirrors `rustc_middle::mir` but is decoupled from the compiler,
/// making the VCGen logic fully testable on stable Rust.
/// The driver crate converts `rustc` MIR → this IR.
/// A generic type parameter on a function.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GenericParam {
    /// Parameter name, e.g., "T"
    pub name: String,
    /// Trait bounds, e.g., ["Ord", "Clone"]
    pub trait_bounds: Vec<String>,
}

/// Closure trait classification (Fn, FnMut, FnOnce).
/// These correspond to Rust's closure capture modes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClosureTrait {
    /// Immutable borrow capture — can be called multiple times
    Fn,
    /// Mutable borrow capture — can be called multiple times, requires mutability
    FnMut,
    /// Move capture — can only be called once
    FnOnce,
}

/// A method in a trait definition with contract specifications.
#[derive(Debug, Clone)]
pub struct TraitMethod {
    /// Method name (e.g., "push", "pop")
    pub name: String,
    /// Parameter names and types (including &self/&mut self)
    pub params: Vec<(String, Ty)>,
    /// Return type
    pub return_ty: Ty,
    /// Preconditions (trait-level requirements)
    pub requires: Vec<SpecExpr>,
    /// Postconditions (trait-level guarantees)
    pub ensures: Vec<SpecExpr>,
    /// Whether this is a pure/specification-only method
    pub is_pure: bool,
}

/// A trait definition with methods and contract specifications.
#[derive(Debug, Clone)]
pub struct TraitDef {
    /// Trait name (e.g., "Stack", "Iterator")
    pub name: String,
    /// Methods defined in this trait
    pub methods: Vec<TraitMethod>,
    /// Whether this trait is sealed (pub(crate), private, or sealed super-trait pattern)
    pub is_sealed: bool,
    /// Super-trait names for inheritance
    pub super_traits: Vec<String>,
}

/// An implementation of a trait for a concrete type.
#[derive(Debug, Clone)]
pub struct TraitImpl {
    /// The trait being implemented (e.g., "Stack")
    pub trait_name: String,
    /// The concrete type implementing the trait (e.g., "VecStack")
    pub impl_type: String,
    /// Names of the trait methods this impl provides
    pub method_names: Vec<String>,
}

/// A named lifetime parameter in a function signature.
///
/// Lifetime parameters represent regions in the program where borrows are valid.
/// Examples: `'a`, `'b`, `'static`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LifetimeParam {
    /// Lifetime name (e.g., "'a", "'b", "'static")
    pub name: String,
    /// True if this is the 'static lifetime
    pub is_static: bool,
}

/// An outlives constraint between two lifetimes.
///
/// `OutlivesConstraint { longer: "'a", shorter: "'b" }` represents `'a: 'b`
/// (lifetime 'a must outlive lifetime 'b).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OutlivesConstraint {
    /// The lifetime that must outlive (e.g., "'a")
    pub longer: String,
    /// The lifetime that is outlived (e.g., "'b")
    pub shorter: String,
}

/// Information about a borrow in the function.
///
/// Tracks the borrow origin, region, mutability, and whether it's a reborrow.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BorrowInfo {
    /// The local variable holding the borrow (e.g., "_1")
    pub local_name: String,
    /// The lifetime/region associated with this borrow (e.g., "'a")
    pub region: String,
    /// True for &mut, false for &
    pub is_mutable: bool,
    /// Deref level: 0 for direct borrow, 1 for reborrow of &mut, etc.
    pub deref_level: u32,
    /// If this is a reborrow, the original borrow local name
    pub source_local: Option<String>,
}

/// A chain of reborrows from an original borrow.
///
/// Example: if `&mut x` is borrowed as `y`, then `y` is borrowed as `z`,
/// the reborrow chain is `{original: "x", reborrows: ["y", "z"]}`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReborrowChain {
    /// Original borrow local name
    pub original: String,
    /// Chain of reborrow local names in order
    pub reborrows: Vec<String>,
}

/// Information about a closure type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClosureInfo {
    /// Unique closure identifier (e.g., "closure_add_captured")
    pub name: String,
    /// Captured variable names and their types (environment)
    pub env_fields: Vec<(String, Ty)>,
    /// Closure parameter names and types
    pub params: Vec<(String, Ty)>,
    /// Closure return type
    pub return_ty: Ty,
    /// Which Fn trait this closure implements
    pub trait_kind: ClosureTrait,
}

/// A function to be verified.
#[derive(Debug, Clone)]
pub struct Function {
    pub name: String,
    pub params: Vec<Local>,
    pub return_local: Local,
    pub locals: Vec<Local>,
    pub basic_blocks: Vec<BasicBlock>,
    pub contracts: Contracts,
    /// Detected loops with optional user-supplied invariants.
    pub loops: Vec<LoopInfo>,
    /// Generic type parameters with trait bounds.
    /// Empty for non-generic functions.
    pub generic_params: Vec<GenericParam>,
    /// Prophecy variables for mutable borrow parameters.
    /// Empty for functions without `&mut T` parameters.
    pub prophecies: Vec<ProphecyInfo>,
    /// Lifetime parameters extracted from function signature.
    /// Empty for functions without lifetime parameters.
    pub lifetime_params: Vec<LifetimeParam>,
    /// Outlives constraints between lifetime parameters.
    /// Empty if no lifetime constraints exist.
    pub outlives_constraints: Vec<OutlivesConstraint>,
    /// Information about all borrows in the function.
    /// Empty if function has no borrows.
    pub borrow_info: Vec<BorrowInfo>,
    /// Reborrow chains tracking original-to-reborrow relationships.
    /// Empty if function has no reborrows.
    pub reborrow_chains: Vec<ReborrowChain>,
}

impl Function {
    /// Returns true if this function has generic type parameters.
    pub fn is_generic(&self) -> bool {
        !self.generic_params.is_empty()
    }

    /// Returns true if this function has mutable reference parameters.
    pub fn has_mut_ref_params(&self) -> bool {
        self.params
            .iter()
            .any(|p| matches!(p.ty, Ty::Ref(_, Mutability::Mutable)))
    }
}

/// A local variable (parameter, return place, or temporary).
#[derive(Debug, Clone)]
pub struct Local {
    /// MIR-style name: `_0` (return), `_1`, `_2`, ...
    pub name: String,
    pub ty: Ty,
    /// Whether this local is specification-only (ghost variable).
    /// Ghost locals are used in specifications but erased from executable encoding.
    pub is_ghost: bool,
}

impl Local {
    /// Create a new non-ghost local variable.
    pub fn new(name: impl Into<String>, ty: Ty) -> Self {
        Self {
            name: name.into(),
            ty,
            is_ghost: false,
        }
    }

    /// Create a new ghost local variable (specification-only).
    pub fn ghost(name: impl Into<String>, ty: Ty) -> Self {
        Self {
            name: name.into(),
            ty,
            is_ghost: true,
        }
    }
}

/// Formal contracts on a function.
#[derive(Debug, Clone, Default)]
pub struct Contracts {
    /// Preconditions (`#[requires(...)]`)
    pub requires: Vec<SpecExpr>,
    /// Postconditions (`#[ensures(...)]`)
    pub ensures: Vec<SpecExpr>,
    /// Loop invariants (`#[invariant(...)]`)
    pub invariants: Vec<SpecExpr>,
    /// Whether the function is marked `#[pure]`
    pub is_pure: bool,
    /// Termination measure (`#[decreases(expr)]`) for recursive functions.
    /// None means no termination measure specified.
    pub decreases: Option<SpecExpr>,
}

/// Information about a loop detected in the CFG.
#[derive(Debug, Clone)]
pub struct LoopInfo {
    /// Basic block index of the loop header (target of back-edge)
    pub header_block: BlockId,
    /// Basic block indices that have back-edges to the header
    pub back_edge_blocks: Vec<BlockId>,
    /// User-supplied loop invariant expressions
    pub invariants: Vec<SpecExpr>,
}

/// Prophecy variable information for mutable borrow reasoning.
///
/// In order to specify and verify properties about mutable borrows (e.g., `&mut T`),
/// we need to reason about both the initial value at function entry and the final
/// value at function return. Prophecy variables implement this Creusot/RustHornBelt-style
/// encoding:
///
/// - At function entry: declare initial and prophecy (final) variables
/// - In specifications: `old(*x)` refers to initial, `final_value(x)` refers to prophecy
/// - At function return: assert that the actual final value equals the prophecy
#[derive(Debug, Clone)]
pub struct ProphecyInfo {
    /// The mutable borrow parameter name (e.g., "_1")
    pub param_name: String,
    /// The initial value variable name (e.g., "_1_initial")
    pub initial_var: String,
    /// The prophecy (final value) variable name (e.g., "_1_prophecy")
    pub prophecy_var: String,
    /// The type being pointed to (e.g., Ty::Int(IntTy::I32) for &mut i32)
    pub inner_ty: Ty,
    /// Deref level: 0 for direct &mut T, 1 for outer of &mut &mut T, etc.
    pub deref_level: u32,
}

/// A specification expression (parsed from attribute strings).
/// For Phase 1 we store the raw string and interpret simple expressions.
#[derive(Debug, Clone)]
pub struct SpecExpr {
    pub raw: String,
}

/// A basic block in the control-flow graph.
#[derive(Debug, Clone)]
pub struct BasicBlock {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}

/// A MIR statement.
#[derive(Debug, Clone)]
pub enum Statement {
    /// `place = rvalue`
    Assign(Place, Rvalue),
    /// No-op (padding, debug info, etc.)
    Nop,
}

/// A MIR terminator — ends a basic block.
#[derive(Debug, Clone)]
pub enum Terminator {
    /// Function return (value is in `_0`)
    Return,
    /// Unconditional jump to block
    Goto(BlockId),
    /// Conditional branch on an integer discriminant
    SwitchInt {
        discr: Operand,
        /// (value, target_block) pairs
        targets: Vec<(i128, BlockId)>,
        /// Fallback block
        otherwise: BlockId,
    },
    /// Function call
    Call {
        func: String,
        args: Vec<Operand>,
        destination: Place,
        /// Block to jump to after the call returns
        target: BlockId,
    },
    /// `assert!(cond == expected)` — panics if false
    Assert {
        cond: Operand,
        expected: bool,
        target: BlockId,
        /// Classification of the assertion for specific error messages
        kind: AssertKind,
    },
    /// Unreachable code (e.g. after a guaranteed panic)
    Unreachable,
}

/// Classification of MIR Assert terminators for specific error messages.
///
/// Rustc generates `Assert` terminators for various panic-producing operations:
/// bounds checks, overflow checks, division-by-zero, etc. This enum lets
/// the VCGen produce targeted error messages identifying the panic source.
#[derive(Debug, Clone)]
pub enum AssertKind {
    /// User-written `assert!(expr)` or `assert_eq!(a, b)`
    UserAssert,
    /// Array/slice bounds check: index < len
    BoundsCheck { len: Operand, index: Operand },
    /// Integer overflow in arithmetic (add, sub, mul, etc.)
    Overflow(BinOp),
    /// Division by zero
    DivisionByZero,
    /// Remainder by zero
    RemainderByZero,
    /// Negation overflow (e.g., -i32::MIN)
    NegationOverflow,
    /// unwrap() on None
    UnwrapNone,
    /// expect() on None/Err
    ExpectFailed(String),
    /// Generic/unclassified assertion
    Other(String),
}

/// Block index.
pub type BlockId = usize;

/// An rvalue (right-hand side of an assignment).
#[derive(Debug, Clone)]
pub enum Rvalue {
    /// Direct use of an operand
    Use(Operand),
    /// Binary operation: `op(lhs, rhs)`
    BinaryOp(BinOp, Operand, Operand),
    /// Checked binary operation: produces `(result, overflow_flag)`
    CheckedBinaryOp(BinOp, Operand, Operand),
    /// Unary operation: `op(operand)`
    UnaryOp(UnOp, Operand),
    /// Type cast
    Cast(CastKind, Operand, Ty),
    /// Reference to a place
    Ref(Mutability, Place),
    /// Aggregate construction (tuple, struct, enum variant)
    Aggregate(AggregateKind, Vec<Operand>),
    /// Length of an array/slice
    Len(Place),
    /// Discriminant of an enum
    Discriminant(Place),
}

/// Aggregate kinds.
#[derive(Debug, Clone)]
pub enum AggregateKind {
    Tuple,
    Struct(String),
    Enum(String, usize),
    /// Closure environment construction (closure name)
    Closure(String),
}

/// An operand — either a place (variable) or a constant.
#[derive(Debug, Clone)]
pub enum Operand {
    /// Read from a place
    Copy(Place),
    /// Move from a place
    Move(Place),
    /// Compile-time constant
    Constant(Constant),
}

/// A place expression (l-value).
#[derive(Debug, Clone)]
pub struct Place {
    pub local: String,
    pub projections: Vec<Projection>,
}

impl Place {
    pub fn local(name: impl Into<String>) -> Self {
        Self {
            local: name.into(),
            projections: Vec::new(),
        }
    }

    pub fn field(mut self, idx: usize) -> Self {
        self.projections.push(Projection::Field(idx));
        self
    }

    pub fn index(mut self, operand: String) -> Self {
        self.projections.push(Projection::Index(operand));
        self
    }

    pub fn deref(mut self) -> Self {
        self.projections.push(Projection::Deref);
        self
    }
}

/// Place projection.
#[derive(Debug, Clone)]
pub enum Projection {
    /// Dereference: `*place`
    Deref,
    /// Struct field access by index
    Field(usize),
    /// Array/slice index: `place[idx]`
    Index(String),
    /// Downcast to enum variant
    Downcast(usize),
}

/// A constant value.
#[derive(Debug, Clone)]
pub enum Constant {
    Bool(bool),
    Int(i128, IntTy),
    Uint(u128, UintTy),
    Float(f64, FloatTy),
    Unit,
    /// String for unresolved constants
    Str(String),
}

/// Binary operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl BinOp {
    /// Returns true for comparison operations whose result is Bool
    /// but whose signedness depends on the operand types.
    pub fn is_comparison(self) -> bool {
        matches!(
            self,
            Self::Eq | Self::Ne | Self::Lt | Self::Le | Self::Gt | Self::Ge
        )
    }
}

/// Unary operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Not,
    Neg,
}

/// Cast kinds.
#[derive(Debug, Clone)]
pub enum CastKind {
    /// Integer-to-integer (widening, narrowing, sign change)
    IntToInt,
    /// Integer-to-float
    IntToFloat,
    /// Float-to-integer
    FloatToInt,
    /// Float-to-float
    FloatToFloat,
    /// Pointer casts
    Pointer,
}

/// Mutability flag.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mutability {
    Shared,
    Mutable,
}

/// Rust type representation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ty {
    Bool,
    Int(IntTy),
    Uint(UintTy),
    Float(FloatTy),
    Char,
    Unit,
    Never,
    Tuple(Vec<Ty>),
    Array(Box<Ty>, usize),
    Slice(Box<Ty>),
    Ref(Box<Ty>, Mutability),
    RawPtr(Box<Ty>, Mutability),
    Struct(String, Vec<(String, Ty)>),
    Enum(String, Vec<(String, Vec<Ty>)>),
    /// Opaque/unresolved type
    Named(String),
    /// Unbounded mathematical integer (specification-only).
    /// Used with `as int` casts in specs to express arithmetic without overflow.
    /// SOUNDNESS: Never silently mixed with bitvectors -- `as int` cast must be explicit.
    SpecInt,
    /// Non-negative unbounded integer (specification-only).
    /// Encoded as Int with non-negativity constraint added separately.
    SpecNat,
    /// Generic type parameter (e.g., T in fn foo<T>).
    /// Replaced with concrete types during monomorphization.
    Generic(String),
    /// Closure type with environment, parameters, return type, and trait kind.
    /// Box is used to avoid recursive type size explosion.
    Closure(Box<ClosureInfo>),
    /// Trait object type (dyn Trait).
    /// Represents dynamic dispatch via trait objects (Box<dyn Trait>, &dyn Trait, etc.).
    /// The outer container (Box, &, &mut) is represented separately via Ref/RawPtr wrappers.
    TraitObject(String),
}

/// Signed integer types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntTy {
    I8,
    I16,
    I32,
    I64,
    I128,
    Isize,
}

/// Unsigned integer types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UintTy {
    U8,
    U16,
    U32,
    U64,
    U128,
    Usize,
}

/// Floating-point types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FloatTy {
    F32,
    F64,
}

// === Helpers ===

impl IntTy {
    pub fn bit_width(self) -> u32 {
        match self {
            Self::I8 => 8,
            Self::I16 => 16,
            Self::I32 => 32,
            Self::I64 => 64,
            Self::I128 => 128,
            Self::Isize => 64, // assume 64-bit target
        }
    }

    pub fn min_value(self) -> i128 {
        match self {
            Self::I8 => i128::from(i8::MIN),
            Self::I16 => i128::from(i16::MIN),
            Self::I32 => i128::from(i32::MIN),
            Self::I64 => i128::from(i64::MIN),
            Self::I128 => i128::MIN,
            Self::Isize => i128::from(i64::MIN),
        }
    }

    pub fn max_value(self) -> i128 {
        match self {
            Self::I8 => i128::from(i8::MAX),
            Self::I16 => i128::from(i16::MAX),
            Self::I32 => i128::from(i32::MAX),
            Self::I64 => i128::from(i64::MAX),
            Self::I128 => i128::MAX,
            Self::Isize => i128::from(i64::MAX),
        }
    }
}

impl UintTy {
    pub fn bit_width(self) -> u32 {
        match self {
            Self::U8 => 8,
            Self::U16 => 16,
            Self::U32 => 32,
            Self::U64 => 64,
            Self::U128 => 128,
            Self::Usize => 64,
        }
    }

    pub fn max_value(self) -> u128 {
        match self {
            Self::U8 => u128::from(u8::MAX),
            Self::U16 => u128::from(u16::MAX),
            Self::U32 => u128::from(u32::MAX),
            Self::U64 => u128::from(u64::MAX),
            Self::U128 => u128::MAX,
            Self::Usize => u128::from(u64::MAX),
        }
    }
}

impl Ty {
    /// Returns the bit width for integer types, or `None` for non-integer types.
    pub fn bit_width(&self) -> Option<u32> {
        match self {
            Self::Bool => Some(1),
            Self::Int(ity) => Some(ity.bit_width()),
            Self::Uint(uty) => Some(uty.bit_width()),
            Self::Char => Some(32),
            Self::Generic(_) => None,
            _ => None,
        }
    }

    /// Whether this is a signed integer type.
    pub fn is_signed(&self) -> bool {
        matches!(self, Self::Int(_))
    }

    /// Whether this is an unsigned integer type.
    pub fn is_unsigned(&self) -> bool {
        matches!(self, Self::Uint(_))
    }

    /// Whether this is any integer type (signed or unsigned).
    pub fn is_integer(&self) -> bool {
        matches!(self, Self::Int(_) | Self::Uint(_))
    }

    /// Whether this is a boolean type.
    pub fn is_bool(&self) -> bool {
        matches!(self, Self::Bool)
    }

    /// Whether this is a specification-only unbounded integer type.
    pub fn is_spec_int(&self) -> bool {
        matches!(self, Self::SpecInt | Self::SpecNat)
    }

    /// Whether this is a closure type.
    pub fn is_closure(&self) -> bool {
        matches!(self, Self::Closure(_))
    }

    /// Whether this is a trait object type.
    pub fn is_trait_object(&self) -> bool {
        matches!(self, Self::TraitObject(_))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ====== Function::is_generic tests ======

    #[test]
    fn function_is_generic_true() {
        let func = Function {
            name: "foo".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            loops: vec![],
            generic_params: vec![GenericParam {
                name: "T".to_string(),
                trait_bounds: vec!["Ord".to_string()],
            }],
            prophecies: vec![],
            lifetime_params: vec![],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
        };
        assert!(func.is_generic());
    }

    #[test]
    fn function_is_generic_false() {
        let func = Function {
            name: "bar".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
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
        };
        assert!(!func.is_generic());
    }

    // ====== Function::has_mut_ref_params tests ======

    #[test]
    fn function_has_mut_ref_params_true() {
        let func = Function {
            name: "mutate".to_string(),
            params: vec![Local::new(
                "_1",
                Ty::Ref(Box::new(Ty::Int(IntTy::I32)), Mutability::Mutable),
            )],
            return_local: Local::new("_0", Ty::Unit),
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
        };
        assert!(func.has_mut_ref_params());
    }

    #[test]
    fn function_has_mut_ref_params_false_shared_ref() {
        let func = Function {
            name: "read".to_string(),
            params: vec![Local::new(
                "_1",
                Ty::Ref(Box::new(Ty::Int(IntTy::I32)), Mutability::Shared),
            )],
            return_local: Local::new("_0", Ty::Unit),
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
        };
        assert!(!func.has_mut_ref_params());
    }

    #[test]
    fn function_has_mut_ref_params_false_no_refs() {
        let func = Function {
            name: "pure".to_string(),
            params: vec![Local::new("_1", Ty::Int(IntTy::I32))],
            return_local: Local::new("_0", Ty::Unit),
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
        };
        assert!(!func.has_mut_ref_params());
    }

    #[test]
    fn function_has_mut_ref_params_false_empty() {
        let func = Function {
            name: "noargs".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
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
        };
        assert!(!func.has_mut_ref_params());
    }

    #[test]
    fn function_has_mut_ref_params_mixed() {
        let func = Function {
            name: "mixed".to_string(),
            params: vec![
                Local::new("_1", Ty::Int(IntTy::I32)),
                Local::new("_2", Ty::Ref(Box::new(Ty::Bool), Mutability::Mutable)),
            ],
            return_local: Local::new("_0", Ty::Unit),
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
        };
        assert!(func.has_mut_ref_params());
    }

    // ====== Local::new and Local::ghost tests ======

    #[test]
    fn local_new_is_not_ghost() {
        let local = Local::new("_1", Ty::Int(IntTy::I32));
        assert_eq!(local.name, "_1");
        assert_eq!(local.ty, Ty::Int(IntTy::I32));
        assert!(!local.is_ghost);
    }

    #[test]
    fn local_ghost_is_ghost() {
        let local = Local::ghost("spec_x", Ty::SpecInt);
        assert_eq!(local.name, "spec_x");
        assert_eq!(local.ty, Ty::SpecInt);
        assert!(local.is_ghost);
    }

    // ====== Place::deref tests ======

    #[test]
    fn place_deref_adds_projection() {
        let place = Place::local("_1").deref();
        assert_eq!(place.local, "_1");
        assert_eq!(place.projections.len(), 1);
        assert!(matches!(place.projections[0], Projection::Deref));
    }

    #[test]
    fn place_field_adds_projection() {
        let place = Place::local("_1").field(2);
        assert_eq!(place.projections.len(), 1);
        assert!(matches!(place.projections[0], Projection::Field(2)));
    }

    #[test]
    fn place_index_adds_projection() {
        let place = Place::local("_1").index("_2".to_string());
        assert_eq!(place.projections.len(), 1);
        assert!(matches!(&place.projections[0], Projection::Index(s) if s == "_2"));
    }

    #[test]
    fn place_chained_projections() {
        let place = Place::local("_1").deref().field(0);
        assert_eq!(place.projections.len(), 2);
        assert!(matches!(place.projections[0], Projection::Deref));
        assert!(matches!(place.projections[1], Projection::Field(0)));
    }

    // ====== BinOp::is_comparison tests ======

    #[test]
    fn binop_comparison_ops() {
        assert!(BinOp::Eq.is_comparison());
        assert!(BinOp::Ne.is_comparison());
        assert!(BinOp::Lt.is_comparison());
        assert!(BinOp::Le.is_comparison());
        assert!(BinOp::Gt.is_comparison());
        assert!(BinOp::Ge.is_comparison());
    }

    #[test]
    fn binop_arithmetic_not_comparison() {
        assert!(!BinOp::Add.is_comparison());
        assert!(!BinOp::Sub.is_comparison());
        assert!(!BinOp::Mul.is_comparison());
        assert!(!BinOp::Div.is_comparison());
        assert!(!BinOp::Rem.is_comparison());
    }

    #[test]
    fn binop_bitwise_not_comparison() {
        assert!(!BinOp::BitAnd.is_comparison());
        assert!(!BinOp::BitOr.is_comparison());
        assert!(!BinOp::BitXor.is_comparison());
        assert!(!BinOp::Shl.is_comparison());
        assert!(!BinOp::Shr.is_comparison());
    }

    // ====== Ty::is_signed tests ======

    #[test]
    fn ty_is_signed_for_int_types() {
        assert!(Ty::Int(IntTy::I8).is_signed());
        assert!(Ty::Int(IntTy::I16).is_signed());
        assert!(Ty::Int(IntTy::I32).is_signed());
        assert!(Ty::Int(IntTy::I64).is_signed());
        assert!(Ty::Int(IntTy::I128).is_signed());
        assert!(Ty::Int(IntTy::Isize).is_signed());
    }

    #[test]
    fn ty_is_signed_false_for_non_int() {
        assert!(!Ty::Uint(UintTy::U32).is_signed());
        assert!(!Ty::Bool.is_signed());
        assert!(!Ty::Unit.is_signed());
        assert!(!Ty::SpecInt.is_signed());
    }

    // ====== Ty::is_unsigned tests ======

    #[test]
    fn ty_is_unsigned_for_uint_types() {
        assert!(Ty::Uint(UintTy::U8).is_unsigned());
        assert!(Ty::Uint(UintTy::U16).is_unsigned());
        assert!(Ty::Uint(UintTy::U32).is_unsigned());
        assert!(Ty::Uint(UintTy::U64).is_unsigned());
        assert!(Ty::Uint(UintTy::U128).is_unsigned());
        assert!(Ty::Uint(UintTy::Usize).is_unsigned());
    }

    #[test]
    fn ty_is_unsigned_false_for_non_uint() {
        assert!(!Ty::Int(IntTy::I32).is_unsigned());
        assert!(!Ty::Bool.is_unsigned());
        assert!(!Ty::SpecInt.is_unsigned());
    }

    // ====== Ty::is_integer tests ======

    #[test]
    fn ty_is_integer_signed() {
        assert!(Ty::Int(IntTy::I32).is_integer());
    }

    #[test]
    fn ty_is_integer_unsigned() {
        assert!(Ty::Uint(UintTy::U64).is_integer());
    }

    #[test]
    fn ty_is_integer_false_for_non_int() {
        assert!(!Ty::Bool.is_integer());
        assert!(!Ty::Unit.is_integer());
        assert!(!Ty::Float(FloatTy::F64).is_integer());
        assert!(!Ty::SpecInt.is_integer());
    }

    // ====== Ty::is_bool tests ======

    #[test]
    fn ty_is_bool_true() {
        assert!(Ty::Bool.is_bool());
    }

    #[test]
    fn ty_is_bool_false() {
        assert!(!Ty::Int(IntTy::I32).is_bool());
        assert!(!Ty::Unit.is_bool());
    }

    // ====== Ty::is_spec_int tests ======

    #[test]
    fn ty_is_spec_int_for_spec_int() {
        assert!(Ty::SpecInt.is_spec_int());
    }

    #[test]
    fn ty_is_spec_int_for_spec_nat() {
        assert!(Ty::SpecNat.is_spec_int());
    }

    #[test]
    fn ty_is_spec_int_false_for_regular_int() {
        assert!(!Ty::Int(IntTy::I32).is_spec_int());
        assert!(!Ty::Uint(UintTy::U64).is_spec_int());
        assert!(!Ty::Bool.is_spec_int());
    }

    // ====== Ty::bit_width tests ======

    #[test]
    fn ty_bit_width_bool() {
        assert_eq!(Ty::Bool.bit_width(), Some(1));
    }

    #[test]
    fn ty_bit_width_signed() {
        assert_eq!(Ty::Int(IntTy::I8).bit_width(), Some(8));
        assert_eq!(Ty::Int(IntTy::I32).bit_width(), Some(32));
        assert_eq!(Ty::Int(IntTy::I64).bit_width(), Some(64));
    }

    #[test]
    fn ty_bit_width_unsigned() {
        assert_eq!(Ty::Uint(UintTy::U8).bit_width(), Some(8));
        assert_eq!(Ty::Uint(UintTy::U32).bit_width(), Some(32));
    }

    #[test]
    fn ty_bit_width_char() {
        assert_eq!(Ty::Char.bit_width(), Some(32));
    }

    #[test]
    fn ty_bit_width_none_for_non_integer() {
        assert_eq!(Ty::Unit.bit_width(), None);
        assert_eq!(Ty::Float(FloatTy::F64).bit_width(), None);
        assert_eq!(Ty::Generic("T".to_string()).bit_width(), None);
    }

    // ====== IntTy helper tests ======

    #[test]
    fn int_ty_bit_widths() {
        assert_eq!(IntTy::I8.bit_width(), 8);
        assert_eq!(IntTy::I16.bit_width(), 16);
        assert_eq!(IntTy::I32.bit_width(), 32);
        assert_eq!(IntTy::I64.bit_width(), 64);
        assert_eq!(IntTy::I128.bit_width(), 128);
        assert_eq!(IntTy::Isize.bit_width(), 64);
    }

    #[test]
    fn int_ty_min_max_i8() {
        assert_eq!(IntTy::I8.min_value(), -128);
        assert_eq!(IntTy::I8.max_value(), 127);
    }

    #[test]
    fn int_ty_min_max_i32() {
        assert_eq!(IntTy::I32.min_value(), i128::from(i32::MIN));
        assert_eq!(IntTy::I32.max_value(), i128::from(i32::MAX));
    }

    // ====== UintTy helper tests ======

    #[test]
    fn uint_ty_bit_widths() {
        assert_eq!(UintTy::U8.bit_width(), 8);
        assert_eq!(UintTy::U16.bit_width(), 16);
        assert_eq!(UintTy::U32.bit_width(), 32);
        assert_eq!(UintTy::U64.bit_width(), 64);
        assert_eq!(UintTy::U128.bit_width(), 128);
        assert_eq!(UintTy::Usize.bit_width(), 64);
    }

    #[test]
    fn uint_ty_max_u8() {
        assert_eq!(UintTy::U8.max_value(), 255);
    }

    #[test]
    fn uint_ty_max_u32() {
        assert_eq!(UintTy::U32.max_value(), u128::from(u32::MAX));
    }

    #[test]
    fn uint_ty_max_u128() {
        assert_eq!(UintTy::U128.max_value(), u128::MAX);
    }

    // ====== Contracts.decreases tests (Phase 6) ======

    #[test]
    fn test_contracts_default_has_no_decreases() {
        let contracts = Contracts::default();
        assert!(contracts.decreases.is_none());
    }

    #[test]
    fn test_contracts_with_decreases() {
        let contracts = Contracts {
            decreases: Some(SpecExpr {
                raw: "n".to_string(),
            }),
            ..Default::default()
        };
        assert!(contracts.decreases.is_some());
        assert_eq!(contracts.decreases.unwrap().raw, "n");
    }

    // ====== Closure types tests (Phase 7) ======

    #[test]
    fn test_closure_trait_equality() {
        assert_eq!(ClosureTrait::Fn, ClosureTrait::Fn);
        assert_eq!(ClosureTrait::FnMut, ClosureTrait::FnMut);
        assert_eq!(ClosureTrait::FnOnce, ClosureTrait::FnOnce);
        assert_ne!(ClosureTrait::Fn, ClosureTrait::FnMut);
        assert_ne!(ClosureTrait::Fn, ClosureTrait::FnOnce);
        assert_ne!(ClosureTrait::FnMut, ClosureTrait::FnOnce);
    }

    #[test]
    fn test_closure_info_creation() {
        let env_fields = vec![
            ("captured_x".to_string(), Ty::Int(IntTy::I32)),
            ("captured_y".to_string(), Ty::Bool),
        ];
        let params = vec![("arg1".to_string(), Ty::Int(IntTy::I32))];
        let return_ty = Ty::Bool;
        let trait_kind = ClosureTrait::Fn;

        let info = ClosureInfo {
            name: "closure_test".to_string(),
            env_fields: env_fields.clone(),
            params: params.clone(),
            return_ty: return_ty.clone(),
            trait_kind,
        };

        assert_eq!(info.name, "closure_test");
        assert_eq!(info.env_fields.len(), 2);
        assert_eq!(info.env_fields[0].0, "captured_x");
        assert_eq!(info.env_fields[0].1, Ty::Int(IntTy::I32));
        assert_eq!(info.params.len(), 1);
        assert_eq!(info.params[0].0, "arg1");
        assert_eq!(info.return_ty, Ty::Bool);
        assert_eq!(info.trait_kind, ClosureTrait::Fn);
    }

    #[test]
    fn test_ty_closure_variant() {
        let info = ClosureInfo {
            name: "closure_add".to_string(),
            env_fields: vec![("x".to_string(), Ty::Int(IntTy::I32))],
            params: vec![("y".to_string(), Ty::Int(IntTy::I32))],
            return_ty: Ty::Int(IntTy::I32),
            trait_kind: ClosureTrait::Fn,
        };
        let closure_ty = Ty::Closure(Box::new(info));
        assert!(closure_ty.is_closure());
    }

    #[test]
    fn test_ty_non_closure_is_not_closure() {
        assert!(!Ty::Int(IntTy::I32).is_closure());
        assert!(!Ty::Bool.is_closure());
        assert!(!Ty::Unit.is_closure());
        assert!(!Ty::SpecInt.is_closure());
    }

    #[test]
    fn test_aggregate_kind_closure() {
        let closure_agg = AggregateKind::Closure("test_closure".to_string());
        let debug_output = format!("{:?}", closure_agg);
        assert!(debug_output.contains("Closure"));
        assert!(debug_output.contains("test_closure"));
    }

    // ====== Trait types tests (Phase 8) ======

    #[test]
    fn test_trait_method_creation() {
        let method = TraitMethod {
            name: "push".to_string(),
            params: vec![
                (
                    "self".to_string(),
                    Ty::Ref(
                        Box::new(Ty::Named("Stack".to_string())),
                        Mutability::Mutable,
                    ),
                ),
                ("item".to_string(), Ty::Int(IntTy::I32)),
            ],
            return_ty: Ty::Unit,
            requires: vec![SpecExpr {
                raw: "item > 0".to_string(),
            }],
            ensures: vec![SpecExpr {
                raw: "self.len() == old(self.len()) + 1".to_string(),
            }],
            is_pure: false,
        };
        assert_eq!(method.name, "push");
        assert_eq!(method.params.len(), 2);
        assert_eq!(method.requires.len(), 1);
        assert_eq!(method.ensures.len(), 1);
        assert!(!method.is_pure);
    }

    #[test]
    fn test_trait_def_creation() {
        let trait_def = TraitDef {
            name: "Stack".to_string(),
            methods: vec![TraitMethod {
                name: "push".to_string(),
                params: vec![],
                return_ty: Ty::Unit,
                requires: vec![],
                ensures: vec![],
                is_pure: false,
            }],
            is_sealed: false,
            super_traits: vec![],
        };
        assert_eq!(trait_def.name, "Stack");
        assert_eq!(trait_def.methods.len(), 1);
        assert!(!trait_def.is_sealed);
        assert_eq!(trait_def.super_traits.len(), 0);
    }

    #[test]
    fn test_trait_def_sealed() {
        let sealed_trait = TraitDef {
            name: "InternalStack".to_string(),
            methods: vec![],
            is_sealed: true,
            super_traits: vec![],
        };
        assert!(sealed_trait.is_sealed);

        let public_trait = TraitDef {
            name: "PublicStack".to_string(),
            methods: vec![],
            is_sealed: false,
            super_traits: vec![],
        };
        assert!(!public_trait.is_sealed);
    }

    #[test]
    fn test_trait_impl_creation() {
        let trait_impl = TraitImpl {
            trait_name: "Stack".to_string(),
            impl_type: "VecStack".to_string(),
            method_names: vec!["push".to_string(), "pop".to_string()],
        };
        assert_eq!(trait_impl.trait_name, "Stack");
        assert_eq!(trait_impl.impl_type, "VecStack");
        assert_eq!(trait_impl.method_names.len(), 2);
        assert_eq!(trait_impl.method_names[0], "push");
    }

    #[test]
    fn test_ty_trait_object() {
        let trait_obj = Ty::TraitObject("Stack".to_string());
        assert!(trait_obj.is_trait_object());
        if let Ty::TraitObject(name) = trait_obj {
            assert_eq!(name, "Stack");
        } else {
            panic!("Expected TraitObject variant");
        }
    }

    #[test]
    fn test_ty_non_trait_object_is_not_trait_object() {
        assert!(!Ty::Int(IntTy::I32).is_trait_object());
        assert!(!Ty::Bool.is_trait_object());
        assert!(!Ty::Unit.is_trait_object());
        assert!(!Ty::SpecInt.is_trait_object());
        assert!(
            !Ty::Closure(Box::new(ClosureInfo {
                name: "test".to_string(),
                env_fields: vec![],
                params: vec![],
                return_ty: Ty::Unit,
                trait_kind: ClosureTrait::Fn,
            }))
            .is_trait_object()
        );
    }

    // ====== Lifetime IR types tests ======

    #[test]
    fn test_lifetime_param_creation() {
        let lifetime = LifetimeParam {
            name: "'a".to_string(),
            is_static: false,
        };
        assert_eq!(lifetime.name, "'a");
        assert!(!lifetime.is_static);
    }

    #[test]
    fn test_lifetime_param_static() {
        let static_lifetime = LifetimeParam {
            name: "'static".to_string(),
            is_static: true,
        };
        assert_eq!(static_lifetime.name, "'static");
        assert!(static_lifetime.is_static);
    }

    #[test]
    fn test_outlives_constraint() {
        let constraint = OutlivesConstraint {
            longer: "'a".to_string(),
            shorter: "'b".to_string(),
        };
        assert_eq!(constraint.longer, "'a");
        assert_eq!(constraint.shorter, "'b");
    }

    #[test]
    fn test_borrow_info_shared() {
        let borrow = BorrowInfo {
            local_name: "_1".to_string(),
            region: "'a".to_string(),
            is_mutable: false,
            deref_level: 0,
            source_local: None,
        };
        assert_eq!(borrow.local_name, "_1");
        assert_eq!(borrow.region, "'a");
        assert!(!borrow.is_mutable);
        assert_eq!(borrow.deref_level, 0);
        assert!(borrow.source_local.is_none());
    }

    #[test]
    fn test_borrow_info_mutable() {
        let borrow = BorrowInfo {
            local_name: "_2".to_string(),
            region: "'b".to_string(),
            is_mutable: true,
            deref_level: 0,
            source_local: None,
        };
        assert!(borrow.is_mutable);
    }

    #[test]
    fn test_borrow_info_reborrow() {
        let borrow = BorrowInfo {
            local_name: "_3".to_string(),
            region: "'c".to_string(),
            is_mutable: true,
            deref_level: 1,
            source_local: Some("_2".to_string()),
        };
        assert_eq!(borrow.deref_level, 1);
        assert_eq!(borrow.source_local, Some("_2".to_string()));
    }

    #[test]
    fn test_reborrow_chain() {
        let chain = ReborrowChain {
            original: "_1".to_string(),
            reborrows: vec!["_2".to_string(), "_3".to_string()],
        };
        assert_eq!(chain.original, "_1");
        assert_eq!(chain.reborrows.len(), 2);
        assert_eq!(chain.reborrows[0], "_2");
        assert_eq!(chain.reborrows[1], "_3");
    }

    #[test]
    fn test_function_lifetime_fields() {
        let func = Function {
            name: "test_fn".to_string(),
            params: vec![],
            return_local: Local::new("_0", Ty::Unit),
            locals: vec![],
            basic_blocks: vec![],
            contracts: Contracts::default(),
            loops: vec![],
            generic_params: vec![],
            prophecies: vec![],
            lifetime_params: vec![LifetimeParam {
                name: "'a".to_string(),
                is_static: false,
            }],
            outlives_constraints: vec![],
            borrow_info: vec![],
            reborrow_chains: vec![],
        };
        assert_eq!(func.lifetime_params.len(), 1);
        assert_eq!(func.lifetime_params[0].name, "'a");
        assert_eq!(func.outlives_constraints.len(), 0);
        assert_eq!(func.borrow_info.len(), 0);
        assert_eq!(func.reborrow_chains.len(), 0);
    }
}
