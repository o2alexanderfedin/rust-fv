use crate::sort::Sort;

/// SMT-LIB term (expression) representation.
#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    // === Literals ===
    /// Boolean literal
    BoolLit(bool),
    /// Integer literal (unbounded)
    IntLit(i128),
    /// Bitvector literal with value and width
    BitVecLit(i128, u32),

    // === Variables ===
    /// Named constant/variable reference
    Const(String),

    // === Boolean operations ===
    /// Logical NOT
    Not(Box<Term>),
    /// Logical AND (n-ary)
    And(Vec<Term>),
    /// Logical OR (n-ary)
    Or(Vec<Term>),
    /// Logical implication: `(=> a b)`
    Implies(Box<Term>, Box<Term>),
    /// Logical if-and-only-if: `(= a b)` for Bool
    Iff(Box<Term>, Box<Term>),

    // === Core ===
    /// Equality: `(= a b)`
    Eq(Box<Term>, Box<Term>),
    /// Distinct: `(distinct a b ...)`
    Distinct(Vec<Term>),
    /// If-then-else: `(ite cond then else)`
    Ite(Box<Term>, Box<Term>, Box<Term>),

    // === Bitvector arithmetic ===
    /// `(bvadd a b)`
    BvAdd(Box<Term>, Box<Term>),
    /// `(bvsub a b)`
    BvSub(Box<Term>, Box<Term>),
    /// `(bvmul a b)`
    BvMul(Box<Term>, Box<Term>),
    /// `(bvsdiv a b)` — signed division
    BvSDiv(Box<Term>, Box<Term>),
    /// `(bvudiv a b)` — unsigned division
    BvUDiv(Box<Term>, Box<Term>),
    /// `(bvsrem a b)` — signed remainder
    BvSRem(Box<Term>, Box<Term>),
    /// `(bvurem a b)` — unsigned remainder
    BvURem(Box<Term>, Box<Term>),
    /// `(bvneg a)` — two's complement negation
    BvNeg(Box<Term>),

    // === Bitvector comparison (signed) ===
    /// `(bvslt a b)` — signed less-than
    BvSLt(Box<Term>, Box<Term>),
    /// `(bvsle a b)` — signed less-or-equal
    BvSLe(Box<Term>, Box<Term>),
    /// `(bvsgt a b)` — signed greater-than
    BvSGt(Box<Term>, Box<Term>),
    /// `(bvsge a b)` — signed greater-or-equal
    BvSGe(Box<Term>, Box<Term>),

    // === Bitvector comparison (unsigned) ===
    /// `(bvult a b)` — unsigned less-than
    BvULt(Box<Term>, Box<Term>),
    /// `(bvule a b)` — unsigned less-or-equal
    BvULe(Box<Term>, Box<Term>),
    /// `(bvugt a b)` — unsigned greater-than
    BvUGt(Box<Term>, Box<Term>),
    /// `(bvuge a b)` — unsigned greater-or-equal
    BvUGe(Box<Term>, Box<Term>),

    // === Bitvector bitwise ===
    /// `(bvand a b)`
    BvAnd(Box<Term>, Box<Term>),
    /// `(bvor a b)`
    BvOr(Box<Term>, Box<Term>),
    /// `(bvxor a b)`
    BvXor(Box<Term>, Box<Term>),
    /// `(bvnot a)`
    BvNot(Box<Term>),
    /// `(bvshl a b)` — shift left
    BvShl(Box<Term>, Box<Term>),
    /// `(bvlshr a b)` — logical shift right
    BvLShr(Box<Term>, Box<Term>),
    /// `(bvashr a b)` — arithmetic shift right
    BvAShr(Box<Term>, Box<Term>),

    // === Bitvector conversion ===
    /// `((_ zero_extend n) a)`
    ZeroExtend(u32, Box<Term>),
    /// `((_ sign_extend n) a)`
    SignExtend(u32, Box<Term>),
    /// `((_ extract hi lo) a)`
    Extract(u32, u32, Box<Term>),
    /// `(concat a b)`
    Concat(Box<Term>, Box<Term>),
    /// `(bv2int a)` — convert bitvector to unbounded integer
    Bv2Int(Box<Term>),
    /// `((_ int2bv n) a)` — convert integer to n-bit bitvector
    Int2Bv(u32, Box<Term>),

    // === Integer arithmetic ===
    /// `(+ a b)`
    IntAdd(Box<Term>, Box<Term>),
    /// `(- a b)`
    IntSub(Box<Term>, Box<Term>),
    /// `(* a b)`
    IntMul(Box<Term>, Box<Term>),
    /// `(div a b)` — integer division
    IntDiv(Box<Term>, Box<Term>),
    /// `(mod a b)`
    IntMod(Box<Term>, Box<Term>),
    /// `(- a)` — integer negation
    IntNeg(Box<Term>),
    /// `(< a b)`
    IntLt(Box<Term>, Box<Term>),
    /// `(<= a b)`
    IntLe(Box<Term>, Box<Term>),
    /// `(> a b)`
    IntGt(Box<Term>, Box<Term>),
    /// `(>= a b)`
    IntGe(Box<Term>, Box<Term>),

    // === Array operations ===
    /// `(select array index)`
    Select(Box<Term>, Box<Term>),
    /// `(store array index value)`
    Store(Box<Term>, Box<Term>, Box<Term>),

    // === Quantifiers ===
    /// `(forall ((x Sort) ...) body)`
    Forall(Vec<(String, Sort)>, Box<Term>),
    /// `(exists ((x Sort) ...) body)`
    Exists(Vec<(String, Sort)>, Box<Term>),

    // === Let bindings ===
    /// `(let ((x t) ...) body)`
    Let(Vec<(String, Term)>, Box<Term>),

    // === Function application ===
    /// `(f arg1 arg2 ...)`
    App(String, Vec<Term>),

    // === Annotations ===
    /// Annotated term: `(! body :key1 (val1 val2) :key2 (val3))`
    /// Used for trigger patterns on quantifiers: `(! body :pattern (f x))`
    Annotated(Box<Term>, Vec<(String, Vec<Term>)>),

    // === Floating-point literals ===
    /// IEEE 754 NaN: `(_ NaN eb sb)`
    FpNaN(u32, u32),
    /// Positive infinity: `(_ +oo eb sb)`
    FpPosInf(u32, u32),
    /// Negative infinity: `(_ -oo eb sb)`
    FpNegInf(u32, u32),
    /// Positive zero: `(_ +zero eb sb)`
    FpPosZero(u32, u32),
    /// Negative zero: `(_ -zero eb sb)`
    FpNegZero(u32, u32),
    /// Bit representation: `(fp sign exp sig)` with eb, sb
    FpFromBits(u8, u64, u64, u32, u32),

    // === Rounding mode ===
    /// Rounding mode: RNE, RNA, RTP, RTN, RTZ
    RoundingMode(String),

    // === Floating-point arithmetic ===
    /// `(fp.add rm x y)`
    FpAdd(Box<Term>, Box<Term>, Box<Term>),
    /// `(fp.sub rm x y)`
    FpSub(Box<Term>, Box<Term>, Box<Term>),
    /// `(fp.mul rm x y)`
    FpMul(Box<Term>, Box<Term>, Box<Term>),
    /// `(fp.div rm x y)`
    FpDiv(Box<Term>, Box<Term>, Box<Term>),
    /// `(fp.sqrt rm x)`
    FpSqrt(Box<Term>, Box<Term>),
    /// `(fp.abs x)`
    FpAbs(Box<Term>),
    /// `(fp.neg x)`
    FpNeg(Box<Term>),

    // === Floating-point comparison ===
    /// `(fp.eq x y)` — IEEE 754 equality
    FpEq(Box<Term>, Box<Term>),
    /// `(fp.lt x y)`
    FpLt(Box<Term>, Box<Term>),
    /// `(fp.leq x y)`
    FpLeq(Box<Term>, Box<Term>),
    /// `(fp.gt x y)`
    FpGt(Box<Term>, Box<Term>),
    /// `(fp.geq x y)`
    FpGeq(Box<Term>, Box<Term>),

    // === Floating-point predicates ===
    /// `(fp.isNaN x)`
    FpIsNaN(Box<Term>),
    /// `(fp.isInfinite x)`
    FpIsInfinite(Box<Term>),
    /// `(fp.isZero x)`
    FpIsZero(Box<Term>),
    /// `(fp.isNegative x)`
    FpIsNegative(Box<Term>),
    /// `(fp.isPositive x)`
    FpIsPositive(Box<Term>),
}
