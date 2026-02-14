/// SMT-LIB sort (type) representation.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Sort {
    /// Boolean sort
    Bool,
    /// Mathematical integer sort
    Int,
    /// Real number sort
    Real,
    /// Fixed-width bitvector: `(_ BitVec n)`
    BitVec(u32),
    /// Array sort: `(Array index_sort element_sort)`
    Array(Box<Sort>, Box<Sort>),
    /// Named datatype (user-defined)
    Datatype(String),
    /// IEEE 754 floating-point: `(_ FloatingPoint e s)`
    Float(u32, u32),
    /// Uninterpreted sort
    Uninterpreted(String),
    /// Sequence sort: `(Seq T)` — SMT-LIB sequence theory
    Seq(Box<Sort>),
}
