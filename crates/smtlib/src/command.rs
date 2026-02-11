use crate::sort::Sort;
use crate::term::Term;

/// A single constructor variant in an SMT-LIB datatype declaration.
///
/// Each variant has a constructor name and zero or more named fields (selectors).
#[derive(Debug, Clone, PartialEq)]
pub struct DatatypeVariant {
    /// Constructor name (e.g., `mk-Point`, `mk-None`, `mk-Some`)
    pub constructor: String,
    /// Selector fields: `(name, sort)` pairs
    pub fields: Vec<(String, Sort)>,
}

/// SMT-LIB command representation.
#[derive(Debug, Clone, PartialEq)]
pub enum Command {
    /// `(set-logic LOGIC)`
    SetLogic(String),
    /// `(set-option :key value)`
    SetOption(String, String),
    /// `(declare-sort name arity)`
    DeclareSort(String, u32),
    /// `(define-sort name (params...) body)`
    DefineSort(String, Vec<String>, Sort),
    /// `(declare-const name sort)`
    DeclareConst(String, Sort),
    /// `(declare-fun name (param_sorts...) return_sort)`
    DeclareFun(String, Vec<Sort>, Sort),
    /// `(define-fun name ((param sort)...) return_sort body)`
    DefineFun(String, Vec<(String, Sort)>, Sort, Term),
    /// `(assert term)`
    Assert(Term),
    /// `(check-sat)`
    CheckSat,
    /// `(get-model)`
    GetModel,
    /// `(get-value (terms...))`
    GetValue(Vec<Term>),
    /// `(push n)`
    Push(u32),
    /// `(pop n)`
    Pop(u32),
    /// `(echo "message")`
    Echo(String),
    /// `;; comment`
    Comment(String),
    /// `(exit)`
    Exit,
    /// `(declare-datatype name ((constructor (field sort) ...)))`
    DeclareDatatype {
        name: String,
        variants: Vec<DatatypeVariant>,
    },
}
