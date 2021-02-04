//! MMC name resolution pass.
use std::sync::Arc;
use std::collections::{HashMap, hash_map::Entry};
use std::{rc::Rc, result::Result as StdResult};
use crate::elab::{
  Result, ElabError,
  local_context::try_get_span_from,
  environment::{AtomId, Environment}};
use crate::util::FileSpan;
use super::{Compiler, types::{self, Ast, Proc, ProcKind}, parser::TuplePattern};

macro_rules! make_prims {
  {$($(#[$attr0:meta])* enum $name:ident { $($(#[$attr:meta])* $x:ident: $e:expr,)* })* } => {
    $(
      $(#[$attr0])*
      #[derive(Debug, PartialEq, Eq, Copy, Clone)]
      pub enum $name { $($(#[$attr])* $x),* }
      $crate::deep_size_0!($name);

      impl $name {
        /// Evaluate a function on all elements of the type, with their names.
        pub fn scan(mut f: impl FnMut(Self, &'static str)) {
          $(f($name::$x, $e);)*
        }
        /// Convert a string into this type.
        #[allow(clippy::should_implement_trait)]
        #[must_use] pub fn from_str(s: &str) -> Option<Self> {
          match s {
            $($e => Some(Self::$x),)*
            _ => None
          }
        }
        /// Convert a byte string into this type.
        #[must_use] pub fn from_bytes(s: &[u8]) -> Option<Self> {
          // Safety: the function we defined just above doesn't do anything
          // dangerous with the &str
          Self::from_str(unsafe {std::str::from_utf8_unchecked(s)})
        }
      }
    )*
  }
}

make_prims! {
  /// The primitive operations.
  enum PrimOp {
    /// `{x + y}` returns the integer sum of the arguments
    Add: "+",
    /// `(and x1 ... xn)` returns the boolean `AND` of the arguments.
    And: "and",
    /// `{x as T}` performs truncation and non-value preserving casts a la `reinterpret_cast`.
    As: "as",
    /// `(assert p)` evaluates `p` and if it is false, crashes the program with an error.
    /// It returns a proof that `p` is true (because if `p` is false then the
    /// rest of the function is not evaluated).
    Assert: "assert",
    /// `(band e1 ... en)` returns the bitwise `AND` of the arguments.
    BitAnd: "band",
    /// `(bnot e1 ... en)` returns the bitwise `NOR` of the arguments,
    /// usually used in the unary case as `NOT`
    BitNot: "bnot",
    /// `(bor e1 ... en)` returns the bitwise `OR` of the arguments.
    BitOr: "bor",
    /// `(bxor e1 ... en)` returns the bitwise `XOR` of the arguments.
    BitXor: "bxor",
    /// `{x == y}` returns true if `x` is equal to `y`
    Eq: "==",
    /// `(ghost x)` returns the same thing as `x` but in the type `(ghost A)`.
    Ghost: "ghost",
    /// The function `(index a i h)` is the equivalent of `C`'s `a[i]`;
    /// it has type `(own T)` if `a` has type `(own (array T i))` and type `(& T)`
    /// if `a` has type `(& (array T i))`. The hypothesis `h` is a proof that
    /// `i` is in the bounds of the array.
    Index: "index",
    /// `{x * y}` returns the integer product of the arguments
    Mul: "*",
    /// `{x != y}` returns true if `x` is not equal to `y`
    Ne: "!=",
    /// `(not x1 ... xn)` returns the boolean `NOR` of the arguments,
    /// usually used in the unary case as `NOT`
    Not: "not",
    /// `(or x1 ... xn)` returns the boolean `OR` of the arguments.
    Or: "or",
    /// `{x <= y}` returns true if `x` is less than or equal to `y`
    Le: "<=",
    /// `(list e1 ... en)` returns a tuple of the arguments.
    List: "list",
    /// `{x < y}` returns true if `x` is less than `y`
    Lt: "<",
    /// `(pure $e$)` embeds an MM0 expression `$e$` as the target type,
    /// one of the numeric types
    Pure: "pure",
    /// `(pun x h)` returns a value of type `T` if `h` proves `x` has type `T`.
    Pun: "pun",
    /// If `x: (& (array T n))`, then `(slice {x + b} h): (& (array T a))` if
    /// `h` is a proof that `b + a <= n`. Computationally this corresponds to
    /// simply `x + b * sizeof T`, in the manner of C pointer arithmetic.
    Slice: "slice",
    /// `{e : T}` is `e`, with the type `T`. This is used only to direct
    /// type inference, it has no effect otherwise.
    Typed: ":",
    /// If `x` has type `T`, then `(typeof! x)` is a tuple `(x', h)` where `x'` has
    /// a copy type of the same size as `T`, such as `u64` if `sizeof T == 8`, and
    /// `h` is a proof that `x' :> T`. This consumes `x`, so usually `x'` should
    /// be named `x` to shadow it.
    TypeofBang: "typeof!",
    /// If `x` has type `T` where `T` is a copy type, then `(typeof x)` is a
    /// proof that `x :> T`. This version of `typeof!` only works on copy types
    /// so that it doesn't consume `x`.
    Typeof: "typeof",
  }

  /// The primitive types.
  enum PrimType {
    /// `(and A B C)` is an intersection type of `A, B, C`;
    /// `sizeof (and A B C) = max (sizeof A, sizeof B, sizeof C)`, and
    /// the typehood predicate is `x :> (inter A B C)` iff
    /// `x :> A /\ x :> B /\ x :> C`. (Note that this is regular conjunction,
    /// not separating conjunction.)
    And: "and",
    /// The type `(array T n)` is an array of `n` elements of type `T`;
    /// `sizeof (array T n) = sizeof T * n`.
    Array: "array",
    /// `bool` is the type of booleans, that is, bytes which are 0 or 1; `sizeof bool = 1`.
    Bool: "bool",
    /// `(ghost A)` is a compoutationally irrelevant version of `A`, which means
    /// that the logical storage of `(ghost A)` is the same as `A` but the physical storage
    /// is the same as `()`. `sizeof (ghost A) = 0`.
    Ghost: "ghost",
    /// `i8` is the type of 8 bit signed integers; `sizeof i8 = 1`.
    I8: "i8",
    /// `i16` is the type of 16 bit signed integers; `sizeof i16 = 2`.
    I16: "i16",
    /// `i32` is the type of 32 bit signed integers; `sizeof i32 = 4`.
    I32: "i32",
    /// `i64` is the type of 64 bit signed integers; `sizeof i64 = 8`.
    I64: "i64",
    /// The input token (passed to functions that read from input)
    Input: "Input",
    /// `int` is the type of unbounded signed integers; `sizeof int = inf`.
    Int: "int",
    /// `(A, B, C)` is a tuple type with elements `A, B, C`;
    /// `sizeof (A, B, C) = sizeof A + sizeof B + sizeof C`.
    List: "list",
    /// `nat` is the type of unbounded unsigned integers; `sizeof nat = inf`.
    Nat: "nat",
    /// `(or A B C)` is an undiscriminated anonymous union of types `A, B, C`.
    /// `sizeof (or A B C) = max (sizeof A, sizeof B, sizeof C)`, and
    /// the typehood predicate is `x :> (or A B C)` iff
    /// `x :> A \/ x :> B \/ x :> C`.
    Or: "or",
    /// The output token (passed to functions that produce output)
    Output: "Output",
    /// `own T` is a type of owned pointers. The typehood predicate is
    /// `x :> own T` iff `E. v (x |-> v) * v :> T`.
    Own: "own",
    /// `(& T)` is a type of borrowed pointers. This type is elaborated to
    /// `(& a T)` where `a` is a lifetime; this is handled a bit differently than rust
    /// (see [`Lifetime`](super::types::Lifetime)).
    Ref: "&",
    /// `&sn e` is a type of pointers to a place `e`.
    /// This type has the property that if `x: &sn e` then `*x` evaluates to
    /// the place `e`, which can be read or written.
    RefSn: "&sn",
    /// `(sn {a : T})` the type of values of type `T` that are equal to `a`.
    /// This is useful for asserting that a computationally relevant value can be
    /// expressed in terms of computationally irrelevant parts.
    Single: "sn",
    /// `u8` is the type of 8 bit unsigned integers; `sizeof u8 = 1`.
    U8: "u8",
    /// `u16` is the type of 16 bit unsigned integers; `sizeof u16 = 2`.
    U16: "u16",
    /// `u32` is the type of 32 bit unsigned integers; `sizeof u32 = 4`.
    U32: "u32",
    /// `u64` is the type of 64 bit unsigned integers; `sizeof u64 = 8`.
    U64: "u64",
  }

  /// A primitive propositional connective.
  enum PrimProp {
    /// `A. {x : A} p` or `(al {x : A} p)` is universal quantification over a type.
    All: "al",
    /// `E. {x : A} p` or `(ex {x : A} p)` is existential quantification over a type.
    Ex: "ex",
    /// `p /\ q` is the (non-separating) conjunction.
    And: "an",
    /// `p \/ q` is disjunction.
    Or: "or",
    /// `p -> q` is (regular) implication.
    Imp: "->",
    /// `p * q` is separating conjunction.
    Star: "*",
    /// `p -* q` is separating implication.
    Wand: "-*",
    /// `pure p` embeds a MM0 propositional expression.
    Pure: "pure",
  }

  /// Intrinsic functions, which are like [`PrimOp`] but are typechecked like regular
  /// function calls.
  enum Intrinsic {
    /// Intrinsic for the [`fstat`](https://man7.org/linux/man-pages/man2/fstat.2.html) system call.
    FStat: "sys_fstat",
    /// Intrinsic for the [`open`](https://man7.org/linux/man-pages/man2/open.2.html) system call.
    Open: "sys_open",
    /// Intrinsic for the [`mmap`](https://man7.org/linux/man-pages/man2/mmap.2.html) system call.
    MMap: "sys_mmap",
  }
}

/// An entity representing a type.
#[derive(Clone, Debug, DeepSizeOf)]
#[allow(variant_size_differences)]
pub enum Type {
  /// A user type that has not yet been typechecked.
  Unchecked,
  /// A user type that has been typechecked, with the original span,
  /// the (internal) declaration name, and the compiled [`Type`] object.
  Checked(Option<FileSpan>, AtomId, Rc<types::Type>),
}

/// The typechecking status of a procedure.
#[derive(Copy, Clone, Debug, DeepSizeOf)]
pub enum ProcTc {
  /// We have determined that this is a procedure but we have not yet examined the body.
  Unchecked,
  /// This is a compiler intrinsic function.
  Intrinsic(Intrinsic),
}

/// A function / procedure / builtin operator, which is called with function call style.
#[derive(Clone, Debug, DeepSizeOf)]
#[allow(variant_size_differences)]
pub enum Operator {
  /// A user procedure, with a link to the procedure definition and the typechecking status.
  Proc(Arc<Proc>, ProcTc),
}

/// The typechecking status of a global variable.
#[derive(Clone, Debug, DeepSizeOf)]
pub enum GlobalTc {
  /// We know this is a global or const but have not typechecked the body.
  Unchecked,
  /// A user type that has been typechecked, with the original span,
  /// the (internal) declaration name, and the compiled value expression.
  Checked(Option<FileSpan>, AtomId, Rc<types::Type>, Rc<types::Expr>),
}

/// A primitive type, operation, or proposition. Some keywords appear in multiple classes.
#[derive(Copy, Clone, Debug, Default)]
pub struct Prim {
  /// The primitive type record, if applicable.
  pub ty: Option<PrimType>,
  /// The primitive operation record, if applicable.
  pub op: Option<PrimOp>,
  /// The primitive proposition record, if applicable.
  pub prop: Option<PrimProp>
}
crate::deep_size_0!(Prim);

/// An operator, function, or type. These all live in one namespace so user types and
// functions cannot name-overlap.
#[derive(Clone, Debug, DeepSizeOf)]
#[allow(variant_size_differences)]
pub enum Entity {
  /// A primitive type, operation, or proposition. Some keywords appear in multiple classes.
  Prim(Prim),
  /// A named type.
  Type(Type),
  /// A named operator/procedure/function.
  Op(Operator),
  /// A named global variable.
  Global(GlobalTc),
  /// A named constant.
  Const(GlobalTc),
}

impl TuplePattern {
  fn on_names<E>(&self, f: &mut impl FnMut(bool, AtomId, &Option<FileSpan>) -> StdResult<(), E>) -> StdResult<(), E> {
    match self {
      &TuplePattern::Name(ghost, n, ref sp) => if n != AtomId::UNDER { f(ghost, n, sp)? },
      TuplePattern::Typed(p, _) => p.on_names(f)?,
      TuplePattern::Tuple(ps, _) => for p in &**ps { p.on_names(f)? }
      TuplePattern::Ready(_) => unreachable!("for unelaborated tuple patterns"),
    }
    Ok(())
  }
}

impl Compiler {
  /// Construct the initial list of primitive entities.
  pub fn make_names(env: &mut Environment) -> HashMap<AtomId, Entity> {
    fn get(names: &mut HashMap<AtomId, Entity>, a: AtomId) -> &mut Prim {
      let e = names.entry(a).or_insert_with(|| Entity::Prim(Prim::default()));
      if let Entity::Prim(p) = e {p} else {unreachable!()}
    }
    let mut names = HashMap::new();
    PrimType::scan(|p, s| get(&mut names, env.get_atom(s.as_bytes())).ty = Some(p));
    PrimOp::scan(|p, s| get(&mut names, env.get_atom(s.as_bytes())).op = Some(p));
    PrimProp::scan(|p, s| get(&mut names, env.get_atom(s.as_bytes())).prop = Some(p));
    names
  }

  /// Performs name resolution on the given AST, updating the compiler state with
  /// unchecked entities. This function is also responsible for checking for duplicate
  /// procedure declarations.
  pub fn nameck(&mut self, fsp: &FileSpan, a: &Ast) -> Result<()> {
    match a {
      Ast::Proc(p, _) => {
        let sp = try_get_span_from(fsp, p.span.as_ref());
        match self.names.entry(p.name) {
          Entry::Vacant(e) => {e.insert(Entity::Op(Operator::Proc(p.clone(), ProcTc::Unchecked)));}
          Entry::Occupied(mut e) => match e.get() {
            Entity::Op(Operator::Proc(p1, _)) => {
              if !p.eq_decl(p1) {
                return Err(ElabError::with_info(sp, "declaration mismatch".into(),
                  p1.span.iter().map(|fsp| (fsp.clone(), "previously declared here".into())).collect()))
              }
              match (p1.kind, p.kind) {
                (_, ProcKind::ProcDecl) => {}
                (ProcKind::ProcDecl, _) => {
                  e.insert(Entity::Op(Operator::Proc(p.clone(), ProcTc::Unchecked)));
                }
                _ => return Err(ElabError::new_e(sp, "name already in use"))
              }
            }
            _ => return Err(ElabError::new_e(sp, "name already in use"))
          }
        }
      }
      Ast::Global {lhs, ..} => lhs.on_names(&mut |_, a, sp| -> Result<()> {
        if self.names.insert(a, Entity::Global(GlobalTc::Unchecked)).is_some() {
          return Err(ElabError::new_e(try_get_span_from(fsp, sp.as_ref()), "name already in use"))
        }
        Ok(())
      })?,
      Ast::Const {lhs, ..} => lhs.on_names(&mut |_, a, sp| -> Result<()> {
        if self.names.insert(a, Entity::Const(GlobalTc::Unchecked)).is_some() {
          return Err(ElabError::new_e(try_get_span_from(fsp, sp.as_ref()), "name already in use"))
        }
        Ok(())
      })?,
      &Ast::Typedef {name, ref span, ..} |
      &Ast::Struct {name, ref span, ..} =>
        if self.names.insert(name, Entity::Type(Type::Unchecked)).is_some() {
          return Err(ElabError::new_e(try_get_span_from(fsp, span.as_ref()), "name already in use"))
        },
    }
    Ok(())
  }
}