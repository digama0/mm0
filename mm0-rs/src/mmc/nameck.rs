//! MMC name resolution pass.
use std::sync::Arc;
use std::collections::{HashMap, hash_map::Entry};
use std::{rc::Rc, result::Result as StdResult};
use crate::elab::{
  Result, ElabError,
  local_context::try_get_span_from,
  environment::{AtomID, Environment}};
use crate::util::FileSpan;
use super::{Compiler, types::{self, AST, Proc, ProcKind, TuplePattern}};

macro_rules! make_prims {
  {$($(#[$attr0:meta])* enum $name:ident { $($(#[$attr:meta])* $x:ident: $e:expr,)* })* } => {
    $(
      $(#[$attr0])*
      #[derive(Debug, PartialEq, Eq, Copy, Clone)]
      pub enum $name { $($(#[$attr])* $x),* }
      $crate::deep_size_0!($name);

      impl ::std::str::FromStr for $name {
        type Err = ();
        fn from_str(s: &str) -> ::std::result::Result<Self, ()> {
          match s {
            $($e => Ok(Self::$x),)*
            _ => Err(())
          }
        }
      }

      impl $name {
        /// Evaluate a function on all elements of the type, with their names.
        pub fn scan(mut f: impl FnMut(Self, &'static str)) {
          $(f($name::$x, $e);)*
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
      /// `(pun x h)` returns a value of type `T` if `h` proves `x` has type `T`.
    Pun: "pun",
    /// If `x: (& (array T n))`, then `(slice {x + b} h): (& (array T a))` if
    /// `h` is a proof that `b + a <= n`. Computationally this corresponds to
    /// simply `x + b * sizeof T`, in the manner of C pointer arithmetic.
    Slice: "slice",
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
    /// `int` is the type of unbounded signed integers; `sizeof int = inf`.
    Int: "int",
    /// `(list A B C)` is a tuple type with elements `A, B, C`;
    /// `sizeof (list A B C) = sizeof A + sizeof B + sizeof C`.
    List: "list",
    /// `nat` is the type of unbounded unsigned integers; `sizeof nat = inf`.
    Nat: "nat",
    /// `(or A B C)` is an undiscriminated anonymous union of types `A, B, C`.
    /// `sizeof (or A B C) = max (sizeof A, sizeof B, sizeof C)`, and
    /// the typehood predicate is `x :> (or A B C)` iff
    /// `x :> A \/ x :> B \/ x :> C`.
    Or: "or",
    /// `(own T)` is a type of owned pointers. The typehood predicate is
    /// `x :> own T` iff `E. v (x |-> v) * v :> T`.
    Own: "own",
    /// `(& T)` is a type of borrowed pointers. This type is treated specially;
    /// the `x |-> v` assumption is stored separately from regular types, and
    /// `(* x)` is treated as sugar for `v`.
    Ref: "&",
    /// `(&mut T)` is a type of mutable pointers. This is also treated specially;
    /// it is sugar for `(mut {x : (own T)})`, which is to say `x` has
    /// type `own T` in the function but must also be passed back out of the
    /// function.
    RefMut: "&mut",
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
    Imp: "im",
    /// `p * q` is separating conjunction.
    Star: "*",
    /// `p -* q` is separating implication.
    Wand: "-*",
  }

  /// Intrinsic functions, which are like `PrimProc` but are typechecked like regular
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
  /// the (internal) declaration name, and the compiled `Type` object.
  Checked(Option<FileSpan>, AtomID, Rc<types::Type>),
}

/// The typechecking status of a procedure.
#[derive(Copy, Clone, Debug, DeepSizeOf)]
pub enum ProcTC {
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
  Proc(Arc<Proc>, ProcTC),
}

/// The typechecking status of a global variable.
#[derive(Clone, Debug, DeepSizeOf)]
pub enum GlobalTC {
  /// We know this is a global or const but have not typechecked the body.
  Unchecked,
  /// A user type that has been typechecked, with the original span,
  /// the (internal) declaration name, and the compiled value expression.
  Checked(Option<FileSpan>, AtomID, Option<Rc<types::Expr>>),
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
  Global(GlobalTC),
  /// A named constant.
  Const(GlobalTC),
}

impl TuplePattern {
  fn on_names<E>(&self, f: &mut impl FnMut(bool, AtomID, &Option<FileSpan>) -> StdResult<(), E>) -> StdResult<(), E> {
    match self {
      &TuplePattern::Name(ghost, n, ref sp) => if n != AtomID::UNDER { f(ghost, n, sp)? },
      TuplePattern::Typed(p, _) => p.on_names(f)?,
      TuplePattern::Tuple(ps) => for p in &**ps { p.on_names(f)? }
    }
    Ok(())
  }
}

impl Compiler {
  /// Construct the initial list of primitive entities.
  pub fn make_names(env: &mut Environment) -> HashMap<AtomID, Entity> {
    let mut names = HashMap::new();
    fn get(names: &mut HashMap<AtomID, Entity>, a: AtomID) -> &mut Prim {
      let e = names.entry(a).or_insert_with(|| Entity::Prim(Prim::default()));
      if let Entity::Prim(p) = e {p} else {unreachable!()}
    }
    PrimType::scan(|p, s| get(&mut names, env.get_atom(s)).ty = Some(p));
    PrimOp::scan(|p, s| get(&mut names, env.get_atom(s)).op = Some(p));
    PrimProp::scan(|p, s| get(&mut names, env.get_atom(s)).prop = Some(p));
    names
  }

  /// Performs name resolution on the given AST, updating the compiler state with
  /// unchecked entities. This function is also responsible for checking for duplicate
  /// procedure declarations.
  pub fn nameck(&mut self, fsp: &FileSpan, a: &AST) -> Result<()> {
    match a {
      AST::Proc(p) => {
        let sp = try_get_span_from(fsp, p.span.as_ref());
        match self.names.entry(p.name) {
          Entry::Vacant(e) => {e.insert(Entity::Op(Operator::Proc(p.clone(), ProcTC::Unchecked)));}
          Entry::Occupied(mut e) => match e.get() {
            Entity::Op(Operator::Proc(p1, _)) => {
              if !p.eq_decl(p1) {
                return Err(ElabError::with_info(sp, "declaration mismatch".into(),
                  p1.span.iter().map(|fsp| (fsp.clone(), "previously declared here".into())).collect()))
              }
              match (p1.kind, p.kind) {
                (_, ProcKind::ProcDecl) => {}
                (ProcKind::ProcDecl, _) => {
                  e.insert(Entity::Op(Operator::Proc(p.clone(), ProcTC::Unchecked)));
                }
                _ => return Err(ElabError::new_e(sp, "name already in use"))
              }
            }
            _ => return Err(ElabError::new_e(sp, "name already in use"))
          }
        }
      }
      AST::Global {lhs, ..} => lhs.on_names(&mut |_, a, sp| -> Result<()> {
        if self.names.insert(a, Entity::Global(GlobalTC::Unchecked)).is_some() {
          return Err(ElabError::new_e(try_get_span_from(fsp, sp.as_ref()), "name already in use"))
        }
        Ok(())
      })?,
      AST::Const {lhs, ..} => lhs.on_names(&mut |_, a, sp| -> Result<()> {
        if self.names.insert(a, Entity::Const(GlobalTC::Unchecked)).is_some() {
          return Err(ElabError::new_e(try_get_span_from(fsp, sp.as_ref()), "name already in use"))
        }
        Ok(())
      })?,
      &AST::Typedef {name, ref span, ..} |
      &AST::Struct {name, ref span, ..} =>
        if self.names.insert(name, Entity::Type(Type::Unchecked)).is_some() {
          return Err(ElabError::new_e(try_get_span_from(fsp, span.as_ref()), "name already in use"))
        },
    }
    Ok(())
  }
}