//! Types used in the stages of the compiler.

// pub mod parse;
pub mod ast;
pub mod entity;
pub mod ty;
pub mod global;
pub mod hir;
pub mod mir;
pub mod pir;

use std::borrow::Cow;
use std::convert::{TryFrom, TryInto};
use std::fmt::Display;
use std::marker::PhantomData;
use std::ops::{Index, IndexMut};
use num::{BigInt, Signed};
#[cfg(feature = "memory")] use mm0_deepsize_derive::DeepSizeOf;
use crate::{FileSpan, Symbol};

/// A trait for newtyped integers, that can be used as index types in vectors and sets.
pub trait Idx: Copy + Eq {
  /// Convert from `T` to `usize`
  fn into_usize(self) -> usize;
  /// Convert from `usize` to `T`
  fn from_usize(_: usize) -> Self;
}

impl Idx for usize {
  fn into_usize(self) -> usize { self }
  fn from_usize(n: usize) -> Self { n }
}

/// A vector indexed by a custom indexing type `I`, usually a newtyped integer.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct IdxVec<I, T>(pub Vec<T>, PhantomData<I>);

impl<I, T> IdxVec<I, T> {
  /// Construct a new empty [`IdxVec`].
  pub const fn new() -> Self { Self(vec![], PhantomData) }

  /// Construct a new [`IdxVec`] with the specified capacity.
  #[must_use] pub fn with_capacity(capacity: usize) -> Self { Vec::with_capacity(capacity).into() }

  /// Construct a new [`IdxVec`] by calling the specified function.
  #[must_use] pub fn from_fn(size: usize, f: impl FnMut() -> T) -> Self {
    Self::from(std::iter::repeat_with(f).take(size).collect::<Vec<_>>())
  }

  /// Construct a new [`IdxVec`] using the default element `size` times.
  #[must_use] pub fn from_default(size: usize) -> Self where T: Default {
    Self::from_fn(size, T::default)
  }

  /// The number of elements in the [`IdxVec`].
  #[must_use] pub fn len(&self) -> usize { self.0.len() }

  /// Insert a new value at the end of the vector.
  pub fn push(&mut self, val: T) -> I where I: Idx {
    let id = I::from_usize(self.0.len());
    self.0.push(val);
    id
  }

  /// An iterator including the indexes, like `iter().enumerate()`, as `BlockId`s.
  pub fn enum_iter(&self) -> impl Iterator<Item = (I, &T)> where I: Idx {
    self.0.iter().enumerate().map(|(n, val)| (I::from_usize(n), val))
  }

  /// An iterator including the indexes, like `iter_mut().enumerate()`, as `BlockId`s.
  pub fn enum_iter_mut(&mut self) -> impl Iterator<Item = (I, &mut T)> where I: Idx {
    self.0.iter_mut().enumerate().map(|(n, val)| (I::from_usize(n), val))
  }

  /// Returns `true` if the vector contains no elements.
  #[must_use] pub fn is_empty(&self) -> bool { self.0.is_empty() }
}

impl<I, T> From<Vec<T>> for IdxVec<I, T> {
  fn from(vec: Vec<T>) -> Self { Self(vec, PhantomData) }
}

impl<I, T> std::iter::FromIterator<T> for IdxVec<I, T> {
  fn from_iter<J: IntoIterator<Item = T>>(iter: J) -> Self { Vec::from_iter(iter).into() }
}

impl<I, T> Default for IdxVec<I, T> {
  fn default() -> Self { vec![].into() }
}

impl<I: Idx, T> Index<I> for IdxVec<I, T> {
  type Output = T;
  fn index(&self, index: I) -> &Self::Output { &self.0[I::into_usize(index)] }
}

impl<I: Idx, T> IndexMut<I> for IdxVec<I, T> {
  fn index_mut(&mut self, index: I) -> &mut Self::Output { &mut self.0[I::into_usize(index)] }
}

mk_id! {
  /// A variable ID. These are local to a given declaration (function, constant, global),
  /// but are not de Bruijn variables - they are unique identifiers within the declaration.
  VarId,

  /// An ID for an opaque "lambda", an expression modulo an ordered list of free variables.
  /// This is used to embed arbitrary term constructors in the expression language.
  LambdaId,

  /// An ID for an opaque proof object, used in `Entail` nodes in the AST.
  ProofId
}

impl std::fmt::Display for VarId {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "_{}", self.0)
  }
}

/// A spanned expression.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct Spanned<T> {
  /// The span of the expression
  pub span: FileSpan,
  /// The data (the `k` stands for `kind` because it's often a `*Kind` enum
  /// but it can be anything).
  pub k: T,
}

impl<T> Spanned<T> {
  /// Transform a `Spanned<T>` into `Spanned<U>` given `f: T -> U`.
  pub fn map_into<U>(self, f: impl FnOnce(T) -> U) -> Spanned<U> {
    Spanned { span: self.span, k: f(self.k) }
  }
}

/// Possible sizes for integer operations and types.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Size {
  /// 8 bits, or 1 byte. Used for `u8` and `i8`.
  S8,
  /// 16 bits, or 2 bytes. Used for `u16` and `i16`.
  S16,
  /// 32 bits, or 4 bytes. Used for `u32` and `i32`.
  S32,
  /// 64 bits, or 8 bytes. Used for `u64` and `i64`.
  S64,
  /// Unbounded size. Used for `nat` and `int`. (These types are only legal for
  /// ghost variables, but they are also used to indicate "correct to an unbounded model"
  /// for operations like [`Unop::BitNot`] when it makes sense. We do not actually support
  /// bignum compilation.)
  Inf,
}
#[cfg(feature = "memory")] mm0_deepsize::deep_size_0!(Size);

impl Default for Size {
  fn default() -> Self { Self::Inf }
}

impl Size {
  /// The number of bits of this type, or `None` for the infinite case.
  #[must_use] pub fn bits(self) -> Option<u8> {
    match self {
      Size::Inf => None,
      Size::S8 => Some(8),
      Size::S16 => Some(16),
      Size::S32 => Some(32),
      Size::S64 => Some(64),
    }
  }

  /// The number of bytes of this type, or `None` for the infinite case.
  #[must_use] pub fn bytes(self) -> Option<u8> {
    match self {
      Size::Inf => None,
      Size::S8 => Some(1),
      Size::S16 => Some(2),
      Size::S32 => Some(4),
      Size::S64 => Some(8),
    }
  }
}

/// The set of integral types, `N_s` and `Z_s`, representing the signed and unsigned integers
/// of various bit widths, plus the computationally unrepresentable types of
/// unbounded natural numbers and unbounded integers.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum IntTy {
  /// The type of signed integers of given bit width, or all integers.
  Int(Size),
  /// The type of unsigned integers of given bit width, or all nonnegative integers.
  UInt(Size),
}
#[cfg(feature = "memory")] mm0_deepsize::deep_size_0!(IntTy);

impl std::fmt::Display for IntTy {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.to_str().fmt(f)
  }
}

impl IntTy {
  /// The type of unbounded nonnegative integers.
  pub const NAT: Self = Self::UInt(Size::Inf);

  /// The type of unbounded integers.
  pub const INT: Self = Self::Int(Size::Inf);

  /// The size of this integral type.
  #[must_use] pub fn size(self) -> Size {
    match self { IntTy::Int(sz) | IntTy::UInt(sz) => sz }
  }

  /// A string description of this type.
  #[must_use] pub fn to_str(self) -> &'static str {
    match self {
      IntTy::Int(Size::Inf) => "int",
      IntTy::Int(Size::S8) => "i8",
      IntTy::Int(Size::S16) => "i16",
      IntTy::Int(Size::S32) => "i32",
      IntTy::Int(Size::S64) => "i64",
      IntTy::UInt(Size::Inf) => "nat",
      IntTy::UInt(Size::S8) => "u8",
      IntTy::UInt(Size::S16) => "u16",
      IntTy::UInt(Size::S32) => "u32",
      IntTy::UInt(Size::S64) => "u64",
    }
  }

  /// Returns true if `n` is a valid member of this integral type.
  #[must_use] pub fn contains(self, n: &BigInt) -> bool {
    match self {
      IntTy::Int(Size::Inf) => true,
      IntTy::Int(Size::S8) => i8::try_from(n).is_ok(),
      IntTy::Int(Size::S16) => i16::try_from(n).is_ok(),
      IntTy::Int(Size::S32) => i32::try_from(n).is_ok(),
      IntTy::Int(Size::S64) => i64::try_from(n).is_ok(),
      IntTy::UInt(Size::Inf) => !n.is_negative(),
      IntTy::UInt(Size::S8) => u8::try_from(n).is_ok(),
      IntTy::UInt(Size::S16) => u16::try_from(n).is_ok(),
      IntTy::UInt(Size::S32) => u32::try_from(n).is_ok(),
      IntTy::UInt(Size::S64) => u64::try_from(n).is_ok(),
    }
  }
}

impl PartialOrd for IntTy {
  /// `IntTy` is partially ordered by inclusion.
  fn le(&self, other: &Self) -> bool {
    match (self, other) {
      (IntTy::Int(sz1), IntTy::Int(sz2)) |
      (IntTy::UInt(sz1), IntTy::UInt(sz2)) => sz1 <= sz2,
      (IntTy::Int(_), IntTy::UInt(_)) => false,
      (IntTy::UInt(sz1), IntTy::Int(sz2)) => sz1 < sz2,
    }
  }

  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    match (self <= other, other <= self) {
      (true, true) => Some(std::cmp::Ordering::Equal),
      (true, false) => Some(std::cmp::Ordering::Less),
      (false, true) => Some(std::cmp::Ordering::Greater),
      (false, false) => None,
    }
  }
  fn lt(&self, other: &Self) -> bool { self <= other && self != other }
  fn gt(&self, other: &Self) -> bool { other < self }
  fn ge(&self, other: &Self) -> bool { other <= self }
}

/// (Elaborated) unary operations.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Unop {
  /// Integer negation
  Neg,
  /// Logical (boolean) NOT
  Not,
  /// Bitwise NOT. For fixed size this is the operation `2^n - x - 1`, and
  /// for infinite size this is `-x - 1`. Note that signed NOT always uses
  /// [`Size::Inf`].
  ///
  /// Infinite size is also the default value before type checking.
  BitNot(Size),
  /// Truncation into the given type. For fixed size this is the operation `x % 2^n`,
  /// for `int` this is the identity, and for `nat` this is invalid.
  As(IntTy),
}
#[cfg(feature = "memory")] mm0_deepsize::deep_size_0!(Unop);

impl Unop {
  /// Return a string representation of the [`Unop`].
  #[must_use] pub fn to_str(self) -> &'static str {
    match self {
      Unop::Neg => "-",
      Unop::Not => "not",
      Unop::BitNot(_) => "bnot",
      Unop::As(_) => "as..",
    }
  }

  /// Returns true if this takes integral arguments,
  /// and false if it takes booleans.
  #[must_use] pub fn int_in_out(self) -> bool {
    match self {
      Unop::Neg |
      Unop::BitNot(_) |
      Unop::As(_) => true,
      Unop::Not => false,
    }
  }

  /// Apply this unary operation as a `bool -> bool` function.
  /// Panics if it is not a `bool -> bool` function.
  #[must_use] pub fn apply_bool(self, b: bool) -> bool {
    match self {
      Unop::Not => !b,
      Unop::Neg |
      Unop::BitNot(_) |
      Unop::As(_) => panic!("not a bool op"),
    }
  }

  /// Apply this unary operation as a `int -> int` function. Returns `None` if the function
  /// inputs are out of range or if it is not a `int -> int` function.
  #[must_use] pub fn apply_int(self, n: &BigInt) -> Option<Cow<'_, BigInt>> {
    macro_rules! truncate_signed {($iN:ty, $uN:ty) => {{
      if <$iN>::try_from(n).is_ok() { Cow::Borrowed(n) }
      else { Cow::Owned((<$uN>::try_from(n & BigInt::from(<$uN>::MAX)).unwrap() as $iN).into()) }
    }}}
    macro_rules! truncate_unsigned {($uN:ty) => {{
      if <$uN>::try_from(n).is_ok() { Cow::Borrowed(n) }
      else { Cow::Owned(n & BigInt::from(<$uN>::MAX)) }
    }}}
    match self {
      Unop::Neg => Some(Cow::Owned(-n)),
      Unop::Not => None,
      Unop::BitNot(Size::Inf) => Some(Cow::Owned(!n)),
      Unop::BitNot(Size::S8) => Some(Cow::Owned(u8::into(!n.try_into().ok()?))),
      Unop::BitNot(Size::S16) => Some(Cow::Owned(u16::into(!n.try_into().ok()?))),
      Unop::BitNot(Size::S32) => Some(Cow::Owned(u32::into(!n.try_into().ok()?))),
      Unop::BitNot(Size::S64) => Some(Cow::Owned(u64::into(!n.try_into().ok()?))),
      Unop::As(IntTy::Int(Size::Inf)) => Some(Cow::Borrowed(n)),
      Unop::As(IntTy::Int(Size::S8)) => Some(truncate_signed!(i8, u8)),
      Unop::As(IntTy::Int(Size::S16)) => Some(truncate_signed!(i16, u16)),
      Unop::As(IntTy::Int(Size::S32)) => Some(truncate_signed!(i32, u32)),
      Unop::As(IntTy::Int(Size::S64)) => Some(truncate_signed!(i64, u64)),
      Unop::As(IntTy::UInt(Size::Inf)) => panic!("{}", "{n as nat} does not exist"),
      Unop::As(IntTy::UInt(Size::S8)) => Some(truncate_unsigned!(u8)),
      Unop::As(IntTy::UInt(Size::S16)) => Some(truncate_unsigned!(u16)),
      Unop::As(IntTy::UInt(Size::S32)) => Some(truncate_unsigned!(u32)),
      Unop::As(IntTy::UInt(Size::S64)) => Some(truncate_unsigned!(u64)),
    }
  }
}

impl std::fmt::Display for Unop {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.to_str().fmt(f)
  }
}

/// Classification of the binary operations into types.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum BinopType {
  /// `(int, int) -> int` functions, like `x + y`, `x * y`, `x & y`
  IntIntInt,
  /// `(int, int) -> bool` functions, like `x < y`, `x = y`, `x <= y`
  IntIntBool,
  /// `(int, nat) -> int` functions: `x << y` and `x >> y`
  IntNatInt,
  /// `(bool, bool) -> bool` functions: `x && y` and `x || y`
  BoolBoolBool,
}

impl BinopType {
  /// Does this function take integral types as input, or booleans?
  #[must_use] pub fn int_in(self) -> bool {
    matches!(self, Self::IntIntInt | Self::IntIntBool | Self::IntNatInt)
  }
  /// Does this function produce integral types as output, or booleans?
  #[must_use] pub fn int_out(self) -> bool {
    matches!(self, Self::IntIntInt | Self::IntNatInt)
  }
}

/// (Elaborated) binary operations.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Binop {
  /// Integer addition
  Add,
  /// Integer multiplication
  Mul,
  /// Integer subtraction
  Sub,
  /// Maximum
  Max,
  /// Minimum
  Min,
  /// Logical (boolean) AND
  And,
  /// Logical (boolean) OR
  Or,
  /// Bitwise AND, for signed or unsigned integers of any size
  BitAnd,
  /// Bitwise OR, for signed or unsigned integers of any size
  BitOr,
  /// Bitwise XOR, for signed or unsigned integers of any size
  BitXor,
  /// Shift left
  Shl,
  /// Shift right (arithmetic)
  Shr,
  /// Less than, for signed or unsigned integers of any size
  Lt,
  /// Less than or equal, for signed or unsigned integers of any size
  Le,
  /// Equal, for signed or unsigned integers of any size
  Eq,
  /// Not equal, for signed or unsigned integers of any size
  Ne,
}
#[cfg(feature = "memory")] mm0_deepsize::deep_size_0!(Binop);

impl Binop {
  /// Return a string representation of the [`Binop`].
  #[must_use] pub fn to_str(self) -> &'static str {
    match self {
      Binop::Add => "+",
      Binop::Mul => "*",
      Binop::Sub => "-",
      Binop::Max => "max",
      Binop::Min => "min",
      Binop::And => "and",
      Binop::Or => "or",
      Binop::BitAnd => "band",
      Binop::BitOr => "bor",
      Binop::BitXor => "bxor",
      Binop::Shl => "shl",
      Binop::Shr => "shr",
      Binop::Lt => "<",
      Binop::Le => "<=",
      Binop::Eq => "=",
      Binop::Ne => "!=",
    }
  }

  /// Returns the type of this binop.
  #[must_use] pub fn ty(self) -> BinopType {
    match self {
      Binop::Add | Binop::Mul | Binop::Sub |
      Binop::Max | Binop::Min |
      Binop::BitAnd | Binop::BitOr | Binop::BitXor => BinopType::IntIntInt,
      Binop::Shl | Binop::Shr => BinopType::IntNatInt,
      Binop::Lt | Binop::Le | Binop::Eq | Binop::Ne => BinopType::IntIntBool,
      Binop::And | Binop::Or => BinopType::BoolBoolBool,
    }
  }

  /// Returns true if this integral function returns a `nat` on nonnegative inputs.
  #[must_use] pub fn preserves_nat(self) -> bool {
    match self {
      Binop::Add | Binop::Mul |
      Binop::Max | Binop::Min |
      Binop::BitAnd | Binop::BitOr | Binop::BitXor |
      Binop::Shl | Binop::Shr => true,
      Binop::Sub => false,
      Binop::Lt | Binop::Le | Binop::Eq | Binop::Ne |
      Binop::And | Binop::Or => panic!("not an int -> int binop"),
    }
  }

  /// Returns true if this integral function returns a `UInt(sz)` on `UInt(sz)` inputs.
  #[must_use] pub fn preserves_usize(self) -> bool {
    match self {
      Binop::Add | Binop::Mul |
      Binop::Max | Binop::Min |
      Binop::Shl | Binop::Sub => false,
      Binop::BitAnd | Binop::BitOr | Binop::BitXor | Binop::Shr => true,
      Binop::Lt | Binop::Le | Binop::Eq | Binop::Ne |
      Binop::And | Binop::Or => panic!("not an int -> int binop"),
    }
  }

  /// Apply this unary operation as a `(int, int) -> int` function. Returns `None` if the function
  /// inputs are out of range or if it is not a `(int, int) -> int` function.
  /// (The `(int, nat) -> int` functions are also evaluated here.)
  #[must_use] pub fn apply_int_int(self, n1: &BigInt, n2: &BigInt) -> Option<BigInt> {
    match self {
      Binop::Add => Some(n1 + n2),
      Binop::Mul => Some(n1 * n2),
      Binop::Sub => Some(n1 - n2),
      Binop::Max => Some(n1.max(n2).clone()),
      Binop::Min => Some(n1.min(n2).clone()),
      Binop::BitAnd => Some(n1 & n2),
      Binop::BitOr => Some(n1 | n2),
      Binop::BitXor => Some(n1 ^ n2),
      Binop::Shl => Some(n1 << usize::try_from(n2).ok()?),
      Binop::Shr => Some(n1 >> usize::try_from(n2).ok()?),
      Binop::Lt | Binop::Le | Binop::Eq | Binop::Ne |
      Binop::And | Binop::Or => None,
    }
  }

  /// Apply this unary operation as a `(int, int) -> bool` function.
  /// Panics if it is not a `(int, int) -> bool` function.
  #[must_use] pub fn apply_int_bool(self, n1: &BigInt, n2: &BigInt) -> bool {
    match self {
      Binop::Lt => n1 < n2,
      Binop::Le => n1 <= n2,
      Binop::Eq => n1 == n2,
      Binop::Ne => n1 != n2,
      Binop::Add | Binop::Mul | Binop::Sub |
      Binop::Max | Binop::Min |
      Binop::BitAnd | Binop::BitOr | Binop::BitXor |
      Binop::Shl | Binop::Shr |
      Binop::And | Binop::Or => panic!("not int -> int -> bool binop"),
    }
  }

  /// Apply this unary operation as a `(bool, bool) -> bool` function.
  /// Panics if it is not a `(bool, bool) -> bool` function.
  #[must_use] pub fn apply_bool_bool(self, b1: bool, b2: bool) -> bool {
    match self {
      Binop::Add | Binop::Mul | Binop::Sub |
      Binop::Max | Binop::Min |
      Binop::BitAnd | Binop::BitOr | Binop::BitXor |
      Binop::Shl | Binop::Shr |
      Binop::Lt | Binop::Le | Binop::Eq | Binop::Ne => panic!("not bool -> bool -> bool binop"),
      Binop::And => b1 && b2,
      Binop::Or => b1 || b2,
    }
  }
}

impl std::fmt::Display for Binop {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.to_str().fmt(f)
  }
}

/// A field accessor.
#[derive(Copy, Clone, Debug)]
pub enum FieldName {
  /// A numbered field access like `x.1`.
  Number(u32),
  /// A named field access like `x.foo`.
  Named(Symbol),
}
#[cfg(feature = "memory")] mm0_deepsize::deep_size_0!(FieldName);

impl Display for FieldName {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match *self {
      FieldName::Number(n) => n.fmt(f),
      FieldName::Named(a) => a.fmt(f),
    }
  }
}

/// An embedded MM0 expression inside MMC. All free variables have been replaced by indexes,
/// with `subst` holding the internal names of these variables.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct Mm0Expr<T> {
  /// The mapping from indexes in the `expr` to internal names.
  /// (The user-facing names have been erased.)
  pub subst: Vec<T>,
  /// The root node of the expression.
  pub expr: LambdaId,
}
