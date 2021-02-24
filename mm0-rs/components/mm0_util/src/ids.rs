//! Primitive mm0 types that consuming crates will probably want.

use std::fmt;
use std::iter::FromIterator;
use std::ops::{Deref, DerefMut, Index, IndexMut};
#[cfg(feature = "memory")] use deepsize_derive::DeepSizeOf;

macro_rules! id_wrapper {
  ($id:ident: $ty:ty, $vec:ident) => {
    id_wrapper!($id: $ty, $vec,
      concat!("An index into a [`", stringify!($vec), "`]"));
  };
  ($id:ident: $ty:ty, $vec:ident, $svec:expr) => {
    #[doc=$svec]
    #[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Default)]
    pub struct $id(pub $ty);
    #[cfg(feature = "memory")]
    deepsize_0::deep_size_0!($id);

    impl $id {
      /// Convert this newtyped integer into its underlying integer.
      #[must_use]
      pub fn into_inner(self) -> $ty {
        self.0
      }
    }

    impl fmt::Debug for $id {
      fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.0.fmt(f) }
    }

    /// A vector wrapper with a strongly typed index interface.
    #[cfg_attr(feature = "memory", derive(DeepSizeOf))]
    #[derive(Clone, Debug)]
    pub struct $vec<T>(pub Vec<T>);

    #[allow(dead_code)]
    impl<T> $vec<T> {
      /// Get a reference to the element at the given index.
      #[must_use]
      pub fn get(&self, i: $id) -> Option<&T> { self.0.get(i.0 as usize) }

      /// Get a mutable reference to the element at the given index.
      #[must_use]
      pub fn get_mut(&mut self, i: $id) -> Option<&mut T> { self.0.get_mut(i.0 as usize) }

      /// Returns the equivalent of `iter().enumerate()` but with the right indexing type.
      pub fn enum_iter(&self) -> impl Iterator<Item=($id, &T)> {
        self.0.iter().enumerate().map(|(i, t)| ($id(i as $ty), t))
      }
    }

    impl<T> Default for $vec<T> {
      fn default() -> $vec<T> { $vec(Vec::new()) }
    }

    impl<T> Index<$id> for $vec<T> {
      type Output = T;
      fn index(&self, i: $id) -> &T { &self.0[i.0 as usize] }
    }

    impl<T> IndexMut<$id> for $vec<T> {
      fn index_mut(&mut self, i: $id) -> &mut T { &mut self.0[i.0 as usize] }
    }

    impl<T> Deref for $vec<T> {
      type Target = Vec<T>;
      fn deref(&self) -> &Vec<T> { &self.0 }
    }

    impl<T> DerefMut for $vec<T> {
      fn deref_mut(&mut self) -> &mut Vec<T> { &mut self.0 }
    }

    impl<T> FromIterator<T> for $vec<T> {
      fn from_iter<I: IntoIterator<Item=T>>(iter: I) -> Self { $vec(Vec::from_iter(iter)) }
    }
  };
}

id_wrapper!(SortId: u8, SortVec);
id_wrapper!(TermId: u32, TermVec);
id_wrapper!(ThmId: u32, ThmVec);
id_wrapper!(AtomId: u32, AtomVec);

bitflags! {
  /// Visibility and sort modifiers for Sort statements and Declarations.
  pub struct Modifiers: u8 {
    // Note: These particular values are important because they are used in the MMB format.

    /// The `pure` sort modifier, used to indicate that
    /// term constructors can not target this sort.
    const PURE = 1;

    /// The `strict` sort modifier, used to indicate that
    /// bound variables (in the sense of [`LocalKind::is_bound`]) of this sort are not allowed.
    const STRICT = 2;

    /// The `provable` sort modifier, used to indicate that this sort
    /// can appear as the sort of hypotheses and conclusions of
    /// `axiom` and `theorem` declarations.
    const PROVABLE = 4;

    /// The `free` sort modifier, used to indicate that
    /// dummy variables of this sort (in `def` and `theorem`) are not allowed.
    const FREE = 8;


    /// The `pub` visibility modifier, used on `theorem` to indicate that a theorem
    /// appears in the specification file (otherwise the theorem is only
    /// usable in the proof file).
    const PUB = 16;

    /// The `abstract` visibility modifier, used on `def` to indicate that
    /// the definition should not be supplied in the specification file.
    const ABSTRACT = 32;

    /// The `local` visibility modifier, the opposite of `pub` and used on
    /// `def`, because `def`s have default public visibility. A `local def`
    /// will not appear in the specification file at all.
    const LOCAL = 64;
  }
}

#[cfg(feature = "memory")]
deepsize_0::deep_size_0!(Modifiers);

impl Modifiers {
  /// The null modifier set. Modifiers are represented as bitfields, so this is the same as `0`.
  pub const NONE: Modifiers = Self::empty();

  /// Construct a [`Modifiers`] from a byte.
  #[must_use]
  pub fn new(bits: u8) -> Self { Self {bits} }

  /// The set of all valid sort modifiers. One can check if a modifier set is valid for a sort
  /// using `sort_data().contains(m)`.
  #[must_use]
  pub fn sort_data() -> Modifiers {
    Modifiers::PURE | Modifiers::STRICT | Modifiers::PROVABLE | Modifiers::FREE
  }

  /// Parses a string into a singleton [`Modifiers`], or [`NONE`](Self::NONE) if the string is not valid.
  #[must_use]
  pub fn from_name(s: &[u8]) -> Modifiers {
    match s {
      b"pure" => Modifiers::PURE,
      b"strict" => Modifiers::STRICT,
      b"provable" => Modifiers::PROVABLE,
      b"free" => Modifiers::FREE,
      b"pub" => Modifiers::PUB,
      b"abstract" => Modifiers::ABSTRACT,
      b"local" => Modifiers::LOCAL,
      _ => Modifiers::NONE
    }
  }
}

impl fmt::Display for Modifiers {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if self.contains(Modifiers::PURE) {write!(f, "pure ")?}
    if self.contains(Modifiers::STRICT) {write!(f, "strict ")?}
    if self.contains(Modifiers::PROVABLE) {write!(f, "provable ")?}
    if self.contains(Modifiers::FREE) {write!(f, "free ")?}
    if self.contains(Modifiers::PUB) {write!(f, "pub ")?}
    if self.contains(Modifiers::ABSTRACT) {write!(f, "abstract ")?}
    if self.contains(Modifiers::LOCAL) {write!(f, "local ")?}
    Ok(())
  }
}
