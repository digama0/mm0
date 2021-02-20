//! Primitive mm0 types that consuming crates will probably want.

use std::fmt;
use byteorder::LE;
use zerocopy::{FromBytes, Unaligned, U64};
use std::iter::FromIterator;
use std::ops::{Deref, DerefMut, Index, IndexMut};
#[cfg(feature = "memory")] use deepsize_derive::DeepSizeOf;

/// bound mask: 10000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000
pub const TYPE_BOUND_MASK: u64 = 1 << 63;

/// 10000000_11111111_11111111_11111111_11111111_11111111_11111111_11111111
pub const TYPE_SORT_MASK: u64 = (1 << 63) | ((1 << 56) - 1);

/// deps mask: 00000000_11111111_11111111_11111111_11111111_11111111_11111111_11111111
pub const TYPE_DEPS_MASK: u64 = (1 << 56) - 1;

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
        #[must_use] pub fn get(&self, i: $id) -> Option<&T> { self.0.get(i.0 as usize) }
        /// Get a mutable reference to the element at the given index.
        #[must_use] pub fn get_mut(&mut self, i: $id) -> Option<&mut T> { self.0.get_mut(i.0 as usize) }
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
  
  //impl TryFrom<SortData> for Modifiers {
  //  type Error = ();
  //  fn try_from(s: SortData) -> Result<Modifiers, ()> {
  //    let m = Modifiers::new(s.0);
  //    if Modifiers::sort_data().contains(m) {Ok(m)} else {Err(())}
  //  }
  //}
  
  /// An argument binder in a term/def or axiom/theorem.
  /// * Bit 63 (the high bit of the high byte) is 1 if this is a bound variable.
  /// * Bits 56-62 (the low 7 bits of the high byte) give the sort of the variable.
  /// * Bits 0-55 (the low 7 bytes) are a bitset giving the set of bound variables
  ///   earlier in the list that this variable is allowed to depend on.
  #[repr(C)]
  #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, FromBytes, Unaligned)]
  pub struct Type(pub U64<LE>);
  
  /// Newtype for `Type` that makes some situations easier to read.
  pub type Arg = Type;

  impl std::default::Default for Type {
      fn default() -> Self {
          Type(U64::new(0))
      }
  }
  
  impl From<u64> for Type {
      fn from(n: u64) -> Type {
          Type(U64::new(n))
      }
  }
  
  impl Type {
      /// Make a new `Type` of sort `sort_num`
      pub fn new_of_sort(sort_num: u8) -> Self {
          Type::from((sort_num as u64) << 56)
      }
  
      /// A brand new `Type`; bool indicates whether it's bound.
      pub fn new(bound: bool) -> Self {
          if bound {
              Type::from(1 << 63)
          } else {
              Type::from(0)
          }
      }
  
      /// Annotate a `Type` with a sort.
      ///
      /// Since types are often built incrementally, you may have built a "blank"
      /// type that you knew was bound, but you'll only know it's sort later.
      /// This is how you add the sort. If the `Type` already had a sort, 
      /// it's overwritten by `sort_id`.
      pub fn add_sort(&mut self, sort_id: SortId) {
          // clear existing sort if any;
          std::ops::BitAndAssign::bitand_assign(self, Type::from(TYPE_SORT_MASK));
          // Add new sort
          std::ops::BitOrAssign::bitor_assign(self, Type::from((sort_id.into_inner() as u64) << 56));
      }
  
      /// Add a dependency on bv_idx
      pub fn add_dep(&mut self, bv_idx: u64) {
          std::ops::BitOrAssign::bitor_assign(self, Type::from(1 << bv_idx));
      }
  
      /// Does this type depend on the bth bound variable?
      ///
      /// This is 0 indexed.
      pub fn depends_on(self, bv_idx: u64) -> bool {
          (self.0.get() & 1u64 << bv_idx) != 0
      }
  
      /// True if this argument is a bound variable.
      #[inline]
      #[must_use]
      pub fn bound(self) -> bool {
          self.0.get() & (1 << 63) != 0
      }
      /// The sort of this variable.
      #[allow(clippy::cast_possible_truncation)]
      #[inline]
      #[must_use]
      pub fn sort(self) -> SortId {
          SortId(((self.0.get() >> 56) & 0x7F) as u8)
      }    
  
      /// If this is the type of a bound variable, return a u64
      /// whose only activated bit is the bit indicating which bv
      /// it is.
      pub fn bound_digit(self) -> Option<u64> {
          if self.bound() {
              Some(self.0.get() & !(0xFF << 56))
          } else {
              None
          }
      }
  
      /// The POSITION (1 - 55) of this bound variable, NOT the literal u64.
      pub fn bound_pos(self) -> Option<u64> {
          if self.bound() {
              for i in 0..56 {
                  if ((1 << i) & self.0.get()) != 0 {
                      return Some(i + 1);
                  }
              }
              unreachable!("Something's wrong with `is_bound`")
          } else {
              None
          }
      }
  
      /// Does this `Type` have dependencies?
      pub fn has_deps(self) -> bool {
          if self.bound() {
              false
          } else {
              (self.0.get() & TYPE_DEPS_MASK) > 0
          }
      }
  
      /// If this is a regular/not-bound variable, return a u64
      /// whose only activated bits are the ones marking the bvs
      /// on which it depends.
      pub fn deps(self) -> Option<u64> {
          if !self.bound() {
              Some(self.0.get() & !(0xFF << 56))
          } else {
              None
          }
      }
  
      /// Get the high bit only, which holds the boundedness and the sort.
      pub fn high_bit(self) -> Self {
          Type(U64::new(self.0.get() & (!TYPE_DEPS_MASK)))
      }
  
      /// Are these two types totally bitwise-disjoint
      pub fn disjoint(self, other: Self) -> bool {
          (self.0.get() & other.0.get()) == 0
      }
  }
  
  impl std::ops::BitAnd<Type> for Type {
      type Output = Self;
      fn bitand(self, rhs: Self) -> Self::Output {
          Type::from(self.0.get() & rhs.0.get())
      }
  }
  
  impl std::ops::BitAndAssign<Type> for Type {
      fn bitand_assign(&mut self, other: Self) {
          self.0.set(self.0.get() & other.0.get())
      }
  }
  
  impl std::ops::BitOr<Type> for Type {
      type Output = Self;
      fn bitor(self, rhs: Self) -> Self::Output {
          Type::from(self.0.get() | rhs.0.get())
      }
  }
  
  impl std::ops::BitOrAssign<Type> for Type {
      fn bitor_assign(&mut self, other: Self) {
          self.0.set(self.0.get() | other.0.get())
      }
  }
  
  impl std::ops::Not for Type {
      type Output = Type;
      fn not(self) -> Self::Output {
          Type::from(!self.0.get())
      }
  }
  
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
    #[must_use] pub fn new(bits: u8) -> Self { Self {bits} }
  
    /// The set of all valid sort modifiers. One can check if a modifier set is valid for a sort
    /// using `sort_data().contains(m)`.
    #[must_use] pub fn sort_data() -> Modifiers {
      Modifiers::PURE | Modifiers::STRICT | Modifiers::PROVABLE | Modifiers::FREE
    }
  
    /// Parses a string into a singleton [`Modifiers`], or [`NONE`](Self::NONE) if the string is not valid.
    #[must_use] pub fn from_name(s: &[u8]) -> Modifiers {
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
  