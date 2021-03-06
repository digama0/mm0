//! Basic types involved in MMB file parsing.

use byteorder::LE;
use mm0_util::SortId;
use zerocopy::{FromBytes, Unaligned, U64};

/// bound mask: `10000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000`
pub const TYPE_BOUND_MASK: u64 = 1 << 63;

/// `10000000_11111111_11111111_11111111_11111111_11111111_11111111_11111111`
pub const TYPE_SORT_MASK: u64 = (1 << 63) | ((1 << 56) - 1);

/// deps mask: `00000000_11111111_11111111_11111111_11111111_11111111_11111111_11111111`
pub const TYPE_DEPS_MASK: u64 = (1 << 56) - 1;

/// An argument binder in a term/def or axiom/theorem.
/// * Bit 63 (the high bit of the high byte) is 1 if this is a bound variable.
/// * Bits 56-62 (the low 7 bits of the high byte) give the sort of the variable.
/// * Bits 0-55 (the low 7 bytes) are a bitset giving the set of bound variables
///   earlier in the list that this variable is allowed to depend on.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, FromBytes, Unaligned)]
pub struct Type(U64<LE>);

/// Newtype for `Type` that makes some situations easier to read.
pub type Arg = Type;

impl std::default::Default for Type {
  fn default() -> Self { Type(U64::new(0)) }
}

impl From<u64> for Type {
  fn from(n: u64) -> Type { Type(U64::new(n)) }
}

impl Type {
  /// Get the u64 comprising a type
  pub fn into_inner(self) -> u64 {
    self.0.get()
  }

  /// Make a new `Type` of sort `sort_num`
  #[must_use]
  pub fn new_of_sort(sort_num: u8) -> Self { Type::from(u64::from(sort_num) << 56) }

  /// A brand new `Type`; bool indicates whether it's bound.
  #[must_use]
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
    *self &= Type::from(TYPE_SORT_MASK);
    // Add new sort
    *self |= Type::from(u64::from(sort_id.into_inner()) << 56)
  }

  /// Add a dependency on `bv_idx`
  pub fn add_dep(&mut self, bv_idx: u64) { *self |= Type::from(1 << bv_idx) }

  /// Does this type depend on the bth bound variable?
  ///
  /// This is 0 indexed.
  #[must_use]
  pub fn depends_on(self, bv_idx: u64) -> bool { self.0.get() & (1 << bv_idx) != 0 }

  /// True if this argument is a bound variable.
  #[inline]
  #[must_use]
  pub fn bound(self) -> bool { self.0.get() & (1 << 63) != 0 }
  /// The sort of this variable.
  #[allow(clippy::cast_possible_truncation)]
  #[inline]
  #[must_use]
  pub fn sort(self) -> SortId { SortId(((self.0.get() >> 56) & 0x7F) as u8) }

  /// If this is the type of a bound variable, return a u64
  /// whose only activated bit is the bit indicating which bv
  /// it is.
  #[inline]
  #[must_use]
  pub fn bound_digit(self) -> Option<u64> {
    if self.bound() {
      Some(self.0.get() & !(0xFF << 56))
    } else {
      None
    }
  }

  /// The POSITION (1 - 55) of this bound variable, NOT the literal u64.
  #[must_use]
  pub fn bound_pos(self) -> Option<u64> {
    if self.bound() {
      for i in 0..56 {
        if ((1 << i) & self.0.get()) != 0 {
          return Some(i + 1)
        }
      }
      unreachable!("Something's wrong with `is_bound`")
    } else {
      None
    }
  }

  /// Does this `Type` have dependencies?
  #[inline]
  #[must_use]
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
  #[inline]
  #[must_use]
  pub fn deps(self) -> Option<u64> {
    if self.bound() {
      None
    } else {
      Some(self.deps_unchecked())
    }
  }

  /// Assuming this is a regular/not-bound variable, return a u64
  /// whose only activated bits are the ones marking the bvs
  /// on which it depends.
  #[inline]
  #[must_use]
  pub fn deps_unchecked(self) -> u64 { self.0.get() & !(0xFF << 56) }

  /// Get the high bit only, which holds the boundedness and the sort.
  #[must_use]
  pub fn high_bit(self) -> Self { Type(U64::new(self.0.get() & !TYPE_DEPS_MASK)) }

  /// Are these two types totally bitwise-disjoint
  #[must_use]
  pub fn disjoint(self, other: Self) -> bool { (self.0.get() & other.0.get()) == 0 }
}

impl std::ops::BitAnd<Type> for Type {
  type Output = Self;
  fn bitand(self, rhs: Self) -> Self::Output { Type::from(self.0.get() & rhs.0.get()) }
}

impl std::ops::BitAndAssign<Type> for Type {
  fn bitand_assign(&mut self, other: Self) { self.0.set(self.0.get() & other.0.get()) }
}

impl std::ops::BitOr<Type> for Type {
  type Output = Self;
  fn bitor(self, rhs: Self) -> Self::Output { Type::from(self.0.get() | rhs.0.get()) }
}

impl std::ops::BitOrAssign<Type> for Type {
  fn bitor_assign(&mut self, other: Self) { self.0.set(self.0.get() | other.0.get()) }
}

impl std::ops::Not for Type {
  type Output = Type;
  fn not(self) -> Self::Output { Type::from(!self.0.get()) }
}
