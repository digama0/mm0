//! A compact binary encoding for the compiler's own data, used for the `Dyn` procedure
//! blob (the `CustomProc` `kind = 4` case in `mm0-rs/mmb-lisp.md`).
//!
//! The encoding is the `.mmb` value stream's: `uleb` for unsigned, `sleb` for signed,
//! length-prefixed byte strings, and a variant tag before an enum's payload. What is new
//! is that [`Encode`] takes an [`EncodeCtx`] *by parameter*, which is what lets the hash-consed
//! types be encoded at all.
//!
//! # Why the context is explicit
//!
//! The owned types in `global`/`mir` are interned: one `Rc` stands for each distinct node
//! and is shared at every occurrence, so writing the graph as a tree is unbounded — a
//! chain of `n` nodes each referenced twice denotes `2^n` leaves. An [`Rc`] therefore
//! encodes as a back-reference the second time it is seen, exactly as the lisp table's
//! `Save`/`Ref` do.
//!
//! Interning is stateful and keyed on pointer identity, so an impl must be able to reach
//! that state. Taking it as a parameter makes "this type needs a context" a fact the type
//! checker enforces, rather than a discipline the caller has to remember.

use std::{collections::HashMap, rc::Rc};

/// The four bytes identifying this encoding to whatever carries it.
/// This is written just before the length-prefixed blob.
pub const MAGIC: [u8; 4] = *b"MMCC";

/// A malformed or truncated stream.
#[derive(Copy, Clone, Debug)]
pub struct DecodeErr(pub &'static str);

impl std::fmt::Display for DecodeErr {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { f.write_str(self.0) }
}
impl std::error::Error for DecodeErr {}

/// The result of reading.
pub type Result<T> = std::result::Result<T, DecodeErr>;

/// Write `self` to `out`, interning any shared nodes into `ctx`.
pub trait Encode {
  /// Append the encoding of `self`.
  fn encode(&self, ctx: &mut EncodeCtx<'_>, out: &mut Vec<u8>);
}

/// Read a value back, resolving interned nodes through `ctx`.
pub trait Decode: Sized {
  /// Consume the encoding of one value from the front of `buf`.
  fn decode(ctx: &mut DecodeCtx<'_>, buf: &mut &[u8]) -> Result<Self>;
}

// ------------------------------------------------------------------ primitives

/// An unsigned LEB128: 7 payload bits per byte, low group first, high bit set on every
/// byte but the last.
pub fn uleb(n: u64, out: &mut Vec<u8>) {
  let mut n = n;
  loop {
    #[allow(clippy::cast_possible_truncation)]
    let b = (n & 0x7f) as u8;
    n >>= 7;
    if n == 0 { return out.push(b) }
    out.push(b | 0x80);
  }
}

/// A signed LEB128, sign-extended from bit 6 of the final byte.
pub fn sleb(n: i64, out: &mut Vec<u8>) {
  let mut n = n;
  loop {
    #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
    let b = (n & 0x7f) as u8;
    n >>= 7;
    if n == if b & 0x40 == 0 { 0 } else { -1 } { return out.push(b) }
    out.push(b | 0x80);
  }
}

/// Read one byte.
fn byte(buf: &mut &[u8]) -> Result<u8> {
  let (&b, rest) = buf.split_first().ok_or(DecodeErr("unexpected end of stream"))?;
  *buf = rest;
  Ok(b)
}

/// Read an unsigned LEB128.
pub fn read_uleb(buf: &mut &[u8]) -> Result<u64> {
  let (mut n, mut shift) = (0u64, 0u32);
  loop {
    let b = byte(buf)?;
    if shift >= 64 { return Err(DecodeErr("integer overflow")) }
    n |= u64::from(b & 0x7f) << shift;
    shift += 7;
    if b & 0x80 == 0 { return Ok(n) }
  }
}

/// Read a signed LEB128.
pub fn read_sleb(buf: &mut &[u8]) -> Result<i64> {
  let (mut n, mut shift) = (0i64, 0u32);
  loop {
    let b = byte(buf)?;
    if shift >= 64 { return Err(DecodeErr("integer overflow")) }
    n |= i64::from(b & 0x7f) << shift;
    shift += 7;
    if b & 0x80 == 0 {
      if shift < 64 && b & 0x40 != 0 { n |= -1i64 << shift }
      return Ok(n)
    }
  }
}

macro_rules! impl_int {
  ($enc:ident, $dec:ident, $($t:ty),*) => {$(
    impl Encode for $t {
      fn encode(&self, _: &mut EncodeCtx<'_>, out: &mut Vec<u8>) { $enc((*self).into(), out) }
    }
    impl Decode for $t {
      fn decode(_: &mut DecodeCtx<'_>, buf: &mut &[u8]) -> Result<Self> {
        Self::try_from($dec(buf)?).map_err(|_| DecodeErr("integer out of range"))
      }
    }
  )*}
}
impl_int!(uleb, read_uleb, u8, u16, u32, u64);
impl_int!(sleb, read_sleb, i8, i16, i32, i64);

impl Encode for usize {
  #[allow(clippy::cast_possible_truncation)]
  fn encode(&self, _: &mut EncodeCtx<'_>, out: &mut Vec<u8>) { uleb(*self as u64, out) }
}
impl Decode for usize {
  fn decode(_: &mut DecodeCtx<'_>, buf: &mut &[u8]) -> Result<Self> {
    Self::try_from(read_uleb(buf)?).map_err(|_| DecodeErr("length out of range"))
  }
}

impl Encode for bool {
  fn encode(&self, _: &mut EncodeCtx<'_>, out: &mut Vec<u8>) { out.push((*self).into()) }
}
impl Decode for bool {
  fn decode(_: &mut DecodeCtx<'_>, buf: &mut &[u8]) -> Result<Self> {
    match byte(buf)? { 0 => Ok(false), 1 => Ok(true), _ => Err(DecodeErr("not a bool")) }
  }
}

impl Encode for str {
  fn encode(&self, ctx: &mut EncodeCtx<'_>, out: &mut Vec<u8>) {
    self.len().encode(ctx, out);
    out.extend_from_slice(self.as_bytes());
  }
}
impl Decode for Box<str> {
  fn decode(ctx: &mut DecodeCtx<'_>, buf: &mut &[u8]) -> Result<Self> {
    let len = usize::decode(ctx, buf)?;
    if len > buf.len() { return Err(DecodeErr("unexpected end of stream")) }
    let (s, rest) = buf.split_at(len);
    *buf = rest;
    Ok(std::str::from_utf8(s).map_err(|_| DecodeErr("not UTF-8"))?.into())
  }
}

impl<T: Encode> Encode for Option<T> {
  fn encode(&self, ctx: &mut EncodeCtx<'_>, out: &mut Vec<u8>) {
    match self {
      None => out.push(0),
      Some(v) => { out.push(1); v.encode(ctx, out) }
    }
  }
}
impl<T: Decode> Decode for Option<T> {
  fn decode(ctx: &mut DecodeCtx<'_>, buf: &mut &[u8]) -> Result<Self> {
    match byte(buf)? {
      0 => Ok(None),
      1 => Ok(Some(T::decode(ctx, buf)?)),
      _ => Err(DecodeErr("not an option tag")),
    }
  }
}

/// A `Result` is a two-variant enum like any other; MIR's `Block<T>` is one.
impl<T: Encode, E: Encode> Encode for std::result::Result<T, E> {
  fn encode(&self, ctx: &mut EncodeCtx<'_>, out: &mut Vec<u8>) {
    match self {
      Ok(v) => { out.push(0); v.encode(ctx, out) }
      Err(e) => { out.push(1); e.encode(ctx, out) }
    }
  }
}
impl<T: Decode, E: Decode> Decode for std::result::Result<T, E> {
  fn decode(ctx: &mut DecodeCtx<'_>, buf: &mut &[u8]) -> Result<Self> {
    match byte(buf)? {
      0 => Ok(Ok(T::decode(ctx, buf)?)),
      1 => Ok(Err(E::decode(ctx, buf)?)),
      _ => Err(DecodeErr("not a result tag")),
    }
  }
}

/// A `Box` is invisible on the wire: it holds one value and adds nothing to it. This
/// covers `Box<str>` and `Box<[T]>` too, whose contents impl [`Encode`] unsized.
impl<T: Encode + ?Sized> Encode for Box<T> {
  fn encode(&self, ctx: &mut EncodeCtx<'_>, out: &mut Vec<u8>) { (**self).encode(ctx, out) }
}
/// Reading is by value, so the unsized cases need their own impls below.
impl<T: Decode> Decode for Box<T> {
  fn decode(ctx: &mut DecodeCtx<'_>, buf: &mut &[u8]) -> Result<Self> {
    Ok(Self::new(T::decode(ctx, buf)?))
  }
}

impl<T: Encode> Encode for [T] {
  fn encode(&self, ctx: &mut EncodeCtx<'_>, out: &mut Vec<u8>) {
    self.len().encode(ctx, out);
    for v in self { v.encode(ctx, out) }
  }
}
impl<T: Decode> Decode for Box<[T]> {
  fn decode(ctx: &mut DecodeCtx<'_>, buf: &mut &[u8]) -> Result<Self> {
    let len = usize::decode(ctx, buf)?;
    (0..len).map(|_| T::decode(ctx, buf)).collect()
  }
}

impl<T: Encode> Encode for Vec<T> {
  fn encode(&self, ctx: &mut EncodeCtx<'_>, out: &mut Vec<u8>) { (**self).encode(ctx, out) }
}
impl<T: Decode> Decode for Vec<T> {
  fn decode(ctx: &mut DecodeCtx<'_>, buf: &mut &[u8]) -> Result<Self> {
    Ok(Box::<[T]>::decode(ctx, buf)?.into())
  }
}

// ------------------------------------------------------------------- interning

/// One interned node type's identity map: the index already assigned to each distinct
/// node, keyed by pointer.
#[derive(Debug)]
pub struct Table<T>(HashMap<*const T, u32>);

impl<T> Default for Table<T> {
  fn default() -> Self { Self(HashMap::new()) }
}

/// The nodes rebuilt so far, so a node shared in the original is shared again.
#[derive(Debug)]
pub struct Memo<T>(Vec<Rc<T>>);

impl<T> Default for Memo<T> {
  fn default() -> Self { Self(vec![]) }
}

/// A node type with a table of its own in the context.
///
/// This is what makes a type shared rather than copied: an `Rc<T>` for `T: Interned`
/// encodes as a back-reference the second time it is seen, against `T`'s own table.
pub trait Interned: Sized + Encode + Decode {
  /// This type's identity map while encoding.
  fn table<'a>(ctx: &'a mut EncodeCtx<'_>) -> &'a mut Table<Self>;
  /// This type's rebuilt nodes while decoding.
  fn memo<'a>(ctx: &'a mut DecodeCtx<'_>) -> &'a mut Memo<Self>;
}

impl<T: Interned> Encode for Rc<T> {
  /// A node is written inline the first time it is seen and by back-reference after,
  /// exactly as the lisp table's `Save`/`Ref` do. `0` introduces a new node, `i + 1` is
  /// the node already at index `i`.
  ///
  /// The id is claimed *after* the contents, so any node interned while encoding them
  /// takes a smaller one — which is what the reader does too, pushing to the memo once
  /// it has read the contents. The two stay in step with no global ordering to maintain.
  fn encode(&self, ctx: &mut EncodeCtx<'_>, out: &mut Vec<u8>) {
    let ptr: *const T = Rc::as_ptr(self);
    if let Some(&idx) = T::table(ctx).0.get(&ptr) {
      return uleb(u64::from(idx) + 1, out)
    }
    uleb(0, out);
    (**self).encode(ctx, out);
    let table = T::table(ctx);
    #[allow(clippy::cast_possible_truncation)]
    let idx = table.0.len() as u32;
    table.0.insert(ptr, idx);
  }
}

impl<T: Interned> Decode for Rc<T> {
  fn decode(ctx: &mut DecodeCtx<'_>, buf: &mut &[u8]) -> Result<Self> {
    match read_uleb(buf)? {
      0 => {
        let node = Rc::new(T::decode(ctx, buf)?);
        T::memo(ctx).0.push(Rc::clone(&node));
        Ok(node)
      }
      i => {
        let i = usize::try_from(i - 1).map_err(|_| DecodeErr("back-reference too large"))?;
        T::memo(ctx).0.get(i).cloned()
          .ok_or(DecodeErr("interned back-reference out of range"))
      }
    }
  }
}

// -------------------------------------------------------------- the node types

/// Declares the interned node types: the ones an `Rc` of which is written once and
/// back-referenced thereafter.
///
/// One central invocation rather than a derive per type, because what it generates is
/// *shared*: the two context structs each gain a field per node type. A derive sees one
/// type at a time and emits its tokens before the next runs, so it can never be the one
/// to declare an object every type contributes to. Adding a node type is one line here.
macro_rules! interned {
  ($($field:ident: $node:ty),* $(,)?) => {
    /// The state threaded through encoding.
    #[derive(Debug)]
    pub struct EncodeCtx<'a> {
      /// The output file's directory: span paths are written relative to it.
      base: &'a std::path::Path,
      $($field: Table<$node>),*
    }

    /// The state threaded through decoding.
    #[derive(Debug)]
    pub struct DecodeCtx<'a> {
      /// The file's directory, against which span paths are resolved.
      base: &'a std::path::Path,
      $($field: Memo<$node>),*
    }

    impl<'a> EncodeCtx<'a> {
      /// Begin writing, with `base` the output file's directory.
      #[must_use] pub fn new(base: &'a std::path::Path) -> Self {
        Self { base, $($field: Default::default()),* }
      }
    }

    impl<'a> DecodeCtx<'a> {
      /// Begin reading, with `base` the file's own directory.
      #[must_use] pub fn new(base: &'a std::path::Path) -> Self {
        Self { base, $($field: Default::default()),* }
      }
    }

    $(impl Interned for $node {
      fn table<'a>(ctx: &'a mut EncodeCtx<'_>) -> &'a mut Table<Self> { &mut ctx.$field }
      fn memo<'a>(ctx: &'a mut DecodeCtx<'_>) -> &'a mut Memo<Self> { &mut ctx.$field }
    })*
  }
}

interned! {
  tpat: crate::types::global::TuplePatternS,
  arg: crate::types::global::ArgS,
  ty: crate::types::global::TyKind,
  place: crate::types::global::PlaceKind,
  expr: crate::types::global::ExprKind,
  mir_ty: crate::types::mir::TyKind,
  mir_expr: crate::types::mir::ExprKind,
  mir_eplace: crate::types::mir::EPlaceKind,
  allocs: crate::mir_opt::storage::Allocations,
}

// ------------------------------------------------------------------ the stream

/// Encode `value` into a self-contained buffer.
pub fn to_bytes<T: Encode>(value: &T, base: &std::path::Path) -> Vec<u8> {
  let mut out = Vec::new();
  value.encode(&mut EncodeCtx::new(base), &mut out);
  out
}

/// Read back a value written by [`to_bytes`]. The caller has already identified the
/// stream by its [`MAGIC`]; this is the payload alone.
pub fn from_bytes<T: Decode>(buf: &[u8], base: &std::path::Path) -> Result<T> {
  let mut buf = buf;
  let value = T::decode(&mut DecodeCtx::new(base), &mut buf)?;
  if !buf.is_empty() { return Err(DecodeErr("trailing bytes")) }
  Ok(value)
}

/// A reference encodes as what it points at, so a caller can hand over borrowed fields
/// without cloning them.
impl<T: Encode + ?Sized> Encode for &T {
  fn encode(&self, ctx: &mut EncodeCtx<'_>, out: &mut Vec<u8>) { (**self).encode(ctx, out) }
}

/// A tuple writes its elements back to back: the shape is static, so nothing marks the
/// boundaries. `ArgS` and friends are tuple aliases, not structs, so they cannot derive.
macro_rules! impl_tuple {
  ($(($($n:ident),*)),*) => {$(
    #[allow(non_snake_case)]
    impl<$($n: Encode),*> Encode for ($($n,)*) {
      fn encode(&self, ctx: &mut EncodeCtx<'_>, out: &mut Vec<u8>) {
        let ($($n,)*) = self;
        $($n.encode(ctx, out);)*
      }
    }
    #[allow(non_snake_case)]
    impl<$($n: Decode),*> Decode for ($($n,)*) {
      fn decode(ctx: &mut DecodeCtx<'_>, buf: &mut &[u8]) -> Result<Self> {
        $(let $n = $n::decode(ctx, buf)?;)*
        Ok(($($n,)*))
      }
    }
  )*}
}
impl_tuple!((A, B), (A, B, C), (A, B, C, D), (A, B, C, D, E), (A, B, C, D, E, F));

/// A fixed-size array, whose length is static and so unwritten.
impl<T: Encode, const N: usize> Encode for [T; N] {
  fn encode(&self, ctx: &mut EncodeCtx<'_>, out: &mut Vec<u8>) {
    for v in self { v.encode(ctx, out) }
  }
}
impl<T: Decode, const N: usize> Decode for [T; N] {
  fn decode(ctx: &mut DecodeCtx<'_>, buf: &mut &[u8]) -> Result<Self> {
    let mut v = Vec::with_capacity(N);
    for _ in 0..N { v.push(T::decode(ctx, buf)?) }
    Ok(v.try_into().ok().expect("N elements were just pushed"))
  }
}

/// A map writes its length then its pairs. Iteration order is unspecified, so a stream is
/// not byte-reproducible across runs; nothing here depends on that, but a caller wanting
/// a stable blob would have to sort first.
impl<K: Encode, V: Encode, S> Encode for std::collections::HashMap<K, V, S> {
  fn encode(&self, ctx: &mut EncodeCtx<'_>, out: &mut Vec<u8>) {
    self.len().encode(ctx, out);
    for (k, v) in self { k.encode(ctx, out); v.encode(ctx, out) }
  }
}
impl<K: Decode + std::hash::Hash + Eq, V: Decode, S: std::hash::BuildHasher + Default>
  Decode for std::collections::HashMap<K, V, S> {
  fn decode(ctx: &mut DecodeCtx<'_>, buf: &mut &[u8]) -> Result<Self> {
    let len = usize::decode(ctx, buf)?;
    if len > buf.len() { return Err(DecodeErr("map longer than the stream")) }
    let mut m = Self::with_capacity_and_hasher(len, S::default());
    for _ in 0..len { m.insert(K::decode(ctx, buf)?, V::decode(ctx, buf)?); }
    Ok(m)
  }
}

/// A [`SmallVec`](smallvec::SmallVec) is a `Vec` that may not have spilled; the inline
/// capacity is a property of the type, so the wire format is a plain sequence.
impl<A: smallvec::Array> Encode for smallvec::SmallVec<A> where A::Item: Encode {
  fn encode(&self, ctx: &mut EncodeCtx<'_>, out: &mut Vec<u8>) { (**self).encode(ctx, out) }
}
impl<A: smallvec::Array> Decode for smallvec::SmallVec<A> where A::Item: Decode {
  fn decode(ctx: &mut DecodeCtx<'_>, buf: &mut &[u8]) -> Result<Self> {
    let len = usize::decode(ctx, buf)?;
    if len > buf.len() { return Err(DecodeErr("sequence longer than the stream")) }
    (0..len).map(|_| A::Item::decode(ctx, buf)).collect()
  }
}

/// A [`BitVec`](bit_vec::BitVec) is its length in bits followed by its bytes, since the
/// last byte's spare bits are not part of the value.
impl Encode for bit_vec::BitVec {
  fn encode(&self, ctx: &mut EncodeCtx<'_>, out: &mut Vec<u8>) {
    self.len().encode(ctx, out);
    out.extend_from_slice(&self.to_bytes());
  }
}
impl Decode for bit_vec::BitVec {
  fn decode(ctx: &mut DecodeCtx<'_>, buf: &mut &[u8]) -> Result<Self> {
    let len = usize::decode(ctx, buf)?;
    let bytes = len.div_ceil(8);
    if bytes > buf.len() { return Err(DecodeErr("bit vector longer than the stream")) }
    let (bits, rest) = buf.split_at(bytes);
    *buf = rest;
    let mut v = Self::from_bytes(bits);
    v.truncate(len);
    Ok(v)
  }
}

/// A [`Span`](mm0_util::Span) is its two byte offsets.
impl Encode for mm0_util::Span {
  fn encode(&self, ctx: &mut EncodeCtx<'_>, out: &mut Vec<u8>) {
    self.start.encode(ctx, out);
    (self.end - self.start).encode(ctx, out);
  }
}
impl Decode for mm0_util::Span {
  fn decode(ctx: &mut DecodeCtx<'_>, buf: &mut &[u8]) -> Result<Self> {
    let start = usize::decode(ctx, buf)?;
    let len = usize::decode(ctx, buf)?;
    Ok((start..start.checked_add(len).ok_or(DecodeErr("span overflow"))?).into())
  }
}

/// A [`FileSpan`](mm0_util::FileSpan) is a path and a range.
///
/// The path is stored relative to the `.mmb`'s own directory and resolved against it on
/// read, exactly as the `Lisp` table stores a span's file — so a built tree stays
/// movable. The two tables cannot share the path, though: each has its own heap, so a
/// file named in both is written twice.
impl Encode for mm0_util::FileSpan {
  fn encode(&self, ctx: &mut EncodeCtx<'_>, out: &mut Vec<u8>) {
    let path = self.file.path();
    let rel = pathdiff::diff_paths(path, ctx.base).unwrap_or_else(|| path.clone());
    rel.to_string_lossy().as_ref().encode(ctx, out);
    self.span.encode(ctx, out);
  }
}
impl Decode for mm0_util::FileSpan {
  fn decode(ctx: &mut DecodeCtx<'_>, buf: &mut &[u8]) -> Result<Self> {
    let rel = String::from(Box::<str>::decode(ctx, buf)?);
    let file = mm0_util::FileRef::from(ctx.base.join(rel));
    Ok(Self { file, span: mm0_util::Span::decode(ctx, buf)? })
  }
}

/// An [`IdxVec`](crate::types::IdxVec) is its elements; the index type is a tag.
impl<I, T: Encode> Encode for crate::types::IdxVec<I, T> {
  fn encode(&self, ctx: &mut EncodeCtx<'_>, out: &mut Vec<u8>) { self.0.encode(ctx, out) }
}
impl<I, T: Decode> Decode for crate::types::IdxVec<I, T> {
  fn decode(ctx: &mut DecodeCtx<'_>, buf: &mut &[u8]) -> Result<Self> {
    Ok(Self::from(Vec::<T>::decode(ctx, buf)?))
  }
}

// ----------------------------------------------------------------- leaf types

/// A `bitflags` struct has a private field, so it cannot derive: it round-trips as the
/// integer it is, and rejects bits no flag claims rather than keeping them silently.
macro_rules! impl_bitflags {
  ($($t:ty: $repr:ty),*) => {$(
    impl Encode for $t {
      fn encode(&self, ctx: &mut EncodeCtx<'_>, out: &mut Vec<u8>) { self.bits().encode(ctx, out) }
    }
    impl Decode for $t {
      fn decode(ctx: &mut DecodeCtx<'_>, buf: &mut &[u8]) -> Result<Self> {
        Self::from_bits(<$repr>::decode(ctx, buf)?).ok_or(DecodeErr("unknown flag bits"))
      }
    }
  )*}
}
impl_bitflags!(crate::types::ast::ArgAttr: u8, crate::types::mir::ArgAttr: u8);

/// A `mk_id!` newtype is a plain `u32` index.
macro_rules! impl_id {
  ($($t:ty),*) => {$(
    impl Encode for $t {
      fn encode(&self, ctx: &mut EncodeCtx<'_>, out: &mut Vec<u8>) { self.0.encode(ctx, out) }
    }
    impl Decode for $t {
      fn decode(ctx: &mut DecodeCtx<'_>, buf: &mut &[u8]) -> Result<Self> {
        Ok(Self(u32::decode(ctx, buf)?))
      }
    }
  )*}
}
impl_id!(crate::types::VarId, crate::types::LambdaId, crate::types::ProofId,
  crate::types::ty::LftMVarId, crate::types::mir::VarId, crate::types::mir::BlockId,
  crate::types::mir::CtxBufId, crate::types::hir::GenId, crate::mir_opt::storage::AllocId);

/// A [`Symbol`](crate::Symbol) is an index into a process-wide interner, so it cannot
/// travel as one: it round-trips by name, re-interning on the way in.
impl Encode for crate::Symbol {
  fn encode(&self, ctx: &mut EncodeCtx<'_>, out: &mut Vec<u8>) { self.as_str().encode(ctx, out) }
}
impl Decode for crate::Symbol {
  fn decode(ctx: &mut DecodeCtx<'_>, buf: &mut &[u8]) -> Result<Self> {
    Ok(crate::intern(&Box::<str>::decode(ctx, buf)?))
  }
}

/// A `BigInt` round-trips through its two's-complement bytes.
impl Encode for num::BigInt {
  fn encode(&self, ctx: &mut EncodeCtx<'_>, out: &mut Vec<u8>) {
    self.to_signed_bytes_le().encode(ctx, out)
  }
}
impl Decode for num::BigInt {
  fn decode(ctx: &mut DecodeCtx<'_>, buf: &mut &[u8]) -> Result<Self> {
    Ok(Self::from_signed_bytes_le(&Vec::<u8>::decode(ctx, buf)?))
  }
}

#[cfg(test)]
mod test {
  use super::{from_bytes, to_bytes};
  use crate::types::global::{Ty, TyKind};
  use std::path::{PathBuf, Path};
  use std::rc::Rc;

  /// The directory a stream is written relative to. Nothing here touches the disk, so it
  /// need not exist.
  fn base() -> &'static Path { Path::new("/build/out") }

  /// Fold away `..` components, as opening the file would.
  fn normalize(p: &Path) -> PathBuf {
    let mut out = PathBuf::new();
    for c in p.components() {
      if c.as_os_str() == ".." { out.pop(); } else { out.push(c) }
    }
    out
  }

  /// A type whose DAG has `2^depth` leaves but only `depth` distinct nodes: each level is
  /// one `Rc` used twice. Writing it as a tree is what the interning exists to avoid.
  fn doubling(depth: usize) -> Ty {
    let mut ty: Ty = Rc::new(TyKind::Unit);
    for _ in 0..depth { ty = Rc::new(TyKind::Imp(ty.clone(), ty)) }
    ty
  }

  /// The encoding round-trips, and — the point of the whole design — a node shared in the
  /// original is written once and shared again on the way back, rather than expanded.
  #[test]
  fn interned_graph_round_trips() {
    let ty = doubling(20);
    let bytes = to_bytes(&ty, base());
    // 2^20 leaves; if the DAG were written as a tree this could not be a few dozen bytes.
    assert!(bytes.len() < 200, "the DAG was expanded: {} bytes", bytes.len());

    let back: Ty = from_bytes(&bytes, base()).expect("decode");
    assert_eq!(ty, back, "the graph did not round-trip");

    // Sharing restored, not duplicated: the two children of each node are one allocation.
    let mut node = &back;
    for _ in 0..20 {
      let TyKind::Imp(a, b) = &**node else { panic!("expected Imp") };
      assert!(Rc::ptr_eq(a, b), "the two children were rebuilt as separate nodes");
      node = a;
    }

    // The stream carries no header of its own — the container identifies it — so a
    // truncated one has to be caught by the decoding itself rather than by a check.
    assert!(from_bytes::<Ty>(&bytes[1..], base()).is_err(), "a truncated stream was accepted");
    assert!(from_bytes::<Ty>(&bytes[..bytes.len() - 1], base()).is_err(),
      "a stream cut short was accepted");
  }

  /// A span's file travels relative to the output directory, so moving the build tree
  /// moves the spans with it — and a file outside the tree still resolves, by the `..`
  /// path back out.
  #[test]
  fn file_spans_are_relative() {
    use mm0_util::{FileRef, FileSpan};
    let fsp = |p: &str| FileSpan { file: FileRef::from(PathBuf::from(p)), span: (3..7).into() };

    let bytes = to_bytes(&fsp("/build/out/sub/a.mm1"), base());
    assert!(bytes.windows(9).any(|w| w == b"sub/a.mm1"), "the path was not made relative");

    // Read back under a different base: the same stream names a different file, which is
    // exactly what makes the tree movable.
    let moved: FileSpan = from_bytes(&bytes, &PathBuf::from("/elsewhere")).expect("decode");
    assert_eq!(moved.file.path(), &PathBuf::from("/elsewhere/sub/a.mm1"));
    assert_eq!(moved.span, (3..7).into());

    // A file beside the tree rather than under it goes out through `..` and comes back the
    // same file — spelled with the `..` still in it, which is what the OS resolves on open.
    let up = fsp("/build/shared/b.mm1");
    let back: FileSpan = from_bytes(&to_bytes(&up, base()), base()).expect("decode");
    assert_eq!(normalize(back.file.path()), *up.file.path(),
      "a path outside the tree did not survive");
  }
}
