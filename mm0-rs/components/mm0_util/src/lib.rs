//! Utilities, mainly path manipulation with some newtype definitions.
//!
//! The types `Position` and `Range` will be different depending on whether
//! the `server` feature is enabled.

// rust lints we want
#![warn(
  bare_trait_objects,
  elided_lifetimes_in_paths,
  missing_copy_implementations,
  missing_debug_implementations,
  future_incompatible,
  rust_2018_idioms,
  trivial_numeric_casts,
  variant_size_differences,
  unreachable_pub,
  unused,
  missing_docs
)]
#![deny(unsafe_op_in_unsafe_fn)]
// all the clippy
#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
// all the clippy::restriction lints we want
#![warn(
  clippy::else_if_without_else,
  clippy::float_arithmetic,
  clippy::get_unwrap,
  clippy::inline_asm_x86_att_syntax,
  clippy::integer_division,
  clippy::rc_buffer,
  clippy::rest_pat_in_fully_bound_structs,
  clippy::string_add,
  clippy::undocumented_unsafe_blocks,
  clippy::unwrap_used
)]
// all the clippy lints we don't want
#![allow(
  clippy::cognitive_complexity,
  clippy::comparison_chain,
  clippy::default_trait_access,
  clippy::inline_always,
  clippy::manual_filter_map,
  clippy::map_err_ignore,
  clippy::missing_const_for_fn,
  clippy::missing_errors_doc,
  clippy::missing_panics_doc,
  clippy::module_name_repetitions,
  clippy::multiple_crate_versions,
  clippy::option_if_let_else,
  clippy::redundant_pub_crate,
  clippy::semicolon_if_nothing_returned,
  clippy::shadow_unrelated,
  clippy::too_many_lines,
  clippy::use_self
)]

#[macro_use]
extern crate bitflags;

#[cfg(feature = "memory")]
use mm0_deepsize_derive::DeepSizeOf;
use std::borrow::Borrow;
use std::collections::{
  hash_map::{Entry, OccupiedEntry},
  HashMap,
};
use std::error::Error;
use std::fmt;
use std::hash::{BuildHasher, Hash, Hasher};
use std::mem::{self, MaybeUninit};
use std::ops::{Deref, DerefMut};
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::Arc;

mod atoms;
mod ids;
mod lined_string;

pub use {ids::*, lined_string::*};

/// Newtype for `Box<dyn Error + Send + Sync>`
pub type BoxError = Box<dyn Error + Send + Sync>;

/// Extension trait for `cloned_box`.
pub trait SliceExt<T> {
  /// Clones a slice into a boxed slice.
  fn cloned_box(&self) -> Box<[T]>
  where T: Clone;
}

impl<T> SliceExt<T> for [T] {
  fn cloned_box(&self) -> Box<[T]>
  where T: Clone {
    self.to_vec().into()
  }
}

/// Extension trait for [`HashMap`]`<K, V>`.
pub trait HashMapExt<K, V> {
  /// Like `insert`, but if the insertion fails then it returns the value
  /// that it attempted to insert, as well as an [`OccupiedEntry`] containing
  /// the other value that was found.
  // TODO: Change this to try_insert when #82766 lands
  fn try_insert_ext(&mut self, k: K, v: V) -> Option<(V, OccupiedEntry<'_, K, V>)>;
}

impl<K: Hash + Eq, V, S: BuildHasher> HashMapExt<K, V> for HashMap<K, V, S> {
  fn try_insert_ext(&mut self, k: K, v: V) -> Option<(V, OccupiedEntry<'_, K, V>)> {
    match self.entry(k) {
      Entry::Vacant(e) => {
        e.insert(v);
        None
      }
      Entry::Occupied(e) => Some((v, e)),
    }
  }
}

/// Extension trait for [`HashMap`]`<K, V>`.
pub trait RcExt<T> {
  /// Extract `T` from `Rc<T>` by cloning the inner data unless it is unshared.
  fn unwrap(this: Self) -> T
  where T: Clone;
}

impl<T> RcExt<T> for Rc<T> {
  #[inline]
  fn unwrap(this: Self) -> T
  where T: Clone {
    Rc::try_unwrap(this).unwrap_or_else(|r| (*r).clone())
  }
}

/// Does the same as `panic!` but works in a `const fn`.
#[macro_export]
macro_rules! const_panic {
  () => {{
    #[allow(unconditional_panic)]
    [][0]
  }};
}

/// Converts `n` from `u32` to `usize` or panics (which should not happen since we don't support
/// 16 bit systems).
#[inline]
#[must_use]
pub fn u32_as_usize(n: u32) -> usize {
  n.try_into().expect("here's a nickel, get a better computer")
}

/// Translate a number into an alphabetic numbering system, indexing into the following infinite
/// sequence:
/// ```ignore
/// a, b, c, ... z, aa, ab, ... az, ba, ... bz, ... zz, aaa, ...
/// ```
#[must_use]
pub fn alphanumber(n: usize) -> String {
  let mut out = Vec::with_capacity(2);
  let mut n = n + 1;
  while n != 0 {
    #[allow(clippy::cast_possible_truncation)]
    {
      out.push(b'a' + ((n - 1) % 26) as u8);
    }
    #[allow(clippy::integer_division)]
    {
      n = (n - 1) / 26;
    }
  }
  out.reverse();
  // Safety: the string consists of ASCII letters
  unsafe { String::from_utf8_unchecked(out) }
}

/// Extension trait for [`Mutex`](std::sync::Mutex)`<T>`.
pub trait MutexExt<T> {
  /// Like `lock`, but propagates instead of catches panics.
  fn ulock(&self) -> std::sync::MutexGuard<'_, T>;
}

impl<T> MutexExt<T> for std::sync::Mutex<T> {
  fn ulock(&self) -> std::sync::MutexGuard<'_, T> {
    self.lock().expect("propagating poisoned mutex")
  }
}
/// Extension trait for [`Condvar`](std::sync::Condvar).
pub trait CondvarExt {
  /// Like `wait`, but propagates instead of catches panics.
  #[cfg(not(target_arch = "wasm32"))]
  fn uwait<'a, T>(&self, g: std::sync::MutexGuard<'a, T>) -> std::sync::MutexGuard<'a, T>;
}

impl CondvarExt for std::sync::Condvar {
  #[cfg(not(target_arch = "wasm32"))]
  fn uwait<'a, T>(&self, g: std::sync::MutexGuard<'a, T>) -> std::sync::MutexGuard<'a, T> {
    self.wait(g).expect("propagating poisoned mutex")
  }
}

/// Newtype for an `Arc<String>`, so that we can implement `From<&str>`.
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
#[derive(Clone, Hash, PartialEq, Eq)]
pub struct ArcString(pub Arc<[u8]>);

impl Borrow<[u8]> for ArcString {
  fn borrow(&self) -> &[u8] { &self.0 }
}
impl Deref for ArcString {
  type Target = [u8];
  fn deref(&self) -> &[u8] { &self.0 }
}
impl ArcString {
  /// Constructs a new [`ArcString`].
  #[must_use]
  pub fn new(s: Box<[u8]>) -> Self { Self(s.into()) }
}
impl fmt::Display for ArcString {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}", String::from_utf8_lossy(self))
  }
}
impl fmt::Debug for ArcString {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{:?}", String::from_utf8_lossy(self))
  }
}
impl From<&[u8]> for ArcString {
  fn from(s: &[u8]) -> Self { Self::new(s.into()) }
}
impl From<Box<[u8]>> for ArcString {
  fn from(s: Box<[u8]>) -> Self { Self::new(s) }
}
impl From<Vec<u8>> for ArcString {
  fn from(s: Vec<u8>) -> Self { s.into_boxed_slice().into() }
}
impl From<String> for ArcString {
  fn from(s: String) -> Self { s.into_bytes().into() }
}

impl ArcString {
  /// Turn this `ArcString` into a `&str`.
  ///
  /// # Safety
  /// This is potentially unsafe because `ArcString` do not have to be valid unicode.
  #[must_use]
  pub fn as_str(&self) -> &str {
    // Safety: ensured by caller
    unsafe { std::str::from_utf8_unchecked(self) }
  }
}

/// A structure that allows constructing linked lists on the call stack.
#[derive(Debug, Clone, Copy)]
pub struct StackList<'a, T>(pub Option<&'a (StackList<'a, T>, T)>);

impl<T> StackList<'_, T> {
  /// Returns true if this list contains the given element.
  pub fn contains(&self, t: &T) -> bool
  where T: PartialEq {
    let mut s = self;
    loop {
      match s.0 {
        None => return false,
        Some((_, t2)) if *t2 == *t => return true,
        Some((s2, _)) => s = s2,
      }
    }
  }
}

/// A linked list data structure based on `Arc`.
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
#[derive(Debug)]
pub struct ArcList<T>(Option<Arc<(ArcList<T>, T)>>);

impl<T> Default for ArcList<T> {
  fn default() -> Self { Self(None) }
}
impl<T> Clone for ArcList<T> {
  fn clone(&self) -> Self { Self(self.0.clone()) }
}

impl<T> ArcList<T> {
  /// Return true if the list is empty.
  #[must_use]
  pub fn is_empty(&self) -> bool { self.0.is_none() }
  /// Append a new node on the end of the list.
  #[must_use]
  pub fn push(self, t: T) -> Self { Self(Some(Arc::new((self, t)))) }
  /// Check if the list contains an item.
  #[must_use]
  pub fn contains(&self, t: &T) -> bool
  where T: PartialEq {
    let mut s = self;
    loop {
      match s.0.as_deref() {
        None => return false,
        Some((_, t2)) if *t2 == *t => return true,
        Some((s2, _)) => s = s2,
      }
    }
  }

  /// Construct `self[..t2] ++ t :: tail` where `t2`
  /// is the first element of `self` equal to `t`.
  /// Panics if no such `t2` exists (i.e. `self.contains(t)` is a precondition).
  #[must_use]
  pub fn join(&self, t: T, tail: Self) -> Self
  where T: PartialEq + Clone {
    let (l, t2) = &**self.0.as_ref().expect("self should contain t");
    if *t2 == t {
      return tail.push(t)
    }
    l.join(t, tail).push(t2.clone())
  }
}

/// An iterator over an [`ArcList`].
#[must_use]
#[derive(Debug, Clone)]
pub struct ArcListIter<'a, T>(&'a ArcList<T>);

impl<'a, T> Iterator for ArcListIter<'a, T> {
  type Item = &'a T;
  fn next(&mut self) -> Option<&'a T> {
    let (l, t) = &**self.0.0.as_ref()?;
    self.0 = l;
    Some(t)
  }
}

impl<'a, T> IntoIterator for &'a ArcList<T> {
  type Item = &'a T;
  type IntoIter = ArcListIter<'a, T>;
  fn into_iter(self) -> ArcListIter<'a, T> { ArcListIter(self) }
}

/// A way to initialize a `Box<[T]>` by first constructing the array (giving the length),
/// initializing the elements in some order, and then using the unsafe function
/// [`assume_init`] to assert that every element of the array has been initialized and
/// transmute the `SliceUninit<T>` into a `Box<[T]>`.
///
/// [`assume_init`]: SliceUninit::assume_init
#[derive(Debug)]
pub struct SliceUninit<T>(Box<[MaybeUninit<T>]>);

impl<T> SliceUninit<T> {
  /// Create a new uninitialized slice of length `size`.
  #[inline]
  #[must_use]
  pub fn new(size: usize) -> Self {
    let mut res = Vec::with_capacity(size);
    #[allow(clippy::uninit_vec)] // rust-clippy#10565
    // Safety: the newly constructed elements have type MaybeUninit<T>
    // so it's fine to not initialize them
    unsafe { res.set_len(size) };
    Self(res.into_boxed_slice())
  }

  /// Assign the value `val` to location `i` of the slice. Warning: this does not
  /// call the destructor for `T` on the previous value, so this should be used only
  /// once per location unless `T` has no `Drop` impl.
  #[inline]
  pub fn set(&mut self, i: usize, val: T) { self.0[i] = MaybeUninit::new(val) }

  /// Finalizes the construction, returning an initialized `Box<[T]>`.
  ///
  /// # Safety
  ///
  /// This causes undefined behavior if the content is not fully initialized.
  #[inline]
  #[must_use]
  pub unsafe fn assume_init(self) -> Box<[T]> {
    // Safety: ensured by caller
    unsafe { mem::transmute(self.0) }
  }
}

/// Points to a specific region of a source file by identifying the region's start and end points.
#[derive(Copy, Clone, Default, PartialEq, Eq, Hash)]
pub struct Span {
  /// The byte index of the beginning of the span (inclusive).
  pub start: usize,
  /// The byte index of the end of the span (exclusive).
  pub end: usize,
}

#[cfg(feature = "memory")]
mm0_deepsize::deep_size_0!(Span);

impl From<std::ops::Range<usize>> for Span {
  #[inline]
  fn from(r: std::ops::Range<usize>) -> Self { Span { start: r.start, end: r.end } }
}

impl From<std::ops::RangeInclusive<usize>> for Span {
  #[inline]
  fn from(r: std::ops::RangeInclusive<usize>) -> Self {
    Span { start: *r.start(), end: *r.end() + 1 }
  }
}

impl From<usize> for Span {
  #[inline]
  fn from(n: usize) -> Self { Span { start: n, end: n } }
}

impl From<Span> for std::ops::Range<usize> {
  #[inline]
  fn from(s: Span) -> Self { s.start..s.end }
}

impl Deref for Span {
  type Target = std::ops::Range<usize>;
  fn deref(&self) -> &std::ops::Range<usize> {
    // Safety: Range<usize> and Span are layout compatible
    unsafe { &*<*const _>::cast(self) }
  }
}

impl DerefMut for Span {
  fn deref_mut(&mut self) -> &mut std::ops::Range<usize> {
    // Safety: Range<usize> and Span are layout compatible
    unsafe { &mut *<*mut _>::cast(self) }
  }
}

impl IntoIterator for Span {
  type Item = usize;
  type IntoIter = std::ops::Range<usize>;
  fn into_iter(self) -> std::ops::Range<usize> { (*self).clone() }
}

impl fmt::Debug for Span {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}..{}", self.start, self.end)
  }
}

#[cfg(feature = "server")]
pub use lsp_types::{Position, Range};

#[cfg(not(feature = "server"))]
/// Position in a text document expressed as zero-based line and character offset.
/// A position is between two characters like an 'insert' cursor in a editor.
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Copy, Clone, Default)]
pub struct Position {
  /// Line position in a document (zero-based).
  pub line: u32,
  /// Character offset on a line in a document (zero-based).
  pub character: u32,
}

#[cfg(not(feature = "server"))]
/// A range in a text document expressed as (zero-based) start and end positions.
/// A range is comparable to a selection in an editor. Therefore the end position is exclusive.
#[derive(Debug, Eq, PartialEq, Copy, Clone, Default)]
pub struct Range {
  /// The range's start position.
  pub start: Position,
  /// The range's end position.
  pub end: Position,
}

#[cfg(feature = "lined_string")]
/// A [`PathBuf`] lazily initialized to a canonicalized "."
static CURRENT_DIR: once_cell::sync::Lazy<PathBuf> =
  once_cell::sync::Lazy::new(|| {
    #[cfg(target_arch = "wasm32")]
    let buf = PathBuf::from(".");
    #[cfg(not(target_arch = "wasm32"))]
    let buf = std::fs::canonicalize(".").expect("failed to find current directory");
    buf
  });

/// Given a [`PathBuf`] 'buf', constructs a relative path from [`CURRENT_DIR`]
/// to buf, returning it as a String.
///
/// Example: If [`CURRENT_DIR`] is `/home/johndoe/mm0`, and `buf` is
/// `/home/johndoe/Documents/ahoy.mm1` will return `../Documents/ahoy.mm1`
///
/// [`CURRENT_DIR`]: struct@CURRENT_DIR
#[cfg(feature = "lined_string")]
fn make_relative(buf: &std::path::Path) -> String {
  pathdiff::diff_paths(buf, &*CURRENT_DIR)
    .as_deref()
    .unwrap_or(buf)
    .to_str()
    .expect("bad unicode in file path")
    .to_owned()
}

#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
#[derive(Default)]
struct FileRefInner {
  path: PathBuf,
  rel: String,
  #[cfg(feature = "server")]
  url: Option<lsp_types::Url>,
}

/// A reference to a file. It wraps an [`Arc`] so it can be cloned thread-safely.
/// A [`FileRef`] can be constructed either from a [`PathBuf`] or a
/// (`file://`) [`Url`](lsp_types::Url),
/// and provides (precomputed) access to these views using
/// [`path()`](FileRef::path) and [`url()`](FileRef::url), as well as
/// [`rel()`](FileRef::rel) to get the relative path from [`struct@CURRENT_DIR`].
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
#[derive(Clone, Default)]
pub struct FileRef(Arc<FileRefInner>);

#[cfg(any(target_arch = "wasm32", feature = "lined_string"))]
impl From<PathBuf> for FileRef {
  fn from(path: PathBuf) -> FileRef {
    let rel = make_relative(&path);
    FileRef(Arc::new(FileRefInner {
      #[cfg(all(not(target_arch = "wasm32"), feature = "server"))]
      url: lsp_types::Url::from_file_path(&path).ok(),
      #[cfg(all(target_arch = "wasm32", feature = "server"))]
      url: lsp_types::Url::parse(&format!("wasm:/{rel}")).ok(),
      rel,
      path,
    }))
  }
}

#[cfg(feature = "server")]
impl From<lsp_types::Url> for FileRef {
  fn from(url: lsp_types::Url) -> FileRef {
    #[cfg(not(target_arch = "wasm32"))]
    let path = url.to_file_path().expect("bad URL");
    #[cfg(target_arch = "wasm32")]
    let path = PathBuf::from(url.path());
    let rel = make_relative(&path);
    FileRef(Arc::new(FileRefInner { path, rel, url: Some(url) }))
  }
}

impl FileRef {
  /// Convert this [`FileRef`] to a [`PathBuf`], for use with OS file actions.
  #[must_use]
  pub fn path(&self) -> &PathBuf { &self.0.path }

  /// Convert this [`FileRef`] to a relative path (as a `&str`).
  #[must_use]
  pub fn rel(&self) -> &str { &self.0.rel }

  /// Convert this [`FileRef`] to a `file://` URL, for use with LSP.
  #[cfg(feature = "server")]
  #[must_use]
  pub fn url(&self) -> &lsp_types::Url { self.0.url.as_ref().expect("bad file location") }

  /// Get a pointer to this allocation, for use in hashing.
  #[must_use]
  pub fn ptr(&self) -> *const PathBuf { self.path() }

  /// Compare this with `other` for pointer equality.
  #[must_use]
  pub fn ptr_eq(&self, other: &FileRef) -> bool { Arc::ptr_eq(&self.0, &other.0) }

  /// Returns true if this file has the provided extension.
  #[must_use]
  pub fn has_extension(&self, ext: &str) -> bool {
    self.path().extension().map_or(false, |s| s == ext)
  }
}
impl PartialEq for FileRef {
  fn eq(&self, other: &Self) -> bool { self.0.rel == other.0.rel }
}
impl Eq for FileRef {}

impl Hash for FileRef {
  fn hash<H: Hasher>(&self, state: &mut H) { self.0.rel.hash(state) }
}

impl fmt::Display for FileRef {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let s = self.0.path.file_name().unwrap_or(self.0.path.as_os_str());
    s.to_str().expect("bad unicode in path").fmt(f)
  }
}

impl fmt::Debug for FileRef {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { fmt::Display::fmt(self, f) }
}

/// A span paired with a [`FileRef`].
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
#[derive(Clone, Default, PartialEq, Eq)]
pub struct FileSpan {
  /// The file in which this span occured.
  pub file: FileRef,
  /// The span (as byte indexes into the file source text).
  pub span: Span,
}

impl fmt::Debug for FileSpan {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}:{:?}", self.file, self.span)
  }
}
impl<'a> From<&'a FileSpan> for Span {
  fn from(fsp: &'a FileSpan) -> Self { fsp.span }
}

/// Try to get memory usage (resident set size) in bytes using the
/// [`getrusage()`](libc::getrusage) function from libc.
#[allow(unused)]
#[cfg(all(feature = "memory", unix))]
fn get_memory_rusage() -> usize {
  // Safety: getrusage() initializes the passed-in buffer
  let usage = unsafe {
    let mut usage = MaybeUninit::uninit();
    assert_eq!(libc::getrusage(libc::RUSAGE_SELF, usage.as_mut_ptr()), 0);
    usage.assume_init()
  };
  let x: usize = usage.ru_maxrss.try_into().expect("negative memory?");
  x * 1024
}

/// Try to get memory usage (resident set size) in bytes using the
/// [`getrusage()`](libc::getrusage) function from libc.
#[allow(unused)]
#[cfg(all(feature = "memory", not(unix)))]
fn get_memory_rusage() -> usize { 0 }

/// Try to get total memory usage (stack + data) in bytes using the `/proc` filesystem.
/// Falls back on [`getrusage()`](libc::getrusage) if procfs doesn't exist.
#[cfg(all(feature = "memory", target_os = "linux"))]
#[must_use]
pub fn get_memory_usage() -> usize {
  procfs::process::Process::myself().and_then(|me| me.statm())
    .map_or_else(|_| get_memory_rusage(), |stat|
      usize::try_from(stat.data).expect("overflow") * 4096)
}

/// Try to get total memory usage (stack + data) in bytes using the `/proc` filesystem.
/// Falls back on [`getrusage()`](libc::getrusage) if procfs doesn't exist.
#[cfg(all(feature = "memory", not(target_os = "linux")))]
#[must_use]
pub fn get_memory_usage() -> usize { get_memory_rusage() }

/// Try to get total memory usage (stack + data) in bytes using the `/proc` filesystem.
/// Falls back on [`getrusage()`](libc::getrusage) if procfs doesn't exist.
#[cfg(not(feature = "memory"))]
#[must_use]
pub fn get_memory_usage() -> usize { 0 }
