//! Utilities, mainly path manipulation with some newtype definitions.

use std::ops::{Deref, DerefMut};
use std::borrow::Borrow;
use std::ffi::CStr;
use std::mem::{self, MaybeUninit};
use std::fmt;
use std::error::Error;
use std::path::PathBuf;
use std::sync::Arc;
use std::hash::{Hash, Hasher, BuildHasher};
use std::collections::{HashMap, hash_map::{Entry, OccupiedEntry}};

/// Newtype for `Box<dyn Error + Send + Sync>`
pub type BoxError = Box<dyn Error + Send + Sync>;

/// Extension trait for `cloned_box`.
pub trait SliceExt<T> {
  /// Clones a slice into a boxed slice.
  fn cloned_box(&self) -> Box<[T]> where T: Clone;
}

impl<T> SliceExt<T> for [T] {
  fn cloned_box(&self) -> Box<[T]> where T: Clone { self.to_vec().into() }
}

/// Extension trait for [`HashMap`]`<K, V>`.
pub trait HashMapExt<K, V> {
  /// Like `insert`, but if the insertion fails then it returns the value
  /// that it attempted to insert, as well as an [`OccupiedEntry`] containing
  /// the other value that was found.
  fn try_insert(&mut self, k: K, v: V) -> Option<(V, OccupiedEntry<'_, K, V>)>;
}

impl<K: Hash + Eq, V, S: BuildHasher> HashMapExt<K, V> for HashMap<K, V, S> {
  fn try_insert(&mut self, k: K, v: V) -> Option<(V, OccupiedEntry<'_, K, V>)> {
    match self.entry(k) {
      Entry::Vacant(e) => { e.insert(v); None }
      Entry::Occupied(e) => Some((v, e))
    }
  }
}
/// Extension trait for [`Option`]`<T>`.
pub trait OptionExt<T> {
  /// Like `unwrap`, but invokes undefined behavior instead of panicking.
  ///
  /// # Safety
  /// This function must not be called on a [`None`] value.
  unsafe fn unwrap_unchecked(self) -> T;
}

impl<T> OptionExt<T> for Option<T> {
  #[inline]
  unsafe fn unwrap_unchecked(self) -> T {
    match self {
      Some(x) => x,
      None => std::hint::unreachable_unchecked()
    }
  }
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
  fn uwait<'a, T>(&self, g: std::sync::MutexGuard<'a, T>) -> std::sync::MutexGuard<'a, T>;
}

impl CondvarExt for std::sync::Condvar {
  fn uwait<'a, T>(&self, g: std::sync::MutexGuard<'a, T>) -> std::sync::MutexGuard<'a, T> {
    self.wait(g).expect("propagating poisoned mutex")
  }
}

/// Newtype for an `Arc<String>`, so that we can implement `From<&str>`.
#[derive(Clone, Hash, PartialEq, Eq, DeepSizeOf)]
pub struct ArcString(pub Arc<[u8]>);

impl Borrow<[u8]> for ArcString {
  fn borrow(&self) -> &[u8] { &*self.0 }
}
impl Deref for ArcString {
  type Target = [u8];
  fn deref(&self) -> &[u8] { &*self.0 }
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
  pub(crate) fn as_str(&self) -> &str {
    unsafe {std::str::from_utf8_unchecked(self)}
  }
}

/// A structure that allows constructing linked lists on the call stack.
#[derive(Debug, Clone, Copy)]
pub struct StackList<'a, T>(pub Option<&'a (StackList<'a, T>, T)>);

impl<T> StackList<'_, T> {
  /// Returns true if this list contains the given element.
  pub fn contains(&self, t: &T) -> bool where T: PartialEq {
    let mut s = self;
    loop {
      match s.0 {
        None => return false,
        Some((_, t2)) if *t2 == *t => return true,
        Some((s2, _)) => s = s2
      }
    }
  }
}

/// A linked list data structure based on `Arc`.
#[derive(Debug, DeepSizeOf)]
pub struct ArcList<T>(Option<Arc<(ArcList<T>, T)>>);

impl<T> Default for ArcList<T> {
  fn default() -> Self { Self(None) }
}
impl<T> Clone for ArcList<T> {
  fn clone(&self) -> Self { Self(self.0.clone()) }
}

impl<T> ArcList<T> {
  /// Return true if the list is empty.
  #[must_use] pub fn is_empty(&self) -> bool { self.0.is_none() }
  /// Append a new node on the end of the list.
  #[must_use] pub fn push(self, t: T) -> Self { Self(Some(Arc::new((self, t)))) }
  /// Check if the list contains an item.
  #[must_use] pub fn contains(&self, t: &T) -> bool where T: PartialEq {
    let mut s = self;
    loop {
      match s.0.as_deref() {
        None => return false,
        Some((_, t2)) if *t2 == *t => return true,
        Some((s2, _)) => s = s2
      }
    }
  }

  /// Construct `self[..t2] ++ t :: tail` where `t2`
  /// is the first element of `self` equal to `t`.
  /// Panics if no such `t2` exists (i.e. `self.contains(t)` is a precondition).
  #[must_use] pub fn join(&self, t: T, tail: Self) -> Self where T: PartialEq + Clone {
    let (l, t2) = &**self.0.as_ref().expect("self should contain t");
    if *t2 == t { return tail.push(t) }
    l.join(t, tail).push(t2.clone())
  }
}

/// An iterator over an [`ArcList`].
#[derive(Debug, Clone)]
pub struct ArcListIter<'a, T>(&'a ArcList<T>);

impl<'a, T> Iterator for ArcListIter<'a, T> {
  type Item = &'a T;
  fn next(&mut self) -> Option<&'a T> {
    let (l, t) = &**self.0 .0.as_ref()?;
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
  #[must_use] pub fn new(size: usize) -> Self {
    let mut res = Vec::with_capacity(size);
    // safety: the newly constructed elements have type MaybeUninit<T>
    // so it's fine to not initialize them
    unsafe { res.set_len(size) };
    Self(res.into_boxed_slice())
  }

  /// Assign the value `val` to location `i` of the slice. Warning: this does not
  /// call the destructor for `T` on the previous value, so this should be used only
  /// once per location unless `T` has no `Drop` impl.
  pub fn set(&mut self, i: usize, val: T) { self.0[i] = MaybeUninit::new(val) }

  /// Finalizes the construction, returning an initialized `Box<[T]>`.
  ///
  /// # Safety
  ///
  /// This causes undefined behavior if the content is not fully initialized.
  #[must_use] pub unsafe fn assume_init(self) -> Box<[T]> { mem::transmute(self.0) }
}

/// Points to a specific region of a source file by identifying the region's start and end points.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Span {
  /// The byte index of the beginning of the span (inclusive).
  pub start: usize,
  /// The byte index of the end of the span (exclusive).
  pub end: usize,
}
crate::deep_size_0!(Span);

impl From<std::ops::Range<usize>> for Span {
  #[inline] fn from(r: std::ops::Range<usize>) -> Self {
    Span {start: r.start, end: r.end}
  }
}

impl From<std::ops::RangeInclusive<usize>> for Span {
  #[inline] fn from(r: std::ops::RangeInclusive<usize>) -> Self {
    Span {start: *r.start(), end: *r.end()+1}
  }
}

impl From<usize> for Span {
  #[inline] fn from(n: usize) -> Self { Span {start: n, end: n} }
}

impl From<Span> for std::ops::Range<usize> {
  #[inline] fn from(s: Span) -> Self { s.start..s.end }
}

impl Deref for Span {
  type Target = std::ops::Range<usize>;
  fn deref(&self) -> &std::ops::Range<usize> {
    unsafe { &*(self as *const Span as *const std::ops::Range<usize>) }
  }
}

impl DerefMut for Span {
  fn deref_mut(&mut self) -> &mut std::ops::Range<usize> {
    unsafe { &mut *(self as *mut Span as *mut std::ops::Range<usize>) }
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

lazy_static! {
  /// A [`PathBuf`] created by `lazy_static!` pointing to a canonicalized "."
  pub static ref CURRENT_DIR: PathBuf =
    std::fs::canonicalize(".").expect("failed to find current directory");
}

/// Given a [`PathBuf`] 'buf', constructs a relative path from [`CURRENT_DIR`]
/// to buf, returning it as a String.
///
/// Example: If [`CURRENT_DIR`] is `/home/johndoe/mm0`, and `buf` is
/// `/home/johndoe/Documents/ahoy.mm1` will return `../Documents/ahoy.mm1`
///
/// [`CURRENT_DIR`]: struct@CURRENT_DIR
fn make_relative(buf: &PathBuf) -> String {
  pathdiff::diff_paths(buf, &*CURRENT_DIR).as_ref().unwrap_or(buf)
    .to_str().expect("bad unicode in file path").to_owned()
}

#[derive(DeepSizeOf)]
struct FileRefInner {
  path: PathBuf,
  rel: String,
  #[cfg(feature = "server")]
  url: lsp_types::Url
}

/// A reference to a file. It wraps an [`Arc`] so it can be cloned thread-safely.
/// A [`FileRef`] can be constructed either from a [`PathBuf`] or a
/// (`file://`) [`Url`](lsp_types::Url),
/// and provides (precomputed) access to these views using
/// [`path()`](FileRef::path) and [`url()`](FileRef::url), as well as
/// [`rel()`](FileRef::rel) to get the relative path from [`struct@CURRENT_DIR`].
#[derive(Clone, DeepSizeOf)]
pub struct FileRef(Arc<FileRefInner>);

impl From<PathBuf> for FileRef {
  fn from(path: PathBuf) -> FileRef {
    FileRef(Arc::new(FileRefInner {
      rel: make_relative(&path),
      #[cfg(feature = "server")]
      url: lsp_types::Url::from_file_path(&path).expect("bad file path"),
      path,
    }))
  }
}

#[cfg(feature = "server")]
impl From<lsp_types::Url> for FileRef {
  fn from(url: lsp_types::Url) -> FileRef {
    let path = url.to_file_path().expect("bad URL");
    let rel = make_relative(&path);
    FileRef(Arc::new(FileRefInner {path, rel, url}))
  }
}

impl FileRef {
  /// Convert this [`FileRef`] to a [`PathBuf`], for use with OS file actions.
  #[must_use] pub fn path(&self) -> &PathBuf { &self.0.path }
  /// Convert this [`FileRef`] to a relative path (as a `&str`).
  #[must_use] pub fn rel(&self) -> &str { &self.0.rel }
  /// Convert this [`FileRef`] to a `file:://` URL, for use with LSP.
  #[cfg(feature = "server")]
  #[must_use] pub fn url(&self) -> &lsp_types::Url { &self.0.url }
  /// Get a pointer to this allocation, for use in hashing.
  #[must_use] pub fn ptr(&self) -> *const PathBuf { self.path() }
  /// Compare this with `other` for pointer equality.
  #[must_use] pub fn ptr_eq(&self, other: &FileRef) -> bool { Arc::ptr_eq(&self.0, &other.0) }

  /// Returns true if this file has the provided extension.
  #[must_use] pub fn has_extension(&self, ext: &str) -> bool {
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
    self.0.path.file_name().unwrap_or_else(|| self.0.path.as_os_str())
      .to_str().expect("bad unicode in path").fmt(f)
  }
}

impl fmt::Debug for FileRef {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    fmt::Display::fmt(self, f)
  }
}

/// A span paired with a [`FileRef`].
#[derive(Clone, PartialEq, Eq, DeepSizeOf)]
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

/// Construct a `&`[`CStr`] from a prefix byte slice, by terminating at
/// the first nul character. The second output is the remainder of the slice.
#[must_use] pub fn cstr_from_bytes_prefix(bytes: &[u8]) -> Option<(&CStr, &[u8])> {
  let mid = memchr::memchr(0, bytes)? + 1;
  unsafe {
    Some((CStr::from_bytes_with_nul_unchecked(bytes.get_unchecked(..mid)),
      bytes.get_unchecked(..mid)))
  }
}

/// Try to get memory usage (resident set size) in bytes using the
/// [`getrusage()`](libc::getrusage) function from libc.
#[cfg(feature = "memory")]
pub(crate) fn get_memory_rusage() -> usize {
  use std::convert::TryInto;
  let usage = unsafe {
    let mut usage = MaybeUninit::uninit();
    assert_eq!(libc::getrusage(libc::RUSAGE_SELF, usage.as_mut_ptr()), 0);
    usage.assume_init()
  };
  let x: usize = usage.ru_maxrss.try_into().expect("negative memory?");
  x * 1024
}

/// Try to get total memory usage (stack + data) in bytes using the `/proc` filesystem.
/// Falls back on [`getrusage()`](libc::getrusage) if procfs doesn't exist.
#[cfg(all(feature = "memory", target_os = "linux"))]
pub(crate) fn get_memory_usage() -> usize {
  procinfo::pid::statm_self().map_or_else(|_| get_memory_rusage(), |stat| stat.data * 4096)
}

/// Try to get total memory usage (stack + data) in bytes using the `/proc` filesystem.
/// Falls back on [`getrusage()`](libc::getrusage) if procfs doesn't exist.
#[cfg(all(feature = "memory", not(target_os = "linux")))]
pub(crate) fn get_memory_usage() -> usize {
  get_memory_rusage()
}

/// Try to get total memory usage (stack + data) in bytes using the `/proc` filesystem.
/// Falls back on [`getrusage()`](libc::getrusage) if procfs doesn't exist.
#[cfg(not(feature = "memory"))]
pub(crate) fn get_memory_usage() -> usize { 0 }