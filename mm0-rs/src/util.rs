//! Utilities, mainly path manipulation with some newtype definitions.

use std::ops::{Deref, DerefMut, Add, AddAssign};
use std::borrow::Borrow;
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

/// Extension trait for `try_insert`.
pub trait HashMapExt<K, V> {
  /// Like `insert`, but if the insertion fails then it returns the value
  /// that it attempted to insert, as well as an `OccupiedEntry` containing
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

/// Newtype for an `Arc<String>`, so that we can implement `From<&str>`.
#[derive(Clone, Hash, PartialEq, Eq, DeepSizeOf)]
pub struct ArcString(pub Arc<Vec<u8>>);

impl Borrow<[u8]> for ArcString {
  fn borrow(&self) -> &[u8] { &*self.0 }
}
impl Deref for ArcString {
  type Target = [u8];
  fn deref(&self) -> &[u8] { &*self.0 }
}
impl ArcString {
  /// Constructs a new `ArcString`.
  pub fn new(s: Vec<u8>) -> ArcString { ArcString(Arc::new(s)) }
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
  fn from(s: &[u8]) -> ArcString { ArcString::new(s.to_owned()) }
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
  pub fn contains(&self, t: T) -> bool where T: PartialEq {
    let mut s = self;
    loop {
      match s.0 {
        None => return false,
        Some((_, t2)) if *t2 == t => return true,
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
  pub fn is_empty(&self) -> bool { self.0.is_none() }
  /// Append a new node on the end of the list.
  pub fn push(self, t: T) -> Self { Self(Some(Arc::new((self, t)))) }
  /// Check if the list contains an item.
  pub fn contains(&self, t: &T) -> bool where T: PartialEq {
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
  pub fn join(&self, t: T, tail: ArcList<T>) -> ArcList<T> where T: PartialEq + Clone {
    let (l, t2) = &**self.0.as_ref().unwrap();
    if *t2 == t { return tail.push(t) }
    l.join(t, tail).push(t2.clone())
  }
}

impl<'a, T> Iterator for &'a ArcList<T> {
  type Item = &'a T;
  fn next(&mut self) -> Option<&'a T> {
    let (l, t) = &**self.0.as_ref()?;
    *self = l;
    Some(t)
  }
}

/// A way to initialize a `Box<[T]>` by first constructing the array (giving the length),
/// initializing the elements in some order, and then using the unsafe function
/// [`assume_init`] to assert that every element of the array has been initialized and
/// transmute the `SliceUninit<T>` into a `Box<[T]>`.
///
/// [`assume_init`]: struct.SliceUninit.html#method.assume_init
#[derive(Debug)]
pub struct SliceUninit<T>(Box<[MaybeUninit<T>]>);

impl<T> SliceUninit<T> {
  /// Create a new uninitialized slice of length `size`.
  pub fn new(size: usize) -> Self {
    let mut res = Vec::with_capacity(size);
    // safety: the newly constructed elements have type MaybeUninit<T>
    // so it's fine to not initialize them
    unsafe { res.set_len(size) };
    SliceUninit(res.into_boxed_slice())
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
  pub unsafe fn assume_init(self) -> Box<[T]> { mem::transmute(self.0) }
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
  #[inline] fn from(r: std::ops::Range<usize>) -> Self { Span {start: r.start, end: r.end} }
}

impl From<usize> for Span {
  #[inline] fn from(n: usize) -> Self { Span {start: n, end: n} }
}

impl From<Span> for std::ops::Range<usize> {
  #[inline] fn from(s: Span) -> Self { s.start..s.end }
}

impl Add<usize> for Span {
  type Output = Self;
  fn add(self, i: usize) -> Self {
    Span {start: self.start + i, end: self.start + i}
  }
}

impl AddAssign<usize> for Span {
  fn add_assign(&mut self, i: usize) { *self = *self + i }
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

impl Iterator for Span {
  type Item = usize;
  fn next(&mut self) -> Option<usize> { self.deref_mut().next() }
}
impl DoubleEndedIterator for Span {
  fn next_back(&mut self) -> Option<usize> { self.deref_mut().next_back() }
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
    pub line: u64,
    /// Character offset on a line in a document (zero-based).
    pub character: u64,
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
  /// A PathBuf created by lazy_static! pointing to a canonicalized "."
  static ref CURRENT_DIR: PathBuf =
    std::fs::canonicalize(".").expect("failed to find current directory");
}

/// Given a PathBuf 'buf', constructs a relative path from [`CURRENT_DIR`]
/// to buf, returning it as a String.
///
/// Example : If CURRENT_DIR is /home/johndoe/mm0, and buf is
/// /home/johndoe/Documents/ahoy.mm1 will return "../Documents/ahoy.mm1"
///
/// [`CURRENT_DIR`]: struct.CURRENT_DIR.html
fn make_relative(buf: &PathBuf) -> String {
  pathdiff::diff_paths(buf, &*CURRENT_DIR).as_ref().unwrap_or(buf)
    .to_str().unwrap().to_owned()
}

#[derive(DeepSizeOf)]
struct FileRefInner {
  path: PathBuf,
  rel: String,
  #[cfg(feature = "server")]
  url: lsp_types::Url
}

/// A reference to a file. It wraps an `Arc` so it can be cloned thread-safely.
/// A `FileRef` can be constructed either from a `PathBuf` or a (`file://`) [`Url`],
/// and provides (precomputed) access to these views using `path()` and `url()`,
/// as well as `rel()` to get the relative path from CURRENT_DIR.
///
/// [`Url`]: ../lined_string/struct.Url.html
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
  /// Convert this `FileRef` to a `PathBuf`, for use with OS file actions.
  pub fn path(&self) -> &PathBuf { &self.0.path }
  /// Convert this `FileRef` to a relative path (as a `&str`).
  pub fn rel(&self) -> &str { &self.0.rel }
  /// Convert this `FileRef` to a `file:://` URL, for use with LSP.
  #[cfg(feature = "server")]
  pub fn url(&self) -> &lsp_types::Url { &self.0.url }
  /// Get a pointer to this allocation, for use in hashing.
  pub fn ptr(&self) -> *const PathBuf { self.path() }
  /// Compare this with `other` for pointer equality.
  pub fn ptr_eq(&self, other: &FileRef) -> bool { Arc::ptr_eq(&self.0, &other.0) }

  /// Returns true if this file has the provided extension.
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
    self.0.path.file_name().unwrap_or_else(|| self.0.path.as_os_str())
      .to_str().unwrap().fmt(f)
  }
}

impl fmt::Debug for FileRef {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    fmt::Display::fmt(self, f)
  }
}

/// A span paired with a [`FileRef`]
///
/// [`FileRef`]: struct.FileRef.html
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

/// Try to get memory usage (resident set size) in bytes using the `getrusage()` function from libc.
#[cfg(feature = "memory")]
pub(crate) fn get_memory_rusage() -> usize {
  let usage = unsafe {
    let mut usage = MaybeUninit::uninit();
    assert_eq!(libc::getrusage(libc::RUSAGE_SELF, usage.as_mut_ptr()), 0);
    usage.assume_init()
  };
  usage.ru_maxrss as usize * 1024
}

/// Try to get total memory usage (stack + data) in bytes using the `/proc` filesystem.
/// Falls back on `getrusage()` if procfs doesn't exist.
#[cfg(all(feature = "memory", target_os = "linux"))]
pub(crate) fn get_memory_usage() -> usize {
  procinfo::pid::statm_self().map_or_else(|_| get_memory_rusage(), |stat| stat.data * 4096)
}

/// Try to get total memory usage (stack + data) in bytes using the `/proc` filesystem.
/// Falls back on `getrusage()` if procfs doesn't exist.
#[cfg(all(feature = "memory", not(target_os = "linux")))]
pub(crate) fn get_memory_usage() -> usize {
  get_memory_rusage()
}

/// Try to get total memory usage (stack + data) in bytes using the `/proc` filesystem.
/// Falls back on `getrusage()` if procfs doesn't exist.
#[cfg(not(feature = "memory"))]
pub(crate) fn get_memory_usage() -> usize { 0 }