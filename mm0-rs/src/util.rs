use std::ops::{Deref, DerefMut, Range, Add, AddAssign};
use std::borrow::Borrow;
use std::mem::{self, MaybeUninit};
use std::fmt;
use std::error::Error;
use std::path::PathBuf;
use std::sync::Arc;
use std::hash::{Hash, Hasher, BuildHasher};
use std::collections::{HashMap, hash_map::{Entry, OccupiedEntry}};
use lsp_types::Url;

pub type BoxError = Box<dyn Error + Send + Sync>;

pub trait HashMapExt<K, V> {
  fn try_insert(&mut self, k: K, v: V) -> Option<(V, OccupiedEntry<K, V>)>;
}
impl<K: Hash + Eq, V, S: BuildHasher> HashMapExt<K, V> for HashMap<K, V, S> {
  fn try_insert(&mut self, k: K, v: V) -> Option<(V, OccupiedEntry<K, V>)> {
    match self.entry(k) {
      Entry::Vacant(e) => { e.insert(v); None }
      Entry::Occupied(e) => Some((v, e))
    }
  }
}

#[derive(Clone, Hash, PartialEq, Eq)] pub struct ArcString(pub Arc<String>);

impl Borrow<str> for ArcString {
  fn borrow(&self) -> &str { &*self.0 }
}
impl Deref for ArcString {
  type Target = str;
  fn deref(&self) -> &str { &*self.0 }
}
impl ArcString {
  pub fn new(s: String) -> ArcString { ArcString(Arc::new(s)) }
}
impl fmt::Display for ArcString {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self.0.fmt(f) }
}
impl fmt::Debug for ArcString {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self.0.fmt(f) }
}
impl From<&str> for ArcString {
  fn from(s: &str) -> ArcString { ArcString::new(s.to_owned()) }
}

pub struct VecUninit<T>(Vec<MaybeUninit<T>>);

impl<T> VecUninit<T> {
  pub fn new(size: usize) -> Self {
    let mut res = Vec::with_capacity(size);
    unsafe { res.set_len(size) };
    VecUninit(res)
  }

  pub fn set(&mut self, i: usize, val: T) {
    self.0[i] = MaybeUninit::new(val);
  }

  pub unsafe fn assume_init(self) -> Vec<T> {
    mem::transmute(self.0)
  }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Span {
  pub start: usize,
  pub end: usize,
}

impl From<Range<usize>> for Span {
  #[inline] fn from(r: Range<usize>) -> Self { Span {start: r.start, end: r.end} }
}

impl From<usize> for Span {
  #[inline] fn from(n: usize) -> Self { Span {start: n, end: n} }
}

impl From<Span> for Range<usize> {
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
  type Target = Range<usize>;
  fn deref(&self) -> &Range<usize> {
    unsafe { mem::transmute(self) }
  }
}

impl DerefMut for Span {
  fn deref_mut(&mut self) -> &mut Range<usize> {
    unsafe { mem::transmute(self) }
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
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}..{}", self.start, self.end)
  }
}

lazy_static! {
  static ref CURRENT_DIR: PathBuf =
    std::fs::canonicalize(".").expect("failed to find current directory");
}

fn make_relative(buf: &PathBuf) -> String {
  pathdiff::diff_paths(buf, &CURRENT_DIR).as_ref().unwrap_or(buf)
    .to_str().unwrap().to_owned()
}

#[derive(Clone)]
pub struct FileRef(Arc<(PathBuf, String, Url)>);
impl FileRef {
  pub fn new(buf: PathBuf) -> FileRef {
    let u = Url::from_file_path(&buf).expect("bad file path");
    let rel = make_relative(&buf);
    FileRef(Arc::new((buf, rel, u)))
  }
  pub fn from_url(url: Url) -> FileRef {
    let buf = url.to_file_path().expect("bad URL");
    let rel = make_relative(&buf);
    FileRef(Arc::new((buf, rel, url)))
  }
  pub fn path(&self) -> &PathBuf { &self.0 .0 }
  pub fn rel(&self) -> &str { &self.0 .1 }
  pub fn url(&self) -> &Url { &self.0 .2 }
  pub fn ptr(&self) -> *const PathBuf { self.path() }
  pub fn ptr_eq(&self, other: &FileRef) -> bool { Arc::ptr_eq(&self.0, &other.0) }

  pub fn has_extension(&self, ext: &str) -> bool {
    self.path().extension().map_or(false, |s| s == ext)
  }
}
impl PartialEq for FileRef {
  fn eq(&self, other: &Self) -> bool { self.0 == other.0 }
}
impl Eq for FileRef {}

impl Hash for FileRef {
  fn hash<H: Hasher>(&self, state: &mut H) { self.0.hash(state) }
}

impl fmt::Display for FileRef {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    self.0 .0.file_name().unwrap_or(self.0 .0.as_os_str()).to_str().unwrap().fmt(f)
  }
}

impl fmt::Debug for FileRef {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    fmt::Display::fmt(self, f)
  }
}

#[derive(Clone, PartialEq, Eq)]
pub struct FileSpan {
  pub file: FileRef,
  pub span: Span,
}

impl fmt::Debug for FileSpan {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}:{:?}", self.file, self.span)
  }
}
