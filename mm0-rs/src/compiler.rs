//! The standalone (command line) MM1 compiler interface.
//!
//! This is similar to [`mm0_rs::server`] but it reports diagnostics using Rust-style errors using
//! the [`annotate_snippets`] crate.
//!
//! Additionally, unlike the server, the MM1 compiler will go on and generate MMB or MMU proofs,
//! which can then be checked using an external MM0 checker such as [`mm0-c`].
//!
//! [`mm0_rs::server`]: crate::server
//! [`mm0-c`]: https://github.com/digama0/mm0/tree/master/mm0-c
use std::sync::{atomic::{AtomicBool, AtomicU8, Ordering}, Arc, LazyLock, Mutex};
use std::collections::{HashMap, hash_map::Entry};
use std::{io, fs, path::PathBuf};
use futures::{FutureExt, future::BoxFuture};
use futures::channel::oneshot::{Sender as FSender, channel};
use futures::executor::{ThreadPool, block_on};
use futures::lock::Mutex as FMutex;
use annotate_snippets::{Message, Snippet, Level, Renderer};
use typed_arena::Arena;
#[cfg(feature = "memory")] use mm0_deepsize_derive::DeepSizeOf;
use mm1_parser::{parse, ErrorLevel, ParseError};
use crate::elab::{ElabError, ElabErrorKind, ElabResult, ElaborateBuilder};
use crate::{ArcList, FileRef, FileSpan, FrozenEnv, LinedString, MutexExt, Position, Range, Span};
use crate::mmb::import::{elab as mmb_elab, read_deps};
use crate::mmu::import::elab as mmu_elab;
use crate::mmb::export::Exporter as MmbExporter;

/// The thread pool (used for running MM1 files in parallel, when possible)
static POOL: LazyLock<ThreadPool> = LazyLock::new(||
  ThreadPool::new().expect("could not start thread pool"));
/// The virtual file system of files that have been included via
/// transitive imports, protected for concurrent access by a mutex.
static VFS: LazyLock<Vfs> = LazyLock::new(|| Vfs(Mutex::new(HashMap::new())));

static QUIET: AtomicBool = AtomicBool::new(false);
static MAX_EMITTED_ERROR: AtomicU8 = AtomicU8::new(0);

/// The cached [`Environment`](crate::elab::environment::Environment) representing a
/// completed parse, or an incomplete parse.
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
enum FileCache {
  /// This file is currently being worked on on another thread. The list
  /// contains tasks that are waiting to be sent the completed [`Environment`];
  /// A thread that sees that the file is in progress should construct a
  /// channel, store the [`Sender`] here, and return the [`Receiver`] to
  /// the elaborator (in the [`recv_dep`](ElaborateBuilder::recv_dep) callback).
  ///
  /// [`Environment`]: crate::elab::environment::Environment
  /// [`Sender`]: FSender
  /// [`Receiver`]: futures::channel::oneshot::Receiver
  InProgress(Vec<FSender<ElabResult<()>>>),
  /// The file has been elaborated and the result is ready.
  Ready(FrozenEnv),
}

#[derive(Clone)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub(crate) enum FileContents {
  Ascii(Arc<LinedString>),
  #[cfg(not(target_arch = "wasm32"))]
  MMap(Arc<memmap::Mmap>),
  Bin(Arc<[u8]>),
}

impl FileContents {
  /// Constructs a new [`FileContents`] from source text.
  pub(crate) fn new(text: String) -> Self {
    Self::Ascii(Arc::new(text.into()))
  }

  /// Constructs a new [`FileContents`] from a memory map.
  #[cfg(not(target_arch = "wasm32"))]
  pub(crate) fn new_mmap(data: memmap::Mmap) -> Self {
    Self::MMap(Arc::new(data))
  }

  /// Constructs a new [`FileContents`] from a memory map.
  #[allow(unused)]
  pub(crate) fn new_bin(data: Box<[u8]>) -> Self {
    Self::Bin(data.into())
  }

  pub(crate) fn new_bin_from_file(path: &std::path::Path) -> io::Result<Self> {
    #[cfg(not(target_arch = "wasm32"))] {
      let file = fs::File::open(path)?;
      // Safety: Well, memory mapping files is never totally safe, but we're assuming
      // some reasonableness assumptions on the part of the user here.
      // If they delete the file from under us then interesting things will happen.
      // (I blame linux for not having a sensible locking model.)
      Ok(Self::new_mmap(unsafe { memmap::MmapOptions::new().map(&file)? }))
    }
    #[cfg(target_arch = "wasm32")] {
      Ok(Self::new_bin(fs::read(path)?.into_boxed_slice()))
    }
  }

  pub(crate) fn try_ascii(&self) -> Option<&Arc<LinedString>> {
    if let Self::Ascii(e) = self {Some(e)} else {None}
  }

  #[track_caller]
  pub(crate) fn ascii(&self) -> &Arc<LinedString> {
    self.try_ascii().expect("expected ASCII file")
  }

  #[allow(unused)]
  pub(crate) fn ptr_eq(&self, other: &Self) -> bool {
    match (self, other) {
      (Self::Ascii(e1), Self::Ascii(e2)) => Arc::ptr_eq(e1, e2),
      #[cfg(not(target_arch = "wasm32"))]
      (Self::MMap(e1), Self::MMap(e2)) => Arc::ptr_eq(e1, e2),
      (Self::Bin(e1), Self::Bin(e2)) => Arc::ptr_eq(e1, e2),
      _ => false
    }
  }
}

impl std::ops::Deref for FileContents {
  type Target = [u8];
  fn deref(&self) -> &[u8] {
    match self {
      Self::Ascii(e) => e.as_bytes(),
      #[cfg(not(target_arch = "wasm32"))]
      Self::MMap(e) => e,
      Self::Bin(e) => e
    }
  }
}

/// A file that has been loaded from disk, along with the
/// parsed representation of the file (which may be in progress on another thread).
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
struct VirtualFile {
    /// The file's text as a [`LinedString`].
    text: FileContents,
    /// The file parse. This is protected behind a future-aware mutex,
    /// so that elaboration can block on accessing the result of another file's
    /// elaboration job to represent dependency relations. A result of `None`
    /// means that the file parse job has not yet been started.
    parsed: FMutex<Option<FileCache>>,
}

impl VirtualFile {
  /// Constructs a new [`VirtualFile`] from source text.
  fn new(text: FileContents) -> VirtualFile {
    VirtualFile { text, parsed: FMutex::new(None) }
  }
}

/// The virtual file system (a singleton accessed through the global variable [`static@VFS`]).
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
struct Vfs(Mutex<HashMap<FileRef, Arc<VirtualFile>>>);

impl Vfs {
  /// Get the file at `path`, returning the canonicalized `path` and the file record.
  ///
  /// **Note:** If the file has not yet been read, it will read the file from disk
  /// while still holding the [`VFS`] mutex, so other threads will not be able to
  /// perform file operations (although they will be able to elaborate otherwise).
  fn get_or_insert(&self, path: FileRef) -> io::Result<(FileRef, Arc<VirtualFile>)> {
    let mut lock = self.0.ulock();
    let entry = lock.entry(path);
    match entry {
      Entry::Occupied(e) => Ok((e.key().clone(), e.get().clone())),
      Entry::Vacant(e) => {
        let path = e.key().clone();
        let fc = if path.has_extension("mmb") {
          FileContents::new_bin_from_file(path.path())?
        } else {
          FileContents::new(fs::read_to_string(path.path())?)
        };
        let val = e.insert(Arc::new(VirtualFile::new(fc))).clone();
        Ok((path, val))
      }
    }
  }
}

fn mk_to_range() -> impl FnMut(&FileSpan) -> Option<Range> {
  let mut srcs = HashMap::new();
  move |fsp: &FileSpan| -> Option<Range> {
    srcs.entry(fsp.file.ptr())
      .or_insert_with(|| VFS.0.ulock()[&fsp.file].text.clone())
      .try_ascii().map(|f| f.to_range(fsp.span))
  }
}

impl ElabErrorKind {
  /// Convert the payload of an elaboration error to the footer data
  /// of a [`Snippet`].
  ///
  /// # Parameters
  ///
  /// - `arena`: A temporary [`typed_arena::Arena`] for storing [`String`]s that are
  ///   allocated for the snippet
  /// - `to_range`: a function for converting (index-based) spans to (line/col) ranges
  pub fn to_footer<'a: 'b, 'b>(&'b self, arena: &'a Arena<String>,
    mut to_range: impl FnMut(&FileSpan) -> Option<Range> + 'b
  ) -> impl IntoIterator<Item = Message<'a>> + 'b {
    let info = match self {
      ElabErrorKind::Boxed(_, Some(info)) => &**info,
      _ => &[],
    };
    info.iter().map(move |(fs, e)| Level::Note.title(arena.alloc({
      if let Some(Range {start, ..}) = to_range(fs) {
        format!("{}:{}:{}: {e}", fs.file.rel(), start.line + 1, start.character + 1)
      } else {
        format!("{}:{:#x}: {e}", fs.file.rel(), fs.span.start)
      }
    })))
  }
}

/// Create a [`Snippet`] from a message.
///
/// # Parameters
///
/// - `path`: The file that sourced the error
/// - `file`: The file contents
/// - `pos`: The position of the error
/// - `msg`: The error message
/// - `level`: The error level
/// - `footer`: The snippet footer (calculated by [`ElabErrorKind::to_footer`])
/// - `to_range`: a function for converting (index-based) spans to (line/col) ranges
fn make_snippet<'a>(path: &'a FileRef, file: &'a LinedString, pos: Span,
    msg: &'a str, level: ErrorLevel, footer: impl IntoIterator<Item = Message<'a>>) -> Message<'a> {
  let annotation_type = level.to_annotation_type();
  let (start, start_line) = file.line_start(pos.start);
  let (_, end_line) = file.line_start(pos.end);
  #[allow(clippy::or_fun_call)]
  let end = file.to_idx(Position {
    line: u32::try_from(end_line).expect("too many lines") + 1,
    character: 0
  }).unwrap_or(file.len());
  // Safety: We assume `Span` is coming from the correct file.
  let source = unsafe { std::str::from_utf8_unchecked(&file[(start..end).into()]) };
  annotation_type.title(msg)
    .snippet(Snippet::source(source)
      .line_start(start_line + 1)
      .origin(path.rel())
      .fold(end_line - start_line >= 5)
      .annotation(annotation_type.span(pos.start - start..pos.end - start)))
    .footers(footer)
}

impl ElabError {
  /// Create a [`Message`] from this error.
  ///
  /// Because [`Message`] is a borrowed type, we "return" the snippet in CPS form,
  /// passing it to `f` which is used to produce an (unborrowed) value `T` that is returned.
  /// This idiom allows us to scope references to the snippet to the passed closure.
  ///
  /// # Parameters
  ///
  /// - `path`: The file that sourced the error
  /// - `file`: The file contents
  /// - `to_range`: a function for converting (index-based) spans to (line/col) ranges
  /// - `f`: The function to pass the constructed snippet
  fn to_snippet<T>(&self, path: &FileRef, file: &LinedString,
      to_range: impl FnMut(&FileSpan) -> Option<Range>,
      f: impl for<'a> FnOnce(Message<'a>) -> T) -> T {
    f(make_snippet(path, file, self.pos, &self.kind.msg(), self.level,
      self.kind.to_footer(&Arena::new(), to_range)))
  }

  /// Create a [`Message`] from an error when the file source is not available
  /// (e.g. for binary files).
  ///
  /// # Parameters
  ///
  /// - `path`: The location of the error
  /// - `f`: The function to pass the constructed snippet
  fn to_snippet_no_source<T>(&self, path: &FileRef, span: Span,
      f: impl for<'a> FnOnce(Message<'a>) -> T) -> T {
    let s = if span.end == span.start {
      format!("{path}:{:#x}: {}", span.start, self.kind.msg())
    } else {
      format!("{path}:{:#x}-{:#x}: {}", span.start, span.end, self.kind.msg())
    };
    f(self.level.to_annotation_type().title(&s))
  }
}

/// Create a [`Message`] from this error. See [`ElabError::to_snippet`] for information
/// about the parameters.
fn to_snippet<T>(err: &ParseError, path: &FileRef, file: &LinedString,
  f: impl for<'a> FnOnce(Message<'a>) -> T) -> T {
  f(make_snippet(path, file, err.pos, &format!("{}", err.msg), err.level, vec![]))
}

fn log_msg(#[allow(unused_mut)] mut s: String) {
  #[cfg(feature = "memory")]
  match crate::get_memory_usage() {
    0 => {}
    n => {
      use std::fmt::Write;
      write!(s, ", memory = {}M", n >> 20).expect("writing to a string");
    }
  }
  println!("{s}")
}

/// The sibling `.mmb` cache path for a source file.
fn cache_path(src: &FileRef) -> PathBuf { src.path().with_extension("mmb") }

/// The sibling `.mmb` of an imported `.mm1` to load in its place, if it is a usable and
/// up-to-date cache: it must carry a `Deps` table (so it was built by `--cache`) and be
/// at least as new as *every* source file that transitively went into it. Only `.mm1` is
/// cached — a `.mm0` shares its stem with a companion `.mm1` and would collide.
fn fresh_cache(src: &FileRef) -> Option<PathBuf> {
  if !src.has_extension("mm1") { return None }
  let mmb = cache_path(src);
  let mmb_time = fs::metadata(&mmb).ok()?.modified().ok()?;
  // Peek the recorded dependency closure (which includes `src` itself). No table means a
  // non-cache build, whose dependencies are unknown — treat it as unusable.
  let deps = read_deps(&mmb)?;
  let dir = mmb.parent();
  for rel in &deps {
    // Paths are relative to the `.mmb`'s directory; resolve them there to stat them.
    let dep = dir.map_or_else(|| rel.clone(), |d| d.join(rel));
    if fs::metadata(&dep).ok()?.modified().ok()? > mmb_time { return None }
  }
  Some(mmb)
}

/// The transitive source-file closure of `src`'s build, as absolute paths: `src` itself,
/// plus — for each direct import — that dependency's own recorded closure (read from its
/// `.mmb`). The exporter stores each relative to the output file's directory. Returns
/// `None` if a `.mm1` dependency has no readable `Deps` table, so `src` is left uncached
/// rather than recording an unsound (incomplete) closure.
fn dep_closure(src: &FileRef, imports: &[(Span, Vec<u8>)]) -> Option<Vec<PathBuf>> {
  let mut set = std::collections::BTreeSet::new();
  set.insert(src.path().clone());
  let parent = src.path().parent();
  for (_, f) in imports {
    let f = std::str::from_utf8(f).ok()?;
    let dep = parent.map_or_else(|| PathBuf::from(f), |p| p.join(f)).canonicalize().ok()?;
    let is_mm1 = dep.extension().is_some_and(|e| e.eq_ignore_ascii_case("mm1"));
    let dep_mmb = if is_mm1 { dep.with_extension("mmb") } else { dep.clone() };
    set.insert(dep.clone());
    match read_deps(&dep_mmb) {
      // A dependency records its closure relative to its own `.mmb`'s directory; resolve
      // those back to absolute for our (differently-based) closure.
      Some(sub) => {
        let dir = dep_mmb.parent();
        set.extend(sub.iter().map(|rel| dir.map_or_else(|| rel.clone(), |d| d.join(rel))));
      }
      // A `.mm1` dependency must carry its own closure; a directly imported `.mmb` leaf
      // (no table) contributes only itself, already inserted above.
      None if is_mm1 => return None,
      None => {}
    }
  }
  Some(set.into_iter().collect())
}

/// Write `env` to the sibling `.mmb` cache of the `.mm1` `src`, with the debug index (so
/// an importer recovers the whole environment, lisp globals included) and the `Deps`
/// table recording `deps`, the build's transitive source closure.
fn write_cache(src: &FileRef, source: Option<&LinedString>, env: &FrozenEnv, deps: Vec<PathBuf>)
  -> io::Result<()> {
  let mut report = |lvl: ErrorLevel, err: &str| {
    if !QUIET.load(Ordering::Relaxed) {
      println!("{}\n", Renderer::styled().render(lvl.to_annotation_type().title(err)));
    }
  };
  let w = io::BufWriter::new(fs::File::create(cache_path(src))?);
  let mut ex = MmbExporter::new(src.clone(), source, env, &mut report, w);
  ex.set_deps(deps);
  ex.run(true)?;
  ex.finish()
}

/// Elaborate a file for an [`Environment`](crate::elab::environment::Environment) result.
///
/// This is the main elaboration function, as an `async fn`. Given a `path`,
/// it gets it from the [`VFS`] (which will probably load it from the filesystem),
/// and checks if it has already been elaborated, returning it if finished and
/// awaiting if it is in progress in another task.
///
/// If the file has not yet been elaborated, it parses it into an [`Ast`], reports
/// parse errors, then elaborates it using [`ElaborateBuilder::elab`] and reports
/// elaboration errors. Finally, it broadcasts the completed file to all waiting
/// tasks, and returns it.
///
/// The [`recv_dep`](ElaborateBuilder::recv_dep) callback, called on the imports in the file,
/// will allocate a new [`elaborate_and_send`] task to the task pool [`static@POOL`],
/// which will later be joined when the result is required.
/// (**Note**: This can result in deadlock if the import graph has a cycle.)
///
/// [`Ast`]: mm1_parser::Ast
async fn elaborate(path: FileRef, rd: ArcList<FileRef>, cache: bool)
  -> io::Result<ElabResult<()>>
{
  // An imported `.mm1` (not the top-level file, which has an empty reader stack) with a
  // fresh sibling `.mmb` cache is loaded from that cache instead of being rebuilt.
  let path = if cache && !rd.is_empty() {
    fresh_cache(&path).map_or(path, FileRef::from)
  } else { path };
  let (path, file) = VFS.get_or_insert(path)?;
  {
    let mut g = file.parsed.lock().await;
    match &mut *g {
      None => *g = Some(FileCache::InProgress(vec![])),
      Some(FileCache::InProgress(senders)) => {
        let (send, recv) = channel();
        senders.push(send);
        drop(g);
        return Ok(recv.await.unwrap_or(ElabResult::Canceled))
      }
      Some(FileCache::Ready(env)) => return Ok(ElabResult::Ok((), None, env.clone()))
    }
  }
  let text = file.text.clone();
  let (cyc, errors, env) = if path.has_extension("mmb") {
    let (error, env) = mmb_elab(&path, &text);
    (None, if let Err(e) = error {vec![e]} else {vec![]}, FrozenEnv::new(env))
  } else if path.has_extension("mmu") {
    let (error, env) = mmu_elab(&path, &text);
    (None, if let Err(e) = error {vec![e]} else {vec![]}, FrozenEnv::new(env))
  } else {
    let (_, ast) = parse(text.ascii().clone(), None);
    if !ast.errors.is_empty() {
      let mut level = 0;
      let r = Renderer::styled();
      for e in &ast.errors {
        level = level.max(e.level as u8);
        to_snippet(e, &path, &ast.source, |s| println!("{}", r.render(s)))
      }
      MAX_EMITTED_ERROR.fetch_max(level, Ordering::Relaxed);
    }
    let ast = Arc::new(ast);
    if !QUIET.load(Ordering::Relaxed) { log_msg(format!("elab {path}")) }
    let rd = rd.push(path.clone());
    let fut =
      ElaborateBuilder {
        ast: &ast,
        path: path.clone(),
        mm0_mode: path.has_extension("mm0"),
        options: crate::get_options(),
        report_upstream_errors: false,
        cancel: Arc::default(),
        old: None,
        recv_dep: |p| {
          let p = VFS.get_or_insert(p)?.0;
          let (send, recv) = channel();
          if rd.contains(&p) {
            send.send(ElabResult::ImportCycle(rd.clone())).expect("failed to send");
          } else {
            POOL.spawn_ok(elaborate_and_send(p, send, rd.clone(), cache));
          }
          Ok(recv)
        },
        recv_goal: None,
      }.elab();
    let (cyc, _, errors, env) = fut.await;
    // Cache a clean build to a sibling `.mmb` (top-level or dependency). Skip files with
    // an error-level diagnostic: the environment may be incomplete (e.g. a def with no
    // value), which the exporter cannot write. A `sorry` is only a warning and exports
    // fine, so it is cached.
    if cache && cyc.is_none() && path.has_extension("mm1")
      && !errors.iter().any(|e| e.level == ErrorLevel::Error)
    {
      // A global the exporter cannot encode would be silently omitted, leaving a file
      // that is fine as a debugging index but unusable as a cache — a dependent loading
      // it would be missing definitions. Abort before building anything.
      let decline = |why: String| {
        if !QUIET.load(Ordering::Relaxed) { log_msg(format!("not caching {path}: {why}")) }
      };
      if let Some(name) = crate::mmb::lisp::export::first_unsupported(&env) {
        decline(format!("global '{name}' cannot be serialized"));
      } else if let Some(deps) = dep_closure(&path, &ast.imports) {
        // Every direct dependency's `.mmb` already exists here — the elaboration awaited
        // each one, and each wrote its cache first.
        if let Err(e) = write_cache(&path, file.text.try_ascii().map(|fc| &**fc), &env, deps) {
          decline(format!("cache write failed: {e}"));
        }
      } else {
        // The dependency closure can't be made sound: a `.mm1` dependency was itself not
        // cached, so it has no `Deps` table to union in.
        decline("a dependency was not cached".to_string());
      }
    }
    (cyc, errors, env)
  };
  if !QUIET.load(Ordering::Relaxed) { log_msg(format!("elabbed {path}")) }
  let errors: Option<Arc<[_]>> = if errors.is_empty() { None } else {
    fn print(s: Message<'_>) { println!("{}\n", Renderer::styled().render(s)) }
    let mut to_range = mk_to_range();
    let mut level = 0;
    if let FileContents::Ascii(text) = &file.text {
      for e in &errors {
        level = level.max(e.level as u8);
        e.to_snippet(&path, text, &mut to_range, print)
      }
    } else {
      for e in &errors {
        level = level.max(e.level as u8);
        e.to_snippet_no_source(&path, e.pos, print)
      }
    }
    MAX_EMITTED_ERROR.fetch_max(level, Ordering::Relaxed);
    Some(errors.into())
  };
  let res = match cyc {
    None => ElabResult::Ok((), errors, env.clone()),
    Some(cyc) => ElabResult::ImportCycle(cyc),
  };
  {
    let mut g = file.parsed.lock().await;
    if let Some(FileCache::InProgress(senders)) = g.take() {
      for s in senders {
        drop(s.send(res.clone()));
      }
    }
    *g = Some(FileCache::Ready(env));
  }
  Ok(res)
}

/// Elaborate a file, and pass the [`Environment`](crate::elab::environment::Environment)
/// result to a [`Sender`](FSender).
///
/// See [`elaborate`] for details on elaboration. This function encapsulates
/// the `async fn` into a [`BoxFuture`], in order to avoid a recursion between
/// this function and [`elaborate`] resulting in infinite sized futures.
fn elaborate_and_send(
  path: FileRef, send: FSender<ElabResult<()>>, rd: ArcList<FileRef>, cache: bool
) -> BoxFuture<'static, ()> {
  async move {
    if let Ok(env) = elaborate(path, rd, cache).await {
      drop(send.send(env));
    }
  }.boxed()
}

/// Elaborate a file, and return the completed [`FrozenEnv`] result, along with the
/// file contents.
pub(crate) fn elab_for_result(
  path: FileRef, cache: bool
) -> io::Result<(FileContents, Option<FrozenEnv>)> {
  let (path, file) = VFS.get_or_insert(path)?;
  let env = match block_on(elaborate(path, Default::default(), cache))? {
    ElabResult::Ok((), _, env) => Some(env),
    _ => None
  };
  Ok((file.text.clone(), env))
}

/// Compile MM1 files into MMB
#[allow(clippy::struct_excessive_bools)]
#[derive(clap::Args, Debug, Default)]
pub struct Args {
  /// Disable proof checking until (check-proofs #t)
  #[clap(short, long)]
  pub no_proofs: bool,
  /// Warn on unnecessary parentheses
  #[clap(long = "warn-unnecessary-parens")]
  pub check_parens: bool,
  /// Hide diagnostic messages
  #[clap(short, long)]
  pub quiet: bool,
  /// Don't add debugging data to .mmb files
  #[clap(short, long)]
  pub strip: bool,
  /// Cache each elaborated `.mm1` to a sibling `.mmb`
  #[clap(long, action = clap::ArgAction::Set, num_args = 0..=1, require_equals = true,
    default_value_t = false, default_missing_value = "true")]
  pub cache: bool,
  /// Report error code 1 for warnings
  #[clap(short = 'W', long)]
  pub warn_as_error: bool,
  /// Print 'output' commands to a file (use '-' to print to stdout)
  #[clap(short, long = "output", value_name = "FILE")]
  pub output_str: Option<std::ffi::OsString>,
  /// Sets the input file (.mm1 or .mm0)
  pub input: PathBuf,
  /// Sets the output file (.mmb or .mmu)
  pub output: Option<PathBuf>,
}

impl Args {
  /// Main entry point for `mm0-rs compile` subcommand.
  ///
  /// # Arguments
  ///
  /// `mm0-rs compile <in.mm1> [out.mmb]`, where:
  ///
  /// - `in.mm1` is the MM1 (or MM0) file to elaborate
  /// - `out.mmb` (or `out.mmu`) is the MMB file to generate, if the elaboration is
  ///   successful. The file extension is used to determine if we are outputting
  ///   binary. If this argument is omitted, the input is only elaborated.
  pub fn main(self) -> io::Result<()> {
    let path: FileRef = fs::canonicalize(self.input)?.into();
    QUIET.store(self.quiet, Ordering::Relaxed);
    let (file, env) = elab_for_result(path.clone(), self.cache)?;
    let env = env.unwrap_or_else(|| std::process::exit(1));
    if let Some(s) = self.output_str {
      if let Err((fsp, e)) =
        if s == "-" { env.run_output(io::stdout()) }
        else { env.run_output(fs::File::create(s)?) }
      {
        let e = ElabError::new_e(fsp.span, e);
        let file = VFS.get_or_insert(fsp.file.clone())?.1;
        e.to_snippet(&fsp.file, file.text.ascii(), &mut mk_to_range(),
          |s| println!("{}\n", Renderer::styled().render(s)));
        std::process::exit(1);
      }
    }
    if !self.quiet {
      println!("{} sorts, {} term/def, {} ax/thm",
        env.sorts().len(), env.terms().len(), env.thms().len());
    }
    if let Some(out) = self.output {
      use {fs::File, io::BufWriter};
      let w = BufWriter::new(File::create(&out)?);
      if out.extension().and_then(|s| s.to_str())
        .is_some_and(|ext| ext.eq_ignore_ascii_case("mmu"))
      {
        env.export_mmu(w)?;
      } else {
        let mut report = |lvl: ErrorLevel, err: &str| {
          println!("{}\n", Renderer::styled().render(lvl.to_annotation_type().title(err)));
          MAX_EMITTED_ERROR.fetch_max(lvl as u8, Ordering::Relaxed);
        };
        let mut ex = MmbExporter::new(path, file.try_ascii().map(|fc| &**fc), &env, &mut report, w);
        ex.run(!self.strip)?;
        ex.finish()?;
      }
    }
    let max_error = if self.warn_as_error { ErrorLevel::Warning } else { ErrorLevel::Error };
    #[allow(clippy::manual_assert)]
    if max_error as u8 <= MAX_EMITTED_ERROR.load(Ordering::Relaxed) {
      #[cfg(test)] panic!("errors emitted");
      #[cfg(not(test))] std::process::exit(1);
    }
    Ok(())
  }
}
