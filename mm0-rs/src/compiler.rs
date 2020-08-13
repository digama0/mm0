//! The standalone (command line) MM1 compiler interface.
//!
//! This is similar to [`mm0_rs::server`] but it reports diagnostics using Rust-style errors using
//! the [`annotate_snippets`] crate.
//!
//! Additionally, unlike the server, the MM1 compiler will go on and generate MMB or MMU proofs,
//! which can then be checked using an external MM0 checker such as [`mm0-c`].
//!
//! [`mm0_rs::server`]: ../server/index.html
//! [`annotate_snippets`]: ../../annotate_snippets/index.html
//! [`mm0-c`]: https://github.com/digama0/mm0/tree/master/mm0-c
use std::sync::{Arc, Mutex};
use std::collections::{HashMap, hash_map::Entry};
use std::{io, fs};
use futures::{FutureExt, future::BoxFuture};
use futures::channel::oneshot::{Sender as FSender, channel};
use futures::executor::{ThreadPool, block_on};
use futures::lock::Mutex as FMutex;
use lsp_types::{Position, Range};
use annotate_snippets::{
  snippet::{Snippet, Annotation, AnnotationType, SourceAnnotation, Slice},
  display_list::{DisplayList, FormatOptions}};
use typed_arena::Arena;
use clap::ArgMatches;
use crate::elab::{ElabError, ElabErrorKind, Environment, Elaborator};
use crate::parser::{parse, ParseError, ErrorLevel};
use crate::lined_string::LinedString;
use crate::mmu::import::elab as mmu_elab;
use crate::mmb::export::Exporter as MMBExporter;
use crate::util::{FileRef, FileSpan, Span};

lazy_static! {
  /// The thread pool (used for running MM1 files in parallel, when possible)
  static ref POOL: ThreadPool = ThreadPool::new().unwrap();
  /// The virtual file system of files that have been included via
  /// transitive imports, protected for concurrent access by a mutex.
  static ref VFS_: VFS = VFS(Mutex::new(HashMap::new()));
}

/// The cached [`Environment`] representing a completed parse, or an incomplete
/// parse.
///
/// [`Environment`]: ../elab/environment/struct.Environment.html
enum FileCache {
  /// This file is currently being worked on on another thread. The list
  /// contains tasks that are waiting to be sent the completed [`Environment`];
  /// A thread that sees that the file is in progress should construct a
  /// channel, store the [`Sender`] here, and return the [`Receiver`] to
  /// the elaborator (in the `mk` callback of [`Elaborator::as_fut`]).
  ///
  /// [`Environment`]: ../elab/environment/struct.Environment.html
  /// [`Sender`]: ../../futures_channel/oneshot/struct.Sender.html
  /// [`Receiver`]: ../../futures_channel/oneshot/struct.Receiver.html
  /// [`Elaborator::as_fut`]: ../elab/struct.Elaborator.html#method.as_fut
  InProgress(Vec<FSender<((), Arc<Environment>)>>),
  /// The file has been elaborated and the result is ready.
  Ready(Arc<Environment>),
}

/// A file that has been loaded from disk, along with the
/// parsed representation of the file (which may be in progress on another thread).
struct VirtualFile {
    /// The file's text as a [`LinedString`].
    ///
    /// [`LinedString`]: ../lined_string/struct.LinedString.html
    text: Arc<LinedString>,
    /// The file parse. This is protected behind a future-aware mutex,
    /// so that elaboration can block on accessing the result of another file's
    /// elaboration job to represent dependency relations. A result of `None`
    /// means that the file parse job has not yet been started.
    parsed: FMutex<Option<FileCache>>,
}

impl VirtualFile {
  /// Constructs a new `VirtualFile` from source text.
  fn new(text: String) -> VirtualFile {
    VirtualFile {
      text: Arc::new(text.into()),
      parsed: FMutex::new(None),
    }
  }
}

/// The virtual file system (a singleton accessed through the global variable [`VFS_`]).
///
/// [`VFS_`]: struct.VFS_.html
struct VFS(Mutex<HashMap<FileRef, Arc<VirtualFile>>>);

impl VFS {
  /// Get the file at `path`, returning the canonicalized `path` and the file record.
  ///
  /// **Note:** If the file has not yet been read, it will read the file from disk
  /// while still holding the [`VFS`] mutex, so other threads will not be able to
  /// perform file operations (although they will be able to elaborate otherwise).
  ///
  /// [`VFS`]: struct.VFS.html
  fn get_or_insert(&self, path: FileRef) -> io::Result<(FileRef, Arc<VirtualFile>)> {
    match self.0.lock().unwrap().entry(path) {
      Entry::Occupied(e) => Ok((e.key().clone(), e.get().clone())),
      Entry::Vacant(e) => {
        let path = e.key().clone();
        let s = fs::read_to_string(path.path())?;
        let val = e.insert(Arc::new(VirtualFile::new(s))).clone();
        Ok((path, val))
      }
    }
  }
}

impl ElabErrorKind {
  /// Convert the payload of an elaboration error to the footer data
  /// of a [`Snippet`].
  ///
  /// # Parameters
  ///
  /// - `arena`: A temporary [`typed_arena::Arena`] for storing `String`s that are
  ///   allocated for the snippet
  /// - `to_range`: a function for converting (index-based) spans to (line/col) ranges
  ///
  /// [`Snippet`]: ../../annotate_snippets/snippet/struct.Snippet.html
  /// [`typed_arena::Arena`]: ../../typed_arena/struct.Arena.html
  pub fn to_footer<'a>(&self, arena: &'a Arena<String>,
      mut to_range: impl FnMut(&FileSpan) -> Range) -> Vec<Annotation<'a>> {
    match self {
      ElabErrorKind::Boxed(_, Some(info)) =>
        info.iter().map(|(fs, e)| Annotation {
          id: None,
          label: {
            let start = to_range(fs).start;
            Some(arena.alloc(format!("{}:{}:{}: {}", fs.file.rel(),
              start.line + 1, start.character + 1, e)))
          },
          annotation_type: AnnotationType::Note,
        }).collect(),
      _ => vec![]
    }
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
///
/// [`Snippet`]: ../../annotate_snippets/snippet/struct.Snippet.html
/// [`ElabErrorKind::to_footer`]: ../elab/enum.ElabErrorKind.html#method.to_footer
fn make_snippet<'a>(path: &'a FileRef, file: &'a LinedString, pos: Span,
    msg: &'a str, level: ErrorLevel, footer: Vec<Annotation<'a>>) -> Snippet<'a> {
  let annotation_type = level.to_annotation_type();
  let Range {start, end} = file.to_range(pos);
  let start2 = pos.start - start.character as usize;
  let end2 = file.to_idx(Position {line: end.line + 1, character: 0})
    .unwrap_or_else(|| file.s.len());
  Snippet {
    title: Some(Annotation {
      id: None,
      label: Some(msg),
      annotation_type,
    }),
    slices: vec![Slice {
      source: &file[(start2..end2).into()],
      line_start: start.line as usize + 1,
      origin: Some(path.rel()),
      fold: end.line - start.line >= 5,
      annotations: vec![SourceAnnotation {
        range: (pos.start - start2, pos.end - start2),
        label: "",
        annotation_type,
      }],
    }],
    footer,
    opt: FormatOptions { color: true, anonymized_line_numbers: false }
  }
}

impl ElabError {
  /// Create a [`Snippet`] from this error.
  ///
  /// Because [`Snippet`] is a borrowed type, we "return" the snippet in CPS form,
  /// passing it to `f` which is used to produce an (unborrowed) value `T` that is returned.
  /// This idiom allows us to scope references to the snippet to the passed closure.
  ///
  /// # Parameters
  ///
  /// - `path`: The file that sourced the error
  /// - `file`: The file contents
  /// - `to_range`: a function for converting (index-based) spans to (line/col) ranges
  /// - `f`: The function to pass the constructed snippet
  ///
  /// [`Snippet`]: ../../annotate_snippets/snippet/struct.Snippet.html
  fn to_snippet<T>(&self, path: &FileRef, file: &LinedString,
      to_range: impl FnMut(&FileSpan) -> Range,
      f: impl for<'a> FnOnce(Snippet<'a>) -> T) -> T {
    f(make_snippet(path, file, self.pos, &self.kind.msg(), self.level,
      self.kind.to_footer(&Arena::new(), to_range)))
  }
}

impl ParseError {
  /// Create a [`Snippet`] from this error. See [`ElabError::to_snippet`] for information
  /// about the parameters.
  ///
  /// [`Snippet`]: ../../annotate_snippets/snippet/struct.Snippet.html
  /// [`ElabError::to_snippet`]: ../elab/struct.ElabError.html#method.to_snippet
  fn to_snippet<T>(&self, path: &FileRef, file: &LinedString,
    f: impl for<'a> FnOnce(Snippet<'a>) -> T) -> T {
    f(make_snippet(path, file, self.pos, &format!("{}", self.msg), self.level, vec![]))
  }
}

/// Elaborate a file for an `Environment` result.
///
/// This is the main elaboration function, as an `async fn`. Given a `path`,
/// it gets it from the [`VFS`] (which will probably load it from the filesystem),
/// and checks if it has already been elaborated, returning it if finished and
/// awaiting if it is in progress in another task.
///
/// If the file has not yet been elaborated, it parses it into an [`AST`], reports
/// parse errors, then elaborates it using [`Elaborator::as_fut`] and reports
/// elaboration errors. Finally, it broadcasts the completed file to all waiting
/// tasks, and returns it.
///
/// The callback passed to [`Elaborator::as_fut`], called on the imports in the file,
/// will allocate a new [`elaborate_and_send`] task to the task pool [`POOL`], which will
/// later be joined when the result is required. (**Note**: This can result in
/// deadlock if the import graph has a cycle.)
///
/// [`VFS`]: struct.VFS.html
/// [`AST`]: ../parser/ast/struct.AST.html
/// [`Elaborator::as_fut`]: ../elab/struct.Elaborator.html#method.as_fut
/// [`elaborate_and_send`]: fn.elaborate_and_send.html
async fn elaborate(path: FileRef) -> io::Result<Arc<Environment>> {
  let (path, file) = VFS_.get_or_insert(path)?;
  {
    let mut g = file.parsed.lock().await;
    match &mut *g {
      None => *g = Some(FileCache::InProgress(vec![])),
      Some(FileCache::InProgress(senders)) => {
        let (send, recv) = channel();
        senders.push(send);
        drop(g);
        return Ok(recv.await.unwrap().1)
      }
      Some(FileCache::Ready(env)) => return Ok(env.clone())
    }
  }
  let text = file.text.clone();
  let (errors, env) = if path.has_extension("mmb") {
    unimplemented!()
  } else if path.has_extension("mmu") {
    mmu_elab(path.clone(), &text)
  } else {
    let (_, ast) = parse(text, None);
    if !ast.errors.is_empty() {
      for e in &ast.errors {
        e.to_snippet(&path, &ast.source,
          |s| println!("{}", DisplayList::from(s).to_string()))
      }
    }
    let ast = Arc::new(ast);
    let mut deps = Vec::new();
    let elab = Elaborator::new(ast.clone(), path.clone(), path.has_extension("mm0"), Arc::default());
    let (_, errors, env) = elab.as_fut(None, |path| {
      let path = VFS_.get_or_insert(path)?.0;
      let (send, recv) = channel();
      POOL.spawn_ok(elaborate_and_send(path.clone(), send));
      deps.push(path);
      Ok(recv)
    }).await;
    (errors, env)
  };
  if !errors.is_empty() {
    let mut srcs = HashMap::new();
    let mut to_range = |fsp: &FileSpan| -> Range {
      if fsp.file.ptr_eq(&path) {
        &file.text
      } else {
        srcs.entry(fsp.file.ptr()).or_insert_with(||
          VFS_.0.lock().unwrap().get(&fsp.file).unwrap().text.clone())
      }.to_range(fsp.span)
    };
    for e in &errors {
      e.to_snippet(&path, &file.text, &mut to_range,
        |s| println!("{}\n", DisplayList::from(s).to_string()))
    }
  }
  let env = Arc::new(env);
  {
    let mut g = file.parsed.lock().await;
    if let Some(FileCache::InProgress(senders)) = g.take() {
      for s in senders {
        let _ = s.send(((), env.clone()));
      }
    }
    *g = Some(FileCache::Ready(env.clone()));
  }
  Ok(env)
}

/// Elaborate a file, and pass the `Environment` result to a [`Sender`].
///
/// See [`elaborate`] for details on elaboration. This function encapsulates
/// the `async fn` into a [`BoxFuture`], in order to avoid a recursion between
/// this function and [`elaborate`] resulting in infinite sized futures.
///
/// [`Sender`]: ../../futures_channel/oneshot/struct.Sender.html
/// [`elaborate`]: fn.elaborate.html
/// [`BoxFuture`]: ../../futures_core/future/type.BoxFuture.html
fn elaborate_and_send(path: FileRef, send: FSender<((), Arc<Environment>)>) ->
  BoxFuture<'static, ()> {
  async {
    if let Ok(env) = elaborate(path).await {
      let _ = send.send(((), env));
    }
  }.boxed()
}

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
pub fn main(args: &ArgMatches<'_>) -> io::Result<()> {
  let path = args.value_of("INPUT").unwrap();
  let (path, file) = VFS_.get_or_insert(fs::canonicalize(path)?.into())?;
  let env = block_on(elaborate(path.clone()))?;
  if let Some(out) = args.value_of("OUTPUT") {
    let bin = !out.ends_with(".mmu");
    use {fs::File, io::BufWriter};
    let mut w = BufWriter::new(File::create(out)?);
    if bin {
      let mut ex = MMBExporter::new(path, &file.text, &env, &mut w);
      ex.run(true)?;
      ex.finish()?;
    } else {
      env.export_mmu(&mut w)?;
    }
  }
  Ok(())
}