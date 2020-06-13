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
use crate::elab::{ElabError, ElabErrorKind, Environment, Elaborator};
use crate::parser::{parse, ParseError, ErrorLevel};
use crate::lined_string::LinedString;
use crate::mmu::import::elab as mmu_elab;
use crate::mmb::export::Exporter as MMBExporter;
use crate::util::{FileRef, FileSpan, Span};

lazy_static! {
  static ref POOL: ThreadPool = ThreadPool::new().unwrap();
  static ref VFS_: VFS = VFS(Mutex::new(HashMap::new()));
}

enum FileCache {
  InProgress(Vec<FSender<((), Arc<Environment>)>>),
  Ready(Arc<Environment>),
}

struct VirtualFile {
    text: Arc<LinedString>,
    /// File parse
    parsed: FMutex<Option<FileCache>>,
}

impl VirtualFile {
  fn new(text: String) -> VirtualFile {
    VirtualFile {
      text: Arc::new(text.into()),
      parsed: FMutex::new(None),
    }
  }
}

struct VFS(Mutex<HashMap<FileRef, Arc<VirtualFile>>>);

impl VFS {
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
  fn to_snippet<T>(&self, path: &FileRef, file: &LinedString,
      to_range: impl FnMut(&FileSpan) -> Range,
      f: impl for<'a> FnOnce(Snippet<'a>) -> T) -> T {
    f(make_snippet(path, file, self.pos, &self.kind.msg(), self.level,
      self.kind.to_footer(&Arena::new(), to_range)))
  }
}

impl ParseError {
  fn to_snippet<T>(&self, path: &FileRef, file: &LinedString,
    f: impl for<'a> FnOnce(Snippet<'a>) -> T) -> T {
    f(make_snippet(path, file, self.pos, &format!("{}", self.msg), self.level, vec![]))
  }
}

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
    let (_, errors, env) = elab.as_fut(None,
      |path| {
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
  let mut g = file.parsed.lock().await;
  if let Some(FileCache::InProgress(senders)) = g.take() {
    for s in senders {
      let _ = s.send(((), env.clone()));
    }
  }
  *g = Some(FileCache::Ready(env.clone()));
  drop(g);
  Ok(env)
}

fn elaborate_and_send(path: FileRef, send: FSender<((), Arc<Environment>)>) ->
  BoxFuture<'static, ()> {
  async {
    if let Ok(env) = elaborate(path).await {
      let _ = send.send(((), env));
    }
  }.boxed()
}

pub fn main(mut args: impl Iterator<Item=String>) -> io::Result<()> {
  let path = args.next().expect("expected a .mm1 file");
  let (path, file) = VFS_.get_or_insert(FileRef::new(fs::canonicalize(path)?))?;
  let env = block_on(elaborate(path.clone()))?;
  if let Some(out) = args.next() {
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