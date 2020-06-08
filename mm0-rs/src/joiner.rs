use std::collections::HashSet;
use std::fs;
use std::io::{self, Write};
use std::path::PathBuf;
use std::sync::Arc;
use crate::util::FileRef;
use crate::lined_string::LinedString;
use crate::parser::{parse, ast::StmtKind};

struct Joiner<W: Write> {
  stack: Vec<FileRef>,
  done: HashSet<FileRef>,
  w: W,
}

impl<W: Write> Joiner<W> {
  fn write(&mut self, path: FileRef) -> io::Result<()> {
    if let Some(i) = self.stack.iter().rposition(|x| x == &path) {
      self.stack.push(path);
      panic!("import cycle: {:?}", &self.stack[i..])
    }
    self.stack.push(path.clone());
    let src = Arc::<LinedString>::new(fs::read_to_string(path.path())?.into());
    let (_, ast) = parse(src.clone(), None);
    let mut start = 0;
    for s in &ast.stmts {
      if let StmtKind::Import(_, f) = &s.k {
        let r = FileRef::new(path.path().parent()
          .map_or_else(|| PathBuf::from(f), |p| p.join(f))
          .canonicalize()?);
        self.w.write_all(&src.as_bytes()[start..s.span.start])?;
        if self.done.insert(r.clone()) {
          self.write(r)?;
          self.w.write(&[b'\n'])?;
        }
        start = s.span.end;
      }
    }
    write!(self.w, "{}\n-- {} --\n{0}\n",
      // Safety: '-' is utf8
      unsafe { String::from_utf8_unchecked(vec![b'-'; path.rel().len() + 6]) },
      path.rel())?;
    self.w.write_all(&src.as_bytes()[start..])?;
    self.stack.pop();
    Ok(())
  }
}

pub fn main(mut args: impl Iterator<Item=String>) -> io::Result<()> {
  let path = args.next().expect("expected a .mm0 file");
  Joiner {
    stack: vec![],
    done: HashSet::new(),
    w: io::stdout(),
  }.write(FileRef::new(fs::canonicalize(path)?))
}