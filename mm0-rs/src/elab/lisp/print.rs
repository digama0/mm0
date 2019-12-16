use std::fmt;
use super::super::{AtomID, LinedString, FileServer, Environment, Elaborator};
use super::{LispKind, Proc, ProcPos};

#[derive(Copy, Clone)]
pub struct LispFormat<'a> {
  source: &'a LinedString,
  env: &'a Environment,
  e: &'a LispKind
}

impl<'a> LispFormat<'a> {
  fn to(&'a self, e: &'a LispKind) -> LispFormat<'a> {
    LispFormat {source: self.source, env: self.env, e}
  }
  fn atom(&self, a: AtomID) -> &str { &self.env.data[a].name }

  fn list(&self, mut start: bool, f: &mut fmt::Formatter) -> fmt::Result {
    match self.e {
      LispKind::List(es) => {
        for e in es {
          if start {
            write!(f, "({}", self.to(e))?;
            start = false
          } else {
            write!(f, " {}", self.to(e))?
          }
        }
        if start {write!(f, "()")} else {write!(f, ")")}
      }
      LispKind::DottedList(es, r) => {
        for e in es {
          if start {
            write!(f, "({}", self.to(e))?;
            start = false
          } else {
            write!(f, " {}", self.to(e))?
          }
        }
        self.to(r).list(start, f)
      }
      e => if start {write!(f, "{}", self.to(e))} else {write!(f, ". {})", self.to(e))}
    }
  }
}

fn alphanumber(n: usize) -> String {
  let mut out = String::with_capacity(2);
  let mut n = n + 1;
  while n != 0 {
    out.push((b'a' + ((n - 1) % 26) as u8) as char);
    n = (n - 1) / 26;
  }
  out
}

impl<'a> fmt::Display for LispFormat<'a> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self.e {
      &LispKind::Atom(a) => self.atom(a).fmt(f),
      LispKind::List(es) if es.is_empty() => "()".fmt(f),
      LispKind::DottedList(es, r) if es.is_empty() => self.to(r).fmt(f),
      LispKind::DottedList(_, _) |
      LispKind::List(_) => self.list(true, f),
      LispKind::Annot(_, e) => self.to(e).fmt(f),
      LispKind::Number(n) => n.fmt(f),
      LispKind::String(s) => write!(f, "{:?}", s),
      LispKind::UnparsedFormula(s) => write!(f, "${}$", s),
      LispKind::Bool(true) => "#t".fmt(f),
      LispKind::Bool(false) => "#f".fmt(f),
      LispKind::Syntax(s) => s.fmt(f),
      LispKind::Undef => write!(f, "#undef"),
      LispKind::Proc(Proc::Builtin(p)) => p.fmt(f),
      LispKind::Proc(Proc::Lambda {pos: ProcPos::Unnamed(pos), ..}) => {
        let r = self.source.to_pos(pos.span.start);
        let fname = pos.file.path().file_name().unwrap().to_str().unwrap();
        write!(f, "#[fn at {} {}:{}]", fname, r.line + 1, r.character + 1)
      }
      &LispKind::Proc(Proc::Lambda {pos: ProcPos::Named(ref pos, a), ..}) => {
        let r = self.source.to_pos(pos.span.start);
        let fname = pos.file.path().file_name().unwrap().to_str().unwrap();
        let x = &self.atom(a);
        write!(f, "#[fn {} at {} {}:{}]", x, fname, r.line + 1, r.character + 1)
      }
      LispKind::Proc(Proc::MatchCont(_)) => write!(f, "#[match cont]"),
      LispKind::AtomMap(m) => {
        write!(f, "(atom-map!")?;
        for (a, v) in m {write!(f, " [{} {}]", self.atom(*a), self.to(v))?}
        write!(f, ")")
      }
      LispKind::Ref(m) => self.to(&m.lock().unwrap()).fmt(f),
      &LispKind::MVar(n, _) => write!(f, "?{}", alphanumber(n)),
      LispKind::Goal(e) => write!(f, "(goal {})", self.to(e)),
    }
  }
}

impl<'a, T: FileServer + ?Sized> Elaborator<'a, T> {
  pub fn printer<'b>(&'b self, e: &'b LispKind) -> LispFormat<'b> {
    LispFormat {source: &self.ast.source, env: self, e}
  }
}