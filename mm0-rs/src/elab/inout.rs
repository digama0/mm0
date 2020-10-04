//! Support for the `input` and `output` commands.

use super::environment::{DeclKey, SortID, TermID, Type, Expr, ExprNode, StmtTrace};
use super::{ElabError, Elaborator, Span, HashMap, Result, SExpr,
  lisp::{InferTarget, LispVal}};

/// The elaboration data used by input/output commands. This caches precomputed
/// evaluations of `output string` commands.
#[derive(Default, Debug)]
pub struct InoutHandlers {
  string: Option<(Sorts, HashMap<TermID, InoutStringType>)>
}

#[derive(Debug)]
enum InoutStringType {
  S0,
  S1,
  SAdd,
  SCons,
  Ch,
  Hex(u8),
  #[allow(unused)]
  Str(Box<[u8]>),
  #[allow(unused)]
  Gen(usize, Box<[StringSeg]>),
}

#[derive(Clone, Debug, EnvDebug, PartialEq, Eq)]
enum StringSeg {
  Str(Box<[u8]>),
  Var(SortID, u32),
  Term(TermID, Box<[Box<[StringSeg]>]>),
  Hex(u8),
}

#[derive(Default, Debug)]
struct StringSegBuilder {
  built: Vec<StringSeg>,
  str: Vec<u8>,
  hex: Option<u8>,
}

impl StringSegBuilder {
  fn make(f: impl FnOnce(&mut StringSegBuilder) -> Result<()>) -> Result<Box<[StringSeg]>> {
    let mut out = StringSegBuilder::default();
    f(&mut out)?;
    out.flush();
    Ok(out.built.into_boxed_slice())
  }
  fn flush(&mut self) -> &mut Self {
    let s = std::mem::take(&mut self.str);
    if !s.is_empty() { self.built.push(StringSeg::Str(s.into())) }
    if let Some(h) = self.hex.take() {
      self.built.push(StringSeg::Hex(h))
    }
    self
  }

  fn push_hex(&mut self, hex: u8) -> &mut Self {
    match self.hex {
      None => self.hex = Some(hex),
      Some(hi) => self.str.push(hi << 4 | hex)
    }
    self
  }

  fn push_str(&mut self, s: &[u8]) -> &mut Self {
    self.str.extend_from_slice(s);
    self
  }

  fn push_seg(&mut self, seg: StringSeg) -> &mut Self {
    match seg {
      StringSeg::Str(s) => self.push_str(&s),
      StringSeg::Hex(h) => self.push_hex(h),
      _ => {self.flush().built.push(seg); self}
    }
  }
}

#[derive(Copy, Clone, Debug, EnvDebug)]
struct Sorts {
  str: SortID,
  hex: SortID,
  chr: SortID,
}

impl Elaborator {
  fn check_sort(&self, sp: Span, s: &str) -> Result<SortID> {
    self.atoms.get(s).and_then(|&a| self.data[a].sort)
      .ok_or_else(|| ElabError::new_e(sp, format!("sort '{}' not found", s)))
  }
  fn new_sorts(&self, sp: Span) -> Result<Sorts> {
    Ok(Sorts {
      str: self.check_sort(sp, "string")?,
      hex: self.check_sort(sp, "hex")?,
      chr: self.check_sort(sp, "char")?,
    })
  }

  fn check_term<'a>(&'a mut self, sp: Span, s: &str,
      args: &[SortID], ret: SortID, def: bool) -> Result<TermID> {
    let t = self.atoms.get(s)
      .and_then(|&a| if let Some(DeclKey::Term(t)) = self.data[a].decl {Some(t)} else {None})
      .ok_or_else(|| ElabError::new_e(sp, format!("term '{}' not found", s)))?;
    let td = &self.terms[t];
    match (def, &td.val) {
      (false, Some(_)) => return Err(ElabError::new_e(sp, format!("def '{}' should be a term", s)))?,
      (true, None) => return Err(ElabError::new_e(sp, format!("term '{}' should be a def", s)))?,
      _ => {}
    }
    let ok = td.ret == (ret, 0) &&
      td.args.len() == args.len() &&
      td.args.iter().zip(args).all(|(&(_, ty), &arg)| ty == Type::Reg(arg, 0));
    if !ok {
      use std::fmt::Write;
      let mut s = format!("term '{}' has incorrect type, expected: ", s);
      for &i in args {
        write!(s, "{} > ", self.data[self.sorts[i].atom].name).unwrap();
      }
      write!(s, "{}", self.data[self.sorts[ret].atom].name).unwrap();
      return Err(ElabError::new_e(sp, s))
    }
    Ok(t)
  }

  fn process_node<T>(&self, sp: Span, s: Sorts,
    terms: &HashMap<TermID, InoutStringType>,
    args: &[(T, Type)], e: &ExprNode,
    heap: &[Box<[StringSeg]>],
    out: &mut StringSegBuilder,
  ) -> Result<()> {
    match e {
      ExprNode::Dummy(_, _) => return Err(ElabError::new_e(sp, "dummy not permitted")),
      &ExprNode::Ref(i) => match i.checked_sub(args.len()) {
        None => {
          if let (_, Type::Reg(s, 0)) = args[i] {
            out.push_seg(StringSeg::Var(s, i as u32));
          } else {unreachable!()}
        }
        Some(j) => out.flush().built.extend_from_slice(&heap[j]),
      },
      &ExprNode::App(t, ref ns) => match terms.get(&t) {
        Some(InoutStringType::S0) => {}
        Some(InoutStringType::S1) =>
          self.process_node(sp, s, terms, args, &ns[0], heap, out)?,
        Some(InoutStringType::SAdd) |
        Some(InoutStringType::SCons) |
        Some(InoutStringType::Ch) => {
          self.process_node(sp, s, terms, args, &ns[0], heap, out)?;
          self.process_node(sp, s, terms, args, &ns[1], heap, out)?;
        }
        Some(&InoutStringType::Hex(h)) => {out.push_hex(h);}
        Some(InoutStringType::Str(s)) => {out.push_str(s);}
        _ => {
          let args = ns.iter().map(|n| StringSegBuilder::make(|arg|
              self.process_node(sp, s, terms, args, n, heap, arg)))
            .collect::<Result<Vec<_>>>()?.into_boxed_slice();
          out.push_seg(StringSeg::Term(t, args));
        }
      }
    }
    Ok(())
  }

  fn process_def(&self, sp: Span, s: Sorts,
      terms: &HashMap<TermID, InoutStringType>,
      t: TermID) -> Result<Box<[StringSeg]>> {
    let td = &self.terms[t];
    if let Some(Some(Expr {heap, head})) = &td.val {
      let mut refs = Vec::with_capacity(heap.len() - td.args.len());
      for e in &heap[td.args.len()..] {
        let res = StringSegBuilder::make(|out|
          self.process_node(sp, s, terms, &td.args, e, &refs, out))?;
        refs.push(res);
      }
      StringSegBuilder::make(|out|
        self.process_node(sp, s, terms, &td.args, head, &refs, out))
    } else {
      Err(ElabError::new_e(sp, format!("term '{}' should be a def", self.print(&t))))
    }
  }

  fn init_string_handler(&mut self, sp: Span) -> Result<()> {
    if self.inout.string.is_some() {return Ok(())}
    let s = self.new_sorts(sp)?;
    let mut map = HashMap::new();
    use InoutStringType::*;
    map.insert(self.check_term(sp, "s0", &[], s.str, false)?, S0);
    map.insert(self.check_term(sp, "s1", &[s.chr], s.str, false)?, S1);
    map.insert(self.check_term(sp, "sadd", &[s.str, s.str], s.str, false)?, SAdd);
    map.insert(self.check_term(sp, "ch", &[s.hex, s.hex], s.chr, false)?, Ch);
    for i in 0..16 {
      map.insert(self.check_term(sp, &format!("x{:x}", i), &[], s.hex, false)?, Hex(i));
    }
    if let Ok(t) = self.check_term(sp, "scons", &[s.chr, s.str], s.str, true) {
      if let Ok(ss) = self.process_def(sp, s, &map, t) {
        if &*ss == &[StringSeg::Var(s.chr, 0), StringSeg::Var(s.str, 1)] {
          map.insert(t, SCons);
        }
      }
    }
    self.inout.string = Some((s, map));
    Ok(())
  }

  fn get_string_handler(&mut self, sp: Span) -> Result<(Sorts, &mut HashMap<TermID, InoutStringType>)> {
    self.init_string_handler(sp)?;
    if let Some((s, map)) = &mut self.inout.string {Ok((*s, map))}
    else {unsafe {std::hint::unreachable_unchecked()}}
  }

  fn elab_output_string(&mut self, sp: Span, hs: &[SExpr]) -> Result<()> {
    let (sorts, _) = self.get_string_handler(sp)?;
    let mut args = Vec::with_capacity(hs.len());
    for f in hs {
      let e = self.eval_lisp(f)?;
      let val = self.elaborate_term(f.span, &e,
        InferTarget::Reg(self.sorts[sorts.str].atom))?;
      let s = self.infer_sort(sp, &val)?;
      if s != sorts.str {
        return Err(ElabError::new_e(sp, format!("type error: expected string, got {}",
          self.env.sorts[s].name)))
      }
      args.push(val);
    }
    let fsp = self.fspan(sp);
    self.stmts.push(StmtTrace::OutputString(LispVal::list(args).span(fsp)));
    Ok(())
  }

  /// Elaborate an `output` command. Note that in server mode, this does not actually run
  /// the operation of printing a string to standard out, as this would be disruptive.
  /// It is triggered only in "compile" mode, and by manual selection in server mode.
  pub fn elab_output(&mut self, sp: Span, kind: Span, hs: &[SExpr]) -> Result<()> {
    match self.span(kind) {
      "string" => self.elab_output_string(sp, hs),
      _ => return Err(ElabError::new_e(kind, "unsupported output kind")),
    }
  }

  /// Elaborate an `input` command. This is not implemented, as it needs to work with the
  /// final MM0 file, which is not available. More design work is needed.
  pub fn elab_input(&mut self, _: Span, kind: Span, _: &[SExpr]) -> Result<()> {
    match self.span(kind) {
      _ => return Err(ElabError::new_e(kind, "unsupported input kind")),
    }
  }
}