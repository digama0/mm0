//! Support for the `input` and `output` commands.

use std::io;
use super::proof::{Dedup, NodeHasher, ProofKind, build};
use super::environment::{DeclKey, SortId, TermId, Type, Expr, ExprNode,
  TermKind, OutputString, StmtTrace, Environment};
use super::{ElabError, Elaborator, Span, HashMap, Result as EResult, SExpr,
  lisp::{InferTarget, LispVal}, local_context::try_get_span, FrozenEnv};
use crate::util::{FileSpan, BoxError};

/// The elaboration data used by input/output commands. This caches precomputed
/// evaluations of `output string` commands.
#[derive(Default, Debug)]
pub struct InoutHandlers {
  string: Option<(Sorts, HashMap<TermId, InoutStringType>)>
}

#[derive(Debug)]
enum InoutStringType {
  S0,
  S1,
  SAdd,
  SCons,
  Ch,
  Hex(u8),
  // Str(Box<[u8]>),
  // Gen(usize, Box<[StringSeg]>),
}

#[derive(Clone, Debug, EnvDebug, PartialEq, Eq)]
enum StringSeg {
  Str(Box<[u8]>),
  Var(SortId, u32),
  Term(TermId, Box<[Box<[StringSeg]>]>),
  Hex(u8),
}

#[derive(Default, Debug)]
struct StringSegBuilder {
  built: Vec<StringSeg>,
  str: Vec<u8>,
  hex: Option<u8>,
}

impl StringSegBuilder {
  fn make<E>(f: impl FnOnce(&mut StringSegBuilder) -> Result<(), E>) -> Result<Box<[StringSeg]>, E> {
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

/// The error type returned by `run_output`.
#[derive(Debug)]
pub enum OutputError {
  /// The underlying writer throwed an IO error
  IoError(io::Error),
  /// There was a logical error preventing the output to be written
  String(String),
}

impl From<io::Error> for OutputError {
  fn from(e: io::Error) -> Self { Self::IoError(e) }
}
impl From<&str> for OutputError {
  fn from(e: &str) -> Self { Self::String(e.into()) }
}

impl From<OutputError> for BoxError {
  fn from(e: OutputError) -> BoxError {
    match e {
      OutputError::IoError(e) => e.into(),
      OutputError::String(s) => s.into(),
    }
  }
}

#[derive(Default)]
struct StringWriter<W> {
  w: W,
  hex: Option<u8>,
}

#[allow(variant_size_differences)]
enum StringPart {
  Hex(u8),
  Str(Vec<u8>)
}

impl<W: io::Write> StringWriter<W> {
  fn write_hex(&mut self, h: u8) -> Result<(), OutputError> {
    match self.hex.take() {
      None => self.hex = Some(h),
      Some(hi) => self.w.write_all(&[hi << 4 | h])?
    }
    Ok(())
  }
  fn write_str(&mut self, buf: &[u8]) -> Result<(), OutputError> {
    Ok(self.w.write_all(buf)?)
  }
  fn write_part(&mut self, s: &StringPart) -> Result<(), OutputError> {
    match s {
      &StringPart::Hex(h) => self.write_hex(h),
      StringPart::Str(s) => self.write_str(s),
    }
  }
}

impl From<StringWriter<Vec<u8>>> for StringPart {
  fn from(s: StringWriter<Vec<u8>>) -> Self {
    match s.hex {
      None => StringPart::Str(s.w),
      Some(h) => StringPart::Hex(h),
    }
  }
}

#[derive(Copy, Clone, Debug, EnvDebug)]
struct Sorts {
  str: SortId,
  hex: SortId,
  chr: SortId,
}

impl Environment {
  #[allow(clippy::unnecessary_lazy_evaluations)] // see rust-clippy#6343
  fn check_sort(&self, s: &str) -> Result<SortId, String> {
    self.atoms.get(s.as_bytes()).and_then(|&a| self.data[a].sort)
      .ok_or_else(|| format!("sort '{}' not found", s))
  }
  fn new_sorts(&self) -> Result<Sorts, String> {
    Ok(Sorts {
      str: self.check_sort("string")?,
      hex: self.check_sort("hex")?,
      chr: self.check_sort("char")?,
    })
  }

  fn check_term<'a>(&'a self, s: &str,
      args: &[SortId], ret: SortId, def: bool) -> Result<TermId, String> {
    let t = self.atoms.get(s.as_bytes())
      .and_then(|&a| if let Some(DeclKey::Term(t)) = self.data[a].decl {Some(t)} else {None})
      .ok_or_else(|| format!("term '{}' not found", s))?;
    let td = &self.terms[t];
    match (def, &td.kind) {
      (false, TermKind::Def(_)) => return Err(format!("def '{}' should be a term", s)),
      (true, TermKind::Term) => return Err(format!("term '{}' should be a def", s)),
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
      return Err(s)
    }
    Ok(t)
  }

  fn process_node<T>(&self,
    terms: &HashMap<TermId, InoutStringType>,
    args: &[(T, Type)], e: &ExprNode,
    heap: &[Box<[StringSeg]>],
    out: &mut StringSegBuilder,
  ) -> Result<(), String> {
    match e {
      ExprNode::Dummy(_, _) => return Err("dummy not permitted".into()),
      &ExprNode::Ref(i) => match i.checked_sub(args.len()) {
        None => {
          use std::convert::TryInto;
          if let (_, Type::Reg(s, 0)) = args[i] {
            out.push_seg(StringSeg::Var(s, i.try_into().expect("too many refs")));
          } else {unreachable!()}
        }
        Some(j) => out.flush().built.extend_from_slice(&heap[j]),
      },
      &ExprNode::App(t, ref ns) => match terms.get(&t) {
        Some(InoutStringType::S0) => {}
        Some(InoutStringType::S1) =>
          self.process_node(terms, args, &ns[0], heap, out)?,
        Some(InoutStringType::SAdd) |
        Some(InoutStringType::SCons) |
        Some(InoutStringType::Ch) => {
          self.process_node(terms, args, &ns[0], heap, out)?;
          self.process_node(terms, args, &ns[1], heap, out)?;
        }
        Some(&InoutStringType::Hex(h)) => {out.push_hex(h);}
        // Some(InoutStringType::Str(s)) => {out.push_str(s);}
        _ => {
          let args = ns.iter().map(|n| StringSegBuilder::make(|arg|
              self.process_node(terms, args, n, heap, arg)))
            .collect::<Result<Vec<_>, _>>()?.into_boxed_slice();
          out.push_seg(StringSeg::Term(t, args));
        }
      }
    }
    Ok(())
  }

  fn write_node<W: io::Write>(&self,
    terms: &HashMap<TermId, InoutStringType>,
    heap: &[StringPart],
    e: &ExprNode,
    w: &mut StringWriter<W>,
  ) -> Result<(), OutputError> {
    match e {
      ExprNode::Dummy(_, _) => Err("Found dummy variable in string definition".into()),
      &ExprNode::Ref(i) => w.write_part(&heap[i]),
      &ExprNode::App(t, ref ns) => match terms.get(&t) {
        Some(InoutStringType::S0) => Ok(()),
        Some(InoutStringType::S1) =>
          self.write_node(terms, heap, &ns[0], w),
        Some(InoutStringType::SAdd) |
        Some(InoutStringType::SCons) |
        Some(InoutStringType::Ch) => {
          self.write_node(terms, heap, &ns[0], w)?;
          self.write_node(terms, heap, &ns[1], w)
        }
        Some(&InoutStringType::Hex(h)) => w.write_hex(h),
        _ => if let TermKind::Def(Some(expr)) = &self.terms[t].kind {
          let mut args: Vec<StringPart> = Vec::with_capacity(heap.len());
          for e in &**ns {
            let mut w = StringWriter::default();
            self.write_node(terms, heap, e, &mut w)?;
            args.push(w.into());
          }
          for e in &expr.heap[ns.len()..] {
            let mut w = StringWriter::default();
            self.write_node(terms, &args, e, &mut w)?;
            args.push(w.into());
          }
          self.write_node(terms, &args, &expr.head, w)
        } else {
          Err("Unknown definition".into())
        }
      }
    }
  }

  fn write_output_string<W: io::Write>(&self,
    terms: &HashMap<TermId, InoutStringType>,
    w: &mut StringWriter<W>,
    heap: &[ExprNode], exprs: &[ExprNode]
  ) -> Result<(), OutputError> {
    let mut args = Vec::with_capacity(heap.len());
    for e in heap {
      let mut w = StringWriter::default();
      self.write_node(terms, &args, e, &mut w)?;
      args.push(w.into());
    }
    for e in exprs {
      self.write_node(terms, &args, e, w)?;
    }
    Ok(())
  }

  fn process_def(&self,
      terms: &HashMap<TermId, InoutStringType>,
      t: TermId, name: &str) -> Result<Box<[StringSeg]>, String> {
    let td = &self.terms[t];
    if let TermKind::Def(Some(Expr {heap, head})) = &td.kind {
      let mut refs = Vec::with_capacity(heap.len() - td.args.len());
      for e in &heap[td.args.len()..] {
        let out = StringSegBuilder::make(|out|
          self.process_node(terms, &td.args, e, &refs, out))?;
        refs.push(out);
      }
      StringSegBuilder::make(|out|
        self.process_node(terms, &td.args, head, &refs, out))
    } else {
      Err(format!("term '{}' should be a def", name))
    }
  }

  fn new_string_handler(&self) -> Result<(Sorts, HashMap<TermId, InoutStringType>), String> {
    use InoutStringType::{Ch, Hex, S0, S1, SAdd, SCons};
    let s = self.new_sorts()?;
    let mut map = HashMap::new();
    map.insert(self.check_term("s0", &[], s.str, false)?, S0);
    map.insert(self.check_term("s1", &[s.chr], s.str, false)?, S1);
    map.insert(self.check_term("sadd", &[s.str, s.str], s.str, false)?, SAdd);
    map.insert(self.check_term("ch", &[s.hex, s.hex], s.chr, false)?, Ch);
    for i in 0..16 {
      map.insert(self.check_term(&format!("x{:x}", i), &[], s.hex, false)?, Hex(i));
    }
    if let Ok(t) = self.check_term("scons", &[s.chr, s.str], s.str, true) {
      if let Ok(ss) = self.process_def(&map, t, "scons") {
        if *ss == [StringSeg::Var(s.chr, 0), StringSeg::Var(s.str, 1)] {
          map.insert(t, SCons);
        }
      }
    }
    Ok((s, map))
  }
}

impl Elaborator {
  fn get_string_handler(&mut self, sp: Span) -> EResult<(Sorts, &mut HashMap<TermId, InoutStringType>)> {
    if self.inout.string.is_none() {
      let (s, map) = self.env.new_string_handler().map_err(|e| ElabError::new_e(sp, e))?;
      self.inout.string = Some((s, map));
    }
    let_unchecked!(Some((s, map)) = &mut self.inout.string, Ok((*s, map)))
  }

  fn elab_output_string(&mut self, sp: Span, hs: &[SExpr]) -> EResult<()> {
    let (sorts, _) = self.get_string_handler(sp)?;
    let fsp = self.fspan(sp);
    let mut es = Vec::with_capacity(hs.len());
    for f in hs {
      let e = self.eval_lisp(f)?;
      let val = self.elaborate_term(f.span, &e,
        InferTarget::Reg(self.sorts[sorts.str].atom))?;
      let s = self.infer_sort(sp, &val)?;
      if s != sorts.str {
        return Err(ElabError::new_e(sp, format!("type error: expected string, got {}",
          self.env.sorts[s].name)))
      }
      es.push(val);
    }
    let nh = NodeHasher::new(&self.lc, self.format_env(), fsp.clone());
    let mut de = Dedup::new(&[]);
    let is = es.into_iter().map(|val| de.dedup(&nh, ProofKind::Expr, &val))
      .collect::<EResult<Vec<_>>>()?;
    let (mut ids, heap) = build(&de);
    let exprs = is.into_iter().map(|i| ids[i].take()).collect();
    self.stmts.push(StmtTrace::OutputString(
      Box::new(OutputString {span: fsp, heap, exprs})));
    Ok(())
  }

  /// Elaborate as if in an `output string` command, but from lisp. The input values
  /// are elaborated as type `string`, and the result is evaluated to produce a byte
  /// vector that is passed back to lisp code.
  pub fn eval_string(&mut self, fsp: &FileSpan, hs: &[LispVal]) -> EResult<Vec<u8>> {
    let (sorts, _) = self.get_string_handler(fsp.span)?;
    let mut es = Vec::with_capacity(hs.len());
    for e in hs {
      let sp = try_get_span(fsp, e);
      let val = self.elaborate_term(sp, e,
        InferTarget::Reg(self.sorts[sorts.str].atom))?;
      let s = self.infer_sort(sp, &val)?;
      if s != sorts.str {
        return Err(ElabError::new_e(sp, format!("type error: expected string, got {}",
          self.env.sorts[s].name)))
      }
      es.push(val);
    }
    let nh = NodeHasher::new(&self.lc, self.format_env(), fsp.clone());
    let mut de = Dedup::new(&[]);
    let is = es.into_iter().map(|val| de.dedup(&nh, ProofKind::Expr, &val))
      .collect::<EResult<Vec<_>>>()?;
    let (mut ids, heap) = build(&de);
    let exprs = is.into_iter().map(|i| ids[i].take()).collect::<Vec<_>>();
    let mut w = StringWriter::default();
    let terms = &self.inout.string.as_ref().expect("string handler should be initialized").1;
    self.env.write_output_string(terms, &mut w, &heap, &exprs).map_err(|e| match e {
      OutputError::IoError(e) => panic!("{}", e),
      OutputError::String(e) => ElabError::new_e(fsp.span, e),
    })?;
    Ok(w.w)
  }

  /// Elaborate an `output` command. Note that in server mode, this does not actually run
  /// the operation of printing a string to standard out, as this would be disruptive.
  /// It is triggered only in "compile" mode, and by manual selection in server mode.
  pub fn elab_output(&mut self, sp: Span, kind: Span, hs: &[SExpr]) -> EResult<()> {
    match self.span(kind) {
      b"string" => self.elab_output_string(sp, hs),
      _ => Err(ElabError::new_e(kind, "unsupported output kind")),
    }
  }

  /// Elaborate an `input` command. This is not implemented, as it needs to work with the
  /// final MM0 file, which is not available. More design work is needed.
  #[allow(clippy::unused_self)]
  pub fn elab_input(&mut self, _: Span, kind: Span, _: &[SExpr]) -> EResult<()> {
    Err(ElabError::new_e(kind, "unsupported input kind"))
  }
}

impl FrozenEnv {
  /// Run all the `output` directives in the environment,
  /// writing output to the provided writer.
  pub fn run_output(&self, w: impl io::Write) -> Result<(), (FileSpan, OutputError)> {
    let mut handler = None;
    let mut w = StringWriter {w, hex: None};
    let env = unsafe {self.thaw()};
    for s in self.stmts() {
      if let StmtTrace::OutputString(os) = s {
        let OutputString {span, heap, exprs} = &**os;
        (|| -> Result<(), OutputError> {
          let terms = {
            handler = Some(unsafe {self.thaw()}.new_string_handler()
              .map_err(OutputError::String)?);
            let_unchecked!(Some((_, t)) = &handler, t)
          };
        env.write_output_string(terms, &mut w, heap, exprs)
        })().map_err(|e| (span.clone(), e))?;
      }
    }
    Ok(())
  }
}