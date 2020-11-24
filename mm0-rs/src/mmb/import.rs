//! Importer for MMB files into the [`Environment`].

use std::convert::{TryFrom, TryInto};
use std::fs::File;
use std::rc::Rc;
use crate::elab::{
  environment::{Environment, Modifiers, AtomID, SortID, TermID, ThmID,
    Type, Term, Thm, TermKind, ThmKind, ExprNode, Expr, ProofNode, Proof},
  proof::{IDedup, NodeHash, ExprHash, ProofHash, build}};
use crate::util::{FileRef, FileSpan, SliceExt};
use super::{StmtCmd, UnifyCmd, ProofCmd,
  parser::{MMBFile, Buffer, ParseError, UnifyIter, ProofIter}};


type Result<T> = std::result::Result<T, ParseError>;

fn parse_unify(
  file: &MMBFile<'_>, nargs: usize, it: UnifyIter<'_>,
  hyps: Option<&mut Vec<(Option<AtomID>, ExprNode)>>,
  dummy: impl FnMut() -> AtomID,
) -> Result<(Box<[ExprNode]>, ExprNode)> {
  use ParseError::StrError;
  struct State<'a, F> {
    dummy: F,
    file: &'a MMBFile<'a>,
    pos: usize,
    it: UnifyIter<'a>,
    heap: Vec<ExprNode>,
    fwd: Vec<Option<usize>>,
  }
  impl<F: FnMut() -> AtomID> State<'_, F> {
    fn go(&mut self) -> Result<ExprNode> {
      let r = match self.it.next().unwrap_or(Err(self.pos)).map_err(|p| StrError("bad unify expr", p))? {
        UnifyCmd::Term {tid, save} => {
          let n = self.fwd.len();
          if save {self.fwd.push(None)}
          let r = ExprNode::App(tid,
            self.file.term(tid).ok_or(StrError("unknown term", self.pos))?
              .args().iter().map(|_| self.go()).collect::<Result<Vec<_>>>()?
              .into_boxed_slice());
          if save {
            let h = self.heap.len();
            self.fwd[n] = Some(h);
            self.heap.push(r);
            ExprNode::Ref(h)
          } else {
            r
          }
        }
        UnifyCmd::Ref(i) => ExprNode::Ref(
          self.fwd.get(usize::try_from(i).expect("impossible"))
            .ok_or(StrError("reference out of range", self.pos))?
            .ok_or(StrError("cyclic reference", self.pos))?),
        UnifyCmd::Dummy(s) => {
          let h = self.heap.len();
          self.fwd.push(Some(h));
          self.heap.push(ExprNode::Dummy((self.dummy)(), s));
          ExprNode::Ref(h)
        }
        UnifyCmd::Hyp => return Err(StrError("bad unify expr", self.pos))
      };
      self.pos = self.it.pos;
      Ok(r)
    }
  }
  let mut st = State {
    dummy, file, pos: it.pos, it,
    heap: (0..nargs).map(ExprNode::Ref).collect::<Vec<_>>(),
    fwd: (0..nargs).map(Some).collect::<Vec<_>>()
  };
  let ret = st.go()?;
  if let Some(hyps) = hyps {
    while let Some(e) = st.it.next() {
      match e {
        Err(p) => return Err(StrError("bad unify expr", p)),
        Ok(UnifyCmd::Hyp) => {st.pos = st.it.pos; hyps.push((None, st.go()?))}
        Ok(_) => return Err(StrError("unify stack underflow", st.pos))
      }
    }
    hyps.reverse()
  }
  if st.it.next().is_some() {
    return Err(StrError("unify stack underflow", st.pos))
  }
  Ok((st.heap.into_boxed_slice(), ret))
}

#[derive(Debug)]
struct Dedup(Vec<(ProofHash, bool)>);

impl Dedup {
  fn new(nargs: usize) -> Dedup {
    Self((0..nargs).map(|i| (ProofHash::Ref(i), true)).collect())
  }

  fn push(&mut self, v: ProofHash) -> usize {
    (self.0.len(), self.0.push((v, false))).0
  }
}

impl std::ops::Index<usize> for Dedup {
  type Output = ProofHash;
  fn index(&self, n: usize) -> &ProofHash { &self.0[n].0 }
}

impl IDedup<ProofHash> for Dedup {
  fn add_direct(&mut self, v: ProofHash) -> usize { self.push(v) }

  fn reuse(&mut self, n: usize) -> usize {
    self.0[n].1 = true;
    n
  }
}

#[derive(Debug)]
struct DedupIter<'a>(std::slice::Iter<'a, (ProofHash, bool)>);

impl<'a> Iterator for DedupIter<'a> {
  type Item = (&'a ProofHash, bool);
  fn next(&mut self) -> Option<(&'a ProofHash, bool)> {
    self.0.next().map(|&(ref e, b)| (e, b))
  }
}

impl<'a> ExactSizeIterator for DedupIter<'a> {
  fn len(&self) -> usize { self.0.len() }
}

impl<'a> IntoIterator for &'a Dedup {
  type Item = (&'a ProofHash, bool);
  type IntoIter = DedupIter<'a>;
  fn into_iter(self) -> DedupIter<'a> { DedupIter(self.0.iter()) }
}

fn parse_proof(
  file: &MMBFile<'_>, nargs: usize, it: &mut ProofIter<'_>,
  mut dummy: impl FnMut() -> AtomID,
) -> Result<Proof> {

  use ParseError::StrError;
  type Idx = usize; // Owned index
  type Ref = usize; // Reference. Does not count toward sharing

  #[derive(Clone, Debug)]
  enum Stack {
    Expr(Idx), // e
    Proof(Idx, Ref), // p: |- e (p is owned, e is not)
    Conv(Idx, Ref, Ref), // c: e1 = e2 (e1, e2 not owned)
    CoConv(Box<CoConv>, Ref, Ref), // c: e1 =?= e2 (e1, e2 not owned)
  }
  type StackRef = Stack; // same as Stack but with Ref instead of Idx

  #[derive(Clone, Debug)]
  enum CoConv {
    Conv {tgt: Idx, pf: Idx}, // (:conv tgt _ pf) - pf: |- src, ?c: tgt = src
    Sym(Box<CoConv>),
    Cong(Box<CoConv>, TermID, std::vec::IntoIter<(Ref, Ref)>, Vec<Idx>),
    Unfold(Box<CoConv>, TermID, Box<[Idx]>, Idx, Idx),
    Cut(Box<CoConv>, Ref, Ref)
  }

  #[allow(clippy::wrong_self_convention)]
  impl Stack {
    fn as_expr(self, pos: usize) -> Result<Idx> {
      if let Stack::Expr(pr) = self {return Ok(pr)}
      Err(StrError("type mismatch", pos))
    }
    fn as_proof(self, pos: usize) -> Result<(Idx, Ref)> {
      if let Stack::Proof(pr, e) = self {return Ok((pr, e))}
      Err(StrError("type mismatch", pos))
    }
    fn as_conv(self, pos: usize) -> Result<(Idx, Ref, Ref)> {
      if let Stack::Conv(c, e1, e2) = self {return Ok((c, e1, e2))}
      Err(StrError("type mismatch", pos))
    }
    fn as_coconv(self, pos: usize) -> Result<(Box<CoConv>, Ref, Ref)> {
      if let Stack::CoConv(c, e1, e2) = self {return Ok((c, e1, e2))}
      Err(StrError("type mismatch", pos))
    }
    fn reuse(&self, de: &mut Dedup) -> Self {
      match *self {
        Stack::Expr(e) => de.reuse(e),
        Stack::Proof(p, _) => de.reuse(p),
        Stack::Conv(c, _, _) => de.reuse(c),
        Stack::CoConv(_, _, _) => unreachable!("co-conv should not be saved"),
      };
      self.clone()
    }
  }

  fn as_term(e: &ProofHash, pos: usize) -> Result<(TermID, &[Ref])> {
    if let ProofHash::Term(t, args) = e {
      Ok((*t, args))
    } else {
      Err(StrError("expected a term", pos))
    }
  }

  struct State<'a, F> {
    file: &'a MMBFile<'a>,
    dummy: F,
    de: Dedup,
    stack: Vec<Stack>,
    hyps: Vec<Ref>,
    heap: Vec<StackRef>,
  }

  impl<F: FnMut() -> AtomID> State<'_, F> {
    fn apply_cong(&mut self, co: Box<CoConv>,
      t: TermID, mut it: std::vec::IntoIter<(Ref, Ref)>, args: Vec<Idx>
    ) -> Result<()> {
      if let Some((e1, e2)) = it.next() {
        self.stack.push(Stack::CoConv(Box::new(CoConv::Cong(co, t, it, args)), e1, e2));
        Ok(())
      } else {
        let r = self.de.push(ProofHash::Cong(t, Rc::from(args)));
        self.apply_coconv(co, r)
      }
    }

    #[allow(clippy::boxed_local)]
    fn apply_coconv(&mut self, co: Box<CoConv>, c: Idx) -> Result<()> {
      match *co {
        CoConv::Conv {tgt, pf} =>
          self.stack.push(Stack::Proof(self.de.push(ProofHash::Conv(tgt, c, pf)), tgt)),
        CoConv::Sym(co) => {
          let r = self.de.push(ProofHash::Sym(c));
          self.apply_coconv(co, r)?
        }
        CoConv::Cong(co, t, it, mut args) => {
          args.push(c);
          self.apply_cong(co, t, it, args)?;
        }
        CoConv::Unfold(co, t, args, lhs, sub_lhs) => {
          let r = self.de.push(ProofHash::Unfold(t, args, lhs, sub_lhs, c));
          self.apply_coconv(co, r)?
        }
        CoConv::Cut(co, e1, e2) => {
          self.apply_coconv(co, c)?;
          self.stack.push(Stack::Conv(c, e1, e2));
        }
      }
      Ok(())
    }

    fn pop(&mut self, pos: usize) -> Result<Stack> {
      self.stack.pop().ok_or(StrError("stack underflow", pos))
    }
    fn popn_mid(&mut self, n: usize, pos: usize) -> Result<usize> {
      self.stack.len().checked_sub(n).ok_or(StrError("stack underflow", pos))
    }
    fn popn<T>(&mut self, n: usize, pos: usize,
      f: impl FnMut(Stack) -> Result<T>
    ) -> Result<Vec<T>> {
      let mid = self.popn_mid(n, pos)?;
      self.stack.drain(mid..).map(f).collect()
    }

    fn apply_cmd(&mut self, cmd: ProofCmd, pos: usize) -> Result<()> {
      match cmd {
        ProofCmd::Term {tid, save} => {
          let nargs = self.file.term(tid).ok_or(StrError("unknown term", pos))?.args().len();
          let args = self.popn(nargs, pos, |e| e.as_expr(pos))?.into_boxed_slice();
          let r = self.de.push(ProofHash::Term(tid, args));
          if save { self.heap.push(StackRef::Expr(r)) }
          self.stack.push(Stack::Expr(r))
        }
        ProofCmd::Ref(i) => self.stack.push(
          self.heap.get(usize::try_from(i).expect("impossible"))
            .ok_or(StrError("reference out of range", pos))?.reuse(&mut self.de)),
        ProofCmd::Dummy(s) => {
          let h = self.heap.len();
          let r = self.de.push(ProofHash::Dummy((self.dummy)(), s));
          self.heap.push(StackRef::Expr(r));
          self.stack.push(Stack::Expr(r))
        }
        ProofCmd::Hyp => {
          let e = self.pop(pos)?.as_expr(pos)?;
          let h = self.de.push(ProofHash::Hyp(self.hyps.len(), e));
          self.hyps.push(h);
          self.heap.push(StackRef::Proof(h, e))
        }
        ProofCmd::Thm {tid, save} => {
          let tgt = self.pop(pos)?.as_expr(pos)?;
          let td = self.file.thm(tid).ok_or(StrError("unknown theorem", pos))?;
          let nargs = td.args().len();
          let mut args: Vec<Idx> = self.popn(nargs, pos, |e| e.as_expr(pos))?;
          let nhyps = td.unify().filter(|e| matches!(e, Ok(UnifyCmd::Hyp))).count();
          let mid = self.popn_mid(nhyps, pos)?;
          for e in self.stack.drain(mid..) { args.push(e.as_proof(pos)?.0); }
          let r = self.de.push(ProofHash::Thm(tid, args.into_boxed_slice(), tgt));
          if save { self.heap.push(StackRef::Proof(r, tgt)) }
          self.stack.push(Stack::Proof(r, tgt))
        }
        ProofCmd::Conv => {
          let (pf, src) = self.pop(pos)?.as_proof(pos)?;
          let tgt = self.pop(pos)?.as_expr(pos)?;
          self.stack.push(Stack::CoConv(Box::new(CoConv::Conv {tgt, pf}), tgt, src));
        }
        ProofCmd::Refl => {
          let (co, e1, e2) = self.pop(pos)?.as_coconv(pos)?;
          if e1 != e2 {return Err(StrError("Refl mismatch", pos))}
          let r = self.de.push(ProofHash::Refl(e1));
          self.apply_coconv(co, r)?;
        }
        ProofCmd::Sym => {
          let (co, e1, e2) = self.pop(pos)?.as_coconv(pos)?;
          self.stack.push(Stack::CoConv(Box::new(CoConv::Sym(co)), e2, e1))
        }
        ProofCmd::Cong => {
          let (co, e1, e2) = self.pop(pos)?.as_coconv(pos)?;
          let (t1, args1) = as_term(&self.de[e1], pos)?;
          let (t2, args2) = as_term(&self.de[e2], pos)?;
          if t1 != t2 {return Err(StrError("Cong mismatch", pos))}
          let it = args1.iter().copied().zip(args2.iter().copied()).collect::<Vec<_>>().into_iter();
          let args = Vec::with_capacity(args1.len());
          self.apply_cong(co, t1, it, args)?;
        }
        ProofCmd::Unfold => {
          let sub_lhs = self.pop(pos)?.as_expr(pos)?;
          let lhs = self.pop(pos)?.as_expr(pos)?;
          let (t, args) = as_term(&self.de[lhs], pos)?;
          let args = args.cloned_box();
          for &e in &*args {self.de.reuse(e);}
          let (co, lhs_, rhs) = self.pop(pos)?.as_coconv(pos)?;
          if lhs != lhs_ {return Err(StrError("Unfold mismatch", pos))}
          let td = self.file.term(t).ok_or(StrError("Expected a term", pos))?;
          self.stack.push(Stack::CoConv(
            Box::new(CoConv::Unfold(co, t, args, lhs, sub_lhs)), sub_lhs, rhs));
        }
        ProofCmd::ConvCut => {
          let (co, e1, e2) = self.pop(pos)?.as_coconv(pos)?;
          self.stack.push(Stack::CoConv(Box::new(CoConv::Cut(co, e1, e2)), e1, e2));
        }
        ProofCmd::ConvRef(i) => {
          let (c, e1, e2) = self.heap.get(usize::try_from(i).expect("impossible"))
            .ok_or(StrError("reference out of range", pos))?.reuse(&mut self.de).as_conv(pos)?;
          let (co, e1_, e2_) = self.pop(pos)?.as_coconv(pos)?;
          if e1 != e1_ || e2 != e2_ {return Err(StrError("ConvRef mismatch", pos))}
          self.apply_coconv(co, c)?;
        }
        ProofCmd::ConvSave => {
          let (c, e1, e2) = self.pop(pos)?.as_conv(pos)?;
          self.heap.push(StackRef::Conv(c, e1, e2));
        }
        ProofCmd::Save => match self.stack.last().ok_or(StrError("stack underflow", pos))? {
          Stack::CoConv(_, _, _) => return Err(StrError("Can't save co-conv", pos)),
          s => self.heap.push(s.clone()),
        }
      }
      Ok(())
    }
  }

  let mut st = State {
    file, dummy,
    de: Dedup::new(nargs),
    stack: vec![],
    heap: (0..nargs).map(StackRef::Expr).collect(),
    hyps: vec![],
  };
  let mut pos = it.pos;
  while let Some(e) = it.next() {
    st.apply_cmd(e.map_err(|p| StrError("bad unify expr", p))?, pos)?;
    pos = it.pos;
  }
  let ret = if let [e] = &*st.stack {e.clone()} else {
    return Err(StrError("stack should have one element", pos))
  }.as_proof(pos)?.0;
  let (ids, heap) = build::<ProofNode, _>(&st.de);
  let (mut ids, heap) = build(&st.de);
  let hyps = st.hyps.into_iter().map(|i| ids[i].take()).collect();
  Ok(Proof {heap, hyps, head: ids[ret].take()})
}

fn parse(fref: &FileRef, buf: &[u8], env: &mut Environment) -> Result<()> {
  use ParseError::{BadIndex, StrError};
  let file = MMBFile::parse(buf)?;
  let diff = |p: *const u8| p as usize - buf.as_ptr() as usize;
  let mut it = file.proof();
  let mut start = it.pos;
  macro_rules! get_get_var {($e:expr) => {{
    let mut vars = vec![];
    move |env: &mut Environment, i: usize| {
      if i >= vars.len() {
        vars.extend((vars.len()..=i).map(|j| env.get_atom(&format!($e, j).as_bytes())));
      }
      vars[i]
    }
  }}};
  let mut get_var = get_get_var!("v{}");
  let mut get_hyp = get_get_var!("h{}");
  macro_rules! next_var {($var:expr) => {{
    let var = $var;
    $var += 1;
    get_var(env, var)
  }}};
  while let Some(e) = it.next() {
    let (stmt, mut pf) = e.map_err(|p| StrError("bad statement", p))?;
    match stmt {
      StmtCmd::Sort => {
        if !pf.is_null() { return Err(StrError("Next statement incorrect", pf.pos)) }
        #[allow(clippy::cast_possible_truncation)]
        let sort = SortID(env.sorts.len() as u8);
        let atom = file.sort_name(sort, |s| env.get_atom(s.as_bytes())).ok_or(BadIndex)?;
        let span = (start..pf.pos).into();
        let fsp = FileSpan {file: fref.clone(), span};
        let sd = file.sort(sort).and_then(|sd| sd.try_into().ok())
          .ok_or(StrError("Step sort overflow", start))?;
        env.add_sort(atom, fsp, span, sd, None)
          .map_err(|_| StrError("double add sort", start))?;
      }
      StmtCmd::TermDef {local} => {
        #[allow(clippy::cast_possible_truncation)]
        let term = TermID(env.terms.len() as u32);
        let atom = file.term_name(term, |s| env.get_atom(s.as_bytes())).ok_or(BadIndex)?;
        let td = file.term(term).ok_or(StrError("Step term overflow", start))?;
        let fsp = FileSpan {file: fref.clone(), span: (start..pf.pos).into()};
        let mut var = 0;
        let args = td.args().iter().enumerate().map(|(i, a)| (
          Some(next_var!(var)),
          if a.bound() { Type::Bound(a.sort()) }
          else { Type::Reg(a.sort(), a.deps()) }
        )).collect::<Box<[_]>>();
        let ret = td.ret();
        if ret.bound() { return Err(StrError("bad return type", start)) }
        let kind = if td.def() {
          let (heap, e) = parse_unify(&file, args.len(), td.unify(), None, || next_var!(var))?;
          TermKind::Def(Some(Expr {head: e, heap}))
        } else {
          if !pf.is_null() { return Err(StrError("Next statement incorrect", pf.pos)) }
          TermKind::Term
        };
        let full = (start..pf.pos).into();
        env.add_term(Term {
          atom, span: fsp, full, doc: None, args, kind,
          vis: if local {Modifiers::LOCAL} else {Modifiers::empty()},
          ret: (ret.sort(), ret.deps()),
        }).map_err(|_| StrError("double add term", start))?;
      }
      StmtCmd::Axiom | StmtCmd::Thm {..} => {
        #[allow(clippy::cast_possible_truncation)]
        let thm = ThmID(env.thms.len() as u32);
        let atom = file.thm_name(thm, |s| env.get_atom(s.as_bytes())).ok_or(BadIndex)?;
        let td = file.thm(thm).ok_or(StrError("Step thm overflow", start))?;
        let fsp = FileSpan {file: fref.clone(), span: (start..pf.pos).into()};
        let mut var = 0;
        let args = td.args().iter().enumerate().map(|(i, a)| (
          Some(next_var!(var)),
          if a.bound() { Type::Bound(a.sort()) }
          else { Type::Reg(a.sort(), a.deps()) }
        )).collect::<Box<[_]>>();
        let mut hyps = vec![];
        let (heap, ret) = parse_unify(&file, args.len(), td.unify(), Some(&mut hyps), || next_var!(var))?;
        hyps.iter_mut().enumerate().for_each(|(i, (a, _))| *a = Some(get_hyp(env, i)));
        let kind = if matches!(stmt, StmtCmd::Axiom) {
          ThmKind::Axiom
        } else {
          ThmKind::Thm(Some(parse_proof(&file, args.len(), &mut pf, || next_var!(var))?))
        };
        let full = (start..pf.pos).into();
        let vis =
          if matches!(stmt, StmtCmd::Thm {local: false}) {Modifiers::PUB}
          else {Modifiers::empty()};
        env.add_thm(Thm {
          atom, span: fsp, full, doc: None, args, kind,
          vis, heap, hyps: hyps.into_boxed_slice(), ret,
        }).map_err(|_| StrError("double add term", start))?;
      }
    }
    start = it.pos;
  }
  Ok(())
}

/// Construct an [`Environment`] from an `mmb` file.
pub fn elab(file: &FileRef, source: &[u8]) -> (crate::elab::Result<()>, Environment) {
  let mut env = Environment::new();
  (parse(file, source, &mut env).map_err(From::from), env)
}