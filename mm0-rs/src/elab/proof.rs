use std::rc::Rc;
use std::hash::Hash;
use std::mem;
use std::collections::{HashMap, hash_map::Entry};
use super::environment::AtomID;
use super::*;
use super::lisp::{LispVal, LispKind, Uncons, UNDEF, InferTarget, print::FormatEnv};
use super::local_context::{InferSort, try_get_span_from};
use crate::util::*;

pub struct NodeHasher<'a> {
  pub lc: &'a LocalContext,
  pub fe: FormatEnv<'a>,
  pub var_map: HashMap<AtomID, usize>,
  pub fsp: FileSpan,
}

impl<'a> NodeHasher<'a> {
  pub fn new(lc: &'a LocalContext, fe: FormatEnv<'a>, fsp: FileSpan) -> Self {
    let mut var_map = HashMap::new();
    for (i, &(_, a, _)) in lc.var_order.iter().enumerate() {
      if let Some(a) = a {var_map.insert(a, i);}
    }
    NodeHasher {lc, fe, var_map, fsp}
  }

  fn err(&self, e: &LispKind, msg: impl Into<BoxError>) -> ElabError {
    self.err_sp(e.fspan().as_ref(), msg)
  }

  fn err_sp(&self, fsp: Option<&FileSpan>, msg: impl Into<BoxError>) -> ElabError {
    ElabError::new_e(try_get_span_from(&self.fsp, fsp), msg)
  }
}

pub trait NodeHash: Hash + Eq + Sized + std::fmt::Debug {
  const VAR: fn(usize) -> Self;
  fn from<'a>(nh: &NodeHasher<'a>, fsp: Option<&FileSpan>, r: &LispVal,
    f: impl FnMut(&LispVal) -> Result<usize>) -> Result<std::result::Result<Self, usize>>;
}

#[derive(Debug)]
pub struct Dedup<H: NodeHash> {
  map: HashMap<Rc<H>, usize>,
  prev: HashMap<*const LispKind, usize>,
  pub vec: Vec<(Rc<H>, bool)>,
}

impl<H: NodeHash> Dedup<H> {
  pub fn new(nargs: usize) -> Dedup<H> {
    let vec: Vec<_> = (0..nargs).map(|i| (Rc::new(H::VAR(i)), true)).collect();
    Dedup {
      map: vec.iter().enumerate().map(|(i, (r, _))| (r.clone(), i)).collect(),
      prev: HashMap::new(),
      vec,
    }
  }

  pub fn add_direct(&mut self, v: H) -> usize {
    match self.map.entry(Rc::new(v)) {
      Entry::Vacant(e) => {
        let n = self.vec.len();
        self.vec.push((e.key().clone(), false));
        e.insert(n);
        n
      }
      Entry::Occupied(e) => {
        let &n = e.get();
        self.vec[n].1 = true;
        n
      }
    }
  }

  pub fn add(&mut self, p: *const LispKind, v: H) -> usize {
    let n = self.add_direct(v);
    self.prev.insert(p, n);
    n
  }

  pub fn dedup(&mut self, nh: &NodeHasher, e: &LispVal) -> Result<usize> {
    let r = LispKind::unwrapped_arc(e);
    let p: *const _ = &*r;
    Ok(match self.prev.get(&p) {
      Some(&n) => {self.vec[n].1 = true; n}
      None => {
        let n = match H::from(nh, e.fspan().as_ref(), &r, |e| self.dedup(nh, e))? {
          Ok(v) => self.add_direct(v),
          Err(n) => n,
        };
        self.prev.insert(p, n); n
      }
    })
    // e.unwrapped_span(None, |sp, r| Ok(match self.prev.get(&(r as *const _)) {
    //   Some(&n) => {self.vec[n].1 = true; n}
    //   None => {
    //     let n = match H::from(nh, sp, r, |e| self.dedup(nh, e))? {
    //       Ok(v) => self.add_direct(v),
    //       Err(n) => n,
    //     };
    //     self.prev.insert(r, n); n
    //   }
    // }))
  }

  fn map_inj<T: NodeHash>(&self, mut f: impl FnMut(&H) -> T) -> Dedup<T> {
    let mut d = Dedup {
      map: HashMap::new(),
      prev: self.prev.clone(),
      vec: Vec::with_capacity(self.vec.len())
    };
    for (i, &(ref h, b)) in self.vec.iter().enumerate() {
      let t = Rc::new(f(h));
      d.map.insert(t.clone(), i);
      d.vec.push((t, b));
    }
    d
  }
}

pub trait Node: Sized + std::fmt::Debug {
  type Hash: NodeHash;
  const REF: fn(usize) -> Self;
  fn from(e: &Self::Hash, ids: &mut [Val<Self>]) -> Self;
}

#[derive(Debug)]
pub enum Val<T: Node> {Built(T), Ref(usize), Done}

impl<T: Node> Val<T> {
  pub fn take(&mut self) -> T {
    match mem::replace(self, Val::Done) {
      Val::Built(x) => x,
      Val::Ref(n) => {*self = Val::Ref(n); T::REF(n)}
      Val::Done => panic!("taking a value twice")
    }
  }
}

pub struct Builder<T: Node> {
  pub ids: Vec<Val<T>>,
  pub heap: Vec<T>,
}

impl<'a, F: FileServer + ?Sized> Elaborator<'a, F> {
  pub fn to_builder<T: Node>(&self, de: &Dedup<T::Hash>) -> Result<Builder<T>> {
    let mut ids: Vec<Val<T>> = Vec::with_capacity(de.vec.len());
    let mut heap = Vec::new();
    for &(ref e, b) in &de.vec {
      let node = T::from(&e, &mut ids);
      if b {
        ids.push(Val::Ref(heap.len()));
        heap.push(node);
      } else {
        ids.push(Val::Built(node))
      }
    }
    Ok(Builder {ids, heap})
  }
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub enum ExprHash {
  Var(usize),
  Dummy(AtomID, SortID),
  App(TermID, Vec<usize>),
}

impl NodeHash for ExprHash {
  const VAR: fn(usize) -> Self = Self::Var;
  fn from<'a>(nh: &NodeHasher<'a>, fsp: Option<&FileSpan>, r: &LispVal,
      mut f: impl FnMut(&LispVal) -> Result<usize>) -> Result<std::result::Result<Self, usize>> {
    Ok(Ok(match &**r {
      &LispKind::Atom(a) => match nh.var_map.get(&a) {
        Some(&i) => ExprHash::Var(i),
        None => match nh.lc.vars.get(&a) {
          Some(&(true, InferSort::Bound {sort})) => ExprHash::Dummy(a, sort),
          _ => Err(nh.err_sp(fsp, format!("variable '{}' not found", nh.fe.data[a].name)))?,
        }
      },
      LispKind::MVar(_, tgt) => Err(nh.err_sp(fsp,
        format!("{}: {}", nh.fe.to(r), nh.fe.to(tgt))))?,
      _ => {
        let mut u = Uncons::from(r.clone());
        let head = u.next().ok_or_else(||
          nh.err_sp(fsp, format!("bad expression {}", nh.fe.to(r))))?;
        let a = head.as_atom().ok_or_else(|| nh.err(&head, "expected an atom"))?;
        let tid = nh.fe.term(a).ok_or_else(||
          nh.err(&head, format!("term '{}' not declared", nh.fe.data[a].name)))?;
        let mut ns = Vec::new();
        for e in &mut u { ns.push(f(&e)?) }
        if !u.exactly(0) {Err(nh.err_sp(fsp, format!("bad expression {}", nh.fe.to(r))))?}
        ExprHash::App(tid, ns)
      }
    }))
  }
}

impl Node for ExprNode {
  type Hash = ExprHash;
  const REF: fn(usize) -> Self = ExprNode::Ref;
  fn from(e: &Self::Hash, ids: &mut [Val<Self>]) -> Self {
    match *e {
      ExprHash::Var(i) => ExprNode::Ref(i),
      ExprHash::Dummy(a, s) => ExprNode::Dummy(a, s),
      ExprHash::App(t, ref ns) => ExprNode::App(t,
        ns.iter().map(|&i| Val::take(&mut ids[i])).collect()),
    }
  }
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub enum ProofHash {
  Var(usize),
  Dummy(AtomID, SortID),
  Term(TermID, Vec<usize>),
  Hyp(usize, usize),
  Thm(ThmID, Vec<usize>),
  Conv(usize, usize, usize),
  Sym(usize),
  Unfold(TermID, Vec<usize>, usize),
}

impl NodeHash for ProofHash {
  const VAR: fn(usize) -> Self = Self::Var;
  fn from<'a>(nh: &NodeHasher<'a>, fsp: Option<&FileSpan>, r: &LispVal,
      mut f: impl FnMut(&LispVal) -> Result<usize>) -> Result<std::result::Result<Self, usize>> {
    Ok(Ok(match &**r {
      &LispKind::Atom(a) => match nh.var_map.get(&a) {
        Some(&i) => ProofHash::Var(i),
        None => match nh.lc.get_proof(a) {
          Some((_, _, p)) => return Ok(Err(f(p)?)),
          None => match nh.lc.vars.get(&a) {
            Some(&(true, InferSort::Bound {sort})) => ProofHash::Dummy(a, sort),
            _ => Err(nh.err_sp(fsp, format!("variable '{}' not found", nh.fe.data[a].name)))?,
          }
        }
      },
      LispKind::MVar(_, tgt) => Err(nh.err_sp(fsp,
        format!("{}: {}", nh.fe.to(r), nh.fe.to(tgt))))?,
      LispKind::Goal(tgt) => Err(nh.err_sp(fsp, format!("|- {}", nh.fe.to(tgt))))?,
      _ => {
        let mut u = Uncons::from(r.clone());
        let head = u.next().ok_or_else(||
          nh.err_sp(fsp, format!("bad expression {}", nh.fe.to(r))))?;
        let a = head.as_atom().ok_or_else(|| nh.err(&head, "expected an atom"))?;
        let adata = &nh.fe.data[a];
        match adata.decl {
          Some(DeclKey::Term(tid)) => {
            let mut ns = Vec::new();
            for e in u { ns.push(f(&e)?) }
            ProofHash::Term(tid, ns)
          }
          Some(DeclKey::Thm(tid)) => {
            let mut ns = Vec::new();
            for e in u { ns.push(f(&e)?) }
            ProofHash::Thm(tid, ns)
          },
          None => match a {
            AtomID::CONV => match (u.next(), u.next(), u.next()) {
              (Some(tgt), Some(c), Some(p)) if u.exactly(0) =>
                ProofHash::Conv(f(&tgt)?, f(&c)?, f(&p)?),
              _ => Err(nh.err_sp(fsp, format!("incorrect :conv format {}", nh.fe.to(r))))?
            },
            AtomID::SYM => match u.next() {
              Some(p) if u.exactly(0) => ProofHash::Sym(f(&p)?),
              _ => Err(nh.err_sp(fsp, format!("incorrect :sym format {}", nh.fe.to(r))))?
            },
            AtomID::UNFOLD => {
              let (t, es, p) = match (u.next(), u.next(), u.next(), u.next()) {
                (Some(t), Some(es), Some(p), None) if u.exactly(0) => (t, es, p),
                (Some(t), Some(es), Some(_), Some(p)) if u.exactly(0) => (t, es, p),
                _ => Err(nh.err_sp(fsp, format!("incorrect :unfold format {}", nh.fe.to(r))))?
              };
              let tid = t.as_atom().and_then(|a| nh.fe.term(a))
                .ok_or_else(|| nh.err(&t, "expected a term"))?;
              let mut ns = Vec::new();
              for e in Uncons::from(es.clone()) { ns.push(f(&e)?) }
              ProofHash::Unfold(tid, ns, f(&p)?)
            },
            _ => Err(nh.err(&head, format!("term/theorem '{}' not declared", adata.name)))?
          }
        }
      }
    }))
  }
}

impl Dedup<ExprHash> {
  pub fn map_proof(&self) -> Dedup<ProofHash> {
    self.map_inj(|e| match *e {
      ExprHash::Var(i) => ProofHash::Var(i),
      ExprHash::Dummy(a, s) => ProofHash::Dummy(a, s),
      ExprHash::App(t, ref ns) => ProofHash::Term(t, ns.clone()),
    })
  }
}

impl Node for ProofNode {
  type Hash = ProofHash;
  const REF: fn(usize) -> Self = ProofNode::Ref;
  fn from(e: &Self::Hash, ids: &mut [Val<Self>]) -> Self {
    match *e {
      ProofHash::Var(i) => ProofNode::Ref(i),
      ProofHash::Dummy(a, s) => ProofNode::Dummy(a, s),
      ProofHash::Term(term, ref ns) => ProofNode::Term {
        term, args: ns.iter().map(|&i| Val::take(&mut ids[i])).collect()
      },
      ProofHash::Hyp(i, e) => ProofNode::Hyp(i, Box::new(Val::take(&mut ids[e]))),
      ProofHash::Thm(thm, ref ns) => ProofNode::Thm {
        thm, args: ns.iter().map(|&i| Val::take(&mut ids[i])).collect()
      },
      ProofHash::Conv(i, j, k) => ProofNode::Conv(Box::new((
        Val::take(&mut ids[i]), Val::take(&mut ids[j]), Val::take(&mut ids[k])))),
      ProofHash::Sym(i) => ProofNode::Sym(Box::new(Val::take(&mut ids[i]))),
      ProofHash::Unfold(term, ref ns, r) => ProofNode::Unfold {
        term, args: ns.iter().map(|&i| Val::take(&mut ids[i])).collect(),
        res: Box::new(Val::take(&mut ids[r]))
      },
    }
  }
}

pub struct Subst<'a> {
  lc: &'a mut LocalContext,
  env: &'a Environment,
  heap: &'a [ExprNode],
  subst: Vec<LispVal>,
}

impl<'a> Subst<'a> {
  pub fn new(lc: &'a mut LocalContext, env: &'a Environment,
      heap: &'a [ExprNode], mut args: Vec<LispVal>) -> Subst<'a> {
    args.resize(heap.len(), UNDEF.clone());
    Subst {lc, env, heap, subst: args}
  }

  pub fn subst(&mut self, e: &ExprNode) -> LispVal {
    match *e {
      ExprNode::Ref(i) => {
        let e = &self.subst[i];
        if e.is_def() {return e.clone()}
        let e = self.subst(&self.heap[i]);
        self.subst[i] = e.clone();
        e
      }
      ExprNode::Dummy(_, s) => self.lc.new_mvar(InferTarget::Bound(self.env.sorts[s].atom)),
      ExprNode::App(t, ref es) => {
        let mut args = vec![Arc::new(LispKind::Atom(self.env.terms[t].atom))];
        args.extend(es.iter().map(|e| self.subst(e)));
        Arc::new(LispKind::List(args))
      }
    }
  }
}
