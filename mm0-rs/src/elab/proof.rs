use std::rc::Rc;
use std::hash::Hash;
use std::mem;
use std::collections::{HashMap, hash_map::Entry};
use super::environment::AtomID;
use super::*;
use super::lisp::{LispVal, LispKind, Uncons, UNDEF, InferTarget};
use super::local_context::{InferSort, try_get_span};
use crate::util::*;

pub struct NodeHasher<'a, F: FileServer + ?Sized> {
  pub elab: &'a Elaborator<'a, F>,
  pub var_map: HashMap<AtomID, usize>,
  pub fsp: FileSpan,
}

impl<'a, F: FileServer + ?Sized> NodeHasher<'a, F> {
  pub fn new(elab: &'a Elaborator<'a, F>, sp: Span) -> Self {
    let mut var_map = HashMap::new();
    for (i, &(_, a, _)) in elab.lc.var_order.iter().enumerate() {
      if let Some(a) = a {var_map.insert(a, i);}
    }
    NodeHasher { fsp: elab.fspan(sp), var_map, elab }
  }

  fn err(&self, e: &LispKind, msg: impl Into<BoxError>) -> ElabError {
    ElabError::new_e(try_get_span(&self.fsp, e), msg)
  }
}

pub trait NodeHash: Hash + Eq + Sized + std::fmt::Debug {
  const VAR: fn(usize) -> Self;
  fn from<'a, F: FileServer + ?Sized>(nh: &NodeHasher<'a, F>,
    e: &LispKind, f: impl FnMut(&LispVal) -> Result<usize>) -> Result<Self>;
}

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
  fn add(&mut self, p: *const LispKind, v: H) -> usize {
    match self.map.entry(Rc::new(v)) {
      Entry::Vacant(e) => {
        let n = self.vec.len();
        self.vec.push((e.key().clone(), false));
        e.insert(n);
        self.prev.insert(p, n);
        n
      }
      Entry::Occupied(e) => {
        let &n = e.get();
        self.vec[n].1 = true;
        self.prev.insert(p, n);
        n
      }
    }
  }

  pub fn dedup<'a, F: FileServer + ?Sized>(&mut self, nh: &NodeHasher<'a, F>, e: &LispVal) -> Result<usize> {
    e.unwrapped(|r| Ok(match self.prev.get(&(r as *const _)) {
      Some(&n) => {self.vec[n].1 = true; n}
      None => {
        let ns = H::from(nh, r, |e| self.dedup(nh, e))?;
        self.add(r, ns)
      }
    }))
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
  fn from<'a, F: FileServer + ?Sized>(nh: &NodeHasher<'a, F>, e: &LispKind,
      mut f: impl FnMut(&LispVal) -> Result<usize>) -> Result<Self> {
    Ok(match e {
      &LispKind::Atom(a) => match nh.var_map.get(&a) {
        Some(&i) => ExprHash::Var(i),
        None => match nh.elab.lc.vars.get(&a) {
          Some(&InferSort::Bound {dummy: true, sort}) => ExprHash::Dummy(a, sort),
          _ => Err(nh.err(e, format!("variable '{}' not found", nh.elab.data[a].name)))?,
        }
      },
      LispKind::List(es) if !es.is_empty() => {
        let a = es[0].as_atom().ok_or_else(|| nh.err(&es[0], "expected an atom"))?;
        let tid = nh.elab.env.term(a).ok_or_else(||
          nh.err(&es[0], format!("term '{}' not declared", nh.elab.env.data[a].name)))?;
        let mut ns = Vec::with_capacity(es.len() - 1);
        for e in &es[1..] { ns.push(f(e)?) }
        ExprHash::App(tid, ns)
      }
      _ => Err(nh.err(e, format!("bad expression {}", nh.elab.printer(e))))?
    })
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
  Thm(ThmID, Vec<usize>),
  Conv(usize, usize, usize),
  Sym(usize),
  Unfold(TermID, Vec<usize>, usize),
}

impl NodeHash for ProofHash {
  const VAR: fn(usize) -> Self = Self::Var;
  fn from<'a, F: FileServer + ?Sized>(nh: &NodeHasher<'a, F>, e: &LispKind,
      mut f: impl FnMut(&LispVal) -> Result<usize>) -> Result<Self> {
    Ok(match e {
      &LispKind::Atom(a) => match nh.var_map.get(&a) {
        Some(&i) => ProofHash::Var(i),
        None => match nh.elab.lc.vars.get(&a) {
          Some(&InferSort::Bound {dummy: true, sort}) => ProofHash::Dummy(a, sort),
          _ => Err(nh.err(e, format!("variable '{}' not found", nh.elab.data[a].name)))?,
        }
      },
      LispKind::List(es) if !es.is_empty() => {
        let a = es[0].as_atom().ok_or_else(|| nh.err(&es[0], "expected an atom"))?;
        let adata = &nh.elab.env.data[a];
        match adata.decl {
          Some(DeclKey::Term(tid)) => {
            let mut ns = Vec::with_capacity(es.len() - 1);
            for e in &es[1..] { ns.push(f(e)?) }
            ProofHash::Term(tid, ns)
          }
          Some(DeclKey::Thm(tid)) => {
            let mut ns = Vec::with_capacity(es.len() - 1);
            for e in &es[1..] { ns.push(f(e)?) }
            ProofHash::Thm(tid, ns)
          },
          None => match a {
            AtomID::CONV => {
              if es.len() != 4 { Err(nh.err(e, "incorrect :conv format"))? }
              ProofHash::Conv(f(&es[1])?, f(&es[2])?, f(&es[3])?)
            }
            AtomID::SYM => {
              if es.len() != 2 { Err(nh.err(e, "incorrect :sym format"))? }
              ProofHash::Sym(f(&es[1])?)
            }
            AtomID::UNFOLD => {
              if es.len() != 4 { Err(nh.err(e, "incorrect :unfold format"))? }
              let tid = es[1].as_atom().and_then(|a| nh.elab.term(a))
                .ok_or_else(|| nh.err(&es[1], "expected a term"))?;
              let mut ns = Vec::new();
              for e in Uncons::from(es[2].clone()) { ns.push(f(&e)?) }
              ProofHash::Unfold(tid, ns, f(&es[3])?)
            }
            _ => Err(nh.err(&es[0], format!("term/theorem '{}' not declared", adata.name)))?
          }
        }
      }
      _ => Err(nh.err(e, format!("bad expression {}", nh.elab.printer(e))))?
    })
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
