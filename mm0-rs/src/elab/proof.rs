//! The proof compacter, which takes an elaborated lisp proof s-expr and produces
//! a [`Proof`] object that will be stored in the environment.
//!
//! [`Proof`]: ../environment/struct.Proof.html

use std::rc::Rc;
use std::hash::Hash;
use std::mem;
use std::collections::{HashMap, hash_map::Entry};
use super::environment::{AtomID, Type};
use super::{LocalContext, ElabError, Result, Environment,
  SortID, TermID, ThmID, ExprNode, ProofNode, DeclKey};
use super::lisp::{LispVal, LispKind, Uncons, InferTarget, print::FormatEnv};
use super::local_context::{InferSort, try_get_span_from};
use crate::util::*;

#[derive(Debug)]
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
}

pub trait LispNodeHash: NodeHash {
  fn from<'a>(nh: &NodeHasher<'a>, fsp: Option<&FileSpan>, r: &LispVal,
    de: &mut Dedup<Self>) -> Result<std::result::Result<Self, usize>>;
  fn vars(&self, bv: &mut u64, deps: impl Fn(usize) -> u64) -> u64;
}

#[derive(Debug)]
pub struct Dedup<H: LispNodeHash> {
  map: HashMap<Rc<H>, usize>,
  prev: HashMap<*const LispKind, (LispVal, usize)>,
  pub vec: Vec<(Rc<H>, bool, u64)>,
  bv: u64,
}

impl<H: LispNodeHash> Dedup<H> {
  pub fn new(args: &[(Option<AtomID>, Type)]) -> Dedup<H> {
    let mut bv = 1;
    let vec: Vec<_> = args.iter().enumerate()
      .map(|(i, (_, t))| (Rc::new(H::VAR(i)), true, match t {
        Type::Bound(_) => (bv, bv *= 2).0,
        &Type::Reg(_, deps) => deps,
      })).collect();
    Dedup {
      map: vec.iter().enumerate().map(|(i, r)| (r.0.clone(), i)).collect(),
      prev: HashMap::new(),
      vec,
      bv,
    }
  }

  pub fn add(&mut self, p: LispVal, v: H) -> usize {
    let n = self.add_direct(v);
    self.prev.insert(&*p, (p, n));
    n
  }

  pub fn dedup(&mut self, nh: &NodeHasher<'_>, e: &LispVal) -> Result<usize> {
    let r = e.unwrapped_arc();
    let p: *const _ = &*r;
    Ok(match self.prev.get(&p) {
      Some(&(_, n)) => self.reuse(n),
      None => {
        let n = match H::from(nh, e.fspan().as_ref(), &r, self)? {
          Ok(v) => self.add_direct(v),
          Err(n) => n,
        };
        self.prev.insert(p, (r, n)); n
      }
    })
  }

  fn map_inj<T: LispNodeHash>(&self, mut f: impl FnMut(&H) -> T) -> Dedup<T> {
    let mut d = Dedup {
      map: HashMap::new(),
      prev: self.prev.clone(),
      vec: Vec::with_capacity(self.vec.len()),
      bv: self.bv,
    };
    for (i, &(ref h, b, v)) in self.vec.iter().enumerate() {
      let t = Rc::new(f(h));
      d.map.insert(t.clone(), i);
      d.vec.push((t, b, v));
    }
    d
  }
}

pub trait IDedup<H> {
  fn add_direct(&mut self, v: H) -> usize;
  fn reuse(&mut self, n: usize) -> usize;
  fn get(&self, n: usize) -> &Rc<H>;
}

impl<H: LispNodeHash> IDedup<H> for Dedup<H> {
  fn add_direct(&mut self, v: H) -> usize {
    match self.map.entry(Rc::new(v)) {
      Entry::Vacant(e) => {
        let vec = &mut self.vec;
        let n = vec.len();
        let vars = e.key().vars(&mut self.bv, |i| vec[i].2);
        vec.push((e.key().clone(), false, vars));
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

  fn reuse(&mut self, n: usize) -> usize {
    self.vec[n].1 = true;
    n
  }

  fn get(&self, n: usize) -> &Rc<H> { &self.vec[n].0 }
}

#[derive(Debug)]
pub struct DedupIter<'a, H: NodeHash>(std::slice::Iter<'a, (Rc<H>, bool, u64)>);

impl<'a, H: LispNodeHash> Iterator for DedupIter<'a, H> {
  type Item = (&'a H, bool);
  fn next(&mut self) -> Option<(&'a H, bool)> {
    self.0.next().map(|&(ref e, b, _)| (&**e, b))
  }
}

impl<'a, H: LispNodeHash> ExactSizeIterator for DedupIter<'a, H> {
  fn len(&self) -> usize { self.0.len() }
}

impl<'a, H: LispNodeHash> IntoIterator for &'a Dedup<H> {
  type Item = (&'a H, bool);
  type IntoIter = DedupIter<'a, H>;
  fn into_iter(self) -> DedupIter<'a, H> { DedupIter(self.vec.iter()) }
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

#[derive(Debug)]
pub struct Builder<T: Node> {
  pub ids: Vec<Val<T>>,
  pub heap: Vec<T>,
}

impl<T: Node> Builder<T> {
  pub fn from<'a, D>(de: D) -> Builder<T> where
    T::Hash: 'a,
    D: IntoIterator<Item=(&'a T::Hash, bool)>,
    D::IntoIter: ExactSizeIterator
  {
    let it = de.into_iter();
    let mut ids: Vec<Val<T>> = Vec::with_capacity(it.len());
    let mut heap = Vec::new();
    for (e, b) in it {
      let node = T::from(e, &mut ids);
      if b {
        ids.push(Val::Ref(heap.len()));
        heap.push(node);
      } else {
        ids.push(Val::Built(node))
      }
    }
    Builder {ids, heap}
  }
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub enum ExprHash {
  Var(usize),
  Dummy(AtomID, SortID),
  App(TermID, Box<[usize]>),
}

impl NodeHash for ExprHash {
  const VAR: fn(usize) -> Self = Self::Var;
}

impl LispNodeHash for ExprHash {
  fn from<'a>(nh: &NodeHasher<'a>, fsp: Option<&FileSpan>, r: &LispVal,
      de: &mut Dedup<Self>) -> Result<std::result::Result<Self, usize>> {
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
        for e in &mut u { ns.push(de.dedup(nh, &e)?) }
        if !u.exactly(0) {Err(nh.err_sp(fsp, format!("bad expression {}", nh.fe.to(r))))?}
        ExprHash::App(tid, ns.into())
      }
    }))
  }

  fn vars(&self, bv: &mut u64, deps: impl Fn(usize) -> u64) -> u64 {
    match self {
      &Self::Var(n) => deps(n),
      &Self::Dummy(_, _) => (*bv, *bv *= 2).0,
      Self::App(_, es) => es.iter().fold(0, |a, &i| a | deps(i)),
    }
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

impl Environment {
  pub fn deps(bvs: &[LispVal], mut v: Vec<LispVal>, xs: u64) -> Vec<LispVal> {
    v.push(if xs == 0 {LispVal::nil()} else {
      let mut i = 1;
      LispVal::list(bvs.iter().filter(|_| (xs & i != 0, i *= 2).0).cloned().collect::<Vec<_>>())
    });
    v
  }

  pub fn binders(&self, bis: &[(Option<AtomID>, Type)],
      heap: &mut Vec<LispVal>, bvs: &mut Vec<LispVal>) -> LispVal {
    LispVal::list(bis.iter().map(|(a, t)| LispVal::list({
      let a = LispVal::atom(a.unwrap_or(AtomID::UNDER));
      heap.push(a.clone());
      match t {
        &Type::Bound(s) => {bvs.push(a.clone()); vec![a, LispVal::atom(self.sorts[s].atom)]}
        &Type::Reg(s, xs) => Self::deps(&bvs, vec![a, LispVal::atom(self.sorts[s].atom)], xs)
      }
    })).collect::<Vec<_>>())
  }

  pub fn expr_node(&self, heap: &[LispVal], ds: &mut Option<&mut Vec<LispVal>>, e: &ExprNode) -> LispVal {
    match e {
      &ExprNode::Ref(n) => heap[n].clone(),
      &ExprNode::Dummy(a, s) => {
        let a = LispVal::atom(a);
        if let Some(ds) = ds {
          ds.push(LispVal::list(vec![a.clone(), LispVal::atom(self.sorts[s].atom)]));
        }
        a
      }
      &ExprNode::App(t, ref es) => {
        let mut args = vec![LispVal::atom(self.terms[t].atom)];
        args.extend(es.iter().map(|e| self.expr_node(heap, ds, e)));
        LispVal::list(args)
      }
    }
  }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum ProofHash {
  Var(usize),
  Dummy(AtomID, SortID),
  Term(TermID, Box<[usize]>),
  Hyp(usize, usize),
  Thm(ThmID, Box<[usize]>, usize),
  Conv(usize, usize, usize),
  Refl(usize),
  Sym(usize),
  Cong(TermID, Box<[usize]>),
  Unfold(TermID, Box<[usize]>, usize, usize, usize),
}

impl ProofHash {
  pub fn subst(de: &mut impl IDedup<Self>, env: &Environment,
    heap: &[ExprNode], nheap: &mut [Option<usize>], e: &ExprNode) -> usize {
    match *e {
      ExprNode::Ref(i) => match nheap[i] {
        Some(n) => de.reuse(n),
        None => {
          let n = Self::subst(de, env, heap, nheap, &heap[i]);
          nheap[i] = Some(n);
          n
        }
      },
      ExprNode::Dummy(_, _) => unreachable!(),
      ExprNode::App(t, ref es) => {
        let es2 = es.iter().map(|e| Self::subst(de, env, heap, nheap, e)).collect();
        de.add_direct(ProofHash::Term(t, es2))
      }
    }
  }

  pub fn conv(de: &impl IDedup<Self>, i: usize) -> bool {
    match **de.get(i) {
      ProofHash::Var(j) => j < i && Self::conv(de, j),
      ProofHash::Dummy(_, _) |
      ProofHash::Term(_, _) |
      ProofHash::Hyp(_, _) |
      ProofHash::Thm(_, _, _) |
      ProofHash::Conv(_, _, _) => false,
      ProofHash::Refl(_) |
      ProofHash::Sym(_) |
      ProofHash::Cong(_, _) |
      ProofHash::Unfold(_, _, _, _, _) => true,
    }
  }

  pub fn conv_side(de: &mut impl IDedup<Self>, i: usize, right: bool) -> usize {
    match *de.get(i).clone() {
      ProofHash::Var(j) => Self::conv_side(de, j, right),
      ProofHash::Dummy(_, _) |
      ProofHash::Term(_, _) |
      ProofHash::Hyp(_, _) |
      ProofHash::Thm(_, _, _) |
      ProofHash::Conv(_, _, _) => unreachable!(),
      ProofHash::Refl(e) => de.reuse(e),
      ProofHash::Sym(c) => Self::conv_side(de, c, !right),
      ProofHash::Cong(t, ref cs) => {
        let ns = cs.iter().map(|&c| Self::conv_side(de, c, right)).collect::<Vec<_>>();
        de.add_direct(ProofHash::Term(t, ns.into()))
      }
      ProofHash::Unfold(_, _, _, _, c) if right => Self::conv_side(de, c, true),
      ProofHash::Unfold(_, _, lhs, _, _) => de.reuse(lhs),
    }
  }

  pub fn to_conv(i: usize, de: &mut impl IDedup<Self>) -> usize {
    if Self::conv(de, i) {i} else {
      de.add_direct(ProofHash::Refl(i))
    }
  }
}

impl NodeHash for ProofHash {
  const VAR: fn(usize) -> Self = Self::Var;
}

impl LispNodeHash for ProofHash {
  fn from<'a>(nh: &NodeHasher<'a>, fsp: Option<&FileSpan>, r: &LispVal,
      de: &mut Dedup<Self>) -> Result<std::result::Result<Self, usize>> {
    Ok(Ok(match &**r {
      &LispKind::Atom(a) => match nh.var_map.get(&a) {
        Some(&i) => ProofHash::Var(i),
        None => match nh.lc.get_proof(a) {
          Some((_, _, p)) => return Ok(Err(de.dedup(nh, p)?)),
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
            for e in u { ns.push(de.dedup(nh, &e)?) }
            if ns.iter().any(|&i| Self::conv(de, i)) {
              for i in &mut ns {*i = Self::to_conv(*i, de)}
              ProofHash::Cong(tid, ns.into())
            } else {
              ProofHash::Term(tid, ns.into())
            }
          }
          Some(DeclKey::Thm(tid)) => {
            let mut ns = Vec::new();
            for e in u { ns.push(de.dedup(nh, &e)?) }
            let td = &nh.fe.thms[tid];
            let mut heap = vec![None; td.heap.len()];
            let mut bvs: Vec<u64> = vec![];
            for (i, (_, t)) in td.args.iter().enumerate() {
              heap[i] = Some(ns[i]);
              let deps = de.vec[ns[i]].2;
              let ok = match t {
                Type::Bound(_) => {
                  bvs.push(deps);
                  ns[..i].iter().all(|&j| de.vec[j].2 & deps == 0)
                }
                &Type::Reg(_, mut d) =>
                  bvs.iter().all(|&bv| (d & 1, d /= 2).0 != 0 || bv & deps == 0),
              };
              if !ok {
                let mut dvs = vec![];
                let mut bvs = vec![];
                for (i, (_, t)) in td.args.iter().enumerate() {
                  match t {
                    Type::Bound(_) => {
                      bvs.push(i);
                      dvs.extend((0..i).map(|j| (j, i)));
                    }
                    &Type::Reg(_, mut d) =>
                      dvs.extend(bvs.iter().filter(|_| (d & 1, d /= 2).0 == 0).map(|&j| (j, i)))
                  }
                }
                let mut err = format!("disjoint variable violation at {}", adata.name);
                let args: Vec<_> = Uncons::from(r.clone()).skip(1).collect();
                for (i, j) in dvs {
                  if de.vec[ns[i]].2 & de.vec[ns[j]].2 != 0 {
                    use std::fmt::Write;
                    write!(err, "\n  ({}, {}) -> ({}, {})",
                      nh.fe.to(&td.args[i].0.unwrap_or(AtomID::UNDER)),
                      nh.fe.to(&td.args[j].0.unwrap_or(AtomID::UNDER)),
                      nh.fe.pp(&args[i], 80), nh.fe.pp(&args[j], 80)).unwrap();
                  }
                }
                return Err(nh.err(&head, err))
              }
            }
            let rhs = Self::subst(de, &nh.fe, &td.heap, &mut heap, &td.ret);
            ProofHash::Thm(tid, ns.into(), rhs)
          },
          None => match a {
            AtomID::CONV => match (u.next(), u.next(), u.next()) {
              (Some(tgt), Some(c), Some(p)) if u.exactly(0) =>
                ProofHash::Conv(
                  de.dedup(nh, &tgt)?,
                  Self::to_conv(de.dedup(nh, &c)?, de),
                  de.dedup(nh, &p)?),
              _ => Err(nh.err_sp(fsp, format!("incorrect :conv format {}", nh.fe.to(r))))?
            },
            AtomID::SYM => match u.next() {
              Some(p) if u.exactly(0) => ProofHash::Sym(Self::to_conv(de.dedup(nh, &p)?, de)),
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
              for e in Uncons::from(es.clone()) { ns.push(de.dedup(nh, &e)?) }
              let lhs = de.add_direct(ProofHash::Term(tid, ns.clone().into()));
              let c = Self::to_conv(de.dedup(nh, &p)?, de);
              let l2 = Self::conv_side(de, c, false);
              ProofHash::Unfold(tid, ns.into(), lhs, l2, c)
            },
            _ => Err(nh.err(&head, format!("term/theorem '{}' not declared", adata.name)))?
          }
        }
      }
    }))
  }

  fn vars(&self, bv: &mut u64, deps: impl Fn(usize) -> u64) -> u64 {
    match self {
      &Self::Var(n) => deps(n),
      &Self::Dummy(_, _) => (*bv, *bv *= 2).0,
      Self::Term(_, es) => es.iter().fold(0, |a, &i| a | deps(i)),
      _ => 0,
    }
  }
}

impl ExprHash {
  pub fn to_proof(&self) -> ProofHash {
    match *self {
      ExprHash::Var(i) => ProofHash::Var(i),
      ExprHash::Dummy(a, s) => ProofHash::Dummy(a, s),
      ExprHash::App(t, ref ns) => ProofHash::Term(t, ns.clone().into()),
    }
  }
}

impl Dedup<ExprHash> {
  pub fn map_proof(&self) -> Dedup<ProofHash> {
    self.map_inj(ExprHash::to_proof)
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
      ProofHash::Thm(thm, ref ns, r) => ProofNode::Thm {
        thm, args: ns.iter().map(|&i| Val::take(&mut ids[i])).collect(),
        res: Box::new(Val::take(&mut ids[r]))
      },
      ProofHash::Conv(i, j, k) => ProofNode::Conv(Box::new((
        Val::take(&mut ids[i]), Val::take(&mut ids[j]), Val::take(&mut ids[k])))),
      ProofHash::Refl(i) => ProofNode::Refl(Box::new(Val::take(&mut ids[i]))),
      ProofHash::Sym(i) => ProofNode::Sym(Box::new(Val::take(&mut ids[i]))),
      ProofHash::Cong(term, ref ns) => ProofNode::Cong {
        term, args: ns.iter().map(|&i| Val::take(&mut ids[i])).collect()
      },
      ProofHash::Unfold(term, ref ns, l, m, c) => ProofNode::Unfold {
        term, args: ns.iter().map(|&i| Val::take(&mut ids[i])).collect(),
        res: Box::new((Val::take(&mut ids[l]), Val::take(&mut ids[m]), Val::take(&mut ids[c])))
      },
    }
  }
}

#[derive(Debug)]
pub struct Subst<'a> {
  env: &'a Environment,
  heap: &'a [ExprNode],
  subst: Vec<LispVal>,
}

impl<'a> Subst<'a> {
  pub fn new(env: &'a Environment,
      heap: &'a [ExprNode], mut args: Vec<LispVal>) -> Subst<'a> {
    args.resize(heap.len(), LispVal::undef());
    Subst {env, heap, subst: args}
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
      ExprNode::Dummy(_, _) => unreachable!(),
      ExprNode::App(t, ref es) => {
        let mut args = vec![LispVal::atom(self.env.terms[t].atom)];
        args.extend(es.iter().map(|e| self.subst(e)));
        LispVal::list(args)
      }
    }
  }

  pub fn subst_mut(&mut self, lc: &mut LocalContext, e: &ExprNode) -> LispVal {
    match *e {
      ExprNode::Ref(i) => {
        let e = &self.subst[i];
        if e.is_def() {return e.clone()}
        let e = self.subst_mut(lc, &self.heap[i]);
        self.subst[i] = e.clone();
        e
      }
      ExprNode::Dummy(_, s) => lc.new_mvar(InferTarget::Bound(self.env.sorts[s].atom), None),
      ExprNode::App(t, ref es) => {
        let mut args = vec![LispVal::atom(self.env.terms[t].atom)];
        args.extend(es.iter().map(|e| self.subst_mut(lc, e)));
        LispVal::list(args)
      }
    }
  }
}
