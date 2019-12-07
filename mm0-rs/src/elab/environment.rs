use std::ops::Deref;
use std::sync::Arc;
use std::hash::Hash;
use std::collections::HashMap;
use super::ElabError;
use crate::util::*;
pub use crate::parser::ast::Modifiers;
pub use crate::lined_string::{Span, FileSpan};

#[derive(Copy, Clone, Hash, PartialEq, Eq)] pub struct SortID(pub usize);
#[derive(Copy, Clone, Hash, PartialEq, Eq)] pub struct TermID(pub usize);
#[derive(Copy, Clone, Hash, PartialEq, Eq)] pub struct ThmID(pub usize);

#[derive(Copy, Clone)]
pub enum Type {
  Bound(SortID),
  Reg(SortID, u64),
}

/// An `ExprNode` is interpreted inside a context containing the `Vec<(String, Type)>`
/// args and the `Vec<ExprNode>` heap.
///   * `Ref(n)` is variable n, if `n < args.len()`
///   * `Ref(n + args.len())` is a reference to heap element `n`
///   * `Dummy(s, sort)` is a fresh dummy variable `s` with sort `sort`
///   * `App(t, nodes)` is an application of term constructor `t` to subterms
#[derive(Clone)]
pub enum ExprNode {
  Ref(usize),
  Dummy(String, SortID),
  App(TermID, Vec<ExprNode>),
}

/// The Expr type stores expression dags using a local context of expression nodes
/// and a final expression. See `ExprNode` for explanation of the variants.
#[derive(Clone)]
pub struct Expr {
  heap: Vec<ExprNode>,
  head: ExprNode,
}

#[derive(Clone)]
pub struct Term {
  span: FileSpan,
  vis: Modifiers,
  id: Span,
  args: Vec<(String, Type)>,
  ret: Type,
  val: Option<Expr>,
}

#[derive(Clone)]
pub enum ProofNode {
  Ref(usize),
  Term { term: TermID, args: Vec<ProofNode> },
  Thm {
    thm: ThmID,
    args: Vec<ProofNode>,
    hyps: Vec<ProofNode>,
    tgt: Box<ProofNode>,
  },
  Conv { tgt: Box<ProofNode>, proof: Box<ProofNode> },
}

/// The Proof type stores Proofession dags using a local context of Proofession nodes
/// and a final Proofession. See `ProofNode` for explanation of the variants.
#[derive(Clone)]
pub struct Proof {
  heap: Vec<ProofNode>,
  head: ProofNode,
}

#[derive(Clone)]
pub struct Thm {
  span: FileSpan,
  vis: Modifiers,
  id: Span,
  args: Vec<(String, Type)>,
  heap: Vec<ExprNode>,
  hyps: Vec<ExprNode>,
  ret: ExprNode,
  proof: Option<Proof>,
}

#[derive(Clone)]
pub enum Stmt {
  Sort(Arc<String>),
  Decl(Arc<String>),
}

#[derive(Copy, Clone)]
pub enum DeclKey {
  Term(TermID),
  Thm(ThmID),
}

#[derive(Default, Clone)]
pub struct Environment {
  pub sort_keys: HashMap<Arc<String>, SortID>,
  pub sorts: Vec<(FileSpan, Modifiers)>,
  pub delims_l: Delims,
  pub delims_r: Delims,
  pub decl_keys: HashMap<Arc<String>, DeclKey>,
  pub terms: Vec<Term>,
  pub thms: Vec<Thm>,
  pub stmts: Vec<Stmt>,
}

#[derive(Default, Clone)]
pub struct Delims([u8; 32]);

impl Delims {
  pub fn get(&self, c: u8) -> bool { self.0[(c >> 3) as usize] & (1 << (c & 7)) != 0 }
  pub fn set(&mut self, c: u8) { self.0[(c >> 3) as usize] |= 1 << (c & 7) }
  pub fn merge(&mut self, other: &Self) {
    for i in 0..32 { self.0[i] |= other.0[i] }
  }
}

#[derive(Default)]
struct Remapper {
  sort: HashMap<SortID, SortID>,
  term: HashMap<TermID, TermID>,
  thm: HashMap<ThmID, ThmID>,
}

trait Remap {
  fn remap(&self, r: &Remapper) -> Self;
}
impl Remap for SortID {
  fn remap(&self, r: &Remapper) -> Self { *r.sort.get(self).unwrap_or(self) }
}
impl Remap for TermID {
  fn remap(&self, r: &Remapper) -> Self { *r.term.get(self).unwrap_or(self) }
}
impl Remap for ThmID {
  fn remap(&self, r: &Remapper) -> Self { *r.thm.get(self).unwrap_or(self) }
}
impl Remap for String {
  fn remap(&self, _: &Remapper) -> Self { self.clone() }
}
impl<A: Remap, B: Remap> Remap for (A, B) {
  fn remap(&self, r: &Remapper) -> Self { (self.0.remap(r), self.1.remap(r)) }
}
impl<A: Remap> Remap for Option<A> {
  fn remap(&self, r: &Remapper) -> Self { self.as_ref().map(|x| x.remap(r)) }
}
impl<A: Remap> Remap for Vec<A> {
  fn remap(&self, r: &Remapper) -> Self { self.iter().map(|x| x.remap(r)).collect() }
}
impl<A: Remap> Remap for Box<A> {
  fn remap(&self, r: &Remapper) -> Self { Box::new(self.deref().remap(r)) }
}
impl Remap for Type {
  fn remap(&self, r: &Remapper) -> Self {
    match self {
      Type::Bound(s) => Type::Bound(s.remap(r)),
      &Type::Reg(s, deps) => Type::Reg(s.remap(r), deps),
    }
  }
}
impl Remap for ExprNode {
  fn remap(&self, r: &Remapper) -> Self {
    match self {
      &ExprNode::Ref(i) => ExprNode::Ref(i),
      ExprNode::Dummy(i, s) => ExprNode::Dummy(i.clone(), s.remap(r)),
      ExprNode::App(t, es) => ExprNode::App(t.remap(r), es.remap(r)),
    }
  }
}
impl Remap for Expr {
  fn remap(&self, r: &Remapper) -> Self {
    Expr {
      heap: self.heap.remap(r),
      head: self.head.remap(r),
    }
  }
}
impl Remap for Term {
  fn remap(&self, r: &Remapper) -> Self {
    Term {
      span: self.span.clone(),
      vis: self.vis,
      id: self.id,
      args: self.args.remap(r),
      ret: self.ret.remap(r),
      val: self.val.remap(r),
    }
  }
}
impl Remap for ProofNode {
  fn remap(&self, r: &Remapper) -> Self {
    match self {
      &ProofNode::Ref(i) => ProofNode::Ref(i),
      ProofNode::Term {term, args} => ProofNode::Term { term: term.remap(r), args: args.remap(r) },
      ProofNode::Thm {thm, args, hyps, tgt} => ProofNode::Thm {
        thm: thm.remap(r), args: args.remap(r), hyps: hyps.remap(r), tgt: tgt.remap(r) },
      ProofNode::Conv {tgt, proof} => ProofNode::Conv { tgt: tgt.remap(r), proof: proof.remap(r) },
    }
  }
}
impl Remap for Proof {
  fn remap(&self, r: &Remapper) -> Self {
    Proof {
      heap: self.heap.remap(r),
      head: self.head.remap(r),
    }
  }
}
impl Remap for Thm {
  fn remap(&self, r: &Remapper) -> Self {
    Thm {
      span: self.span.clone(),
      vis: self.vis,
      id: self.id,
      args: self.args.remap(r),
      heap: self.heap.remap(r),
      hyps: self.hyps.remap(r),
      ret: self.ret.remap(r),
      proof: self.proof.remap(r),
    }
  }
}

pub struct Redeclaration {
  pub msg: String,
  pub othermsg: String,
  pub other: FileSpan
}

impl Environment {
  pub fn sort(&self, id: SortID) -> &(FileSpan, Modifiers) { &self.sorts[id.0] }

  pub fn add_sort(&mut self, s: Arc<String>, fsp: FileSpan, sd: Modifiers) -> (SortID, Result<(), Redeclaration>) {
    let new_id = SortID(self.sorts.len());
    if let Some((_, e)) = self.sort_keys.try_insert(s.clone(), new_id) {
      let old_id = *e.get();
      let (ref fs, m) = self.sorts[old_id.0];
      if sd == m { (old_id, Ok(())) }
      else {
        (old_id, Err(Redeclaration {
          msg: format!("sort '{}' redeclared", e.key()),
          othermsg: "previously declared here".to_owned(),
          other: fs.clone()
        }))
      }
    } else {
      self.sorts.push((fsp, sd));
      self.stmts.push(Stmt::Sort(s));
      (new_id, Ok(()))
    }
  }

  pub fn add_term(&mut self, s: Arc<String>, new: FileSpan, t: impl FnOnce() -> Term) -> Result<TermID, (Option<TermID>, Redeclaration)> {
    let new_id = TermID(self.terms.len());
    if let Some((_, e)) = self.decl_keys.try_insert(s.clone(), DeclKey::Term(new_id)) {
      let (res, sp) = match *e.get() {
        DeclKey::Term(old_id) => {
          let ref sp = self.terms[old_id.0].span;
          if *sp == new { return Ok(old_id) }
          (Some(old_id), sp)
        }
        DeclKey::Thm(old_id) => (None, &self.thms[old_id.0].span)
      };
      Err((res, Redeclaration {
        msg: format!("term '{}' redeclared", e.key()),
        othermsg: "previously declared here".to_owned(),
        other: sp.clone()
      }))
    } else {
      self.terms.push(t());
      self.stmts.push(Stmt::Decl(s));
      Ok(new_id)
    }
  }

  pub fn add_thm(&mut self, s: Arc<String>, new: FileSpan, t: impl FnOnce() -> Thm) -> Result<ThmID, (Option<ThmID>, Redeclaration)> {
    let new_id = ThmID(self.thms.len());
    if let Some((_, e)) = self.decl_keys.try_insert(s.clone(), DeclKey::Thm(new_id)) {
      let (res, sp) = match *e.get() {
        DeclKey::Thm(old_id) => {
          let ref sp = self.thms[old_id.0].span;
          if *sp == new { return Ok(old_id) }
          (Some(old_id), sp)
        }
        DeclKey::Term(old_id) => (None, &self.terms[old_id.0].span)
      };
      Err((res, Redeclaration {
        msg: format!("theorem '{}' redeclared", e.key()),
        othermsg: "previously declared here".to_owned(),
        other: sp.clone()
      }))
    } else {
      self.thms.push(t());
      self.stmts.push(Stmt::Decl(s));
      Ok(new_id)
    }
  }

  pub fn add_delimiters(&mut self, ls: &[u8], rs: &[u8]) {
    for &c in ls { self.delims_l.set(c) }
    for &c in rs { self.delims_r.set(c) }
  }

  pub fn merge(&mut self, other: &Self, sp: Span, errors: &mut Vec<ElabError>) {
    if self.stmts.is_empty() { return *self = other.clone() }
    let mut remap = Remapper::default();
    for s in &other.stmts {
      match s {
        Stmt::Sort(s) => {
          let i = other.sort_keys[s];
          let &(ref fs, m) = other.sort(i);
          let (id, res) = self.add_sort(s.clone(), fs.clone(), m);
          if let Err(r) = res {
            errors.push(ElabError::with_info(sp, r.msg.into(), vec![
              (fs.clone(), r.othermsg.clone().into()),
              (r.other, r.othermsg.into())
            ]));
          }
          if i != id { remap.sort.insert(i, id); }
        }
        Stmt::Decl(s) => match other.decl_keys[s] {
          DeclKey::Term(i) => {
            let ref o = other.terms[i.0];
            let id = match self.add_term(s.clone(), o.span.clone(), || o.remap(&remap)) {
              Ok(id) => id,
              Err((id, r)) => {
                errors.push(ElabError::with_info(sp, r.msg.into(), vec![
                  (o.span.clone(), r.othermsg.clone().into()),
                  (r.other, r.othermsg.into())
                ]));
                match id { None => return, Some(id) => id }
              }
            };
            if i != id { remap.term.insert(i, id); }
          }
          DeclKey::Thm(i) => {
            let ref o = other.thms[i.0];
            let id = match self.add_thm(s.clone(), o.span.clone(), || o.remap(&remap)) {
              Ok(id) => id,
              Err((id, r)) => {
                errors.push(ElabError::with_info(sp, r.msg.into(), vec![
                  (o.span.clone(), r.othermsg.clone().into()),
                  (r.other, r.othermsg.into())
                ]));
                match id { None => return, Some(id) => id }
              }
            };
            if i != id { remap.thm.insert(i, id); }
          }
        }
      }
    }
    self.delims_l.merge(&other.delims_l);
    self.delims_r.merge(&other.delims_r);
  }
}
