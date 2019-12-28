use std::ops::{Deref, DerefMut, Index, IndexMut};
use std::fmt;
use std::convert::TryInto;
use std::iter::FromIterator;
use std::sync::Arc;
use std::fmt::Write;
use std::hash::Hash;
use std::collections::HashMap;
use super::{ElabError, BoxError};
use crate::util::*;
use super::lisp::{LispVal, LispRemapper};
pub use crate::parser::ast::{Modifiers, Prec};

macro_rules! id_wrapper {
  ($id:ident: $ty:ty, $vec:ident) => {
    #[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Default)]
    pub struct $id(pub $ty);

    impl fmt::Debug for $id {
      fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self.0.fmt(f) }
    }

    #[derive(Clone)]
    pub struct $vec<T>(pub Vec<T>);

    #[allow(dead_code)]
    impl<T> $vec<T> {
      pub fn get(&self, i: $id) -> Option<&T> { self.0.get(i.0 as usize) }
      pub fn get_mut(&mut self, i: $id) -> Option<&mut T> { self.0.get_mut(i.0 as usize) }
    }
    impl<T> Default for $vec<T> {
      fn default() -> $vec<T> { $vec(Vec::new()) }
    }
    impl<T> Index<$id> for $vec<T> {
      type Output = T;
      fn index(&self, i: $id) -> &T { &self.0[i.0 as usize] }
    }
    impl<T> IndexMut<$id> for $vec<T> {
      fn index_mut(&mut self, i: $id) -> &mut T { &mut self.0[i.0 as usize] }
    }
    impl<T> Deref for $vec<T> {
      type Target = Vec<T>;
      fn deref(&self) -> &Vec<T> { &self.0 }
    }
    impl<T> DerefMut for $vec<T> {
      fn deref_mut(&mut self) -> &mut Vec<T> { &mut self.0 }
    }
    impl<T> FromIterator<T> for $vec<T> {
      fn from_iter<I: IntoIterator<Item=T>>(iter: I) -> Self { $vec(Vec::from_iter(iter)) }
    }
  };
}

id_wrapper!(SortID: u8, SortVec);
id_wrapper!(TermID: u32, TermVec);
id_wrapper!(ThmID: u32, ThmVec);
id_wrapper!(AtomID: u32, AtomVec);

#[derive(Clone)]
pub struct Sort {
  pub atom: AtomID,
  pub name: ArcString,
  pub span: FileSpan,
  pub mods: Modifiers,
}

#[derive(Copy, Clone, Debug)]
pub enum Type {
  Bound(SortID),
  Reg(SortID, u64),
}

impl Type {
  pub fn _sort(self) -> SortID {
    match self {
      Type::Bound(s) => s,
      Type::Reg(s, _) => s,
    }
  }
  pub fn bound(self) -> bool {
    match self {
      Type::Bound(_) => true,
      _ => false,
    }
  }
}

/// An `ExprNode` is interpreted inside a context containing the `Vec<(String, Type)>`
/// args and the `Vec<ExprNode>` heap.
///   * `Ref(n)` is variable n, if `n < args.len()`
///   * `Ref(n + args.len())` is a reference to heap element `n`
///   * `Dummy(s, sort)` is a fresh dummy variable `s` with sort `sort`
///   * `App(t, nodes)` is an application of term constructor `t` to subterms
#[derive(Clone, Debug)]
pub enum ExprNode {
  Ref(usize),
  Dummy(AtomID, SortID),
  App(TermID, Vec<ExprNode>),
}

/// The Expr type stores expression dags using a local context of expression nodes
/// and a final expression. See `ExprNode` for explanation of the variants.
#[derive(Clone)]
pub struct Expr {
  pub heap: Vec<ExprNode>,
  pub head: ExprNode,
}

#[derive(Clone)]
pub struct Term {
  pub atom: AtomID,
  pub span: FileSpan,
  pub vis: Modifiers,
  pub id: Span,
  pub args: Vec<(Option<AtomID>, Type)>,
  pub ret: (SortID, u64),
  pub val: Option<Expr>,
}

#[derive(Clone, Debug)]
pub enum ProofNode {
  Ref(usize),
  Dummy(AtomID, SortID),
  Term { term: TermID, args: Vec<ProofNode> },
  Hyp(usize, Box<ProofNode>),
  Thm { thm: ThmID, args: Vec<ProofNode> },
  Conv(Box<(ProofNode, ProofNode, ProofNode)>), // tgt, conv, proof
  Sym(Box<ProofNode>),
  Unfold { term: TermID, args: Vec<ProofNode>, res: Box<ProofNode> },
}

impl From<&ExprNode> for ProofNode {
  fn from(e: &ExprNode) -> ProofNode {
    match e {
      &ExprNode::Ref(n) => ProofNode::Ref(n),
      &ExprNode::Dummy(a, s) => ProofNode::Dummy(a, s),
      &ExprNode::App(term, ref es) => ProofNode::Term {
        term, args: es.iter().map(|e| e.into()).collect()
      }
    }
  }
}
#[derive(Clone, Debug)]
pub struct Proof {
  pub heap: Vec<ProofNode>,
  pub hyps: Vec<ProofNode>,
  pub head: ProofNode,
}

#[derive(Clone, Debug)]
pub struct Thm {
  pub atom: AtomID,
  pub span: FileSpan,
  pub vis: Modifiers,
  pub id: Span,
  pub args: Vec<(Option<AtomID>, Type)>,
  pub heap: Vec<ExprNode>,
  pub hyps: Vec<(Option<AtomID>, ExprNode)>,
  pub ret: ExprNode,
  pub proof: Option<Option<Proof>>,
}

#[derive(Copy, Clone)]
pub enum StmtTrace {
  Sort(AtomID),
  Decl(AtomID),
}

#[derive(Copy, Clone)]
pub enum DeclKey {
  Term(TermID),
  Thm(ThmID),
}

#[derive(Clone, Debug)]
pub enum Literal {
  Var(usize, Prec),
  Const(ArcString),
}

#[derive(Clone, Debug)]
pub struct NotaInfo {
  pub span: FileSpan,
  pub term: TermID,
  pub nargs: usize,
  pub rassoc: Option<bool>,
  pub lits: Vec<Literal>,
}

#[derive(Clone)]
pub enum Coe {
  One(FileSpan, TermID),
  Trans(Arc<Coe>, SortID, Arc<Coe>),
}

impl Coe {
  fn write_arrows_r(&self, sorts: &SortVec<Sort>, s: &mut String, related: &mut Vec<(FileSpan, BoxError)>,
      sl: SortID, sr: SortID) -> Result<(), std::fmt::Error> {
    match self {
      Coe::One(fsp, _) => {
        related.push((fsp.clone(), format!("{} -> {}", sorts[sl].name, sorts[sr].name).into()));
        write!(s, " -> {}", sorts[sr].name)
      }
      &Coe::Trans(ref c1, sm, ref c2) => {
        c1.write_arrows_r(sorts, s, related, sl, sm)?;
        c2.write_arrows_r(sorts, s, related, sm, sr)
      }
    }
  }

  fn write_arrows(&self, sorts: &SortVec<Sort>, s: &mut String, related: &mut Vec<(FileSpan, BoxError)>,
      s1: SortID, s2: SortID) -> Result<(), std::fmt::Error> {
    write!(s, "{}", sorts[s1].name)?;
    self.write_arrows_r(sorts, s, related, s1, s2)
  }
}

#[derive(Default, Clone)]
pub struct ParserEnv {
  pub delims_l: Delims,
  pub delims_r: Delims,
  pub consts: HashMap<ArcString, (FileSpan, Prec)>,
  pub prec_assoc: HashMap<u32, (FileSpan, bool)>,
  pub prefixes: HashMap<ArcString, NotaInfo>,
  pub infixes: HashMap<ArcString, NotaInfo>,
  pub coes: HashMap<SortID, HashMap<SortID, Arc<Coe>>>,
  pub coe_prov: HashMap<SortID, SortID>,
}

#[derive(Clone)]
pub struct AtomData {
  pub name: ArcString,
  pub lisp: Option<(Option<FileSpan>, LispVal)>,
  pub sort: Option<SortID>,
  pub decl: Option<DeclKey>,
}

impl AtomData {
  fn new(name: ArcString) -> AtomData {
    AtomData {name, lisp: None, sort: None, decl: None}
  }
}

#[derive(Clone)]
pub struct Environment {
  pub sorts: SortVec<Sort>,
  pub pe: ParserEnv,
  pub terms: TermVec<Term>,
  pub thms: ThmVec<Thm>,
  pub atoms: HashMap<ArcString, AtomID>,
  pub data: AtomVec<AtomData>,
  pub stmts: Vec<StmtTrace>,
}

macro_rules! make_atoms {
  {consts $n:expr;} => {};
  {consts $n:expr; $x:ident $($xs:ident)*} => {
    pub const $x: AtomID = AtomID($n);
    make_atoms! {consts AtomID::$x.0+1; $($xs)*}
  };
  {$($x:ident: $e:expr,)*} => {
    impl AtomID {
      make_atoms! {consts 0; $($x)*}
    }

    impl Environment {
      pub fn new() -> Environment {
        let mut atoms = HashMap::new();
        let mut data = AtomVec::default();
        $({
          let s: ArcString = $e.into();
          atoms.insert(s.clone(), AtomID::$x);
          data.push(AtomData::new(s))
        })*
        Environment {
          atoms, data,
          sorts: Default::default(),
          pe: Default::default(),
          terms: Default::default(),
          thms: Default::default(),
          stmts: Default::default(),
        }
      }
    }
  }
}

make_atoms! {
  UNDER: "_",
  BANG: "!",
  BANG2: "!!",
  VERB: ":verb",
  CONV: ":conv",
  SYM: ":sym",
  UNFOLD: ":unfold",
  COLON: ":",
  QMARK: "?",
  REFINE_EXTRA_ARGS: "refine-extra-args",
  TERM: "term",
  DEF: "def",
  AXIOM: "axiom",
  THM: "theorem",
  PUB: "pub",
  ABSTRACT: "abstract",
  LOCAL: "local",
  SORRY: ":sorry",
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
  atom: HashMap<AtomID, AtomID>,
}

pub trait Remap<R> {
  fn remap(&self, r: &mut R) -> Self;
}
impl Remap<Remapper> for SortID {
  fn remap(&self, r: &mut Remapper) -> Self { *r.sort.get(self).unwrap_or(self) }
}
impl Remap<Remapper> for TermID {
  fn remap(&self, r: &mut Remapper) -> Self { *r.term.get(self).unwrap_or(self) }
}
impl Remap<Remapper> for ThmID {
  fn remap(&self, r: &mut Remapper) -> Self { *r.thm.get(self).unwrap_or(self) }
}
impl Remap<Remapper> for AtomID {
  fn remap(&self, r: &mut Remapper) -> Self { *r.atom.get(self).unwrap_or(self) }
}
impl<R> Remap<R> for String {
  fn remap(&self, _: &mut R) -> Self { self.clone() }
}
impl<R, A: Remap<R>, B: Remap<R>> Remap<R> for (A, B) {
  fn remap(&self, r: &mut R) -> Self { (self.0.remap(r), self.1.remap(r)) }
}
impl<R, A: Remap<R>, B: Remap<R>, C: Remap<R>> Remap<R> for (A, B, C) {
  fn remap(&self, r: &mut R) -> Self { (self.0.remap(r), self.1.remap(r), self.2.remap(r)) }
}
impl<R, A: Remap<R>> Remap<R> for Option<A> {
  fn remap(&self, r: &mut R) -> Self { self.as_ref().map(|x| x.remap(r)) }
}
impl<R, A: Remap<R>> Remap<R> for Vec<A> {
  fn remap(&self, r: &mut R) -> Self { self.iter().map(|x| x.remap(r)).collect() }
}
impl<R, A: Remap<R>> Remap<R> for Box<A> {
  fn remap(&self, r: &mut R) -> Self { Box::new(self.deref().remap(r)) }
}
impl<R, A: Remap<R>> Remap<R> for Arc<A> {
  fn remap(&self, r: &mut R) -> Self { Arc::new(self.deref().remap(r)) }
}
impl<R, A: Remap<R>> Remap<R> for Box<[A]> {
  fn remap(&self, r: &mut R) -> Self { self.iter().map(|v| v.remap(r)).collect() }
}
impl<R, A: Remap<R>> Remap<R> for Arc<[A]> {
  fn remap(&self, r: &mut R) -> Self { self.iter().map(|v| v.remap(r)).collect() }
}
impl Remap<Remapper> for Type {
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      Type::Bound(s) => Type::Bound(s.remap(r)),
      &Type::Reg(s, deps) => Type::Reg(s.remap(r), deps),
    }
  }
}
impl Remap<Remapper> for ExprNode {
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      &ExprNode::Ref(i) => ExprNode::Ref(i),
      ExprNode::Dummy(a, s) => ExprNode::Dummy(a.remap(r), s.remap(r)),
      ExprNode::App(t, es) => ExprNode::App(t.remap(r), es.remap(r)),
    }
  }
}
impl Remap<Remapper> for Expr {
  fn remap(&self, r: &mut Remapper) -> Self {
    Expr {
      heap: self.heap.remap(r),
      head: self.head.remap(r),
    }
  }
}
impl Remap<Remapper> for Term {
  fn remap(&self, r: &mut Remapper) -> Self {
    Term {
      atom: self.atom.remap(r),
      span: self.span.clone(),
      vis: self.vis,
      id: self.id,
      args: self.args.remap(r),
      ret: (self.ret.0.remap(r), self.ret.1),
      val: self.val.remap(r),
    }
  }
}
impl Remap<Remapper> for ProofNode {
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      &ProofNode::Ref(i) => ProofNode::Ref(i),
      ProofNode::Dummy(a, s) => ProofNode::Dummy(a.remap(r), s.remap(r)),
      ProofNode::Term {term, args} => ProofNode::Term { term: term.remap(r), args: args.remap(r) },
      &ProofNode::Hyp(i, ref e) => ProofNode::Hyp(i, e.remap(r)),
      ProofNode::Thm {thm, args} => ProofNode::Thm { thm: thm.remap(r), args: args.remap(r) },
      ProofNode::Conv(p) => ProofNode::Conv(Box::new((p.0.remap(r), p.1.remap(r), p.2.remap(r)))),
      ProofNode::Sym(p) => ProofNode::Sym(p.remap(r)),
      ProofNode::Unfold {term, args, res} => ProofNode::Unfold {
        term: term.remap(r), args: args.remap(r), res: res.remap(r) },
    }
  }
}
impl Remap<Remapper> for Proof {
  fn remap(&self, r: &mut Remapper) -> Self {
    Proof {
      heap: self.heap.remap(r),
      hyps: self.hyps.remap(r),
      head: self.head.remap(r),
    }
  }
}
impl Remap<Remapper> for Thm {
  fn remap(&self, r: &mut Remapper) -> Self {
    Thm {
      atom: self.atom.remap(r),
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
impl Remap<Remapper> for NotaInfo {
  fn remap(&self, r: &mut Remapper) -> Self {
    NotaInfo {
      span: self.span.clone(),
      term: self.term.remap(r),
      nargs: self.nargs,
      rassoc: self.rassoc,
      lits: self.lits.clone(),
    }
  }
}
impl Remap<Remapper> for Coe {
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      Coe::One(sp, t) => Coe::One(sp.clone(), t.remap(r)),
      Coe::Trans(c1, s, c2) => Coe::Trans(c1.remap(r), s.remap(r), c2.remap(r)),
    }
  }
}

pub struct IncompatibleError {
  pub decl1: FileSpan,
  pub decl2: FileSpan,
}

impl ParserEnv {
  pub fn add_delimiters(&mut self, ls: &[u8], rs: &[u8]) {
    for &c in ls { self.delims_l.set(c) }
    for &c in rs { self.delims_r.set(c) }
  }

  pub fn add_const(&mut self, tk: ArcString, sp: FileSpan, p: Prec) -> Result<(), IncompatibleError> {
    if let Some((_, e)) = self.consts.try_insert(tk, (sp.clone(), p)) {
      if e.get().1 == p { return Ok(()) }
      Err(IncompatibleError { decl1: e.get().0.clone(), decl2: sp })
    } else { Ok(()) }
  }

  pub fn add_prec_assoc(&mut self, p: u32, sp: FileSpan, r: bool) -> Result<(), IncompatibleError> {
    if let Some((_, e)) = self.prec_assoc.try_insert(p, (sp.clone(), r)) {
      if e.get().1 == r { return Ok(()) }
      let (decl1, decl2) = if r { (e.get().0.clone(), sp) } else { (sp, e.get().0.clone()) };
      Err(IncompatibleError {decl1, decl2})
    } else { Ok(()) }
  }

  fn add_nota_info(m: &mut HashMap<ArcString, NotaInfo>, tk: ArcString, n: NotaInfo) -> Result<(), IncompatibleError> {
    if let Some((n, e)) = m.try_insert(tk.clone(), n) {
      if e.get().span == n.span { return Ok(()) }
      Err(IncompatibleError { decl1: e.get().span.clone(), decl2: n.span })
    } else { Ok(()) }
  }

  pub fn add_prefix(&mut self, tk: ArcString, n: NotaInfo) -> Result<(), IncompatibleError> {
    Self::add_nota_info(&mut self.prefixes, tk, n)
  }
  pub fn add_infix(&mut self, tk: ArcString, n: NotaInfo) -> Result<(), IncompatibleError> {
    Self::add_nota_info(&mut self.infixes, tk, n)
  }

  fn add_coe1(&mut self, sp: Span, sorts: &SortVec<Sort>, s1: SortID, s2: SortID, c: Arc<Coe>) -> Result<(), ElabError> {
    if s1 == s2 {
      let mut err = "coercion cycle detected: ".to_owned();
      let mut related = Vec::new();
      c.write_arrows(sorts, &mut err, &mut related, s1, s2).unwrap();
      return Err(ElabError::with_info(sp, err.into(), related))
    }
    if let Some((c, e)) = self.coes.entry(s1).or_default().try_insert(s2, c) {
      let mut err = "coercion diamond detected: ".to_owned();
      let mut related = Vec::new();
      e.get().write_arrows(sorts, &mut err, &mut related, s1, s2).unwrap();
      err.push_str(";   ");
      c.write_arrows(sorts, &mut err, &mut related, s1, s2).unwrap();
      return Err(ElabError::with_info(sp, err.into(), related))
    }
    Ok(())
  }

  fn update_provs(&mut self, sp: Span, sorts: &SortVec<Sort>) -> Result<(), ElabError> {
    let mut provs = HashMap::new();
    for (&s1, m) in &self.coes {
      for (&s2, _) in m {
        if sorts[s2].mods.contains(Modifiers::PROVABLE) {
          if let Some(s2_) = provs.insert(s1, s2) {
            let mut err = "coercion diamond to provable detected:\n".to_owned();
            let mut related = Vec::new();
            self.coes[&s1][&s2].write_arrows(sorts, &mut err, &mut related, s1, s2).unwrap();
            err.push_str(" provable\n");
            self.coes[&s1][&s2_].write_arrows(sorts, &mut err, &mut related, s1, s2_).unwrap();
            err.push_str(" provable");
            return Err(ElabError::with_info(sp, err.into(), related))
          }
        }
      }
    }
    self.coe_prov = provs;
    Ok(())
  }

  fn add_coe_raw(&mut self, sp: Span, sorts: &SortVec<Sort>,
      s1: SortID, s2: SortID, fsp: FileSpan, t: TermID) -> Result<(), ElabError> {
    let c1 = Arc::new(Coe::One(fsp, t));
    let mut todo = Vec::new();
    for (&sl, m) in &self.coes {
      if let Some(c) = m.get(&s1) {
        todo.push((sl, s2, Arc::new(Coe::Trans(c.clone(), s1, c1.clone()))));
      }
    }
    todo.push((s1, s2, c1.clone()));
    if let Some(m) = self.coes.get(&s2) {
      for (&sr, c) in m {
        todo.push((s1, sr, Arc::new(Coe::Trans(c1.clone(), s2, c.clone()))));
      }
    }
    for (sl, sr, c) in todo { self.add_coe1(sp, sorts, sl, sr, c)? }
    Ok(())
  }

  pub fn add_coe(&mut self, sp: Span, sorts: &SortVec<Sort>,
      s1: SortID, s2: SortID, fsp: FileSpan, t: TermID) -> Result<(), ElabError> {
    self.add_coe_raw(sp, sorts, s1, s2, fsp, t)?;
    self.update_provs(sp, sorts)
  }

  fn merge(&mut self, other: &Self, r: &mut Remapper, sp: Span, sorts: &SortVec<Sort>, errors: &mut Vec<ElabError>) {
    self.delims_l.merge(&other.delims_l);
    self.delims_r.merge(&other.delims_r);
    for (tk, &(ref fsp, p)) in &other.consts {
      self.add_const(tk.clone(), fsp.clone(), p).unwrap_or_else(|r|
        errors.push(ElabError::with_info(sp,
          format!("constant '{}' declared with two precedences", tk).into(),
          vec![(r.decl1, "declared here".into()), (r.decl2, "declared here".into())])))
    }
    for (&p, &(ref fsp, r)) in &other.prec_assoc {
      self.add_prec_assoc(p, fsp.clone(), r).unwrap_or_else(|r|
        errors.push(ElabError::with_info(sp,
          format!("precedence level {} has incompatible associativity", p).into(),
          vec![(r.decl1, "left assoc here".into()), (r.decl2, "right assoc here".into())])))
    }
    for (tk, i) in &other.prefixes {
      self.add_prefix(tk.clone(), i.remap(r)).unwrap_or_else(|r|
        errors.push(ElabError::with_info(sp,
          format!("constant '{}' declared twice", tk).into(),
          vec![(r.decl1, "declared here".into()), (r.decl2, "declared here".into())])))
    }
    for (tk, i) in &other.infixes {
      self.add_infix(tk.clone(), i.remap(r)).unwrap_or_else(|r|
        errors.push(ElabError::with_info(sp,
          format!("constant '{}' declared twice", tk).into(),
          vec![(r.decl1, "declared here".into()), (r.decl2, "declared here".into())])))
    }
    for (&s1, m) in &other.coes {
      for (&s2, coe) in m {
        if let &Coe::One(ref fsp, t) = coe.deref() {
          self.add_coe_raw(sp, sorts, s1, s2, fsp.clone(), t.remap(r))
            .unwrap_or_else(|r| errors.push(r))
        }
      }
    }
    self.update_provs(sp, sorts).unwrap_or_else(|r| errors.push(r))
  }
}

pub struct RedeclarationError {
  pub msg: String,
  pub othermsg: String,
  pub other: FileSpan
}

impl Environment {
  pub fn term(&self, a: AtomID) -> Option<TermID> {
    if let Some(DeclKey::Term(i)) = self.data[a].decl { Some(i) } else { None }
  }

  pub fn thm(&self, a: AtomID) -> Option<ThmID> {
    if let Some(DeclKey::Thm(i)) = self.data[a].decl { Some(i) } else { None }
  }
}

pub enum AddItemError<A> {
  Redeclaration(A, RedeclarationError),
  Overflow
}
type AddItemResult<A> = Result<A, AddItemError<Option<A>>>;

impl<A> AddItemError<A> {
  pub fn to_elab_error(self, sp: Span) -> ElabError {
    match self {
      AddItemError::Redeclaration(_, r) =>
        ElabError::with_info(sp, r.msg.into(), vec![(r.other, r.othermsg.into())]),
      AddItemError::Overflow =>
        ElabError::new_e(sp, "too many sorts"),
    }
  }
}

impl Environment {
  pub fn add_sort(&mut self, a: AtomID, fsp: FileSpan, sd: Modifiers) -> Result<SortID, AddItemError<SortID>> {
    let new_id = SortID(self.sorts.len().try_into().map_err(|_| AddItemError::Overflow)?);
    let data = &mut self.data[a];
    if let Some(old_id) = data.sort {
      let ref sort = self.sorts[old_id];
      if sd == sort.mods { Ok(old_id) }
      else {
        Err(AddItemError::Redeclaration(old_id, RedeclarationError {
          msg: format!("sort '{}' redeclared", data.name),
          othermsg: "previously declared here".to_owned(),
          other: sort.span.clone()
        }))
      }
    } else {
      data.sort = Some(new_id);
      self.sorts.push(Sort { atom: a, name: data.name.clone(), span: fsp, mods: sd });
      self.stmts.push(StmtTrace::Sort(a));
      Ok(new_id)
    }
  }

  pub fn add_term(&mut self, a: AtomID, new: FileSpan, t: impl FnOnce() -> Term) -> AddItemResult<TermID> {
    let new_id = TermID(self.terms.len().try_into().map_err(|_| AddItemError::Overflow)?);
    let data = &mut self.data[a];
    if let Some(key) = data.decl {
      let (res, sp) = match key {
        DeclKey::Term(old_id) => {
          let ref sp = self.terms[old_id].span;
          if *sp == new { return Ok(old_id) }
          (Some(old_id), sp)
        }
        DeclKey::Thm(old_id) => (None, &self.thms[old_id].span)
      };
      Err(AddItemError::Redeclaration(res, RedeclarationError {
        msg: format!("term '{}' redeclared", data.name),
        othermsg: "previously declared here".to_owned(),
        other: sp.clone()
      }))
    } else {
      data.decl = Some(DeclKey::Term(new_id));
      self.terms.push(t());
      self.stmts.push(StmtTrace::Decl(a));
      Ok(new_id)
    }
  }

  pub fn add_thm(&mut self, a: AtomID, new: FileSpan, t: impl FnOnce() -> Thm) -> AddItemResult<ThmID> {
    let new_id = ThmID(self.thms.len().try_into().map_err(|_| AddItemError::Overflow)?);
    let data = &mut self.data[a];
    if let Some(key) = data.decl {
      let (res, sp) = match key {
        DeclKey::Thm(old_id) => {
          let ref sp = self.thms[old_id].span;
          if *sp == new { return Ok(old_id) }
          (Some(old_id), sp)
        }
        DeclKey::Term(old_id) => (None, &self.terms[old_id].span)
      };
      Err(AddItemError::Redeclaration(res, RedeclarationError {
        msg: format!("theorem '{}' redeclared", data.name),
        othermsg: "previously declared here".to_owned(),
        other: sp.clone()
      }))
    } else {
      data.decl = Some(DeclKey::Thm(new_id));
      self.thms.push(t());
      self.stmts.push(StmtTrace::Decl(a));
      Ok(new_id)
    }
  }

  pub fn add_coe(&mut self, s1: SortID, s2: SortID, fsp: FileSpan, t: TermID) -> Result<(), ElabError> {
    self.pe.add_coe(fsp.span, &self.sorts, s1, s2, fsp, t)
  }

  pub fn get_atom(&mut self, s: &str) -> AtomID {
    match self.atoms.get(s) {
      Some(&a) => a,
      None => {
        let id = AtomID(self.data.len().try_into().expect("too many atoms"));
        let s: ArcString = s.into();
        self.atoms.insert(s.clone(), id);
        self.data.push(AtomData::new(s));
        id
      }
    }
  }
  pub fn get_atom_arc(&mut self, s: ArcString) -> AtomID {
    let ctx = &mut self.data;
    *self.atoms.entry(s.clone()).or_insert_with(move ||
      (AtomID(ctx.len().try_into().expect("too many atoms")), ctx.push(AtomData::new(s))).0)
  }

  pub fn merge(&mut self, other: &Self, sp: Span, errors: &mut Vec<ElabError>) -> Result<(), ElabError> {
    if self.stmts.is_empty() { return Ok(*self = other.clone()) }
    let lisp_remap = &mut LispRemapper {
      atom: other.data.iter().map(|d| self.get_atom_arc(d.name.clone())).collect(),
      lisp: Default::default(),
    };
    for (i, d) in other.data.iter().enumerate() {
      self.data[lisp_remap.atom[AtomID(i as u32)]].lisp =
        d.lisp.as_ref().map(|(fs, v)| (fs.clone(), v.remap(lisp_remap)))
    }
    let remap = &mut Remapper::default();
    for &s in &other.stmts {
      match s {
        StmtTrace::Sort(a) => {
          let i = other.data[a].sort.unwrap();
          let ref sort = other.sorts[i];
          let id = match self.add_sort(a.remap(lisp_remap), sort.span.clone(), sort.mods) {
            Ok(id) => id,
            Err(AddItemError::Redeclaration(id, r)) => {
              errors.push(ElabError::with_info(sp, r.msg.into(), vec![
                (sort.span.clone(), r.othermsg.clone().into()),
                (r.other, r.othermsg.into())
              ]));
              id
            }
            Err(AddItemError::Overflow) => Err(ElabError::new_e(sp, "too many sorts"))?
          };
          if i != id { remap.sort.insert(i, id); }
        }
        StmtTrace::Decl(a) => match other.data[a].decl.unwrap() {
          DeclKey::Term(i) => {
            let ref o = other.terms[i];
            let id = match self.add_term(a.remap(lisp_remap), o.span.clone(), || o.remap(remap)) {
              Ok(id) => id,
              Err(AddItemError::Redeclaration(id, r)) => {
                let e = ElabError::with_info(sp, r.msg.into(), vec![
                  (o.span.clone(), r.othermsg.clone().into()),
                  (r.other, r.othermsg.into())
                ]);
                match id { None => Err(e)?, Some(id) => {errors.push(e); id} }
              }
              Err(AddItemError::Overflow) => Err(ElabError::new_e(sp, "too many terms"))?
            };
            if i != id { remap.term.insert(i, id); }
          }
          DeclKey::Thm(i) => {
            let ref o = other.thms[i];
            let id = match self.add_thm(a.remap(lisp_remap), o.span.clone(), || o.remap(remap)) {
              Ok(id) => id,
              Err(AddItemError::Redeclaration(id, r)) => {
                let e = ElabError::with_info(sp, r.msg.into(), vec![
                  (o.span.clone(), r.othermsg.clone().into()),
                  (r.other, r.othermsg.into())
                ]);
                match id { None => Err(e)?, Some(id) => {errors.push(e); id} }
              }
              Err(AddItemError::Overflow) => Err(ElabError::new_e(sp, "too many theorems"))?
            };
            if i != id { remap.thm.insert(i, id); }
          }
        }
      }
    }
    self.pe.merge(&other.pe, remap, sp, &self.sorts, errors);
    Ok(())
  }

  pub fn check_term_nargs(&self, sp: Span, term: TermID, nargs: usize) -> Result<(), ElabError> {
    let ref t = self.terms[term];
    if t.args.len() == nargs { return Ok(()) }
    Err(ElabError::with_info(sp, "incorrect number of arguments".into(),
      vec![(t.span.clone(), "declared here".into())]))
  }
}
