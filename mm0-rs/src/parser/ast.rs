use std::sync::Arc;
use num::BigUint;
use crate::lined_string::LinedString;
use super::ParseError;

pub type Span = std::ops::Range<usize>;

bitflags! {
  pub struct Modifiers: u8 {
    const PURE = 1;
    const STRICT = 2;
    const PROVABLE = 4;
    const FREE = 8;

    const PUB = 16;
    const ABSTRACT = 32;
    const LOCAL = 64;
  }
}

impl Modifiers {
  pub fn sort_data() -> Modifiers {
    Modifiers::PURE | Modifiers::STRICT | Modifiers::PROVABLE | Modifiers::FREE
  }
  pub fn allowed_visibility(self, k: DeclKind) -> bool {
    match k {
      DeclKind::Term => self.is_empty(),
      DeclKind::Axiom => self.is_empty(),
      DeclKind::Def => self == Modifiers::ABSTRACT || self == Modifiers::LOCAL || self.is_empty(),
      DeclKind::Theorem => self == Modifiers::PUB || self.is_empty(),
    }
  }
  pub fn from_name(s: &str) -> Option<Modifiers> {
    match s {
      "pure" => Some(Modifiers::PURE),
      "strict" => Some(Modifiers::STRICT),
      "provable" => Some(Modifiers::PROVABLE),
      "free" => Some(Modifiers::FREE),
      "pub" => Some(Modifiers::PUB),
      "abstract" => Some(Modifiers::ABSTRACT),
      "local" => Some(Modifiers::LOCAL),
      _ => None
    }
  }
}

pub enum Delimiter {
  Both(Formula),
  LeftRight(Formula, Formula),
}

#[derive(Clone)]
pub struct Formula(pub Span);
impl Formula {
  pub fn inner(&self) -> Span { self.0.start + 1 .. self.0.end - 1 }
}

#[derive(Clone)]
pub struct Const {
  pub fmla: Formula,
  pub trim: Span
}

#[derive(Clone, Copy)]
pub enum DeclKind { Term, Axiom, Theorem, Def }

#[derive(Clone, Copy)]
pub enum LocalKind { Bound, Reg, Dummy, Anon }

#[derive(Clone)]
pub struct DepType {
  pub sort: Span,
  pub deps: Vec<Span>,
}
#[derive(Clone)]
pub enum Type {
  DepType(DepType),
  Formula(Formula)
}
pub struct Binder {
  pub span: Span,
  pub local: (Span, LocalKind),
  pub ty: Option<Type>,
}

pub struct SExpr {
  pub span: Span,
  pub k: SExprKind,
}
pub enum Atom { Ident, Quote, Unquote }
pub enum SExprKind {
  Atom(Atom),
  List(bool, bool, Vec<SExpr>),
  Number(BigUint),
  String(String),
  Bool(bool),
  Formula(Formula),
}
impl SExpr {
  pub fn atom(span: Span, a: Atom) -> SExpr {
    SExpr {span, k: SExprKind::Atom(a)}
  }
  pub fn list(span: Span, dotted: bool, curly: bool, es: Vec<SExpr>) -> SExpr {
    SExpr {span, k: SExprKind::List(dotted, curly, es)}
  }
}

pub struct Decl {
  pub mods: Modifiers,
  pub k: DeclKind,
  pub id: Span,
  pub bis: Vec<Binder>,
  pub ty: Option<Vec<Type>>,
  pub val: Option<SExpr>,
}

pub enum Prec { Prec(u32), Max }
pub enum SimpleNotaKind { Prefix, Infix {right: bool} }
pub struct SimpleNota {
  pub k: SimpleNotaKind,
  pub id: Span,
  pub c: Const,
  pub prec: Prec,
}

pub enum Literal {
  Const(Const, Prec),
  Var(Span),
}

pub struct GenNota {
  pub id: Span,
  pub bis: Vec<Binder>,
  pub ty: Option<Type>,
  pub lits: Vec<Literal>,
  pub prec: Option<(Prec, bool)>
}

pub enum StmtKind {
  Sort(Span, Modifiers),
  Decl(Decl),
  Delimiter(Delimiter),
  SimpleNota(SimpleNota),
  Coercion { id: Span, from: Span, to: Span },
  Notation(GenNota),
  Inout { out: bool, k: Span, hs: Vec<SExpr> },
  Annot(SExpr, Box<Stmt>),
  Do(Vec<SExpr>),
  Import(Span, String),
}

pub struct Stmt {
  pub span: Span,
  pub k: StmtKind,
}

pub struct AST {
  pub source: Arc<LinedString>,
  pub imports: Vec<(Span, String)>,
  pub stmts: Vec<Stmt>,
  pub errors: Vec<ParseError>,
}

impl AST {
  pub fn _span(&self, s: Span) -> &str {
    unsafe { std::str::from_utf8_unchecked(&self.source.as_bytes()[s]) }
  }

  pub fn last_checkpoint(&self, pos: usize) -> (usize, usize) {
    match self.stmts.binary_search_by_key(&pos, |stmt| stmt.span.end) {
      Ok(i) => (i+1, pos),
      Err(0) => (0, 0),
      Err(i) => (i, self.stmts[i-1].span.end)
    }
  }
}