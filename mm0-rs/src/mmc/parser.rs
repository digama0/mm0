use std::mem;
use std::sync::Arc;
use std::collections::HashMap;
use num::BigInt;
use crate::util::{Span, FileSpan};
use crate::elab::{
  Result, Elaborator, ElabError,
  environment::{AtomID, Environment},
  lisp::{LispKind, LispVal, Uncons},
  local_context::try_get_span};

pub struct Arg {
  pub name: Option<(FileSpan, AtomID)>,
  pub ghost: bool,
  pub ty: LispVal,
}

impl PartialEq<Arg> for Arg {
  fn eq(&self, other: &Arg) -> bool {
    let b = match (&self.name, &other.name) {
      (None, None) => true,
      (&Some((_, a)), &Some((_, b))) => a == b,
      _ => false
    };
    b && self.ghost == other.ghost && self.ty == other.ty
  }
}
impl Eq for Arg {}

#[derive(PartialEq, Eq)]
pub enum VariantType {
  Down,
  UpLt(LispVal),
  UpLe(LispVal)
}
pub type Variant = Option<(LispVal, VariantType)>;

pub struct Invariant {
  pub name: AtomID,
  pub ghost: bool,
  pub ty: Option<LispVal>,
  pub val: Option<Expr>,
}

pub struct Block {
  pub muts: Box<[AtomID]>,
  pub stmts: Box<[Expr]>
}

pub enum TuplePattern {
  Name(AtomID, Option<FileSpan>),
  Typed(Box<TuplePattern>, LispVal),
  Tuple(Box<[TuplePattern]>),
}

pub enum Pattern {
  VarOrConst(AtomID),
  Number(BigInt),
  Hyped(AtomID, Box<Pattern>),
  With(Box<(Pattern, Expr)>),
  Or(Box<[Pattern]>),
}

pub enum Expr {
  Nil,
  Var(AtomID),
  Number(BigInt),
  Let {ghost: bool, lhs: TuplePattern, rhs: Option<Box<Expr>>},
  Call(AtomID, Box<[Expr]>, Variant),
  Entail(LispVal, Box<[Expr]>),
  Block(Block),
  Label(AtomID, Box<[Arg]>, Variant, Block),
  If(Box<(Expr, Expr, Expr)>),
  Switch(Box<Expr>, Box<[(Pattern, Expr)]>),
  While {hyp: Option<AtomID>, cond: Box<Expr>, var: Variant, invar: Box<[Invariant]>, body: Block},
  Hole(FileSpan),
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum ProcKind { Func, Proc, ProcDecl, Intrinsic }
pub struct Proc {
  pub kind: ProcKind,
  pub name: AtomID,
  pub span: Option<FileSpan>,
  pub args: Box<[Arg]>,
  pub rets: Box<[Arg]>,
  pub variant: Variant,
  pub body: Block,
}

impl Proc {
  pub fn eq_decl(&self, other: &Proc) -> bool {
    self.name == other.name &&
    self.args == other.args &&
    self.rets == other.rets &&
    self.variant == other.variant &&
    self.body.muts == other.body.muts
  }
}

pub struct Field {
  pub name: AtomID,
  pub ghost: bool,
  pub ty: LispVal,
}

pub enum AST {
  Proc(Arc<Proc>),
  Global {lhs: TuplePattern, rhs: Option<Box<Expr>>},
  Const {lhs: TuplePattern, rhs: Box<Expr>},
  Typedef(AtomID, Option<FileSpan>, Box<[Arg]>, LispVal),
  Struct(AtomID, Option<FileSpan>, Box<[Arg]>, Box<[Field]>),
}

impl AST {
  pub fn proc(p: Proc) -> AST { AST::Proc(Arc::new(p)) }
}
macro_rules! make_keywords {
  {$($x:ident: $e:expr,)*} => {
    #[derive(Debug, PartialEq, Eq, Copy, Clone)]
    pub enum Keyword { $($x),* }

    impl Environment {
      pub fn make_keywords(&mut self) -> HashMap<AtomID, Keyword> {
        let mut atoms = HashMap::new();
        $(atoms.insert(self.get_atom($e), Keyword::$x);)*
        atoms
      }
    }
  }
}

make_keywords! {
  Add: "+",
  Arrow: "=>",
  Begin: "begin",
  Colon: ":",
  ColonEq: ":=",
  Const: "const",
  Entail: "entail",
  Func: "func",
  Finish: "finish",
  Ghost: "ghost",
  Global: "global",
  Intrinsic: "intrinsic",
  Invariant: "invariant",
  If: "if",
  Le: "<=",
  Lt: "<",
  Mut: "mut",
  Or: "or",
  Proc: "proc",
  Struct: "struct",
  Switch: "switch",
  Typedef: "typedef",
  Variant: "variant",
  While: "while",
  With: "with",
}

pub struct Parser<'a> {
  pub elab: &'a mut Elaborator,
  pub kw: &'a HashMap<AtomID, Keyword>,
  pub fsp: FileSpan,
}

fn head_atom(e: &LispVal) -> Option<(AtomID, Uncons)> {
  let mut u = Uncons::from(e.clone());
  Some((u.next()?.as_atom()?, u))
}

impl<'a> Parser<'a> {
  fn try_get_span(&self, e: &LispVal) -> Span {
    try_get_span(&self.fsp, &e)
  }
  fn try_get_fspan(&self, e: &LispVal) -> FileSpan {
    FileSpan { file: self.fsp.file.clone(), span: self.try_get_span(e) }
  }

  fn head_keyword(&self, e: &LispVal) -> Option<(Keyword, Uncons)> {
    let mut u = Uncons::from(e.clone());
    Some((*self.kw.get(&u.next()?.as_atom()?)?, u))
  }

  fn parse_variant(&self, e: &LispVal) -> Option<(LispVal, VariantType)> {
    if let Some((Keyword::Variant, mut u)) = self.head_keyword(e) {
      Some((u.next()?, match u.next() {
        None => VariantType::Down,
        Some(e) => match *self.kw.get(&e.as_atom()?)? {
          Keyword::Lt => VariantType::UpLt(u.next()?),
          Keyword::Le => VariantType::UpLe(u.next()?),
          _ => None?
        }
      }))
    } else {None}
  }

  fn parse_arg1(&self, e: LispVal, ghost: bool) -> Result<Arg> {
    if let Some((AtomID::COLON, mut u)) = head_atom(&e) {
      match (u.next(), u.next(), u.exactly(0)) {
        (Some(ea), Some(ty), true) => {
          let a = ea.as_atom().ok_or_else(||
            ElabError::new_e(self.try_get_span(&ea), "argument syntax error: expecting function name"))?;
          let name = if a == AtomID::UNDER {None} else {
            Some((self.try_get_fspan(&ea), a))
          };
          Ok(Arg { ghost, name, ty })
        }
        _ => Err(ElabError::new_e(self.try_get_span(&e), "syntax error in function arg"))?
      }
    } else {Ok(Arg { ghost, name: None, ty: e })}
  }

  fn parse_arg(&self, e: LispVal, args: &mut Vec<Arg>, muts: Option<&mut Vec<AtomID>>) -> Result<()> {
    Ok(match (self.head_keyword(&e), muts) {
      (Some((Keyword::Ghost, u)), _) => for e in u {
        args.push(self.parse_arg1(e, true)?)
      }
      (Some((Keyword::Mut, u)), Some(muts)) => for e in u {
        muts.push(e.as_atom().ok_or_else(||
          ElabError::new_e(self.try_get_span(&e), "mut: expected an atom"))?)
      }
      _ => args.push(self.parse_arg1(e, false)?)
    })
  }

  fn parse_tuple_pattern(&self, e: LispVal) -> Result<TuplePattern> {
    Ok(match &*e.unwrapped_arc() {
      &LispKind::Atom(a) => TuplePattern::Name(a, e.fspan()),
      LispKind::List(_) | LispKind::DottedList(_, _) => {
        if let Some((Keyword::Colon, mut u)) = self.head_keyword(&e) {
          if let (Some(e), Some(ty), true) = (u.next(), u.next(), u.exactly(0)) {
            return Ok(TuplePattern::Typed(Box::new(self.parse_tuple_pattern(e)?), ty))
          }
          Err(ElabError::new_e(self.try_get_span(&e), "':' syntax error"))?
        }
        let mut args = vec![];
        for e in Uncons::from(e) {args.push(self.parse_tuple_pattern(e)?)}
        TuplePattern::Tuple(args.into_boxed_slice())
      }
      _ => Err(ElabError::new_e(self.try_get_span(&e),
        format!("tuple pattern syntax error: {}", self.elab.print(&e))))?
    })
  }

  fn parse_pattern(&self, e: LispVal) -> Result<Pattern> {
    Ok(match &*e.unwrapped_arc() {
      &LispKind::Atom(a) => Pattern::VarOrConst(a),
      LispKind::List(_) | LispKind::DottedList(_, _) => match self.head_keyword(&e) {
        Some((Keyword::Colon, mut u)) =>
          if let (Some(h), Some(p), true) = (u.next(), u.next(), u.exactly(0)) {
            let h = h.as_atom().ok_or_else(||
              ElabError::new_e(self.try_get_span(&h), "expecting hypothesis name"))?;
            Pattern::Hyped(h, Box::new(self.parse_pattern(p)?))
          } else {
            Err(ElabError::new_e(self.try_get_span(&e), "':' syntax error"))?
          },
        Some((Keyword::Or, u)) => {
          let mut args = vec![];
          for e in u {args.push(self.parse_pattern(e)?)}
          Pattern::Or(args.into_boxed_slice())
        }
        Some((Keyword::With, mut u)) =>
          if let (Some(p), Some(g), true) = (u.next(), u.next(), u.exactly(0)) {
            Pattern::With(Box::new((self.parse_pattern(p)?, self.parse_expr(g)?)))
          } else {
            Err(ElabError::new_e(self.try_get_span(&e), "'with' syntax error"))?
          },
        _ => Err(ElabError::new_e(self.try_get_span(&e), "pattern syntax error"))?
      }
      LispKind::Number(n) => Pattern::Number(n.clone()),
      _ => Err(ElabError::new_e(self.try_get_span(&e), "pattern syntax error"))?
    })
  }

  fn parse_decl(&self, e: LispVal) -> Result<(TuplePattern, Option<Box<Expr>>)> {
    if let Some((Keyword::ColonEq, mut u)) = self.head_keyword(&e) {
      if let (Some(lhs), Some(rhs), true) = (u.next(), u.next(), u.exactly(0)) {
        Ok((self.parse_tuple_pattern(lhs)?, Some(Box::new(self.parse_expr(rhs)?))))
      } else {
        Err(ElabError::new_e(self.try_get_span(&e), "decl: syntax error"))
      }
    } else {
      Ok((self.parse_tuple_pattern(e)?, None))
    }
  }

  fn parse_invariant_decl(&self, ghost: bool, e: LispVal) -> Result<Invariant> {
    match self.parse_decl(e.clone())? {
      (TuplePattern::Typed(v, ty), val) => if let TuplePattern::Name(name, _) = *v {
        return Ok(Invariant {name, ghost, ty: Some(ty), val: val.map(|v| *v)})
      },
      (TuplePattern::Name(name, _), val) =>
        return Ok(Invariant {name, ghost, ty: None, val: val.map(|v| *v)}),
      _ => {}
    }
    Err(ElabError::new_e(self.try_get_span(&e), "while: unexpected invariant"))
  }

  fn parse_expr(&self, e: LispVal) -> Result<Expr> {
    Ok(match &*e.unwrapped_arc() {
      &LispKind::Atom(AtomID::UNDER) => Expr::Hole(self.try_get_fspan(&e)),
      &LispKind::Atom(a) => Expr::Var(a),
      LispKind::List(_) | LispKind::DottedList(_, _) => match self.head_keyword(&e) {
        Some((Keyword::Ghost, mut u)) =>
          if let (Some(e), true) = (u.next(), u.exactly(0)) {
            let (lhs, rhs) = self.parse_decl(e)?;
            Expr::Let {ghost: true, lhs, rhs}
          } else {
            Err(ElabError::new_e(self.try_get_span(&e), "ghost: syntax error"))?
          },
        Some((Keyword::Colon, _)) |
        Some((Keyword::ColonEq, _)) => {
          let (lhs, rhs) = self.parse_decl(e)?;
          Expr::Let {ghost: false, lhs, rhs}
        }
        Some((Keyword::If, mut u)) =>
          if let (Some(c), Some(t)) = (u.next(), u.next()) {
            let (c, t) = (self.parse_expr(c)?, self.parse_expr(t)?);
            Expr::If(Box::new((c, t, match u.next() {
              Some(f) if u.exactly(0) => self.parse_expr(f)?,
              None => Expr::Nil,
              _ => Err(ElabError::new_e(self.try_get_span(&e), "if: syntax error"))?,
            })))
          } else {
            Err(ElabError::new_e(self.try_get_span(&e), "if: syntax error"))?
          },
        Some((Keyword::Switch, mut u)) => {
          let c = self.parse_expr(u.next().ok_or_else(||
            ElabError::new_e(self.try_get_span(&e), "switch: syntax error"))?)?;
          let mut branches = vec![];
          for e in u {
            if let Some((Keyword::Arrow, mut u)) = self.head_keyword(&e) {
              if let (Some(p), Some(e), true) = (u.next(), u.next(), u.exactly(0)) {
                branches.push((self.parse_pattern(p)?, self.parse_expr(e)?));
              } else {
                Err(ElabError::new_e(self.try_get_span(&e), "switch: syntax error"))?
              }
            } else {
              Err(ElabError::new_e(self.try_get_span(&e), "switch: syntax error"))?
            }
          }
          Expr::Switch(Box::new(c), branches.into_boxed_slice())
        }
        Some((Keyword::While, mut u)) => {
          let c = u.next().ok_or_else(||
            ElabError::new_e(self.try_get_span(&e), "while: syntax error"))?;
          let (hyp, c) = if let Some((Keyword::Invariant, mut u)) = self.head_keyword(&c) {
            if let (Some(h), Some(c), true) = (u.next().and_then(|a| a.as_atom()), u.next(), u.exactly(0)) {
              (Some(h), c)
            } else {
              Err(ElabError::new_e(self.try_get_span(&e), "while: bad pattern"))?
            }
          } else {(None, c)};
          let c = self.parse_expr(c)?;
          let mut invar = vec![];
          let mut muts = vec![];
          let mut var = None;
          let mut body = vec![];
          while let Some(e) = u.next() {
            if let Some(v) = self.parse_variant(&e) {
              if mem::replace(&mut var, Some(v)).is_some() {
                Err(ElabError::new_e(self.try_get_span(&e), "while: two variants"))?
              }
            } else if let Some((Keyword::Invariant, u)) = self.head_keyword(&e) {
              for e in u {
                match self.head_keyword(&e) {
                  Some((Keyword::Mut, u)) => for e in u {
                    muts.push(e.as_atom().ok_or_else(||
                      ElabError::new_e(self.try_get_span(&e), "mut: expected an atom"))?)
                  },
                  Some((Keyword::Ghost, u)) => for e in u {
                    invar.push(self.parse_invariant_decl(true, e)?)
                  },
                  _ => invar.push(self.parse_invariant_decl(false, e)?),
                }
              }
            } else {
              body.push(self.parse_expr(e)?);
              break
            }
          }
          for e in u {body.push(self.parse_expr(e)?)}
          Expr::While {
            hyp, cond: Box::new(c), var,
            invar: invar.into_boxed_slice(),
            body: Block { muts: muts.into(), stmts: body.into_boxed_slice() }
          }
        }
        Some((Keyword::Begin, mut u)) => {
          let mut muts = vec![];
          let mut body = vec![];
          while let Some(e) = u.next() {
            if let Some((Keyword::Mut, u)) = self.head_keyword(&e) {
              for e in u {
                muts.push(e.as_atom().ok_or_else(||
                  ElabError::new_e(self.try_get_span(&e), "mut: expected an atom"))?)
              }
            } else {
              body.push(self.parse_expr(e)?);
              break
            }
          }
          for e in u {body.push(self.parse_expr(e)?)}
          Expr::Block(Block {muts: muts.into(), stmts: body.into_boxed_slice()})
        }
        Some((Keyword::Entail, mut u)) => {
          let mut last = u.next().ok_or_else(||
            ElabError::new_e(self.try_get_span(&e), "entail: expected proof"))?;
          let mut args = vec![];
          for e in u {
            args.push(self.parse_expr(mem::replace(&mut last, e))?)
          }
          Expr::Entail(last, args.into_boxed_slice())
        }
        _ => {
          let mut u = Uncons::from(e);
          match u.next() {
            None => Expr::Nil,
            Some(e) => match self.head_keyword(&e) {
              Some((Keyword::Begin, mut u1)) => {
                let name = u1.next().and_then(|e| e.as_atom()).ok_or_else(||
                  ElabError::new_e(self.try_get_span(&e), "label: expected label name"))?;
                let mut args = vec![];
                let mut muts = vec![];
                let mut variant = None;
                for e in u1 {
                  if let Some(v) = self.parse_variant(&e) {
                    if mem::replace(&mut variant, Some(v)).is_some() {
                      Err(ElabError::new_e(self.try_get_span(&e), "label: two variants"))?
                    }
                  } else {
                    self.parse_arg(e, &mut args, Some(&mut muts))?
                  }
                }
                let mut body = vec![];
                for e in u {body.push(self.parse_expr(e)?)}
                Expr::Label(name, args.into(), variant,
                  Block {muts: muts.into(), stmts: body.into_boxed_slice()})
              }
              _ => {
                let f = e.as_atom().ok_or_else(||
                  ElabError::new_e(self.try_get_span(&e), "only variables can be called like functions"))?;
                let mut args = vec![];
                let mut variant = None;
                for e in u {
                  if let Some(v) = self.parse_variant(&e) {
                    if mem::replace(&mut variant, Some(v)).is_some() {
                      Err(ElabError::new_e(self.try_get_span(&e), "call: two variants"))?
                    }
                  } else {
                    args.push(self.parse_expr(e)?)
                  }
                }
                Expr::Call(f, args.into_boxed_slice(), variant)
              }
            }
          }
        }
      },
      LispKind::Number(n) => Expr::Number(n.clone()),
      _ => Err(ElabError::new_e(self.try_get_span(&e), "unknown expression"))?
    })
  }

  fn parse_proc(&self, mut kind: ProcKind, mut u: Uncons) -> Result<Proc> {
    let e = match u.next() {
      None => return Err(ElabError::new_e(self.try_get_span(&u.as_lisp()), "func/proc: syntax error")),
      Some(e) => e,
    };
    let mut muts = vec![];
    let mut args = vec![];
    let mut rets = vec![];
    let (name, span) = match &*e.unwrapped_arc() {
      &LispKind::Atom(a) => (a, e.fspan()),
      LispKind::List(_) | LispKind::DottedList(_, _) => {
        let mut u = Uncons::from(e.clone());
        let e = u.next().ok_or_else(||
          ElabError::new_e(self.try_get_span(&e), "func/proc syntax error: expecting function name"))?;
        let name = e.as_atom().ok_or_else(||
          ElabError::new_e(self.try_get_span(&e), "func/proc syntax error: expecting an atom"))?;
        while let Some(e) = u.next() {
          if let Some(AtomID::COLON) = e.as_atom() { break }
          self.parse_arg(e, &mut args, Some(&mut muts))?
        }
        while let Some(e) = u.next() { self.parse_arg(e, &mut rets, None)? }
        (name, e.fspan())
      },
      _ => Err(ElabError::new_e(self.try_get_span(&e), "func/proc: syntax error"))?
    };
    let mut body = vec![];
    Ok(Proc {
      name, span,
      args: args.into_boxed_slice(),
      rets: rets.into_boxed_slice(),
      variant: if let Some(e) = u.next() {
        match kind {
          ProcKind::Intrinsic => Err(ElabError::new_e(self.try_get_span(&e), "intrinsic: unexpected body"))?,
          ProcKind::ProcDecl => kind = ProcKind::Proc,
          _ => {}
        }
        let v = self.parse_variant(&e);
        if v.is_none() {body.push(self.parse_expr(e)?)}
        for e in u {body.push(self.parse_expr(e)?)}
        v
      } else {None},
      kind,
      body: Block {muts: muts.into(), stmts: body.into_boxed_slice()}
    })
  }

  fn parse_name_and_args(&self, e: LispVal) -> Result<(AtomID, Option<FileSpan>, Vec<Arg>)> {
    let mut args = vec![];
    let (name, sp) = match &*e.unwrapped_arc() {
      &LispKind::Atom(a) => (a, e.fspan()),
      LispKind::List(_) | LispKind::DottedList(_, _) => {
        let mut u = Uncons::from(e.clone());
        let e = u.next().ok_or_else(|| ElabError::new_e(self.try_get_span(&e), "typedef: syntax error"))?;
        let a = e.as_atom().ok_or_else(|| ElabError::new_e(self.try_get_span(&e), "typedef: expected an atom"))?;
        for e in u { self.parse_arg(e, &mut args, None)? }
        (a, e.fspan())
      },
      _ => Err(ElabError::new_e(self.try_get_span(&e), "typedef: syntax error"))?
    };
    Ok((name, sp, args))
  }

  fn parse_field(&self, ghost: bool, e: LispVal) -> Result<Field> {
    if let Some((Keyword::Colon, mut u)) = self.head_keyword(&e) {
      if let (Some(name), Some(ty), true) = (u.next().and_then(|e| e.as_atom()), u.next(), u.exactly(0)) {
        Ok(Field {ghost, name, ty})
      } else {
        Err(ElabError::new_e(self.try_get_span(&e), "struct: syntax error"))?
      }
    } else {
      Err(ElabError::new_e(self.try_get_span(&e), "struct: syntax error"))?
    }
  }

  pub fn parse_ast(&self, ast: &mut Vec<AST>, e: &LispVal) -> Result<()> {
    let mut u = Uncons::from(e.clone());
    while let Some(e) = u.next() {
      match self.head_keyword(&e) {
        Some((Keyword::Proc, u)) => ast.push(AST::proc(self.parse_proc(ProcKind::ProcDecl, u)?)),
        Some((Keyword::Func, u)) => ast.push(AST::proc(self.parse_proc(ProcKind::Func, u)?)),
        Some((Keyword::Intrinsic, u)) => ast.push(AST::proc(self.parse_proc(ProcKind::Intrinsic, u)?)),
        Some((Keyword::Global, u)) => for e in u {
          let (lhs, rhs) = self.parse_decl(e)?;
          ast.push(AST::Global {lhs, rhs})
        },
        Some((Keyword::Const, u)) => for e in u {
          if let (lhs, Some(rhs)) = self.parse_decl(e.clone())? {
            ast.push(AST::Const {lhs, rhs})
          } else {
            Err(ElabError::new_e(self.try_get_span(&e), "const: definition is required"))?
          }
        },
        Some((Keyword::Typedef, mut u)) =>
          if let (Some(e), Some(ty), true) = (u.next(), u.next(), u.exactly(0)) {
            let (name, sp, args) = self.parse_name_and_args(e)?;
            ast.push(AST::Typedef(name, sp, args.into_boxed_slice(), ty));
          } else {
            Err(ElabError::new_e(self.try_get_span(&e), "typedef: syntax error"))?
          },
        Some((Keyword::Struct, mut u)) => {
          let e = u.next().ok_or_else(||
            ElabError::new_e(self.try_get_span(&e), "struct: expecting name"))?;
          let (name, sp, args) = self.parse_name_and_args(e)?;
          let mut fields = vec![];
          for e in u {
            if let Some((Keyword::Ghost, u)) = self.head_keyword(&e) {
              for e in u {fields.push(self.parse_field(true, e)?)}
            }
            fields.push(self.parse_field(false, e)?);
          }
          ast.push(AST::Struct(name, sp, args.into_boxed_slice(), fields.into_boxed_slice()));
        }
        _ => Err(ElabError::new_e(self.try_get_span(&e), "MMC: unknown top level item"))?
      }
    }
    if !u.exactly(0) {
      Err(ElabError::new_e(self.try_get_span(&e), "MMC: syntax error"))?
    }
    Ok(())
  }
}
