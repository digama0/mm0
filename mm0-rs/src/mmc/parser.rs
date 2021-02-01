//! The MMC parser, which takes lisp literals and maps them to MMC AST.
use std::mem;
use std::collections::HashMap;
use num::BigInt;
use crate::util::{Span, FileSpan};
use crate::elab::{Result, ElabError,
  environment::AtomId,
  lisp::{LispKind, LispVal, Uncons, print::FormatEnv},
  local_context::{try_get_span, try_get_span_from}};
use super::types::{Ast, Keyword, Proc, ProcKind,
  Variant, VariantType};

/// A tuple pattern, which destructures the results of assignments from functions with
/// mutiple return values, as well as explicit tuple values and structs.
#[derive(Debug, DeepSizeOf)]
pub enum TuplePattern {
  /// A variable binding, or `_` for an ignored binding. The `bool` is true if the variable
  /// is ghost.
  Name(bool, AtomId, Option<FileSpan>),
  /// A type ascription. The type is unparsed.
  Typed(Box<TuplePattern>, LispVal),
  /// A tuple, with the given arguments.
  Tuple(Box<[TuplePattern]>, Option<FileSpan>),
}

enum MutOut { None, Mut, Out(AtomId) }

impl TuplePattern {
  /// The `_` tuple pattern. This is marked as ghost because it can't be referred to so
  /// it is always safe to make irrelevant.
  pub const UNDER: TuplePattern = TuplePattern::Name(true, AtomId::UNDER, None);

  /// The name of a variable binding (or `_` for a tuple pattern)
  #[must_use] pub fn name(&self) -> AtomId {
    match self {
      &TuplePattern::Name(_, a, _) => a,
      TuplePattern::Typed(p, _) => p.name(),
      _ => AtomId::UNDER
    }
  }

  /// The span of a variable binding or tuple pattern.
  #[must_use] pub fn fspan(&self) -> Option<&FileSpan> {
    match self {
      TuplePattern::Name(_, _, fsp) |
      TuplePattern::Tuple(_, fsp) => fsp.as_ref(),
      TuplePattern::Typed(p, _) => p.fspan(),
    }
  }

  /// True if all the bindings in this pattern are ghost.
  #[must_use] pub fn ghost(&self) -> bool {
    match self {
      &TuplePattern::Name(g, _, _) => g,
      TuplePattern::Typed(p, _) => p.ghost(),
      TuplePattern::Tuple(ps, _) => ps.iter().all(TuplePattern::ghost),
    }
  }

  /// The type of this binding, or `_` if there is no explicit type.
  #[must_use] pub fn ty(&self) -> LispVal {
    match self {
      TuplePattern::Typed(_, ty) => ty.clone(),
      _ => LispVal::atom(AtomId::UNDER)
    }
  }
}

impl PartialEq<TuplePattern> for TuplePattern {
  fn eq(&self, other: &TuplePattern) -> bool {
    match (self, other) {
      (TuplePattern::Name(g1, a1, _), TuplePattern::Name(g2, a2, _)) => g1 == g2 && a1 == a2,
      (TuplePattern::Typed(p1, ty1), TuplePattern::Typed(p2, ty2)) => p1 == p2 && ty1 == ty2,
      (TuplePattern::Tuple(ps1, _), TuplePattern::Tuple(ps2, _)) => ps1 == ps2,
      _ => false
    }
  }
}
impl Eq for TuplePattern {}

/// A pattern, the left side of a switch statement.
#[derive(Debug)]
pub enum Pattern {
  /// A variable binding, unless this is the name of a constant in which case
  /// it is a constant value.
  VarOrConst(AtomId),
  /// A numeric literal.
  Number(BigInt),
  /// A hypothesis pattern, which binds the first argument to a proof that the
  /// scrutinee satisfies the pattern argument.
  Hyped(AtomId, Box<Pattern>),
  /// A pattern guard: Matches the inner pattern, and then if the expression returns
  /// true, this is also considered to match.
  With(Box<(Pattern, LispVal)>),
  /// A disjunction of patterns.
  Or(Box<[Pattern]>),
}

/// A rename is a `{old -> old'}` or `{new' <- new}` clause appearing in a `with`
/// associated to a let binding or assignment, as in `{{x <- 2} with {x -> x_old}}`.
#[derive(Clone, Copy, Debug)]
pub enum Rename {
  /// `{from -> to}` means that the variable `from` should be renamed to `to`
  /// (after evaluation of the main expression).
  Old {
    /** The original name of the variable */ from: AtomId,
    /** The new name of the variable */ to: AtomId
  },
  /// `{to <- from}` means that the new value of the variable `from` should be called `to`,
  /// so that the old value of variable `from` is available by that name.
  New {
    /** The original name of the variable */ from: AtomId,
    /** The new name of the variable */ to: AtomId
  },
}

/// An expression or statement. A block is a list of expressions.
#[derive(Debug)]
pub enum Expr {
  /// A `()` literal.
  Nil,
  /// A variable reference.
  Var(FileSpan, AtomId),
  /// A number literal.
  Number(BigInt),
  /// A let binding.
  Let {
    /// A tuple pattern, containing variable bindings.
    lhs: TuplePattern,
    /// The expression to evaluate.
    rhs: LispVal,
    /// The list of simultaneous variable renames.
    with: Vec<Rename>
  },
  /// An assignment / mutation.
  Assign {
    /// A place (lvalue) to write to.
    lhs: LispVal,
    /// The expression to evaluate.
    rhs: LispVal,
    /// The list of simultaneous variable renames.
    with: Vec<Rename>
  },
  /// A function call (or something that looks like one at parse time).
  Call {
    /// The function to call.
    f: AtomId,
    /// The span of `f`.
    fsp: Option<FileSpan>,
    /// The function arguments.
    args: Vec<LispVal>,
    /// The variant, if needed.
    variant: Option<LispVal>,
  },
  /// An entailment proof, which takes a proof of `P1 * ... * Pn => Q` and expressions proving
  /// `P1, ..., Pn` and is a hypothesis of type `Q`.
  Entail(LispVal, Box<[Expr]>),
  /// A block scope.
  Block(Uncons),
  /// A label, which looks exactly like a local function but has no independent stack frame.
  /// They are called like regular functions but can only appear in tail position.
  Label {
    /// The name of the label
    name: AtomId,
    /// The arguments of the label
    args: Box<[TuplePattern]>,
    /// The variant, for recursive calls
    variant: Option<Variant>,
    /// The code that is executed when you jump to the label
    body: Uncons,
  },
  /// An if-then-else expression (at either block or statement level). The initial atom names
  /// a hypothesis that the expression is true in one branch and false in the other.
  If {
    /// The list of variables that will be updated by each sub-block. Variables
    /// in external scope that are not in this list are treated as read only.
    muts: Box<[(AtomId, Option<FileSpan>)]>,
    /// The list of `(h,C,T)` triples in `if {h1 : C1} T1 if {h2 : C2} T2 else E`.
    branches: Box<[(Option<AtomId>, LispVal, LispVal)]>,
    /// The else case, the `E` in `if {h1 : C1} T1 if {h2 : C2} T2 else E`.
    els: LispVal
  },
  /// A switch (pattern match) statement, given the initial expression and a list of match arms.
  Switch(LispVal, Box<[(Pattern, LispVal)]>),
  /// A while loop.
  While {
    /// A hypothesis that the condition is true in the loop and false after it.
    hyp: Option<AtomId>,
    /// The loop condition.
    cond: LispVal,
    /// The variant, which must decrease on every round around the loop.
    var: Option<Variant>,
    /// The body of the loop.
    body: Uncons,
  },
  /// A hole `_`, which is a compile error but queries the compiler to provide a type context.
  Hole(FileSpan),
}

/// The parser, which has no real state of its own but needs access to the
/// formatting environment for printing, and the keyword list.
#[derive(Debug)]
pub struct Parser<'a> {
  /// The formatting environment.
  pub fe: FormatEnv<'a>,
  /// The keyword list.
  pub kw: &'a HashMap<AtomId, Keyword>,
  /// The base file span, for error reporting.
  pub fsp: FileSpan,
}

fn head_atom(e: &LispVal) -> Option<(AtomId, Uncons)> {
  let mut u = Uncons::from(e.clone());
  Some((u.next()?.as_atom()?, u))
}

/// Try to parse the head keyword of an expression `(KEYWORD args..)`,
/// and return the pair `(KEYWORD, args)` on success.
#[must_use] pub fn head_keyword<S: std::hash::BuildHasher>(
  kw: &HashMap<AtomId, Keyword, S>, e: &LispVal
) -> Option<(Keyword, Uncons)> {
  let mut u = Uncons::from(e.clone());
  u.next()?.unwrapped(|e| match *e {
    LispKind::Atom(a) => Some((*kw.get(&a)?, u)),
    LispKind::Syntax(s) => Some((Keyword::from_syntax(s)?, u)),
    _ => None
  })
}

impl<'a> Parser<'a> {
  fn try_get_span(&self, e: &LispVal) -> Span {
    try_get_span(&self.fsp, e)
  }
  fn try_get_fspan(&self, e: &LispVal) -> FileSpan {
    FileSpan { file: self.fsp.file.clone(), span: self.try_get_span(e) }
  }

  fn head_keyword(&self, e: &LispVal) -> Option<(Keyword, Uncons)> { head_keyword(self.kw, e) }

  fn parse_variant(&self, e: &LispVal) -> Option<(LispVal, VariantType)> {
    if let Some((Keyword::Variant, mut u)) = self.head_keyword(e) {
      Some((u.next()?, match u.next() {
        None => VariantType::Down,
        Some(e) => match self.kw.get(&e.as_atom()?) {
          Some(Keyword::Lt) => VariantType::UpLt(u.next()?),
          Some(Keyword::Le) => VariantType::UpLe(u.next()?),
          _ => return None
        }
      }))
    } else {None}
  }

  fn parse_arg1(&self, e: LispVal, name_required: bool) -> Result<TuplePattern> {
    if let Some((AtomId::COLON, _)) = head_atom(&e) {
      Ok(self.parse_tuple_pattern(false, e)?)
    } else if name_required {
      let a = e.as_atom().ok_or_else(||
        ElabError::new_e(self.try_get_span(&e), "argument syntax error: expecting identifier"))?;
      Ok(TuplePattern::Name(a == AtomId::UNDER, a,
        if a == AtomId::UNDER { None } else { Some(self.try_get_fspan(&e)) }))
    } else {
      Ok(TuplePattern::Typed(Box::new(TuplePattern::UNDER), e))
    }
  }

  fn parse_arg(&self, e: LispVal, name_required: bool,
    mut push_arg: impl FnMut(Span, MutOut, TuplePattern) -> Result<()>,
  ) -> Result<()> {
    match self.head_keyword(&e) {
      Some((Keyword::Mut, u)) => for e in u {
        push_arg(self.try_get_span(&e), MutOut::Mut, self.parse_arg1(e, name_required)?)?
      }
      Some((Keyword::Out, mut u)) => {
        let (a, e) = match (u.next(), u.next(), u.is_empty()) {
          (Some(e), None, _) => (AtomId::UNDER, e),
          (Some(e1), Some(e), true) => {
            let a = e1.as_atom().ok_or_else(||
              ElabError::new_e(self.try_get_span(&e1), "'out' syntax error"))?;
            (a, e)
          }
          _ => return Err(ElabError::new_e(self.try_get_span(&e), "'out' syntax error")),
        };
        push_arg(self.try_get_span(&e), MutOut::Out(a), self.parse_arg1(e, name_required)?)?
      }
      _ => push_arg(self.try_get_span(&e), MutOut::None, self.parse_arg1(e, name_required)?)?
    }
    Ok(())
  }

  /// Parse a tuple pattern.
  pub fn parse_tuple_pattern(&self, ghost: bool, e: LispVal) -> Result<TuplePattern> {
    if let Some(a) = e.as_atom() {
      return Ok(TuplePattern::Name(ghost || a == AtomId::UNDER, a, e.fspan()))
    }
    if !e.is_list() {
      return Err(ElabError::new_e(self.try_get_span(&e),
        format!("tuple pattern syntax error: {}", self.fe.to(&e))))
    }
    Ok(match self.head_keyword(&e) {
      Some((Keyword::Colon, mut u)) => {
        if let (Some(e), Some(ty), true) = (u.next(), u.next(), u.is_empty()) {
          TuplePattern::Typed(Box::new(self.parse_tuple_pattern(ghost, e)?), ty)
        } else {
          return Err(ElabError::new_e(self.try_get_span(&e), "':' syntax error"))
        }
      }
      Some((Keyword::Ghost, u)) => {
        let sp = u.fspan();
        let mut args = vec![];
        for e in u {args.push(self.parse_tuple_pattern(true, e)?)}
        if args.len() == 1 {
          args.drain(..).next().expect("nonempty")
        } else {
          TuplePattern::Tuple(args.into_boxed_slice(), sp)
        }
      }
      _ => {
        let sp = e.fspan();
        let mut args = vec![];
        for e in Uncons::from(e) {args.push(self.parse_tuple_pattern(ghost, e)?)}
        TuplePattern::Tuple(args.into_boxed_slice(), sp)
      }
    })
  }

  fn parse_pattern(&self, e: &LispVal) -> Result<Pattern> {
    Ok(match &*e.unwrapped_arc() {
      &LispKind::Atom(a) => Pattern::VarOrConst(a),
      LispKind::List(_) | LispKind::DottedList(_, _) => match self.head_keyword(e) {
        Some((Keyword::Colon, mut u)) =>
          if let (Some(h), Some(p), true) = (u.next(), u.next(), u.is_empty()) {
            let h = h.as_atom().ok_or_else(||
              ElabError::new_e(self.try_get_span(&h), "expecting hypothesis name"))?;
            Pattern::Hyped(h, Box::new(self.parse_pattern(&p)?))
          } else {
            return Err(ElabError::new_e(self.try_get_span(e), "':' syntax error"))
          },
        Some((Keyword::Or, u)) => {
          let mut args = vec![];
          for e in u {args.push(self.parse_pattern(&e)?)}
          Pattern::Or(args.into_boxed_slice())
        }
        Some((Keyword::With, mut u)) =>
          if let (Some(p), Some(g), true) = (u.next(), u.next(), u.is_empty()) {
            Pattern::With(Box::new((self.parse_pattern(&p)?, g)))
          } else {
            return Err(ElabError::new_e(self.try_get_span(e), "'with' syntax error"))
          },
        _ => return Err(ElabError::new_e(self.try_get_span(e), "pattern syntax error"))
      }
      LispKind::Number(n) => Pattern::Number(n.clone()),
      _ => return Err(ElabError::new_e(self.try_get_span(e), "pattern syntax error"))
    })
  }

  fn parse_decl_asgn(&self, e: &LispVal) -> Result<Expr> {
    match self.head_keyword(e) {
      Some((Keyword::ColonEq, mut u)) => if let (Some(lhs), Some(rhs), true) = (u.next(), u.next(), u.is_empty()) {
        return Ok(Expr::Let {lhs: self.parse_tuple_pattern(false, lhs)?, rhs, with: vec![]})
      },
      Some((Keyword::ArrowL, mut u)) => if let (Some(lhs), Some(rhs), true) = (u.next(), u.next(), u.is_empty()) {
        return Ok(Expr::Assign {lhs, rhs, with: vec![]})
      },
      _ => {}
    }
    Err(ElabError::new_e(self.try_get_span(e), "decl: syntax error"))
  }

  fn parse_decl(&self, e: &LispVal) -> Result<(TuplePattern, LispVal)> {
    if let Expr::Let {lhs, rhs, ..} = self.parse_decl_asgn(e)? {
      Ok((lhs, rhs))
    } else {
      Err(ElabError::new_e(self.try_get_span(e), "decl: assignment not allowed here"))
    }
  }

  fn parse_rename(&self, e: &LispVal) -> Result<Option<Rename>> {
    match self.head_keyword(e) {
      Some((Keyword::ArrowL, mut u)) => if let (Some(to), Some(from), true) =
        (u.next().and_then(|e| e.as_atom()), u.next().and_then(|e| e.as_atom()), u.is_empty()) {
        return Ok(Some(Rename::New {from, to}))
      },
      Some((Keyword::ArrowR, mut u)) => if let (Some(from), Some(to), true) =
        (u.next().and_then(|e| e.as_atom()), u.next().and_then(|e| e.as_atom()), u.is_empty()) {
        return Ok(Some(Rename::Old {from, to}))
      },
      _ => return Ok(None)
    }
    Err(ElabError::new_e(self.try_get_span(e), "with: expected {old -> old'} or {new' <- new}"))
  }

  /// Parse an MMC expression (shallowly), returning a [`parser::Expr`](Expr)
  /// containing [`LispVal`]s for subexpressions.
  pub fn parse_expr(&self, e: LispVal) -> Result<Expr> {
    Ok(match &*e.unwrapped_arc() {
      &LispKind::Atom(AtomId::UNDER) => Expr::Hole(self.try_get_fspan(&e)),
      &LispKind::Atom(a) => Expr::Var(self.try_get_fspan(&e), a),
      LispKind::List(_) | LispKind::DottedList(_, _) => match self.head_keyword(&e) {
        Some((Keyword::ColonEq, _)) |
        Some((Keyword::ArrowL, _)) => self.parse_decl_asgn(&e)?,
        Some((Keyword::With, mut u)) => {
          let mut ret = self.parse_decl_asgn(&u.next().ok_or_else(||
            ElabError::new_e(self.try_get_span(&e), "'with' syntax error"))?)?;
          let with = match &mut ret {
            Expr::Let {with, ..} | Expr::Assign {with, ..} => with,
            _ => unreachable!()
          };
          for e in u {
            if let Some(r) = self.parse_rename(&e)? { with.push(r) }
            else {
              for e in Uncons::New(e) {
                let r = self.parse_rename(&e)?.ok_or_else(||
                  ElabError::new_e(self.try_get_span(&e), "with: expected {old -> old'} or {new' <- new}"))?;
                with.push(r);
              }
            }
          }
          ret
        }
        Some((Keyword::If, mut u)) => {
          let err = || ElabError::new_e(self.try_get_span(&e), "if: syntax error");
          let mut cond = u.next().ok_or_else(err)?;
          let mut tru = u.next().ok_or_else(err)?;
          let mut muts = vec![];
          if let Some((Keyword::Mut, u2)) = self.head_keyword(&tru) {
            for e in u2 {
              muts.push((e.as_atom().ok_or_else(||
                ElabError::new_e(self.try_get_span(&e), "mut: expected an atom"))?, e.fspan()))
            }
            tru = u.next().ok_or_else(err)?
          }
          let mut branches = vec![];
          let mut push = |cond, tru| {
            let (hyp, cond) = match self.head_keyword(&cond) {
              Some((Keyword::Colon, mut u)) =>
                if let (Some(h), Some(cond), true) = (u.next(), u.next(), u.is_empty()) {
                  let h = h.as_atom().ok_or_else(||
                    ElabError::new_e(self.try_get_span(&h), "expecting hypothesis name"))?;
                  (if h == AtomId::UNDER {None} else {Some(h)}, cond)
                } else {
                  return Err(ElabError::new_e(self.try_get_span(&cond), "':' syntax error"))
                },
              _ => (None, cond),
            };
            branches.push((hyp, cond, tru));
            Ok(())
          };
          let mut els;
          loop {
            els = u.next();
            if let Some(Keyword::Else) = els.as_ref().and_then(|e| self.kw.get(&e.as_atom()?)) {
              els = u.next()
            }
            if let Some(Keyword::If) = els.as_ref().and_then(|e| self.kw.get(&e.as_atom()?)) {
              push(mem::replace(&mut cond, u.next().ok_or_else(err)?),
                mem::replace(&mut tru, u.next().ok_or_else(err)?))?;
            } else {break}
          }
          push(cond, tru)?;
          Expr::If {muts: muts.into(), branches: branches.into(), els: els.unwrap_or_else(LispVal::nil)}
        }
        Some((Keyword::Switch, mut u)) => {
          let c =  u.next().ok_or_else(||
            ElabError::new_e(self.try_get_span(&e), "switch: syntax error"))?;
          let mut branches = vec![];
          for e in u {
            if let Some((Keyword::Arrow, mut u)) = self.head_keyword(&e) {
              if let (Some(p), Some(e), true) = (u.next(), u.next(), u.is_empty()) {
                branches.push((self.parse_pattern(&p)?, e));
              } else {
                return Err(ElabError::new_e(self.try_get_span(&e), "switch: syntax error"))
              }
            } else {
              return Err(ElabError::new_e(self.try_get_span(&e), "switch: syntax error"))
            }
          }
          Expr::Switch(c, branches.into_boxed_slice())
        }
        Some((Keyword::While, mut u)) => {
          let c = u.next().ok_or_else(||
            ElabError::new_e(self.try_get_span(&e), "while: syntax error"))?;
          let (hyp, cond) = if let Some((Keyword::Colon, mut u)) = self.head_keyword(&c) {
            if let (Some(h), Some(c), true) = (u.next().and_then(|a| a.as_atom()), u.next(), u.is_empty()) {
              (Some(h), c)
            } else {
              return Err(ElabError::new_e(self.try_get_span(&e), "while: bad pattern"))
            }
          } else {(None, c)};
          let mut var = None;
          while let Some(e) = u.head() {
            if let Some(v) = self.parse_variant(&e) {
              if mem::replace(&mut var, Some(v)).is_some() {
                return Err(ElabError::new_e(self.try_get_span(&e), "while: two variants"))
              }
            } else {break}
            u.next();
          }
          Expr::While { hyp, cond, var, body: u }
        }
        Some((Keyword::Begin, u)) => Expr::Block(u),
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
            Some(e) => if let Some((Keyword::Begin, mut u1)) = self.head_keyword(&e) {
              let name = u1.next().and_then(|e| e.as_atom()).ok_or_else(||
                ElabError::new_e(self.try_get_span(&e), "label: expected label name"))?;
              let mut args = vec![];
              let mut variant = None;
              for e in u1 {
                if let Some(v) = self.parse_variant(&e) {
                  if mem::replace(&mut variant, Some(v)).is_some() {
                    return Err(ElabError::new_e(self.try_get_span(&e), "label: two variants"))
                  }
                } else {
                  args.push(self.parse_arg1(e, true)?)
                }
              }
              Expr::Label {
                name, args: args.into(), variant,
                body: u
              }
            } else {
              let fsp = e.fspan();
              let f = e.as_atom().ok_or_else(||
                ElabError::new_e(try_get_span_from(&self.fsp, fsp.as_ref()), "only variables can be called like functions"))?;
              let mut args = vec![];
              let mut variant = None;
              for e in u {
                if let Some((Keyword::Variant, u)) = self.head_keyword(&e) {
                  if mem::replace(&mut variant, Some(u.as_lisp())).is_some() {
                    return Err(ElabError::new_e(self.try_get_span(&e), "call: two variants"))
                  }
                } else {
                  args.push(e)
                }
              }
              Expr::Call {f, fsp, args, variant}
            }
          }
        }
      },
      LispKind::Number(n) => Expr::Number(n.clone()),
      _ => return Err(ElabError::new_e(self.try_get_span(&e), "unknown expression"))
    })
  }

  fn parse_proc(&self, mut kind: ProcKind, mut u: Uncons) -> Result<(Proc, Uncons)> {
    let e = match u.next() {
      None => return Err(ElabError::new_e(self.try_get_span(&u.into()), "func/proc: syntax error")),
      Some(e) => e,
    };
    let mut args = (vec![], vec![]);
    let mut rets = (vec![], vec![]);
    let (name, span) = match &*e.unwrapped_arc() {
      &LispKind::Atom(a) => (a, e.fspan()),
      LispKind::List(_) | LispKind::DottedList(_, _) => {
        let mut u = Uncons::from(e.clone());
        let e = u.next().ok_or_else(||
          ElabError::new_e(self.try_get_span(&e), "func/proc syntax error: expecting function name"))?;
        let name = e.as_atom().ok_or_else(||
          ElabError::new_e(self.try_get_span(&e), "func/proc syntax error: expecting an atom"))?;
        while let Some(e) = u.next() {
          if let Some(AtomId::COLON) = e.as_atom() { break }
          self.parse_arg(e, true, |sp, mo, arg| {
            args.0.push(match mo {
              MutOut::None => false,
              MutOut::Mut => true,
              MutOut::Out(_) => return Err(ElabError::new_e(sp, "'out' cannot appear in function arguments"))
            });
            args.1.push(arg);
            Ok(())
          })?
        }
        for e in u {
          self.parse_arg(e, false, |sp, mo, arg| {
            rets.0.push(match mo {
              MutOut::None => None,
              MutOut::Out(a) => Some(a),
              MutOut::Mut => return Err(ElabError::new_e(sp, "'mut' cannot appear in function returns"))
            });
            rets.1.push(arg);
            Ok(())
          })?
        }
        (name, e.fspan())
      }
      _ => return Err(ElabError::new_e(self.try_get_span(&e), "func/proc: syntax error"))
    };
    let variant = if let Some(e) = u.head() {
      match kind {
        ProcKind::Intrinsic => return Err(
          ElabError::new_e(self.try_get_span(&e), "intrinsic: unexpected body")),
        ProcKind::ProcDecl => kind = ProcKind::Proc,
        _ => {}
      }
      self.parse_variant(&e)
    } else {None};
    Ok((Proc {name, span, args, rets, variant, kind}, u))
  }

  fn parse_name_and_tyargs(&self, e: &LispVal) -> Result<(AtomId, Option<FileSpan>, Vec<TuplePattern>)> {
    let mut args = vec![];
    let (name, sp) = match &*e.unwrapped_arc() {
      &LispKind::Atom(a) => (a, e.fspan()),
      LispKind::List(_) | LispKind::DottedList(_, _) => {
        let mut u = Uncons::from(e.clone());
        let e = u.next().ok_or_else(|| ElabError::new_e(self.try_get_span(e), "typedef: syntax error"))?;
        let a = e.as_atom().ok_or_else(|| ElabError::new_e(self.try_get_span(&e), "typedef: expected an atom"))?;
        for e in u { args.push(self.parse_arg1(e, true)?) }
        (a, e.fspan())
      },
      _ => return Err(ElabError::new_e(self.try_get_span(e), "typedef: syntax error"))
    };
    Ok((name, sp, args))
  }

  /// Parses the input lisp literal `e` into a list of top level items and appends them to `ast`.
  pub fn parse_ast(&self, ast: &mut Vec<Ast>, e: &LispVal) -> Result<()> {
    let mut u = Uncons::from(e.clone());
    while let Some(e) = u.next() {
      match self.head_keyword(&e) {
        Some((Keyword::Proc, u)) => ast.push(Ast::proc(self.parse_proc(ProcKind::ProcDecl, u)?)),
        Some((Keyword::Func, u)) => ast.push(Ast::proc(self.parse_proc(ProcKind::Func, u)?)),
        Some((Keyword::Intrinsic, u)) => ast.push(Ast::proc(self.parse_proc(ProcKind::Intrinsic, u)?)),
        Some((Keyword::Global, u)) => for e in u {
          let full = e.fspan();
          let (lhs, rhs) = self.parse_decl(&e)?;
          ast.push(Ast::Global {full, lhs, rhs})
        },
        Some((Keyword::Const, u)) => for e in u {
          let (lhs, rhs) = self.parse_decl(&e)?;
          ast.push(Ast::Const {full: e.fspan(), lhs, rhs});
        },
        Some((Keyword::Typedef, mut u)) =>
          if let (Some(e), Some(val), true) = (u.next(), u.next(), u.is_empty()) {
            let (name, span, args) = self.parse_name_and_tyargs(&e)?;
            ast.push(Ast::Typedef {name, span, args: args.into(), val});
          } else {
            return Err(ElabError::new_e(self.try_get_span(&e), "typedef: syntax error"))
          },
        Some((Keyword::Struct, mut u)) => {
          let e = u.next().ok_or_else(||
            ElabError::new_e(self.try_get_span(&e), "struct: expecting name"))?;
          let (name, span, args) = self.parse_name_and_tyargs(&e)?;
          let mut fields = vec![];
          for e in u { fields.push(self.parse_arg1(e, false)?) }
          ast.push(Ast::Struct {name, span, args: args.into(), fields: fields.into()});
        }
        _ => return Err(ElabError::new_e(self.try_get_span(&e), "MMC: unknown top level item"))
      }
    }
    if !u.is_empty() {
      return Err(ElabError::new_e(self.try_get_span(e), "MMC: syntax error"))
    }
    Ok(())
  }
}
