//! The AST building compiler pass.
//!
//! This pass is responsible mainly for name resolution. The [parser](super::parser) works on-demand,
//! so the entire parsed MMC syntax doesn't exist all at once, but conceptually it is made up of recursive
//! applications of the constructors in [`types::parse`](super::types::parse). This contains `AtomId`s
//! referencing variable names as provided by the user, and the task here is to undo all the name shadowing
//! and resolve references to loop labels, named constants, and so on, so that elaboration has a
//! reasonably well formed input to work on.
//!
//! The output of this stage is a full AST according to the types in the
//! [`types::ast`](super::types::ast) module.

use std::collections::{HashMap, hash_map::Entry};
use std::convert::TryInto;
use std::rc::Rc;
use crate::{ElabError, elab::Result, AtomId, LispVal, Uncons, FileSpan};
use super::types::{Binop, Mm0Expr, Size, Spanned, FieldName, Unop, VarId, ast};
#[allow(clippy::wildcard_imports)] use super::types::parse::*;
use super::types::entity::Entity;
use super::parser::{Parser, spanned};

#[derive(Copy, Clone, Debug)]
struct LabelId(VarId, u16);

#[derive(Debug)]
enum Ctx {
  Var(AtomId, VarId),
  Label(AtomId, LabelId),
}

impl From<ArgAttr> for ast::ArgAttr {
  fn from(ArgAttr {mut_, global, implicit, out: _}: ArgAttr) -> Self {
    let mut ret = ast::ArgAttr::empty();
    if mut_ {ret |= ast::ArgAttr::MUT}
    if global {ret |= ast::ArgAttr::GLOBAL}
    if implicit {ret |= ast::ArgAttr::IMPLICIT}
    ret
  }
}

fn let_var(sp: &FileSpan, name: AtomId, v: VarId, rhs: ast::Expr) -> ast::Stmt {
  Spanned {span: sp.clone(), k: ast::StmtKind::Let {
    lhs: Spanned {span: sp.clone(), k:
      ast::TuplePatternKind::Name(false, name, v)},
    rhs
  }}
}

/// The state of the AST building pass.
#[derive(Debug)]
pub struct BuildAst<'a> {
  /// The global mapping of names to entities (globals, constants, intrinsics).
  names: &'a HashMap<AtomId, Entity>,
  /// The parser, which we use to parse `LispVal` terms into [`types::parse`](super::types::parse)
  /// constructions.
  pub(crate) p: Parser<'a>,
  /// The mapping of user-level names to internal variable IDs. The vector represents name
  /// shadowing, with the active variable being the last in the list.
  ///
  /// This is a cache for `ctx`: `name_map.get(name)` is exactly the
  /// list of `v` such that `Var(name, v)` is in `ctx` (in order).
  name_map: HashMap<AtomId, Vec<VarId>>,
  /// The mapping of user-level labels to internal label IDs. The vector represents name
  /// shadowing, with the active label being the last in the list.
  ///
  /// This is a cache for `ctx`: `name_map.get(name)` is exactly the
  /// list of `v` such that `Label(name, v)` is in `ctx` (in order).
  label_map: HashMap<AtomId, Vec<LabelId>>,
  /// The mapping of anonymous loop targets to internal label IDs.
  /// The vector represents scoping, with the active loop being the last in the list.
  /// The boolean is true if there is a `break` to this loop target.
  loops: Vec<(VarId, bool)>,
  /// The context, which contains information about scoped names. Scopes are created by
  /// [`with_ctx`](Self::with_ctx), which remembers the size of the context on entering the scope
  /// and pops everything that has been added when we get to the end of the scope.
  ctx: Vec<Ctx>,
  /// The list of type variables in scope.
  tyvars: Vec<AtomId>,
  /// The mapping from allocated variables to their user facing names.
  pub(crate) var_names: Vec<AtomId>,
}

fn fresh_var(var_names: &mut Vec<AtomId>, name: AtomId) -> VarId {
  let v = VarId(var_names.len().try_into().expect("overflow"));
  var_names.push(name);
  v
}

impl<'a> BuildAst<'a> {
  /// Construct a new AST builder.
  #[must_use] pub fn new(names: &'a HashMap<AtomId, Entity>, p: Parser<'a>) -> Self {
    Self {
      names, p,
      name_map: HashMap::new(),
      label_map: HashMap::new(),
      loops: vec![],
      ctx: vec![],
      var_names: vec![],
      tyvars: vec![]
    }
  }

  fn pop(&mut self) {
    match self.ctx.pop().expect("stack underflow") {
      Ctx::Var(name, _) => {self.name_map.get_mut(&name).and_then(Vec::pop).expect("stack underflow");}
      Ctx::Label(name, _) => {self.label_map.get_mut(&name).and_then(Vec::pop).expect("stack underflow");}
    }
  }

  fn fresh_var(&mut self, name: AtomId) -> VarId { fresh_var(&mut self.var_names, name) }

  fn push_fresh(&mut self, name: AtomId) -> VarId {
    let v = self.fresh_var(name);
    self.push(name, v);
    v
  }

  fn push(&mut self, name: AtomId, v: VarId) {
    self.ctx.push(Ctx::Var(name, v));
    self.name_map.entry(name).or_default().push(v);
  }

  fn push_label(&mut self, name: AtomId, label: LabelId) {
    self.ctx.push(Ctx::Label(name, label));
    self.label_map.entry(name).or_default().push(label);
  }

  fn get_var(&mut self, sp: &FileSpan, name: AtomId) -> Result<VarId> {
    self.name_map.get(&name).and_then(|v| v.last().copied()).ok_or_else(||
      ElabError::new_e(sp, format!("unknown variable '{}'", self.p.fe.to(&name))))
  }

  fn drain_to(&mut self, n: usize) {
    while self.ctx.len() > n { self.pop(); }
  }

  fn apply_rename(&mut self, sp: &FileSpan, renames: &[(AtomId, AtomId)]) -> Result<()> {
    let mut vec = vec![];
    for &(from, to) in renames {
      if from == AtomId::UNDER { return Err(ElabError::new_e(sp, "can't rename variable '_'")) }
      if from == to { continue }
      let var = self.get_var(sp, from)?;
      vec.push((var, to));
    }
    for (var, to) in vec { self.push(to, var) }
    Ok(())
  }

  fn mk_split(&mut self, sp: &FileSpan, Renames {old, new}: Renames) -> Result<HashMap<VarId, (VarId, AtomId, AtomId)>> {
    let mut map = HashMap::new();
    for (from, to) in old {
      if from == AtomId::UNDER { return Err(ElabError::new_e(sp, "can't rename variable '_'")) }
      map.entry(self.get_var(sp, from)?)
        .or_insert_with(|| (self.fresh_var(from), from, from)).2 = to;
    }
    for (from, to) in new {
      if from == AtomId::UNDER { return Err(ElabError::new_e(sp, "can't rename variable '_'")) }
      map.entry(self.get_var(sp, from)?)
        .or_insert_with(|| (self.fresh_var(from), from, from)).1 = to;
    }
    Ok(map)
  }

  fn add_origins(e: &ast::Expr, f: &mut impl FnMut(VarId) -> Result<()>) -> Result<()> {
    match &e.k {
      &ast::ExprKind::Var(v) => f(v)?,
      ast::ExprKind::Index(e, _, _) |
      ast::ExprKind::Proj(e, _) |
      ast::ExprKind::Ghost(e) |
      ast::ExprKind::Borrow(e) |
      ast::ExprKind::Block(ast::Block {expr: Some(e), ..}) => Self::add_origins(e, f)?,
      ast::ExprKind::Slice(e, _) => Self::add_origins(&e.0, f)?,
      ast::ExprKind::If {then, els, ..} => {Self::add_origins(then, f)?; Self::add_origins(els, f)?}
      _ => {}
    }
    Ok(())
  }

  fn push_tuple_pattern(&mut self, Spanned {span, k: pat}: TuplePattern, v: Option<VarId>) -> Result<ast::TuplePattern> {
    let k = match pat {
      TuplePatternKind::Name(g, name) => {
        let v = v.unwrap_or_else(|| self.fresh_var(name));
        self.push(name, v);
        ast::TuplePatternKind::Name(g, name, v)
      }
      TuplePatternKind::Typed(pat, ty) => {
        let ty = self.build_ty(&span, &ty)?;
        let pat = self.push_tuple_pattern(*pat, v)?;
        ast::TuplePatternKind::Typed(Box::new(pat), Box::new(ty))
      }
      TuplePatternKind::Tuple(pats) => ast::TuplePatternKind::Tuple(
        pats.into_iter().map(|pat| {
          let v = self.fresh_var(AtomId::UNDER);
          Ok((v, self.push_tuple_pattern(pat, Some(v))?))
        }).collect::<Result<_>>()?
      ),
    };
    Ok(Spanned {span, k})
  }

  fn push_arg(&mut self, allow_mut: bool, Spanned {span, k: (attr, pat)}: Arg) -> Result<ast::Arg> {
    if attr.out.is_some() {
      return Err(ElabError::new_e(&span, "'out' not expected here"))
    }
    if !allow_mut && attr.mut_ {
      return Err(ElabError::new_e(&span, "'mut' not expected here"))
    }
    let pat = match pat {
      ArgKind::Lam(k) =>
        ast::ArgKind::Lam(self.push_tuple_pattern(Spanned {span: span.clone(), k}, None)?.k),
      ArgKind::Let(pat, val) => {
        let val = Box::new(self.build_expr(&span, val)?);
        ast::ArgKind::Let(self.push_tuple_pattern(pat, None)?, val)
      }
    };
    Ok(Spanned {span, k: (attr.into(), pat)})
  }

  fn with_ctx<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
    let n = self.ctx.len();
    let res = f(self);
    self.drain_to(n);
    res
  }

  fn with_tuple_patterns<T>(&mut self, pats: Vec<TuplePattern>,
    f: impl FnOnce(&mut Self, Box<[ast::TuplePattern]>) -> Result<T>
  ) -> Result<T> {
    self.with_ctx(|this| {
      let pats = pats.into_iter().map(|pat| this.push_tuple_pattern(pat, None)).collect::<Result<_>>()?;
      f(this, pats)
    })
  }

  fn with_args<T>(&mut self, args: Vec<Arg>,
    f: impl FnOnce(&mut Self, Box<[ast::Arg]>) -> Result<T>
  ) -> Result<T> {
    self.with_ctx(|this| {
      let args = args.into_iter().map(|arg| this.push_arg(false, arg)).collect::<Result<_>>()?;
      f(this, args)
    })
  }


  fn build_lft(&mut self, lft: Option<Box<Spanned<Lifetime>>>) -> Result<Option<Box<Spanned<ast::Lifetime>>>> {
    Ok(if let Some(lft) = lft {
      let k = match lft.k {
        Lifetime::Extern => ast::Lifetime::Extern,
        Lifetime::Place(name) => ast::Lifetime::Place(self.get_var(&lft.span, name)?),
        Lifetime::Infer => ast::Lifetime::Infer,
      };
      Some(Box::new(Spanned {span: lft.span, k}))
    } else {None})
  }

  fn build_ty(&mut self, base: &FileSpan, ty: &LispVal) -> Result<ast::Type> {
    let Spanned {span, k: ty} = self.p.parse_ty(base, self.names, ty)?;
    let k = match ty {
      TypeKind::Unit => ast::TypeKind::Unit,
      TypeKind::True => ast::TypeKind::True,
      TypeKind::False => ast::TypeKind::False,
      TypeKind::Bool => ast::TypeKind::Bool,
      TypeKind::Var(name) => {
        let v = self.tyvars.iter().rposition(|&v| name == v).ok_or_else(||
          ElabError::new_e(&span, format!("unknown type variable '{}'", self.p.fe.to(&name))))?;
        ast::TypeKind::Var(v.try_into().expect("too many vars"))
      }
      TypeKind::Int(sz) => ast::TypeKind::Int(sz),
      TypeKind::UInt(sz) => ast::TypeKind::UInt(sz),
      TypeKind::Array(ty, n) => {
        let ty = self.build_ty(&span, &ty)?;
        let n = self.build_expr(&span, n)?;
        ast::TypeKind::Array(Box::new(ty), Box::new(n))
      },
      TypeKind::Own(ty) => ast::TypeKind::Own(Box::new(self.build_ty(&span, &ty)?)),
      TypeKind::Ref(lft, ty) => ast::TypeKind::Ref(self.build_lft(lft)?, Box::new(self.build_ty(&span, &ty)?)),
      TypeKind::Shr(lft, ty) => {
        let k = ast::TypeKind::Ref(self.build_lft(lft)?, Box::new(self.build_ty(&span, &ty)?));
        ast::TypeKind::Own(Box::new(Spanned {span: span.clone(), k}))
      }
      TypeKind::RefSn(e) => ast::TypeKind::RefSn(Box::new(self.build_expr(&span, e)?)),
      TypeKind::List(tys) => ast::TypeKind::List(tys.iter().map(|ty| self.build_ty(&span, ty)).collect::<Result<_>>()?),
      TypeKind::Sn(e) => ast::TypeKind::Sn(Box::new(self.build_expr(&span, e)?)),
      TypeKind::Struct(pats) => ast::TypeKind::Struct(self.with_args(pats, |_, x| Ok(x))?),
      TypeKind::All(args, p) => self.with_tuple_patterns(args, |this, args| {
        Ok(ast::TypeKind::All(args, Box::new(this.build_ty(&span, &p)?)))
      })?,
      TypeKind::Ex(args, p) => self.with_tuple_patterns(args, |this, args| {
        let mut pats = Vec::with_capacity(args.len() + 1);
        let f = |pat| (ast::ArgAttr::empty(), ast::ArgKind::Lam(pat));
        pats.extend(args.into_vec().into_iter().map(|pat| pat.map_into(f)));
        let ty = this.build_ty(&span, &p)?;
        let k = ast::TuplePatternKind::Name(true, AtomId::UNDER, this.fresh_var(AtomId::UNDER));
        let k = f(ast::TuplePatternKind::Typed(Box::new(Spanned {span: span.clone(), k}), Box::new(ty)));
        pats.push(Spanned {span: span.clone(), k});
        Ok(ast::TypeKind::Struct(pats.into_boxed_slice()))
      })?,
      TypeKind::Imp(p1, p2) => ast::TypeKind::Imp(Box::new(self.build_ty(&span, &p1)?), Box::new(self.build_ty(&span, &p2)?)),
      TypeKind::Wand(p1, p2) => ast::TypeKind::Wand(Box::new(self.build_ty(&span, &p1)?), Box::new(self.build_ty(&span, &p2)?)),
      TypeKind::Not(p) => ast::TypeKind::Not(Box::new(self.build_ty(&span, &p)?)),
      TypeKind::And(tys) => ast::TypeKind::And(tys.iter().map(|ty| self.build_ty(&span, ty)).collect::<Result<_>>()?),
      TypeKind::Or(tys) => ast::TypeKind::Or(tys.iter().map(|ty| self.build_ty(&span, ty)).collect::<Result<_>>()?),
      TypeKind::If([c, t, e]) => ast::TypeKind::If(
        Box::new(self.build_expr(&span, c)?),
        Box::new(self.build_ty(&span, &t)?),
        Box::new(self.build_ty(&span, &e)?)),
      TypeKind::Match(e, branches) => {
        let e = Rc::new(self.build_expr(&span, e)?);
        self.build_match(&span, None, &e, branches, false,
          |_, e| e.k,
          |_, c, t, e| ast::TypeKind::If(c, t, e),
          |this, rhs| this.build_ty(&span, &rhs))?
      }
      TypeKind::Ghost(ty) => ast::TypeKind::Ghost(Box::new(self.build_ty(&span, &ty)?)),
      TypeKind::Uninit(ty) => ast::TypeKind::Uninit(Box::new(self.build_ty(&span, &ty)?)),
      TypeKind::Pure(e) => ast::TypeKind::Pure(Box::new(self.build_parsed_expr(span.clone(), *e)?)),
      TypeKind::User(f, tys, es) => {
        let tys = tys.into_vec().iter().map(|ty| self.build_ty(&span, ty)).collect::<Result<_>>()?;
        let es = es.into_vec().into_iter().map(|e| self.build_expr(&span, e)).collect::<Result<_>>()?;
        ast::TypeKind::User(f, tys, es)
      },
      TypeKind::Heap(e1, e2) => ast::TypeKind::Heap(Box::new(self.build_expr(&span, e1)?), Box::new(self.build_expr(&span, e2)?)),
      TypeKind::HasTy(e, ty) => ast::TypeKind::HasTy(Box::new(self.build_expr(&span, e)?), Box::new(self.build_ty(&span, &ty)?)),
      TypeKind::Input => ast::TypeKind::Input,
      TypeKind::Output => ast::TypeKind::Output,
      TypeKind::Moved(ty) => ast::TypeKind::Moved(Box::new(self.build_ty(&span, &ty)?)),
      TypeKind::Infer => ast::TypeKind::Infer,
      TypeKind::Error => ast::TypeKind::Error,
    };
    Ok(Spanned {span, k})
  }

  fn build_expr(&mut self, base: &FileSpan, e: LispVal) -> Result<ast::Expr> {
    self.with_ctx(|this| this.push_expr(base, e))
  }

  fn push_expr(&mut self, base: &FileSpan, e: LispVal) -> Result<ast::Expr> {
    let Spanned {span, k} = self.p.parse_expr(base, e)?;
    self.push_parsed_expr(span, k)
  }

  fn build_parsed_expr(&mut self, span: FileSpan, ek: ExprKind) -> Result<ast::Expr> {
    self.with_ctx(|this| this.push_parsed_expr(span, ek))
  }

  fn push_parsed_expr(&mut self, span: FileSpan, ek: ExprKind) -> Result<ast::Expr> {
    let k = match ek {
      ExprKind::Unit => ast::ExprKind::Unit,
      ExprKind::Var(name) => match self.get_var(&span, name) {
        Ok(v) => ast::ExprKind::Var(v),
        Err(e) => {
          let c = CallExpr {f: Spanned {span: span.clone(), k: name}, args: vec![], variant: None};
          return self.build_call_expr(span, c).map_err(|_| e)
        }
      }
      ExprKind::Bool(b) => ast::ExprKind::Bool(b),
      ExprKind::Int(n) => ast::ExprKind::Int(n),
      ExprKind::Let {..} => return Err(ElabError::new_e(&span, "a let statement is not an expression")),
      ExprKind::Assign {lhs, rhs, with} => {
        let lhs = self.build_expr(&span, lhs)?;
        let rhs = Box::new(self.build_expr(&span, rhs)?);
        let mut split = self.mk_split(&span, with)?;
        Self::add_origins(&lhs, &mut |var| {
          if let Entry::Vacant(e) = split.entry(var) {
            if let Some(from) = self.ctx.iter().find_map(|v| match *v { Ctx::Var(a, v) if v == var => Some(a), _ => None}) {
              e.insert((self.fresh_var(from), from, from));
            }
          }
          Ok(())
        })?;
        let oldmap = split.into_iter().map(|(vnew, (vold, new, old))| {
          self.push(old, vold);
          self.push(new, vnew);
          (vnew, vold)
        }).collect();
        ast::ExprKind::Assign {lhs: Box::new(lhs), rhs, oldmap}
      }
      ExprKind::Proj(e, i) => ast::ExprKind::Proj(Box::new(self.build_expr(&span, e)?), i),
      ExprKind::Call(c) => return self.build_call_expr(span, c),
      ExprKind::Entail(p, hs) => ast::ExprKind::Entail(p,
        hs.into_iter().map(|h| self.build_expr(&span, h)).collect::<Result<_>>()?),
      ExprKind::Block(es) => ast::ExprKind::Block(self.build_block(&span, es)?),
      ExprKind::Label(Label {args, body, ..}) if args.is_empty() => ast::ExprKind::Block(self.build_block(&span, body)?),
      ExprKind::Label(_) => return Err(ElabError::new_e(&span, "a labeled block is a statement, not an expression")),
      ExprKind::If {branches, els} => self.with_ctx(|this| -> Result<_> {
        let branches = branches.into_iter().map(|(h, cond, then)| {
          let cond = Box::new(this.build_expr(&span, cond)?);
          let h = h.map(|h| this.push_fresh(h));
          let then = Box::new(this.build_expr(&span, then)?);
          Ok((h, cond, then))
        }).collect::<Result<Vec<_>>>()?;
        let mut ret = if let Some(els) = els {this.push_expr(&span, els)?.k} else {ast::ExprKind::Unit};
        for (hyp, cond, then) in branches.into_iter().rev() {
          let els = Box::new(Spanned {span: span.clone(), k: ret});
          ret = ast::ExprKind::If {ik: ast::IfKind::If, hyp, cond, then, els};
        }
        Ok(ret)
      })?,
      ExprKind::Match(e, branches) => {
        let e = Rc::new(self.build_expr(&span, e)?);
        let v = self.fresh_var(AtomId::UNDER);
        let k = self.build_match(&span, Some(v), &e, branches, true,
          |stmts, e| ast::ExprKind::Block(ast::Block { stmts, expr: Some(Box::new(e)) }),
          |hyp, cond, then, els| ast::ExprKind::If {ik: ast::IfKind::If, hyp, cond, then, els},
          |this, rhs| this.push_expr(&span, rhs))?;
        ast::ExprKind::Block(ast::Block {
          stmts: vec![let_var(&span, AtomId::UNDER, v,
            Spanned {span: span.clone(), k: ast::ExprKind::Rc(e)})],
          expr: Some(Box::new(Spanned {span: span.clone(), k}))
        })
      }
      ExprKind::While {muts, hyp, cond, var, body} => {
        let label = self.fresh_var(AtomId::UNDER);
        let mut muts2 = Vec::with_capacity(muts.len());
        for Spanned {span, k: name} in muts {
          let a = self.get_var(&span, name)?;
          if muts2.contains(&a) { return Err(ElabError::new_e(&span, "duplicate mut")) }
          muts2.push(a);
        }
        let var = self.build_variant(var)?;
        self.loops.push((label, false));
        let (cond, hyp, body) = self.with_ctx(|this| -> Result<_> { Ok((
          Box::new(this.build_expr(&span, cond)?),
          hyp.as_ref().map(|h| this.push_fresh(h.k)),
          Box::new(this.build_block(&span, body)?),
        ))})?;
        let has_break = self.loops.pop().expect("stack underflow").1;
        ast::ExprKind::While {label, muts: muts2.into(), var, cond, hyp, body, has_break}
      }
      ExprKind::Hole => ast::ExprKind::Infer(true),
    };
    Ok(Spanned {span, k})
  }

  #[allow(clippy::too_many_arguments)]
  fn build_match<T>(&mut self, span: &FileSpan,
    scvar: Option<VarId>, scrut: &Rc<ast::Expr>, branches: Vec<Spanned<(LispVal, LispVal)>>,
    allow_hyps: bool,
    mut mkblock: impl FnMut(Vec<ast::Stmt>, Spanned<T>) -> T,
    mut mkif: impl FnMut(Option<VarId>, Box<ast::Expr>, Box<Spanned<T>>, Box<Spanned<T>>) -> T,
    mut case: impl FnMut(&mut Self, LispVal) -> Result<Spanned<T>>
  ) -> Result<T> {
    macro_rules! sp {($sp:expr, $k:expr) => {Spanned {span: $sp.clone(), k: $k}}}

    struct PushPattern<'a, 'p> {
      ba: &'p mut BuildAst<'a>,
      bind: bool,
      scvar: Option<VarId>,
      scrut: &'p Rc<ast::Expr>,
      uses_hyp: bool,
      posblock: Vec<ast::Stmt>,
      negblock: Vec<ast::Stmt>,
    }

    impl<'a, 'p> PushPattern<'a, 'p> {
      fn push_pattern(&mut self,
        base: &FileSpan,
        pos: Option<&dyn Fn() -> ast::Expr>,
        neg: Option<&dyn Fn() -> ast::Expr>,
        pat: &LispVal,
      ) -> Result<Option<ast::Expr>> {
        macro_rules! binop {($op:expr, $e1:expr, $e2:expr) => {ast::ExprKind::Binop($op, Box::new($e1), Box::new($e2))}}
        fn binop(sp: &FileSpan, op: Binop, e1: ast::Expr, e2: ast::Expr) -> ast::Expr {
          sp!(sp, binop!(op, e1, e2))
        }
        let Spanned {span, k} = self.ba.p.parse_pattern(base, self.ba.names, pat)?;
        let sp = &span;
        let mkscr = || sp!(sp, ast::ExprKind::Rc(self.scrut.clone()));
        Ok(match k {
          PatternKind::Var(AtomId::UNDER) => None,
          PatternKind::Var(a) => {
            if let Some(v) = self.scvar { self.ba.push(a, v) }
            else if self.bind { unreachable!() }
            else { return Err(ElabError::new_e(&span, "can't bind variables in this context")) }
            None
          }
          PatternKind::Const(a) => Some(binop(sp, Binop::Eq, mkscr(), sp!(sp, ast::ExprKind::Const(a)))),
          PatternKind::Number(n) => Some(binop(sp, Binop::Eq, mkscr(), sp!(sp, ast::ExprKind::Int(n)))),
          PatternKind::Hyped(name, pat) => {
            if !self.bind || pos.is_none() && neg.is_none() {
              return Err(ElabError::new_e(&span, "can't bind variables in this context"))
            }
            self.uses_hyp = true;
            let v = self.ba.fresh_var(name);
            let cl = move || sp!(sp, ast::ExprKind::Var(v));
            let pos: Option<&dyn Fn() -> ast::Expr> = if let Some(f) = pos {
              self.posblock.push(let_var(sp, name, v, f()));
              Some(&cl)
            } else { pos };
            let neg: Option<&dyn Fn() -> ast::Expr> = if let Some(f) = neg {
              self.negblock.push(let_var(sp, name, v, f()));
              Some(&cl)
            } else { neg };
            Some(self.push_pattern(sp, pos, neg, &pat)?
              .unwrap_or_else(|| sp!(sp, ast::ExprKind::Bool(true))))
          }
          PatternKind::With(pat, e) => {
            let cl;
            let pos: Option<&dyn Fn() -> ast::Expr> = match pos {
              None => None,
              Some(f) => {
                cl = move || sp!(sp, ast::ExprKind::Proj(Box::new(f()),
                  sp!(sp, FieldName::Number(0))));
                Some(&cl)
              }
            };
            let pat = self.push_pattern(sp, pos, None, &pat)?;
            let e = self.ba.build_expr(&span, e)?;
            Some(match pat {
              Some(p) => binop(sp, Binop::And, p, e),
              None => e
            })
          }
          PatternKind::Or(pats) => {
            fn projn(sp: &FileSpan, mut x: ast::Expr, n: usize) -> ast::Expr {
              macro_rules! proj {($e:expr, $n:expr) => {
                sp!(sp, ast::ExprKind::Proj(Box::new($e), sp!(sp, FieldName::Number($n))))
              }}
              for _ in 0..n { x = proj!(x, 1) }
              proj!(x, 0)
            }
            let mut args = Some(vec![]);
            for pat in pats {
              let cl;
              let neg: Option<&dyn Fn() -> ast::Expr> = if let (Some(f), Some(args)) = (neg, &args) {
                let n = args.len();
                cl = move || projn(sp, f(), n);
                Some(&cl)
              } else {
                None
              };
              if let Some(p) = self.push_pattern(sp, None, neg, &pat)? {
                if let Some(args) = &mut args {args.push(p)}
              } else { args = None }
            }
            args.map(|args| {
              let mut e = sp!(sp, ast::ExprKind::Bool(false));
              for arg in args.into_iter().rev() {
                e = binop(sp, Binop::Or, arg, e);
              }
              e
            })
          }
        })
      }
    }

    fn push_stmts<'a>(ba: &mut BuildAst<'a>, stmts: &[ast::Stmt]) {
      for st in stmts {
        if let ast::StmtKind::Let {lhs, ..} = &st.k {
          if let ast::TuplePatternKind::Name(_, name, v) = lhs.k {
            if name != AtomId::UNDER {
              ba.push(name, v)
            }
          }
        }
      }
    }

    let mut block = move |span: &FileSpan, stmts: Vec<ast::Stmt>, e: Spanned<T>| -> Spanned<T> {
      if stmts.is_empty() { e }
      else { Spanned {span: span.clone(), k: mkblock(stmts, e)} }
    };
    self.with_ctx(|this| {
      let mut stack = vec![];
      let mut iter = branches.into_iter();
      let mut e = loop {
        if let Some(Spanned {span, k: (lhs, rhs)}) = iter.next() {
          let hyp = this.fresh_var(AtomId::UNDER);
          let hvar = || Spanned {span: span.clone(), k: ast::ExprKind::Var(hyp)};
          let mut pp = PushPattern {
            ba: this,
            bind: allow_hyps,
            uses_hyp: false,
            scvar,
            scrut,
            posblock: vec![],
            negblock: vec![],
          };
          let result = pp.push_pattern(&span, Some(&hvar), Some(&hvar), &lhs)?;
          let PushPattern {posblock, negblock, uses_hyp, ..} = pp;
          let rhs = this.with_ctx(|this| {
            push_stmts(this, &posblock);
            case(this, rhs)
          })?;
          let rhs = block(&span, posblock, rhs);
          if let Some(cond) = result {
            stack.push((
              if uses_hyp {Some(hyp)} else {None},
              Box::new(cond),
              Box::new(rhs),
              negblock,
            ));
          } else {
            break rhs
          }
        } else {
          return Err(ElabError::new_e(&scrut.span, "incomplete pattern match"))
        }
      };
      if let Some(arm) = iter.next() {
        return Err(ElabError::new_e(&arm.span, "unreachable pattern"))
      }
      for (hyp, cond, tru, negblock) in stack.into_iter().rev() {
        e = block(span, negblock, e);
        e = Spanned {span: span.clone(), k: mkif(hyp, cond, tru, Box::new(e))};
      }
      Ok(e.k)
    })
  }

  fn build_block(&mut self, span: &FileSpan, es: Uncons) -> Result<ast::Block> {
    self.with_ctx(|this| {
      let mut stmts = Vec::with_capacity(es.len());
      let mut jumps: Vec<Spanned<Label>> = vec![];
      macro_rules! clear_jumps {() => {if !jumps.is_empty() {
        let (v, labels) = (this.push_jumps(std::mem::take(&mut jumps))?);
        stmts.push(Spanned {span: span.clone(), k: ast::StmtKind::Label(v, labels)});
      }}}
      for e in es {
        let Spanned {span: e_span, k} = this.p.parse_expr(span, e)?;
        if let ExprKind::Label(lab) = k {
          if jumps.iter().any(|l| l.k.name == lab.name) { clear_jumps!() }
          jumps.push(Spanned {span: e_span, k: lab})
        } else {
          clear_jumps!();
          if let ExprKind::Let {lhs, rhs, with: Renames {old, new}} = k {
            let rhs = this.build_expr(span, rhs)?;
            this.apply_rename(span, &old)?;
            let lhs = this.push_tuple_pattern(*lhs, None)?;
            this.apply_rename(span, &new)?;
            stmts.push(Spanned {span: e_span, k: ast::StmtKind::Let {lhs, rhs}})
          } else {
            stmts.push(this.push_parsed_expr(e_span, k)?.map_into(ast::StmtKind::Expr))
          }
        }
      }
      if let Some(Spanned {span, ..}) = jumps.first() {
        return Err(ElabError::new_e(span, "a labeled block is a statement, not an expression"))
      }
      let expr = if let Some(Spanned {k: ast::StmtKind::Expr(_), ..}) = stmts.last() {
        let_unchecked!(Some(Spanned {span, k: ast::StmtKind::Expr(expr)}) = stmts.pop(),
          Some(Box::new(Spanned {span, k: expr})))
      } else {
        None
      };
      Ok(ast::Block {stmts, expr})
    })
  }

  fn build_variant(&mut self, variant: Option<Box<Variant>>) -> Result<Option<Box<ast::Variant>>> {
    Ok(if let Some(variant) = variant {
      let Spanned {span, k: (e, vt)} = *variant;
      let e = self.build_expr(&span, e)?;
      let vt = match vt {
        VariantType::Down => ast::VariantType::Down,
        VariantType::UpLt(e) => ast::VariantType::UpLt(self.build_expr(&span, e)?),
        VariantType::UpLe(e) => ast::VariantType::UpLe(self.build_expr(&span, e)?),
      };
      Some(Box::new(Spanned {span, k: (e, vt)}))
    } else {None})
  }

  fn push_jumps(&mut self, jumps: Vec<Spanned<Label>>) -> Result<(VarId, Box<[ast::Label]>)> {
    let group = self.fresh_var(AtomId::UNDER);
    for (i, name) in jumps.iter().map(|j| j.k.name).enumerate() {
      self.push_label(name, LabelId(group, i.try_into().expect("label number overflow")));
    }
    let jumps = jumps.into_iter().map(|Spanned {span, k: Label {name: _, args, variant, body}}| {
      self.with_args(args, |this, args| Ok({
        let variant = this.build_variant(variant)?;
        let body = this.build_block(&span, body)?;
        ast::Label {args, variant, body: Spanned {span, k: body}}
      }))
    }).collect::<Result<_>>()?;
    Ok((group, jumps))
  }

  fn build_lassoc1(&mut self, span: &FileSpan, args: Vec<LispVal>, op: Binop) -> Result<Option<ast::Expr>> {
    let mut it = args.into_iter();
    Ok(if let Some(e) = it.next() {
      let mut out = self.build_expr(span, e)?;
      for e in it {
        let k = ast::ExprKind::binop(span, op, out, self.build_expr(span, e)?);
        out = Spanned {span: span.clone(), k};
      }
      Some(out)
    } else {None})
  }

  /// This function implements desugaring for chained inequalities.
  fn build_ineq(&mut self, sp: &FileSpan, args: Vec<LispVal>, op: Binop) -> Result<ast::ExprKind> {
    // Haskell pseudocode:
    // build_ineq [] = error
    // build_ineq [e1] = { e1; true }
    // build_ineq [e1, e2] = e1 < e2
    // build_ineq (e1:e2:e3:es) = { let v1 = e1; let v2 = e2; mk_and v1 v2 e3 es }
    // mk_and v0 v1 e2 es = (v0 < v1 && mk_block v1 e2 es)
    // mk_block v1 e2 [] = (v1 < e2)
    // mk_block v1 e2 (e3:es) = { let v2 = e2; mk_and v1 v2 e3 es }

    macro_rules! sp {($sp:expr, $k:expr) => {Spanned {span: $sp.clone(), k: $k}}}
    macro_rules! binop {($sp:expr, $op:expr, $e1:expr, $e2:expr) => {
      sp!($sp, ast::ExprKind::binop($sp, $op, $e1, $e2))
    }}
    macro_rules! block {($($e:expr),*; $last:expr) => {
      ast::ExprKind::Block(ast::Block {stmts: vec![$($e),*], expr: Some(Box::new($last))})
    }}
    fn binop(sp: &FileSpan, op: Binop, v1: VarId, e2: ast::Expr) -> ast::Expr {
      binop!(sp, op, sp!(sp, ast::ExprKind::Var(v1)), e2)
    }
    fn and(sp: &FileSpan, op: Binop, v1: VarId, v2: VarId, e: ast::Expr) -> ast::Expr {
      binop!(sp, Binop::And, binop(sp, op, v1, sp!(sp, ast::ExprKind::Var(v2))), e)
    }
    let mut it = args.into_iter();
    let arg_1 = it.next().ok_or_else(|| ElabError::new_e(sp, "inequality: syntax error"))?;
    let arg_1 = self.build_expr(sp, arg_1)?;
    Ok(if let Some(arg_2) = it.next() {
      let arg_2 = self.build_expr(sp, arg_2)?;
      if let Some(arg_3) = it.next() {
        fn mk_and(this: &mut BuildAst<'_>, sp: &FileSpan, op: Binop, v0: VarId, v1: VarId, e2: LispVal,
          mut it: std::vec::IntoIter<LispVal>
        ) -> Result<ast::Expr> {
          let e2 = this.build_expr(sp, e2)?;
          Ok(and(sp, op, v0, v1, if let Some(e3) = it.next() {
            let v2 = this.fresh_var(AtomId::UNDER);
            sp!(sp, block![
              let_var(sp, AtomId::UNDER, v2, e2);
              mk_and(this, sp, op, v1, v2, e3, it)?
            ])
          } else {
            binop(sp, op, v1, e2)
          }))
        }
        let v_1 = self.fresh_var(AtomId::UNDER);
        let v_2 = self.fresh_var(AtomId::UNDER);
        block![
          let_var(sp, AtomId::UNDER, v_1, arg_1),
          let_var(sp, AtomId::UNDER, v_2, arg_2);
          mk_and(self, sp, op, v_1, v_2, arg_3, it)?
        ]
      } else {
        ast::ExprKind::binop(sp, op, arg_1, arg_2)
      }
    } else {
      block![arg_1.map_into(ast::StmtKind::Expr); sp!(sp, ast::ExprKind::Bool(true))]
    })
  }

  fn build_call_expr(&mut self, span: FileSpan, e: CallExpr) -> Result<ast::Expr> {
    macro_rules! lassoc1 {
      ($args:expr, $zero:expr, $op:expr) => { lassoc1!($args, $zero, $op, |e| return Ok(e)) };
      ($args:expr, $zero:expr, $op:expr, |$e:pat| $arg:expr) => {
        if let Some($e) = self.build_lassoc1(&span, $args, {use Binop::*; $op})? { $arg }
        else { #[allow(unused)] use ast::ExprKind::*; $zero }
      }
    }
    if let Some(&LabelId(v, i)) = self.label_map.get(&e.f.k).and_then(|vec| vec.last()) {
      let args = e.args.into_iter().map(|e| self.build_expr(&span, e)).collect::<Result<_>>()?;
      let variant = if let Some(e) = e.variant {Some(Box::new(self.build_expr(&span, e)?))} else {None};
      return Ok(Spanned {span, k: ast::ExprKind::Jump(v, i, args, variant)})
    }
    let is_label = |a| self.label_map.get(&a).map_or(false, |v| !v.is_empty());
    let k = match self.p.parse_call(&span, self.names, is_label, e)? {
      CallKind::Const(a) => ast::ExprKind::Const(a),
      CallKind::Global(a) => return Err(ElabError::new_e(&span, format!(
        "variable '{}' not found. \
        A global with this name exists but must be imported into scope with\n  (global {0})\
        \nin the function signature.", self.p.fe.to(&a)))),
      CallKind::NAry(NAryCall::Add, args) => lassoc1!(args, Int(0.into()), Add),
      CallKind::NAry(NAryCall::Mul, args) => lassoc1!(args, Int(1.into()), Mul),
      CallKind::NAry(NAryCall::Min, args) => lassoc1!(args, unreachable!(), Min),
      CallKind::NAry(NAryCall::Max, args) => lassoc1!(args, unreachable!(), Max),
      CallKind::NAry(NAryCall::And, args) => lassoc1!(args, Bool(true), And),
      CallKind::NAry(NAryCall::Or, args) => lassoc1!(args, Bool(false), Or),
      CallKind::NAry(NAryCall::Not, args) => lassoc1!(args, Bool(true), Or, |e| {
        ast::ExprKind::Unop(Unop::Not, Box::new(e))
      }),
      CallKind::NAry(NAryCall::BitAnd, args) => lassoc1!(args, Int((-1).into()), BitAnd),
      CallKind::NAry(NAryCall::BitOr, args) => lassoc1!(args, Int(0.into()), BitOr),
      CallKind::NAry(NAryCall::BitXor, args) => lassoc1!(args, Int(0.into()), BitXor),
      CallKind::NAry(NAryCall::BitNot, args) => lassoc1!(args, Int((-1).into()), BitOr, |e| {
        ast::ExprKind::Unop(Unop::BitNot(Size::Inf), Box::new(e))
      }),
      CallKind::NAry(NAryCall::Le, args) => self.build_ineq(&span, args, Binop::Le)?,
      CallKind::NAry(NAryCall::Lt, args) => self.build_ineq(&span, args, Binop::Lt)?,
      CallKind::NAry(NAryCall::Eq, args) => self.build_ineq(&span, args, Binop::Eq)?,
      CallKind::NAry(NAryCall::Ne, args) => self.build_ineq(&span, args, Binop::Ne)?,
      CallKind::NAry(NAryCall::List, args) => ast::ExprKind::List(
        args.into_iter().map(|e| self.build_expr(&span, e)).collect::<Result<_>>()?),
      CallKind::NAry(NAryCall::Assert, args) => ast::ExprKind::Assert(Box::new(
        lassoc1!(args, Spanned {span: span.clone(), k: Infer(false)}, And, |e| e))),
      CallKind::NAry(NAryCall::GhostList, args) => match args.len() {
        0 => ast::ExprKind::Unit,
        1 => ast::ExprKind::Ghost(Box::new(self.build_expr(&span, unwrap_unchecked!(args.into_iter().next()))?)),
        _ => {
          let args = args.into_iter().map(|e| self.build_expr(&span, e)).collect::<Result<_>>()?;
          ast::ExprKind::Ghost(Box::new(Spanned {span: span.clone(), k: ast::ExprKind::List(args)}))
        }
      }
      CallKind::NAry(NAryCall::Return, args) => ast::ExprKind::Return(
        args.into_iter().map(|e| self.build_expr(&span, e)).collect::<Result<_>>()?),
      CallKind::Neg(e) => ast::ExprKind::Unop(Unop::Neg, Box::new(self.build_expr(&span, e)?)),
      CallKind::Sub(e, it) => {
        let mut out = self.build_expr(&span, e)?;
        for e in it {
          let k = ast::ExprKind::Binop(Binop::Sub, Box::new(out), Box::new(self.build_expr(&span, e)?));
          out = Spanned {span: span.clone(), k};
        }
        return Ok(out)
      }
      CallKind::Shl(a, b) => ast::ExprKind::Binop(Binop::Shl, Box::new(self.build_expr(&span, a)?), Box::new(self.build_expr(&span, b)?)),
      CallKind::Shr(a, b) => ast::ExprKind::Binop(Binop::Shr, Box::new(self.build_expr(&span, a)?), Box::new(self.build_expr(&span, b)?)),
      CallKind::Mm0(subst, e) => ast::ExprKind::Mm0(self.build_mm0_expr(&span, subst, e)?),
      CallKind::Typed(e, ty) => ast::ExprKind::Typed(Box::new(self.build_expr(&span, e)?), Box::new(self.build_ty(&span, &ty)?)),
      CallKind::As(e, ty) => ast::ExprKind::As(Box::new(self.build_expr(&span, e)?), Box::new(self.build_ty(&span, &ty)?)),
      CallKind::Cast(e, h) => ast::ExprKind::Cast(
        Box::new(self.build_expr(&span, e)?),
        if let Some(h) = h {Some(Box::new(self.build_expr(&span, h)?))} else {None}),
      CallKind::Pun(e, h) => ast::ExprKind::Pun(
        Box::new(self.build_expr(&span, e)?),
        if let Some(h) = h {Some(Box::new(self.build_expr(&span, h)?))} else {None}),
      CallKind::Sn(e, h) => ast::ExprKind::Sn(
        Box::new(self.build_expr(&span, e)?),
        if let Some(h) = h {Some(Box::new(self.build_expr(&span, h)?))} else {None}),
      CallKind::Uninit => ast::ExprKind::Uninit,
      CallKind::TypeofBang(e) => ast::ExprKind::Typeof(Box::new(self.build_expr(&span, e)?)),
      CallKind::Typeof(e) => {
        let k = ast::ExprKind::Ref(Box::new(self.build_expr(&span, e)?));
        ast::ExprKind::Typeof(Box::new(Spanned {span: span.clone(), k}))
      }
      CallKind::Sizeof(ty) => ast::ExprKind::Sizeof(Box::new(self.build_ty(&span, &ty)?)),
      CallKind::Ref(e) => ast::ExprKind::Ref(Box::new(self.build_expr(&span, e)?)),
      CallKind::Deref(e) => ast::ExprKind::Deref(Box::new(self.build_expr(&span, e)?)),
      CallKind::Borrow(e) => ast::ExprKind::Borrow(Box::new(self.build_expr(&span, e)?)),
      CallKind::Index(a, i, h) => ast::ExprKind::Index(
        Box::new(self.build_expr(&span, a)?),
        Box::new(self.build_expr(&span, i)?),
        if let Some(h) = h {Some(Box::new(self.build_expr(&span, h)?))} else {None}),
      CallKind::Slice(a, i, len, h) => ast::ExprKind::Slice(Box::new((
        self.build_expr(&span, a)?,
        self.build_expr(&span, i)?,
        self.build_expr(&span, len)?)),
        if let Some(h) = h {Some(Box::new(self.build_expr(&span, h)?))} else {None}),
      CallKind::Call(CallExpr {f, args, variant}, tyargs) => {
        let mut it = args.into_iter();
        ast::ExprKind::Call {f,
          tys: (&mut it).take(tyargs as usize).map(|ty| self.build_ty(&span, &ty)).collect::<Result<_>>()?,
          args: it.map(|e| self.build_expr(&span, e)).collect::<Result<_>>()?,
          variant: if let Some(e) = variant {Some(Box::new(self.build_expr(&span, e)?))} else {None},
        }
      },
      CallKind::Unreachable(None) => ast::ExprKind::Unreachable(Box::new(
        Spanned {span: span.clone(), k: ast::ExprKind::Infer(false)})),
      CallKind::Unreachable(Some(e)) => ast::ExprKind::Unreachable(Box::new(self.build_expr(&span, e)?)),
      CallKind::Jump(name, args, variant) => {
        let LabelId(v, i) = if let Some(name) = name {
          *self.label_map.get(&name).and_then(|v| v.last()).expect("is_label")
        } else {
          LabelId(self.loops.last().ok_or_else(||
            ElabError::new_e(&span, "can't break, not in a loop"))?.0, 0)
        };
        let args = args.into_iter().map(|e| self.build_expr(&span, e)).collect::<Result<_>>()?;
        let variant = if let Some(e) = variant {Some(Box::new(self.build_expr(&span, e)?))} else {None};
        ast::ExprKind::Jump(v, i, args, variant)
      }
      CallKind::Break(name, args) => ast::ExprKind::Break(
        if let Some(name) = name {
          self.label_map.get(&name).and_then(|v| v.last()).expect("is_label").0
        } else {
          let l = self.loops.last_mut().ok_or_else(||
            ElabError::new_e(&span, "can't break, not in a loop"))?;
          l.1 = true;
          l.0
        },
        Box::new(match args.len() {
          0 => Spanned {span: span.clone(), k: ast::ExprKind::Unit},
          1 => self.build_expr(&span, unwrap_unchecked!(args.into_iter().next()))?,
          _ => Spanned {span: span.clone(), k: ast::ExprKind::List(
            args.map(|e| self.build_expr(&span, e)).collect::<Result<_>>()?)}
        })
      ),
      CallKind::Error => ast::ExprKind::Error,
    };
    Ok(Spanned {span, k})
  }

  fn build_mm0_expr(&mut self,
    base: &FileSpan, subst: Box<[(AtomId, LispVal)]>, e: LispVal
  ) -> Result<Mm0Expr<ast::Expr>> {
    let subst = subst.into_vec().into_iter()
      .map(|(a, e)| Ok((a, self.build_expr(base, e)?)))
      .collect::<Result<_>>()?;
    self.p.parse_mm0_expr(base, e, subst, |e, a| {
      let v = *self.name_map.get(&a)?.last()?;
      Some(spanned(base, e, ast::ExprKind::Var(v)))
    })
  }

  fn build_proc(&mut self, sp: &FileSpan,
    Proc {kind, name, tyargs, args, mut rets, variant, body}: Proc
  ) -> Result<ast::ItemKind> {
    struct OutVal {
      ghost: bool,
      index: u32,
      name: AtomId,
      used: bool,
    }
    self.tyvars.extend(tyargs.iter().map(|p| p.k));
    let tyargs = tyargs.len().try_into().expect("too many type arguments");
    let mut outmap: Vec<OutVal> = vec![];
    let args = args.into_iter().enumerate().map(|(i, arg)| {
      if arg.k.0.out.is_some() {
        return Err(ElabError::new_e(&arg.span, "'out' not permitted on function arguments"))
      }
      let arg = self.push_arg(true, arg)?;
      if arg.k.0.contains(ast::ArgAttr::MUT) {
        if let Some((ghost, _)) = arg.k.1.var().as_single_name() {
          if let Some(&Ctx::Var(name, _)) = self.ctx.last() {
            if outmap.iter().any(|p| p.name == name) {
              return Err(ElabError::new_e(&arg.span, "'mut' variables cannot shadow"))
            }
            outmap.push(OutVal {
              ghost, name, used: false,
              index: i.try_into().expect("too many arguments"),
            });
          } else {unreachable!("bad context")}
        } else { return Err(ElabError::new_e(&arg.span, "cannot use tuple pattern with 'mut'")) }
      }
      Ok(arg)
    }).collect::<Result<Box<[_]>>>()?;
    let rets = self.with_ctx(|this| {
      for arg in &mut rets {
        if let Some(name) = &mut arg.k.0.out {
          if *name == AtomId::UNDER {
            if let Some(v) = arg.k.1.var().as_single_name() {*name = v}
          }
          if let Some(OutVal {used, ..}) = outmap.iter_mut().find(|p| p.name == *name) {
            if std::mem::replace(used, true) {
              return Err(ElabError::new_e(&arg.span, "two 'out' arguments to one 'mut'"))
            }
          } else {
            return Err(ElabError::new_e(&arg.span,
              "'out' does not reference a 'mut' in the function arguments"))
          }
        }
      }
      let mut rets2 = outmap.iter().filter(|val| !val.used)
        .map(|&OutVal {ghost, index, name, ..}|
          ast::Ret::Out(ghost, index, name, this.push_fresh(name), None))
        .collect::<Vec<_>>();
      for arg in rets {
        if arg.k.0.mut_ {
          return Err(ElabError::new_e(&arg.span, "'mut' not permitted on function returns"))
        }
        match arg.k.1 {
          ArgKind::Let(_, _) => return Err(ElabError::new_e(&arg.span, "assignment not permitted here")),
          ArgKind::Lam(pat) => rets2.push(match arg.k.0.out {
            None => ast::Ret::Reg(this.push_tuple_pattern(Spanned {span: arg.span, k: pat}, None)?),
            Some(name) => {
              let mut oty = None;
              let mut sp = &arg.span;
              let mut pat = &pat;
              loop {
                match pat {
                  &TuplePatternKind::Name(g, name2) => {
                    let v = this.fresh_var(name2);
                    this.push(name2, v);
                    let &OutVal {ghost, index, ..} = outmap.iter().find(|p| p.name == name).expect("checked");
                    break ast::Ret::Out(ghost || g, index, name, v, oty)
                  }
                  TuplePatternKind::Typed(pat2, ty) => {
                    if oty.replace(Box::new(this.build_ty(sp, ty)?)).is_some() {
                      return Err(ElabError::new_e(&arg.span, "double type ascription not permitted here"))
                    }
                    sp = &pat2.span;
                    pat = &pat2.k;
                  }
                  TuplePatternKind::Tuple(_) =>
                    return Err(ElabError::new_e(sp, "tuple pattern not permitted in 'out' returns"))
                }
              }
            }
          })
        }
      }
      Ok(rets2)
    })?;
    let variant = self.build_variant(variant)?;
    let body = self.build_block(sp, body)?;
    Ok(ast::ItemKind::Proc {kind, name, tyargs, args, rets, variant, body})
  }

  /// Construct the AST for a top level item, as produced by [`Parser::parse_next_item`].
  pub fn build_item(&mut self, Spanned {span, k: item}: Item) -> Result<ast::Item> {
    let k = match item {
      ItemKind::Proc(proc) => self.build_proc(&span, proc)?,
      ItemKind::Global(lhs, rhs) => {
        let rhs = self.build_expr(&span, rhs)?;
        let lhs = self.push_tuple_pattern(*lhs, None)?;
        ast::ItemKind::Global {lhs, rhs}
      }
      ItemKind::Const(lhs, rhs) => {
        let rhs = self.build_expr(&span, rhs)?;
        let lhs = self.push_tuple_pattern(*lhs, None)?;
        ast::ItemKind::Const {lhs, rhs}
      }
      ItemKind::Typedef {name, tyargs, args, val} => {
        self.tyvars.extend(tyargs.iter().map(|p| p.k));
        let tyargs = tyargs.len().try_into().expect("too many type arguments");
        self.with_args(args, |this, args| {
          let val = this.build_ty(&span, &val)?;
          Ok(ast::ItemKind::Typedef {name, tyargs, args, val})
        })?
      }
      ItemKind::Struct {name, tyargs, args, fields} => {
        self.tyvars.extend(tyargs.iter().map(|p| p.k));
        let tyargs = tyargs.len().try_into().expect("too many type arguments");
        self.with_args(args, |this, args| {
          this.with_args(fields, |_, fields| Ok(ast::ItemKind::Typedef {
            name, tyargs, args,
            val: Spanned {span: span.clone(), k: ast::TypeKind::Struct(fields)}
          }))
        })?
      }
    };
    Ok(Spanned {span, k})
  }
}