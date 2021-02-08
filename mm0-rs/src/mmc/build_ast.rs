//! The AST building compiler pass.
//!
//! This pass is responsible mainly for name resolution. The [parser](super::parser) works on-demand,
//! so the entire parsed MMC syntax doesn't exist all at once, but conceptually it is made up of recursive
//! applications of the constructors in [`types::parser`](super::types::parser). This contains `AtomId`s
//! referencing variable names as provided by the user, and the task here is to undo all the name shadowing
//! and resolve references to loop labels, named constants, and so on, so that elaboration has a
//! reasonably well formed input to work on.
//!
//! The output of this stage is a full AST according to the types in the
//! [`types::ast`](super::types::ast) module.

use std::{collections::{HashMap, hash_map::Entry}, convert::TryInto};

use crate::elab::{ElabError, Result, environment::AtomId, lisp::{LispVal, Uncons}};
use crate::util::FileSpan;
use super::types::{Binop, Mm0Expr, Size, Spanned, Unop, VarId, ast};
#[allow(clippy::wildcard_imports)] use super::types::parse::*;
use super::types::entity::Entity;
use super::parser::Parser;

///
#[derive(Copy, Clone, Debug)]
struct LabelId(VarId, u16);

#[derive(Debug)]
enum Ctx {
  Var(AtomId, VarId),
  Label(AtomId, LabelId),
  Loop(VarId),
}

/// The state of the AST building pass.
#[derive(Debug)]
pub struct BuildAst<'a> {
  /// The global mapping of names to entities (globals, constants, intrinsics).
  names: &'a HashMap<AtomId, Entity>,
  /// The parser, which we use to parse `LispVal` terms into [`types::parser`](super::types::parser)
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
  ///
  /// This is a cache for `ctx`: `loops` is exactly the
  /// list of `v` such that `Loop(v)` is in `ctx` (in order).
  loops: Vec<VarId>,
  /// The context, which contains information about scoped names. Scopes are created by
  /// [`with_ctx`](Self::with_ctx), which remembers the size of the context on entering the scope
  /// and pops everything that has been added when we get to the end of the scope.
  ctx: Vec<Ctx>,
  /// The list of type variables in scope.
  tyvars: Vec<AtomId>,
  /// The first unused variable ID, used for fresh name generation.
  next_var: VarId,
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
      next_var: VarId::default(),
      tyvars: vec![]
    }
  }

  fn clear(&mut self) {
    self.name_map.clear();
    self.ctx.clear();
    self.next_var = VarId::default();
  }

  fn pop(&mut self) {
    match self.ctx.pop().expect("stack underflow") {
      Ctx::Var(name, _) => {self.name_map.get_mut(&name).and_then(Vec::pop).expect("stack underflow");}
      Ctx::Label(name, _) => {self.label_map.get_mut(&name).and_then(Vec::pop).expect("stack underflow");}
      Ctx::Loop(_) => {self.loops.pop().expect("stack underflow");}
    }
  }

  fn fresh_var(&mut self) -> VarId {
    let v = self.next_var;
    self.next_var.0 += 1;
    v
  }

  fn push_fresh(&mut self, name: AtomId) -> VarId {
    let v = self.fresh_var();
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

  fn push_loop(&mut self, label: VarId) {
    self.ctx.push(Ctx::Loop(label));
    self.loops.push(label);
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

  fn mk_split(&mut self, sp: &FileSpan, Renames {old, new}: Renames) -> Result<HashMap<VarId, (AtomId, AtomId, VarId)>> {
    let mut map = HashMap::new();
    for (from, to) in old {
      if from == AtomId::UNDER { return Err(ElabError::new_e(sp, "can't rename variable '_'")) }
      map.entry(self.get_var(sp, from)?).or_insert_with(|| (from, from, self.fresh_var())).0 = to;
    }
    for (from, to) in new {
      if from == AtomId::UNDER { return Err(ElabError::new_e(sp, "can't rename variable '_'")) }
      map.entry(self.get_var(sp, from)?).or_insert_with(|| (from, from, self.fresh_var())).1 = to;
    }
    Ok(map)
  }

  fn add_origins(e: &ast::Expr, f: &mut impl FnMut(VarId) -> Result<()>) -> Result<()> {
    match &e.k {
      &ast::ExprKind::Var(v) => f(v)?,
      ast::ExprKind::Index(e, _, _) |
      ast::ExprKind::Proj(e, _) |
      ast::ExprKind::Slice(e, _, _) |
      ast::ExprKind::Ghost(e) |
      ast::ExprKind::Ref(e) => Self::add_origins(e, f)?,
      ast::ExprKind::Block(es) => if let Some(e) = es.last() {Self::add_origins(e, f)?},
      ast::ExprKind::If {then, els, ..} => {Self::add_origins(then, f)?; Self::add_origins(els, f)?}
      ast::ExprKind::Match(_, pats) => for (_, e) in &**pats {Self::add_origins(e, f)?},
      _ => {}
    }
    Ok(())
  }

  fn push_tuple_pattern(&mut self, Spanned {span, k: pat}: TuplePattern) -> Result<ast::TuplePattern> {
    Ok(Spanned {span, k: match pat {
      TuplePatternKind::Name(g, name) => ast::TuplePatternKind::Name(g, self.push_fresh(name)),
      TuplePatternKind::Typed(pat, ty) => {
        let ty = self.build_ty(&ty)?;
        let pat = self.push_tuple_pattern(*pat)?;
        ast::TuplePatternKind::Typed(Box::new(pat), Box::new(ty))
      }
      TuplePatternKind::Tuple(pats) => ast::TuplePatternKind::Tuple(
        pats.into_iter().map(|pat| self.push_tuple_pattern(pat)).collect::<Result<_>>()?),
    }})
  }

  fn push_pattern(&mut self, pos: bool, neg: bool, negp: &mut Vec<(AtomId, VarId)>, pat: &LispVal) -> Result<ast::Pattern> {
    let Spanned {span, k} = self.p.parse_pattern(self.names, pat)?;
    let k = match k {
      PatternKind::Var(AtomId::UNDER) => ast::PatternKind::Var(self.fresh_var()),
      PatternKind::Var(a) => ast::PatternKind::Var(self.push_fresh(a)),
      PatternKind::Const(a) => ast::PatternKind::Const(a),
      PatternKind::Number(n) => ast::PatternKind::Number(n),
      PatternKind::Hyped(name, pat) => {
        let pn = ast::PosNeg::new(pos, neg).ok_or_else(||
          ElabError::new_e(&span, "can't bind pattern either positively or negatively here"))?;
        let pat = self.push_pattern(pos, neg, negp, &pat)?;
        let h = self.fresh_var();
        if pos { self.push(name, h) }
        if neg { negp.push((name, h)) }
        ast::PatternKind::Hyped(pn, h, Box::new(pat))
      }
      PatternKind::With(pat, e) => ast::PatternKind::With(
        Box::new(self.push_pattern(pos, false, negp, &pat)?),
        Box::new(self.build_expr(e)?)),
      PatternKind::Or(pats) => ast::PatternKind::Or(
        pats.map(|pat| self.push_pattern(false, neg, negp, &pat)).collect::<Result<_>>()?),
    };
    Ok(Spanned {span, k})
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
      let pats = pats.into_iter().map(|pat| this.push_tuple_pattern(pat)).collect::<Result<_>>()?;
      f(this, pats)
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

  fn build_ty(&mut self, ty: &LispVal) -> Result<ast::Type> {
    let Spanned {span, k: ty} = self.p.parse_ty(self.names, ty)?;
    let k = match ty {
      TypeKind::Unit => ast::TypeKind::Unit,
      TypeKind::Bool => ast::TypeKind::Bool,
      TypeKind::Var(name) => {
        let v = self.tyvars.iter().rposition(|&v| name == v).ok_or_else(||
          ElabError::new_e(&span, format!("unknown type variable '{}'", self.p.fe.to(&name))))?;
        ast::TypeKind::Var(v.try_into().expect("too many vars"))
      }
      TypeKind::Int(sz) => ast::TypeKind::Int(sz),
      TypeKind::UInt(sz) => ast::TypeKind::UInt(sz),
      TypeKind::Array(ty, n) => {
        let ty = self.build_ty(&ty)?;
        let n = self.build_expr(n)?;
        ast::TypeKind::Array(Box::new(ty), Box::new(n))
      },
      TypeKind::Own(ty) => ast::TypeKind::Own(Box::new(self.build_ty(&ty)?)),
      TypeKind::Ref(lft, ty) => ast::TypeKind::Ref(self.build_lft(lft)?, Box::new(self.build_ty(&ty)?)),
      TypeKind::Shr(lft, ty) => ast::TypeKind::Shr(self.build_lft(lft)?, Box::new(self.build_ty(&ty)?)),
      TypeKind::RefSn(e) => ast::TypeKind::RefSn(Box::new(self.build_expr(e)?)),
      TypeKind::List(tys) => ast::TypeKind::List(tys.iter().map(|ty| self.build_ty(ty)).collect::<Result<_>>()?),
      TypeKind::Single(e) => ast::TypeKind::Single(Box::new(self.build_expr(e)?)),
      TypeKind::Struct(pats) => ast::TypeKind::Struct(self.with_tuple_patterns(pats.into_vec(), |_, x| Ok(x))?),
      TypeKind::And(tys) => ast::TypeKind::And(tys.iter().map(|ty| self.build_ty(ty)).collect::<Result<_>>()?),
      TypeKind::Or(tys) => ast::TypeKind::Or(tys.iter().map(|ty| self.build_ty(ty)).collect::<Result<_>>()?),
      TypeKind::Ghost(ty) => ast::TypeKind::Ghost(Box::new(self.build_ty(&ty)?)),
      TypeKind::Prop(pk) => ast::TypeKind::Prop(Box::new(self.build_parsed_prop(span.clone(), pk)?)),
      TypeKind::User(f, tys, es) => {
        let tys = tys.into_vec().iter().map(|ty| self.build_ty(ty)).collect::<Result<_>>()?;
        let es = es.into_vec().into_iter().map(|e| self.build_expr(e)).collect::<Result<_>>()?;
        ast::TypeKind::User(f, tys, es)
      },
      TypeKind::Input => ast::TypeKind::Input,
      TypeKind::Output => ast::TypeKind::Output,
      TypeKind::Moved(ty) => ast::TypeKind::Moved(Box::new(self.build_ty(&ty)?)),
    };
    Ok(Spanned {span, k})
  }

  fn build_prop(&mut self, p: &LispVal) -> Result<ast::Prop> {
    let Spanned {span, k} = self.p.parse_prop(self.names, p)?;
    self.build_parsed_prop(span, k)
  }

  fn build_parsed_prop(&mut self, span: FileSpan, pk: PropKind) -> Result<ast::Prop> {
    let k = match pk {
      PropKind::True => ast::PropKind::True,
      PropKind::False => ast::PropKind::False,
      PropKind::Emp => ast::PropKind::Emp,
      PropKind::All(args, p) => self.with_tuple_patterns(args, |this, args| {
        Ok(ast::PropKind::All(args, Box::new(this.build_prop(&p)?)))
      })?,
      PropKind::Ex(args, p) => self.with_tuple_patterns(args, |this, args| {
        Ok(ast::PropKind::Ex(args, Box::new(this.build_prop(&p)?)))
      })?,
      PropKind::Not(p) => ast::PropKind::Not(Box::new(self.build_prop(&p)?)),
      PropKind::And(ps) => ast::PropKind::And(
        ps.iter().map(|p| self.build_prop(p)).collect::<Result<_>>()?),
      PropKind::Or(ps) => ast::PropKind::Or(
        ps.iter().map(|p| self.build_prop(p)).collect::<Result<_>>()?),
      PropKind::Sep(ps) => ast::PropKind::Sep(
        ps.iter().map(|p| self.build_prop(p)).collect::<Result<_>>()?),
      PropKind::Imp(p1, p2) => ast::PropKind::Imp(Box::new(self.build_prop(&p1)?), Box::new(self.build_prop(&p2)?)),
      PropKind::Wand(p1, p2) => ast::PropKind::Wand(Box::new(self.build_prop(&p1)?), Box::new(self.build_prop(&p2)?)),
      PropKind::Pure(e) => ast::PropKind::Pure(Box::new(self.build_parsed_expr(span.clone(), e)?)),
      PropKind::Eq(e1, e2) => ast::PropKind::Eq(Box::new(self.build_expr(e1)?), Box::new(self.build_expr(e2)?)),
      PropKind::Heap(e1, e2) => ast::PropKind::Heap(Box::new(self.build_expr(e1)?), Box::new(self.build_expr(e2)?)),
      PropKind::HasTy(e, ty) => ast::PropKind::HasTy(Box::new(self.build_expr(e)?), Box::new(self.build_ty(&ty)?)),
      PropKind::Moved(p) => ast::PropKind::Moved(Box::new(self.build_prop(&p)?)),
      PropKind::Mm0(e) => ast::PropKind::Mm0(self.build_mm0_expr(e)?),
    };
    Ok(Spanned {span, k})
  }

  fn build_expr(&mut self, e: LispVal) -> Result<ast::Expr> {
    self.with_ctx(|this| this.push_expr(e))
  }

  fn push_expr(&mut self, e: LispVal) -> Result<ast::Expr> {
    let Spanned {span, k} = self.p.parse_expr(e)?;
    self.push_parsed_expr(span, k)
  }

  fn build_parsed_expr(&mut self, span: FileSpan, ek: ExprKind) -> Result<ast::Expr> {
    self.with_ctx(|this| this.push_parsed_expr(span, ek))
  }

  fn push_parsed_expr(&mut self, span: FileSpan, ek: ExprKind) -> Result<ast::Expr> {
    let k = match ek {
      ExprKind::Unit => ast::ExprKind::Unit,
      ExprKind::Var(name) => ast::ExprKind::Var(self.get_var(&span, name)?),
      ExprKind::Bool(b) => ast::ExprKind::Bool(b),
      ExprKind::Int(n) => ast::ExprKind::Int(n),
      ExprKind::Let {lhs, rhs, with: Renames {old, new}} => {
        let rhs = Box::new(self.build_expr(rhs)?);
        self.apply_rename(&span, &old)?;
        let lhs = self.push_tuple_pattern(*lhs)?;
        self.apply_rename(&span, &new)?;
        ast::ExprKind::Let {lhs, rhs}
      }
      ExprKind::Assign {lhs, rhs, with} => {
        let lhs = self.build_expr(lhs)?;
        let rhs = Box::new(self.build_expr(rhs)?);
        let mut split = self.mk_split(&span, with)?;
        Self::add_origins(&lhs, &mut |var| {
          if let Entry::Vacant(e) = split.entry(var) {
            if let Some(from) = self.ctx.iter().find_map(|v| match *v { Ctx::Var(a, v) if v == var => Some(a), _ => None}) {
              e.insert((from, from, self.fresh_var()));
            }
          }
          Ok(())
        })?;
        for (vfrom, (from, to, vto)) in split {
          self.push(from, vfrom);
          self.push(to, vto);
        }
        ast::ExprKind::Assign {lhs: Box::new(lhs), rhs}
      }
      ExprKind::Proj(e, i) => ast::ExprKind::Proj(Box::new(self.build_expr(e)?), i),
      ExprKind::Call(c) => return self.build_call_expr(span, c),
      ExprKind::Entail(p, hs) => ast::ExprKind::Entail(p,
        hs.into_iter().map(|h| self.build_expr(h)).collect::<Result<_>>()?),
      ExprKind::Block(es) => ast::ExprKind::Block(self.build_block(&span, es)?),
      ExprKind::Label(Label {args, body, ..}) if args.is_empty() => ast::ExprKind::Block(self.build_block(&span, body)?),
      ExprKind::Label(_) => return Err(ElabError::new_e(&span, "a labeled block is a statement, not an expression")),
      ExprKind::If {branches, els} => self.with_ctx(|this| -> Result<_> {
        let branches = branches.into_iter().map(|(h, cond, then)| {
          let cond = Box::new(this.build_expr(cond)?);
          let h = h.map(|h| this.push_fresh(h));
          let then = Box::new(this.build_expr(then)?);
          Ok((h, cond, then))
        }).collect::<Result<Vec<_>>>()?;
        let mut ret = if let Some(els) = els {this.push_expr(els)?.k} else {ast::ExprKind::Unit};
        for (hyp, cond, then) in branches.into_iter().rev() {
          let els = Box::new(Spanned {span: span.clone(), k: ret});
          ret = ast::ExprKind::If {hyp, cond, then, els};
        }
        Ok(ret)
      })?,
      ExprKind::Match(e, branches) => ast::ExprKind::Match(Box::new(self.build_expr(e)?),
        self.with_ctx(|this| branches.into_iter().map(|(lhs, rhs)| {
          let mut negp = vec![];
          let res = this.with_ctx(|this| -> Result<_> {
            Ok((this.push_pattern(true, true, &mut negp, &lhs)?, this.push_expr(rhs)?))
          })?;
          for (name, v) in negp { this.push(name, v) }
          Ok(res)
        }).collect::<Result<_>>())?),
      ExprKind::While {hyp, cond, var, body} => {
        let label = self.fresh_var();
        let cond = Box::new(self.build_expr(cond)?);
        let var = self.build_variant(var)?;
        let hyp = hyp.map(|h| self.push_fresh(h.k));
        let body = self.with_ctx(|this| {
          this.push_loop(label);
          this.build_block(&span, body)
        })?;
        let body = Box::new(Spanned {span: span.clone(), k: ast::ExprKind::Block(body)});
        ast::ExprKind::While {label, hyp, cond, var, body}
      },
      ExprKind::Hole => ast::ExprKind::Infer(true),
    };
    Ok(Spanned {span, k})
  }

  fn build_block(&mut self, span: &FileSpan, es: Uncons) -> Result<Vec<ast::Expr>> {
    self.with_ctx(|this| {
      let mut res = Vec::with_capacity(es.len());
      let mut jumps: Vec<Spanned<Label>> = vec![];
      macro_rules! clear_jumps {() => {if !jumps.is_empty() {
        let (v, labels) = (this.push_jumps(std::mem::take(&mut jumps))?);
        res.push(Spanned {span: span.clone(), k: ast::ExprKind::Label(v, labels)});
      }}}
      for e in es {
        let Spanned {span: e_span, k} = this.p.parse_expr(e)?;
        if let ExprKind::Label(lab) = k {
          if jumps.iter().any(|l| l.k.name == lab.name) { clear_jumps!() }
          jumps.push(Spanned {span: e_span, k: lab})
        } else {
          clear_jumps!();
          res.push(this.push_parsed_expr(e_span, k)?);
        }
      }
      if let Some(Spanned {span, ..}) = jumps.first() {
        return Err(ElabError::new_e(span, "a labeled block is a statement, not an expression"))
      }
      Ok(res)
    })
  }

  fn build_variant(&mut self, variant: Option<Box<Variant>>) -> Result<Option<Box<ast::Variant>>> {
    Ok(if let Some(variant) = variant {
      let Spanned {span, k: (e, vt)} = *variant;
      Some(Box::new(Spanned {span, k: (self.build_expr(e)?, match vt {
        VariantType::Down => ast::VariantType::Down,
        VariantType::UpLt(e) => ast::VariantType::UpLt(self.build_expr(e)?),
        VariantType::UpLe(e) => ast::VariantType::UpLe(self.build_expr(e)?),
      })}))
    } else {None})
  }

  fn push_jumps(&mut self, jumps: Vec<Spanned<Label>>) -> Result<(VarId, Box<[ast::Label]>)> {
    let group = self.fresh_var();
    for (i, name) in jumps.iter().map(|j| j.k.name).enumerate() {
      self.push_label(name, LabelId(group, i.try_into().expect("label number overflow")));
    }
    let jumps = jumps.into_iter().map(|Spanned {span, k: Label {name: _, args, variant, body}}| {
      self.with_tuple_patterns(args, |this, args| Ok({
        let variant = this.build_variant(variant)?;
        let body = this.build_block(&span, body)?;
        let body = Box::new(Spanned {span, k: ast::ExprKind::Block(body)});
        ast::Label {args, variant, body}
      }))
    }).collect::<Result<_>>()?;
    Ok((group, jumps))
  }

  fn build_lassoc1(&mut self, span: &FileSpan, args: Vec<LispVal>, op: Binop) -> Result<Option<ast::Expr>> {
    let mut it = args.into_iter();
    Ok(if let Some(e) = it.next() {
      let mut out = self.build_expr(e)?;
      for e in it {
        let k = ast::ExprKind::Binop(op, Box::new(out), Box::new(self.build_expr(e)?));
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

    macro_rules! binop {($op:expr, $e1:expr, $e2:expr) => {ast::ExprKind::Binop($op, Box::new($e1), Box::new($e2))}}
    macro_rules! sp {($sp:expr, $k:expr) => {Spanned {span: $sp.clone(), k: $k}}}
    fn let_var(sp: &FileSpan, v: VarId, e: ast::Expr) -> ast::Expr {
      sp!(sp, ast::ExprKind::Let {
        lhs: sp!(sp, ast::TuplePatternKind::Name(false, v)),
        rhs: Box::new(e)
      })
    }
    fn binop(sp: &FileSpan, op: Binop, v1: VarId, e2: ast::Expr) -> ast::Expr {
      sp!(sp, binop!(op, sp!(sp, ast::ExprKind::Var(v1)), e2))
    }
    fn and(sp: &FileSpan, op: Binop, v1: VarId, v2: VarId, e: ast::Expr) -> ast::Expr {
      sp!(sp, binop!(Binop::And, binop(sp, op, v1, sp!(sp, ast::ExprKind::Var(v2))), e))
    }
    let mut it = args.into_iter();
    let arg_1 = it.next().ok_or_else(|| ElabError::new_e(sp, "inequality: syntax error"))?;
    let arg_1 = self.build_expr(arg_1)?;
    Ok(if let Some(arg_2) = it.next() {
      let arg_2 = self.build_expr(arg_2)?;
      if let Some(arg_3) = it.next() {
        fn mk_and(this: &mut BuildAst<'_>, sp: &FileSpan, op: Binop, v0: VarId, v1: VarId, e2: LispVal,
          mut it: std::vec::IntoIter<LispVal>
        ) -> Result<ast::Expr> {
          let e2 = this.build_expr(e2)?;
          Ok(and(sp, op, v0, v1, if let Some(e3) = it.next() {
            let v2 = this.fresh_var();
            sp!(sp, ast::ExprKind::Block(vec![
              let_var(sp, v2, e2),
              mk_and(this, sp, op, v1, v2, e3, it)?
            ]))
          } else {
            binop(sp, op, v1, e2)
          }))
        }
        let v_1 = self.fresh_var();
        let v_2 = self.fresh_var();
        ast::ExprKind::Block(vec![
          let_var(sp, v_1, arg_1),
          let_var(sp, v_2, arg_2),
          mk_and(self, sp, op, v_1, v_2, arg_3, it)?,
        ])
      } else {
        ast::ExprKind::Binop(op, Box::new(arg_1), Box::new(arg_2))
      }
    } else {
      ast::ExprKind::Block(vec![arg_1, sp!(sp, ast::ExprKind::Bool(true))])
    })
  }

  fn build_call_expr(&mut self, span: FileSpan, e: CallExpr) -> Result<ast::Expr> {
    macro_rules! lassoc1 {
      ($args:expr, $zero:expr, $op:expr) => { lassoc1!($args, $zero, $op, |e| return Ok(e)) };
      ($args:expr, $zero:expr, $op:expr, |$e:pat| $arg:expr) => {
        if let Some($e) = self.build_lassoc1(&span, $args, {use Binop::*; $op})? { $arg }
        else { use ast::ExprKind::*; $zero }
      }
    }
    if let Some(&LabelId(v, i)) = self.label_map.get(&e.f.k).and_then(|vec| vec.last()) {
      let args = e.args.into_iter().map(|e| self.build_expr(e)).collect::<Result<_>>()?;
      return Ok(Spanned {span, k: ast::ExprKind::Jump(v, i, args)})
    }
    let is_label = |a| self.label_map.get(&a).map_or(false, |v| !v.is_empty());
    let k = match self.p.parse_call(self.names, is_label, &span, e)? {
      CallKind::Const(a) => ast::ExprKind::Const(a),
      CallKind::NAry(NAryCall::Add, args) => lassoc1!(args, Int(0.into()), Add),
      CallKind::NAry(NAryCall::And, args) => lassoc1!(args, Bool(true), And),
      CallKind::NAry(NAryCall::Or, args) => lassoc1!(args, Bool(false), Or),
      CallKind::NAry(NAryCall::BitAnd, args) => lassoc1!(args, Int((-1).into()), BitAnd),
      CallKind::NAry(NAryCall::BitOr, args) => lassoc1!(args, Int(0.into()), BitOr),
      CallKind::NAry(NAryCall::BitXor, args) => lassoc1!(args, Int(0.into()), BitXor),
      CallKind::NAry(NAryCall::Mul, args) => lassoc1!(args, Int(1.into()), Mul),
      CallKind::NAry(NAryCall::BitNot, args) => lassoc1!(args, Int((-1).into()), BitOr, |e| {
        ast::ExprKind::Unop(Unop::BitNot(Size::Inf), Box::new(e))
      }),
      CallKind::NAry(NAryCall::Not, args) => lassoc1!(args, Bool(true), Or, |e| {
        ast::ExprKind::Unop(Unop::Not, Box::new(e))
      }),
      CallKind::NAry(NAryCall::Le, args) => self.build_ineq(&span, args, Binop::Le)?,
      CallKind::NAry(NAryCall::Lt, args) => self.build_ineq(&span, args, Binop::Lt)?,
      CallKind::NAry(NAryCall::Eq, args) => self.build_ineq(&span, args, Binop::Eq)?,
      CallKind::NAry(NAryCall::Ne, args) => self.build_ineq(&span, args, Binop::Ne)?,
      CallKind::NAry(NAryCall::List, args) => ast::ExprKind::List(
        args.into_iter().map(|e| self.build_expr(e)).collect::<Result<_>>()?),
      CallKind::NAry(NAryCall::Assert, args) => ast::ExprKind::Assert(Box::new(
        lassoc1!(args, Spanned {span: span.clone(), k: Infer(false)}, And, |e| e))),
      CallKind::NAry(NAryCall::GhostList, args) => match args.len() {
        0 => ast::ExprKind::Unit,
        1 => ast::ExprKind::Ghost(Box::new(self.build_expr(unwrap_unchecked!(args.into_iter().next()))?)),
        _ => {
          let args = args.into_iter().map(|e| self.build_expr(e)).collect::<Result<_>>()?;
          ast::ExprKind::Ghost(Box::new(Spanned {span: span.clone(), k: ast::ExprKind::List(args)}))
        }
      }
      CallKind::NAry(NAryCall::Return, args) => ast::ExprKind::Return(
        args.into_iter().map(|e| self.build_expr(e)).collect::<Result<_>>()?),
      CallKind::Mm0(e) => ast::ExprKind::Mm0(self.build_mm0_expr(e)?),
      CallKind::Typed(e, ty) => ast::ExprKind::Typed(Box::new(self.build_expr(e)?), Box::new(self.build_ty(&ty)?)),
      CallKind::As(e, ty) => ast::ExprKind::As(Box::new(self.build_expr(e)?), Box::new(self.build_ty(&ty)?)),
      CallKind::Pun(e, h) => ast::ExprKind::Pun(
        Box::new(self.build_expr(e)?),
        if let Some(h) = h {Some(Box::new(self.build_expr(h)?))} else {None}),
      CallKind::TypeofBang(e) => ast::ExprKind::Typeof(Box::new(self.build_expr(e)?)),
      CallKind::Typeof(e) => {
        let k = ast::ExprKind::Ref(Box::new(self.build_expr(e)?));
        ast::ExprKind::Typeof(Box::new(Spanned {span: span.clone(), k}))
      }
      CallKind::Index(a, i, h) => ast::ExprKind::Index(
        Box::new(self.build_expr(a)?),
        Box::new(self.build_expr(i)?),
        if let Some(h) = h {Some(Box::new(self.build_expr(h)?))} else {None}),
      CallKind::Slice(a, i, h) => ast::ExprKind::Slice(
        Box::new(self.build_expr(a)?),
        Box::new(self.build_expr(i)?),
        if let Some(h) = h {Some(Box::new(self.build_expr(h)?))} else {None}),
      CallKind::Call(CallExpr {f, args, variant}, tyargs) => {
        let mut it = args.into_iter();
        ast::ExprKind::Call {f,
          tys: (&mut it).take(tyargs as usize).map(|ty| self.build_ty(&ty)).collect::<Result<_>>()?,
          args: it.map(|e| self.build_expr(e)).collect::<Result<_>>()?,
          variant: if let Some(e) = variant {Some(Box::new(self.build_expr(e)?))} else {None},
        }
      },
      CallKind::Unreachable(None) => ast::ExprKind::Unreachable(Box::new(
        Spanned {span: span.clone(), k: ast::ExprKind::Infer(false)})),
      CallKind::Unreachable(Some(e)) => ast::ExprKind::Unreachable(Box::new(self.build_expr(e)?)),
      CallKind::Jump(name, args) => {
        let LabelId(v, i) = *self.label_map.get(&name).and_then(|v| v.last()).expect("is_label");
        let args = args.into_iter().map(|e| self.build_expr(e)).collect::<Result<_>>()?;
        ast::ExprKind::Jump(v, i, args)
      }
      CallKind::Break(name, args) => ast::ExprKind::Break(
        if let Some(name) = name {
          self.label_map.get(&name).and_then(|v| v.last()).expect("is_label").0
        } else {
          *self.loops.last().ok_or_else(|| ElabError::new_e(&span, "can't break, not in a loop"))?
        },
        Box::new(match args.len() {
          0 => Spanned {span: span.clone(), k: ast::ExprKind::Unit},
          1 => self.build_expr(unwrap_unchecked!(args.into_iter().next()))?,
          _ => Spanned {span: span.clone(), k: ast::ExprKind::List(
            args.map(|e| self.build_expr(e)).collect::<Result<_>>()?)}
        })
      ),
    };
    Ok(Spanned {span, k})
  }

  fn build_mm0_expr(&mut self, e: LispVal) -> Result<Mm0Expr<ast::Expr>> {
    self.p.parse_mm0_expr(e, |e, a| {
      let v = *self.name_map.get(&a)?.last()?;
      Some(self.p.spanned(e, ast::ExprKind::Var(v)))
    })
  }

  fn build_proc(&mut self, sp: &FileSpan, Proc {kind, name, args, rets, variant, body}: Proc) -> Result<ast::Proc> {
    let mut outmap: Vec<(u32, AtomId, bool)> = vec![];
    let args = args.into_iter().enumerate().map(|(i, (mo, pat))| {
      let pat = self.push_tuple_pattern(pat)?;
      match mo {
        MutOut::Out(_) => Err(ElabError::new_e(&pat.span, "'out' not permitted on function arguments")),
        MutOut::None => Ok((false, pat)),
        MutOut::Mut => if let ast::TuplePatternKind::Name(_, _) = pat.k {
          if let Some(&Ctx::Var(name, _)) = self.ctx.last() {
            if outmap.iter().any(|p| p.1 == name) {
              return Err(ElabError::new_e(&pat.span, "'mut' variables cannot shadow"))
            }
            outmap.push((i.try_into().expect("too many arguments"), name, false));
            Ok((true, pat))
          } else {unreachable!("bad context")}
        } else {
          Err(ElabError::new_e(&pat.span, "cannot use tuple pattern with 'mut'"))
        }
      }
    }).collect::<Result<Box<[_]>>>()?;
    let rets = self.with_ctx(|this| {
      for &(mo, ref pat) in &rets {
        if let MutOut::Out(name) = mo {
          if let Some((_, _, used)) = outmap.iter_mut().find(|p| p.1 == name) {
            if std::mem::replace(used, true) {
              return Err(ElabError::new_e(&pat.span, "two 'out' arguments to one 'mut'"))
            }
          } else {
            return Err(ElabError::new_e(&pat.span,
              "'out' does not reference a 'mut' in the function arguments"))
          }
        }
      }
      let mut rets2 = outmap.iter().filter(|&(_, _, used)| !used)
        .map(|&(i, name, _)| ast::Ret::OutAnon(i, this.push_fresh(name)))
        .collect::<Vec<_>>();
      for (mo, pat) in rets {
        rets2.push(match mo {
          MutOut::None => ast::Ret::Reg(this.push_tuple_pattern(pat)?),
          MutOut::Out(name) => ast::Ret::Out(
            outmap.iter().find(|p| p.1 == name).expect("checked").0,
            this.push_tuple_pattern(pat)?),
          MutOut::Mut => return Err(ElabError::new_e(&pat.span, "'mut' not permitted on function returns")),
        })
      }
      Ok(rets2)
    })?;
    let variant = self.build_variant(variant)?;
    let body = self.build_block(sp, body)?;
    Ok(ast::Proc {kind, name, args, rets, variant, body})
  }

  /// Construct the AST for a top level item, as produced by [`Parser::parse_next_item`].
  pub fn build_item(&mut self, Spanned {span, k: item}: Item) -> Result<ast::Item> {
    self.clear();
    let k = match item {
      ItemKind::Proc(proc) => ast::ItemKind::Proc(self.build_proc(&span, proc)?),
      ItemKind::Global(lhs, rhs) => {
        let lhs = self.push_tuple_pattern(*lhs)?;
        let rhs = self.push_expr(rhs)?;
        ast::ItemKind::Global {lhs, rhs}
      }
      ItemKind::Const(lhs, rhs) => {
        let lhs = self.push_tuple_pattern(*lhs)?;
        let rhs = self.push_expr(rhs)?;
        ast::ItemKind::Const {lhs, rhs}
      }
      ItemKind::Typedef {name, args, val} => self.with_tuple_patterns(args, |this, args| {
        let val = this.build_ty(&val)?;
        Ok(ast::ItemKind::Typedef {name, args, val})
      })?,
      ItemKind::Struct {name, args, fields} => self.with_tuple_patterns(args, |this, args| {
        this.with_tuple_patterns(fields, |_, fields| Ok(ast::ItemKind::Struct {name, args, fields}))
      })?,
    };
    Ok(Spanned {span, k})
  }
}