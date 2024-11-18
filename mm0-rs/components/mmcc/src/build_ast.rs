//! The AST building compiler pass.
//!
//! This pass is responsible mainly for name resolution. The [parser](super::parser) works on-demand,
//! so the entire parsed MMC syntax doesn't exist all at once, but conceptually it is made up of recursive
//! applications of the constructors in [`types::parse`](super::types::parse). This contains `Symbol`s
//! referencing variable names as provided by the user, and the task here is to undo all the name shadowing
//! and resolve references to loop labels, named constants, and so on, so that elaboration has a
//! reasonably well formed input to work on.
//!
//! The output of this stage is a full AST according to the types in the
//! [`types::ast`](super::types::ast) module.

use std::collections::{HashMap, hash_map::Entry};
use std::fmt::Debug;
use std::marker::PhantomData;
use std::rc::Rc;
#[cfg(feature = "memory")] use mm0_deepsize_derive::DeepSizeOf;
use crate::{FileSpan, Symbol};
use crate::types::{Binop, Spanned, FieldName, VarId, IdxVec, ast::{self, LabelId}};

#[derive(Debug)]
enum Ctx {
  Var(VarId),
  Label(Symbol),
}

fn let_var(sp: &FileSpan, name: Spanned<Symbol>, v: VarId, rhs: ast::Expr) -> ast::Stmt {
  Spanned {span: sp.clone(), k: ast::StmtKind::Let {
    lhs: name.map_into(|name| ast::TuplePatternKind::Name(false, name, v)),
    rhs
  }}
}

/// The state of the AST building pass.
#[derive(Default, Debug)]
pub struct BuildAst {
  /// The mapping of user-level names to internal variable IDs. The vector represents name
  /// shadowing, with the active variable being the last in the list.
  ///
  /// This is a cache for `ctx`: `name_map.get(name)` is exactly the
  /// list of `v` such that `Var(name, v)` is in `ctx` (in order).
  name_map: HashMap<Symbol, Vec<VarId>>,
  /// The mapping of user-level labels to internal label IDs. The vector represents name
  /// shadowing, with the active label being the last in the list.
  ///
  /// This is a cache for `ctx`: `name_map.get(name)` is exactly the
  /// list of `v` such that `Label(name, v)` is in `ctx` (in order).
  label_map: HashMap<Symbol, Vec<LabelId>>,
  /// The mapping of anonymous loop targets to internal label IDs.
  /// The vector represents scoping, with the active loop being the last in the list.
  /// The boolean is true if there is a `break` to this loop target.
  loops: Vec<(VarId, bool)>,
  /// The context, which contains information about scoped names. Scopes are created by
  /// [`with_ctx`](Self::with_ctx), which remembers the size of the context on entering the scope
  /// and pops everything that has been added when we get to the end of the scope.
  ctx: Vec<Ctx>,
  /// The list of type variables in scope.
  tyvars: Vec<Symbol>,
  /// The mapping from allocated variables to their user facing names.
  pub var_names: IdxVec<VarId, Spanned<Symbol>>,
}

macro_rules! sp {($sp:expr, $k:expr) => {Spanned {span: $sp.clone(), k: $k}}}

impl BuildAst {
  /// Get a fresh variable name. Every new binding expression calls this function to prevent scope
  /// confusion issues when variable names are reused in multiple scopes.
  pub fn fresh_var(&mut self, name: Spanned<Symbol>) -> VarId { self.var_names.push(name) }

  /// Get a fresh variable name, and also push it to the context. References to `name` after this
  /// point will resolve to this variable, until the current scope is closed.
  pub fn push_fresh(&mut self, name: Spanned<Symbol>) -> VarId {
    let name_s = name.k;
    let v = self.fresh_var(name);
    self.push(name_s, v);
    v
  }

  /// Get a fresh variable name, and also push it to the context. References to `name` after this
  /// point will resolve to this variable, until the current scope is closed.
  pub fn push_fresh_span(&mut self, name: Spanned<Symbol>) -> Spanned<VarId> {
    sp!(name.span, self.push_fresh(name))
  }

  /// Push a variable with a given name to the context. (This is not exposed because we would like
  /// to prevent reuse of variables in new binding scopes.)
  fn push(&mut self, name: Symbol, v: VarId) {
    self.ctx.push(Ctx::Var(v));
    self.name_map.entry(name).or_default().push(v);
  }

  /// Push a named label. Uses of `break name` or `jump name` will target this label until the
  /// scope is closed.
  pub fn push_label(&mut self, name: Symbol, label: LabelId) {
    self.ctx.push(Ctx::Label(name));
    self.label_map.entry(name).or_default().push(label);
  }

  /// Push a label group from a list of names. Uses of any of the names will target this label
  /// group, until the scope is closed.
  pub fn push_label_group(&mut self, span: FileSpan, it: impl Iterator<Item=Symbol>) -> VarId {
    let group = self.fresh_var(Spanned { span, k: Symbol::UNDER });
    for (i, name) in it.enumerate() {
      self.push_label(name, LabelId(group, i.try_into().expect("label number overflow")));
    }
    group
  }

  /// Push a type variable. Uses of `name` as a type will resolve to this variable.
  /// Type variables are not scoped, since they are global to the item, and
  /// [`BuildAst`] is used for building a single item.
  pub fn push_tyvar(&mut self, name: &Spanned<Symbol>) { self.tyvars.push(name.k) }

  /// Get the total number of type variables that have been pushed.
  #[must_use] pub fn num_tyvars(&self) -> u32 {
    self.tyvars.len().try_into().expect("too many type arguments")
  }

  /// Get an (expression) variable by name.
  #[must_use] pub fn get_var(&self, name: Symbol) -> Option<VarId> {
    self.name_map.get(&name).and_then(|v| v.last().copied())
  }

  /// Get a type variable by name.
  #[must_use] pub fn get_tyvar(&self, name: Symbol) -> Option<ast::TyVarId> {
    Some(self.tyvars.iter().rposition(|&v| name == v)?.try_into().expect("too many vars"))
  }

  /// Get a label by name.
  #[must_use] pub fn get_label(&self, a: Symbol) -> Option<LabelId> {
    Some(*self.label_map.get(&a)?.last()?)
  }

  /// Get the target of an anonymous loop label.
  #[must_use] pub fn get_loop_label(&self) -> Option<LabelId> {
    Some(LabelId(self.loops.last()?.0, 0))
  }

  /// Mark a loop label as having a break that targets it.
  pub fn mark_label_break(&mut self, lab: VarId) {
    if let Some(p) = self.loops.iter_mut().rfind(|p| p.0 == lab) { p.1 = true }
  }
}

/// A scope guard.
///
/// This is constructed by the [`BuildAst::scope`] function to start a scope,
/// and is closed by the `Scope::close` function (which would be a `Drop`
/// implementation except that it requires the client to provide access to the
/// [`BuildAst`]).
#[derive(Debug)] #[allow(missing_copy_implementations)]
#[must_use] pub struct Scope(usize);

impl Scope {
  /// Finish a scope, which drops any variables that have been introduced since
  /// `BuildAst::scope` was called.
  pub fn close(self, ba: &mut BuildAst) { ba.drain_to(self.0); }
}

impl BuildAst {
  /// Start a new scope. All variables introduced after this point can be popped
  /// from the context by calling `Scope::close`. Alternatively, one can use the
  /// [`with_ctx`](Self::with_ctx) function to do scoping from a closure.
  pub fn scope(&self) -> Scope { Scope(self.ctx.len()) }

  fn pop(&mut self) {
    match self.ctx.pop().expect("stack underflow") {
      Ctx::Var(v) => {
        self.name_map.get_mut(&self.var_names[v].k).and_then(Vec::pop).expect("stack underflow");
      }
      Ctx::Label(name) => {
        self.label_map.get_mut(&name).and_then(Vec::pop).expect("stack underflow");
      }
    }
  }

  fn drain_to(&mut self, n: usize) {
    while self.ctx.len() > n { self.pop(); }
  }

  /// Build a scoped expression using a (rust) scoped closure. This is equivalent to calling
  /// `BuildAst::scope` before the closure and `Scope::close` after.
  pub fn with_ctx<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
    let sc = self.scope();
    let res = f(self);
    sc.close(self);
    res
  }
}

/// A builder for `while` loops, constructed by [`BuildAst::build_while`].
#[derive(Debug)]
#[must_use] pub struct WhileBuilder {
  muts: Box<[VarId]>,
  label: VarId,
}

impl BuildAst {
  /// Start a while loop, providing the list of variable mutations up front and deferring the rest
  /// of the arguments to `WhileBuilder::finish`. Between these two calls, anonymous `break` and
  /// `continue` will target the loop under construction.
  pub fn build_while(&mut self, span: FileSpan, muts: Box<[VarId]>) -> WhileBuilder {
    let label = self.fresh_var(Spanned { span, k: Symbol::UNDER });
    self.loops.push((label, false));
    WhileBuilder { muts, label }
  }
}

impl WhileBuilder {
  /// Finish building a while loop expression. This is used in particular to end the scope of the
  /// loop label, so `break` expressions will no longer target this while loop.
  pub fn finish(self, ba: &mut BuildAst,
    var: Option<Box<ast::Variant>>,
    cond: Box<ast::Expr>,
    hyp: Option<Spanned<VarId>>,
    body: Box<ast::Block>,
  ) -> ast::ExprKind {
    let WhileBuilder {muts, label} = self;
    let has_break = ba.loops.pop().expect("stack underflow").1;
    ast::ExprKind::While {label, muts, var, cond, hyp, body, has_break}
  }
}

/// A rename is a `{old -> old'}` or `{new' <- new}` clause appearing in a `with`
/// associated to a let binding or assignment, as in `{{x <- 2} with {x -> x_old}}`.
#[derive(Clone, Debug, Default)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct Renames {
  /// `{from -> to}` means that the variable `from` should be renamed to `to`
  /// (after evaluation of the main expression).
  /// The elements of this list are `(from, to)` pairs.
  pub old: Vec<(Spanned<Symbol>, Spanned<Symbol>)>,
  /// `{to <- from}` means that the new value of the variable `from` should be called `to`,
  /// so that the old value of variable `from` is available by that name.
  /// The elements of this list are `(from, to)` pairs.
  pub new: Vec<(Spanned<Symbol>, Spanned<Symbol>)>,
}

/// The errors that can occur when parsing a `old -> new` rename expression in a let or assignment.
#[derive(Debug, Clone)]
pub enum RenameError {
  /// can't rename variable '_'
  RenameUnder(FileSpan),
  /// variable not found
  MissingVar(Spanned<Symbol>),
}

impl BuildAst {
  /// Apply a rename operation to the current state. For each pair `(a, b)` in the list,
  /// references to `b` after the operation will refer to the variable that was previously called
  /// `a`. Renames are scoped, meaning that when the current scope ends, the variable will be back
  /// to being called `a` (unless `a` itself goes out of scope).
  pub fn apply_rename(&mut self,
    renames: &[(Spanned<Symbol>, Spanned<Symbol>)]
  ) -> Result<(), RenameError> {
    let mut vec = vec![];
    for (from, to) in renames {
      if from.k == Symbol::UNDER { return Err(RenameError::RenameUnder(from.span.clone())) }
      if from.k == to.k { continue }
      let var = self.get_var(from.k).ok_or_else(|| RenameError::MissingVar(from.clone()))?;
      vec.push((var, to.k));
    }
    for (var, to) in vec { self.push(to, var) }
    Ok(())
  }

  #[allow(clippy::type_complexity)]
  fn mk_split(&mut self, Renames {old, new}: Renames
  ) -> Result<HashMap<VarId, (VarId, Spanned<Symbol>, Spanned<Symbol>)>, RenameError> {
    let mut map = HashMap::new();
    for (from, to) in old {
      if from.k == Symbol::UNDER { return Err(RenameError::RenameUnder(from.span)) }
      map.entry(self.get_var(from.k).ok_or_else(|| RenameError::MissingVar(from.clone()))?)
        .or_insert_with(|| (self.fresh_var(from.clone()), from.clone(), from.clone())).2 = to;
    }
    for (from, to) in new {
      if from.k == Symbol::UNDER { return Err(RenameError::RenameUnder(from.span)) }
      map.entry(self.get_var(from.k).ok_or_else(|| RenameError::MissingVar(from.clone()))?)
        .or_insert_with(|| (self.fresh_var(from.clone()), from.clone(), from.clone())).1 = to;
    }
    Ok(map)
  }

  /// Get the "origins" of an lvalue expression, which refers to the source variables that could
  /// possibly be modified by executing an assignment with this expression on the left hand side.
  fn add_origins<E>(e: &ast::Expr, f: &mut impl FnMut(VarId) -> Result<(), E>) -> Result<(), E> {
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

  /// Consume a parsed `Renames` object to construct the `oldmap` argument that is used in
  /// `Assign` expression nodes.
  #[allow(clippy::type_complexity)]
  pub fn mk_oldmap(&mut self, lhs: &ast::Expr, with: Renames
  ) -> Result<Box<[(Spanned<VarId>, Spanned<VarId>)]>, RenameError> {
    let mut split = self.mk_split(with)?;
    Self::add_origins(lhs, &mut |var| {
      if let Entry::Vacant(e) = split.entry(var) {
        if let Some(from) = self.ctx.iter().find_map(|v| match v {
          &Ctx::Var(v) if v == var => Some(self.var_names[v].clone()),
          _ => None
        }) {
          e.insert((self.fresh_var(from.clone()), from.clone(), from));
        }
      }
      Ok(())
    })?;
    let oldmap = split.into_iter().map(|(vnew, (vold, new, old))| {
      let vnew_s = Spanned { span: new.span, k: vnew };
      let vold_s = Spanned { span: old.span, k: vold };
      self.push(old.k, vold);
      self.push(new.k, vnew);
      (vnew_s, vold_s)
    }).collect();
    Ok(oldmap)
  }
}

/// A trait to abstract over the commonalities of `match` expressions in types and expressions.
/// Users should not need to implement this trait.
pub trait BuildMatch: Sized {
  /// True if the context allows hypotheses.
  const ALLOW_HYPS: bool;

  /// Construct an if statement from a condition and a pair of expressions.
  /// `hyp` will only be `None` if `ALLOW_HYPS` is false; otherwise, if it is `Some([vtru, vfal])`
  /// then in `es = [etru, efal]`, `etru` will have `vtru: cond` in scope,
  /// and `efal` will have `vfal: !cond` in scope.
  fn mk_if(hyp: Option<[Spanned<VarId>; 2]>, cond: Box<ast::Expr>, es: [Box<Spanned<Self>>; 2]) -> Self;

  /// Construct a block expression from a list of statements. `stmts` will always be empty if
  /// `ALLOW_HYPS` is false.
  fn mk_block(stmts: Vec<ast::Stmt>, e: Spanned<Self>) -> Self;
}

impl BuildMatch for ast::ExprKind {
  const ALLOW_HYPS: bool = true;
  fn mk_if(hyp: Option<[Spanned<VarId>; 2]>, cond: Box<ast::Expr>, [then, els]: [Box<Spanned<Self>>; 2]) -> Self {
    ast::ExprKind::If {ik: ast::IfKind::If, hyp, cond, then, els}
  }
  fn mk_block(stmts: Vec<ast::Stmt>, e: Spanned<Self>) -> Self {
    ast::ExprKind::Block(ast::Block { stmts, expr: Some(Box::new(e)) })
  }
}

impl BuildMatch for ast::TypeKind {
  const ALLOW_HYPS: bool = false;
  fn mk_if(_: Option<[Spanned<VarId>; 2]>, c: Box<ast::Expr>, [t, e]: [Box<Spanned<Self>>; 2]) -> Self {
    ast::TypeKind::If(c, t, e)
  }
  fn mk_block(_: Vec<ast::Stmt>, e: Spanned<Self>) -> Self { e.k }
}

/// A built branch that is ready for assembly into the final expression.
#[derive(Debug)]
struct PreparedBranch<T> {
  /// The hypotheses on the positive and negative branches.
  hyp: Option<[Spanned<VarId>; 2]>,
  /// The condition to branch on.
  cond: Box<ast::Expr>,
  /// The true branch.
  tru: Box<Spanned<T>>,
  /// A list of let statements to put on the false branch.
  negblock: Vec<ast::Stmt>
}

/// A match builder, which implements what amounts to a coroutine that collaborates with the
/// client to build a match expression.
#[derive(Debug)]
pub struct MatchBuilder<T> {
  /// The span of the whole match expression.
  span: FileSpan,
  /// The scrutinee variable, if applicable.
  scvar: Option<VarId>,
  /// The scrutinee expression, in an `Rc` because it will be used many times in the match.
  scrut: Rc<ast::Expr>,
  /// The stack of `PreparedBranch`es awaiting the final match arm.
  stack: Vec<PreparedBranch<T>>,
  /// If we have received the final match arm, this will be `Some` of the last match arm RHS;
  /// otherwise it is `None`, indicating that we need more branches.
  ready: Option<Spanned<T>>,
}

/// This error indicates that the branch arm being constructed is not reachable.
#[derive(Copy, Clone, Debug)]
 pub struct UnreachablePattern;

/// This error indicates that we ran out of match branches before exhaustively matching the
/// expression. It contains a reference to the scrutinee for error reporting.
#[derive(Clone, Debug)]
pub struct Incomplete(pub Rc<ast::Expr>);

impl BuildAst {
  /// Start building a match expression. We expect the expression `e` in `match e ...`, aka the
  /// "scrutinee".
  pub fn build_match<T: BuildMatch>(&mut self, span: FileSpan, e: ast::Expr) -> MatchBuilder<T> {
    let scvar = if T::ALLOW_HYPS { Some(self.fresh_var(sp!(e.span, Symbol::UNDER))) } else { None };
    MatchBuilder { span, scvar, scrut: Rc::new(e), stack: vec![], ready: None }
  }
}

impl<T: BuildMatch> MatchBuilder<T> {
  /// Start building a new match branch. This will return a `PatternBuilder` that is used to parse
  /// the pattern. If we have already exhaustively matched, then we return the `UnreachablePattern`
  /// error.
  pub fn branch(&mut self, span: &FileSpan, ba: &mut BuildAst) -> Result<PatternBuilder<T>, UnreachablePattern> {
    if self.ready.is_some() { return Err(UnreachablePattern) }
    let hyp1 = ba.fresh_var(sp!(span, Symbol::UNDER));
    let hyp2 = ba.fresh_var(sp!(span, Symbol::UNDER));
    let mk = |hyp| -> Option<Box<dyn Fn() -> ast::Expr>> {
      let span = span.clone();
      Some(Box::new(move || sp!(span, ast::ExprKind::Var(hyp))))
    };
    Ok(PatternBuilder {
      hyp: [Spanned { span: span.clone(), k: hyp1 }, Spanned { span: span.clone(), k: hyp2 }],
      pos: mk(hyp1),
      neg: mk(hyp2),
      uses_hyp: false,
      scvar: self.scvar,
      scrut: self.scrut.clone(),
      posblock: vec![],
      negblock: vec![],
      _mark: PhantomData,
    })
  }

  /// Finish the match once all patterns are completed. Returns the completed match expression,
  /// or the `Incomplete` error (with a reference to the original scrutinee expression) if the
  /// pattern match is not exhaustive.
  pub fn finish(self) -> Result<Spanned<T>, Incomplete> {
    if let Some(mut e) = self.ready {
      for PreparedBranch {hyp, cond, tru, negblock} in self.stack.into_iter().rev() {
        e = sp_block(&self.span, negblock, e);
        e = sp!(self.span, T::mk_if(hyp, cond, [tru, Box::new(e)]));
      }
      if let Some(v) = self.scvar {
        e = sp_block(&self.span, vec![let_var(&self.span, sp!(self.span, Symbol::UNDER), v,
            sp!(self.span, ast::ExprKind::Rc(self.scrut.clone())))], e)
      }
      Ok(e)
    } else { Err(Incomplete(self.scrut)) }
  }
}

/// A pattern builder, which is used to consume the parts of a match arm pattern.
///
/// This implements a coroutine protocol which is mostly but not entirely enforced by the
/// type system. Individual functions specify when they can be called.
/// * `Start`: The initial state upon construction by [`MatchBuilder::branch`].
///    Awaiting a pattern.
/// * `Done`: A pattern has been matched. `prepare_rhs` can be used to set up the context
///    for parsing the RHS of the pattern, and `finish` will return to the `MatchBuilder` context.
pub struct PatternBuilder<T> {
  hyp: [Spanned<VarId>; 2],
  pos: Option<Box<dyn Fn() -> ast::Expr>>,
  neg: Option<Box<dyn Fn() -> ast::Expr>>,
  scvar: Option<VarId>,
  scrut: Rc<ast::Expr>,
  uses_hyp: bool,
  posblock: Vec<ast::Stmt>,
  negblock: Vec<ast::Stmt>,
  _mark: PhantomData<T>,
}

impl<T> Debug for PatternBuilder<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("PatternBuilder")
      .field("hyp", &self.hyp)
      .field("pos", &self.pos.as_deref().map(|f| f()))
      .field("neg", &self.neg.as_deref().map(|f| f()))
      .field("scvar", &self.scvar)
      .field("scrut", &self.scrut)
      .field("uses_hyp", &self.uses_hyp)
      .field("posblock", &self.posblock)
      .field("negblock", &self.negblock)
      .finish()
  }
}

/// A pattern, which is used in an opaque wrapper here to help guide the transitions of the match
/// builder.
///
/// Concretely, a pattern is the conjunction of all the conditions that need to hold for this
/// pattern to match. It is an `Option<Expr>` with `None` representing `true` so that we don't
/// introduce a superfluous `true && ...` conjunct.
#[derive(Debug)]
pub struct Pattern(Option<ast::Expr>);

impl Pattern {
  /// Construct a hyped pattern from a regular pattern. Concretely, this replaces the `None`
  /// variant with `Some(true)`, because a hypothesis has to have an actual type.
  #[must_use] pub fn hyped(self, span: &FileSpan) -> Self {
    Self(Some(self.0.unwrap_or_else(|| sp!(span, ast::ExprKind::Bool(true)))))
  }

  /// Construct a with pattern, which just adjoins `cond` as an extra conjunct in the pattern.
  #[must_use] pub fn with(self, sp: &FileSpan, cond: ast::Expr) -> Pattern {
    Pattern(Some(match self.0 {
      None => cond,
      Some(p) => binop(sp, Binop::And, p, cond)
    }))
  }
}

/// An error that indicates that a variable binding was not expected at this location.
#[derive(Copy, Clone, Debug)]
pub struct BadBinding;

impl<T: BuildMatch> PatternBuilder<T> {
  /// Callable at any point; returns the scrutinee expression.
  fn scrut(&self) -> ast::Expr { sp!(&self.scrut.span, ast::ExprKind::Rc(self.scrut.clone())) }

  /// Callable from `Start`, transitions to `Done`. Match an ignore pattern.
  #[allow(clippy::unused_self)]
  pub fn ignore(&mut self) -> Pattern { Pattern(None) }

  /// Callable from `Start`, transitions to `Done`.
  /// Constructs the pattern `v`, which binds a new variable named `v` to the
  /// value being matched. If variable bindings are not permitted in this context,
  /// then `Err(BadBinding)` is returned.
  pub fn var(&mut self, v: Symbol, ba: &mut BuildAst) -> Result<Pattern, BadBinding> {
    if let Some(var) = self.scvar { ba.push(v, var); Ok(Pattern(None)) }
    else if T::ALLOW_HYPS { panic!("no scrutinee variable available") }
    else { Err(BadBinding) }
  }

  /// Callable from `Start`, transitions to `Done`.
  /// Constructs the constant pattern `c`, which asserts that the value to match is equal to `c`.
  pub fn const_(&mut self, sp: &FileSpan, c: ast::Expr) -> Pattern {
    Pattern(Some(binop(sp, Binop::Eq, self.scrut(), c)))
  }


  /// Callable from `Start`, transitions to `Start`.
  /// Starts a hypothesis pattern `h: pat` , which will make `h` refer to a proof that the pattern
  /// matched in the current arm, and a proof that the pattern did not match in later arms.
  /// Returns `Err(BadBinding)` if hypotheses are not allowed in this context.
  /// Transitions the pattern builder to accept `pat`. The resulting pattern for `pat`
  /// can be transformed to a hyped pattern using [`Pattern::hyped`].
  pub fn hyped(&mut self, sp: &FileSpan, h: Spanned<Symbol>, ba: &mut BuildAst) -> Result<(), BadBinding> {
    if !T::ALLOW_HYPS || self.pos.is_none() && self.neg.is_none() { return Err(BadBinding) }
    self.uses_hyp = true;
    if let Some(f) = self.pos.take() {
      let (v, sp) = (ba.fresh_var(h.clone()), sp.clone());
      self.posblock.push(let_var(&sp, h.clone(), v, f()));
      self.pos = Some(Box::new(move || sp!(sp, ast::ExprKind::Var(v))))
    }
    if let Some(f) = self.neg.take() {
      let (v, sp) = (ba.fresh_var(h.clone()), sp.clone());
      self.negblock.push(let_var(&sp, h, v, f()));
      self.neg = Some(Box::new(move || sp!(sp, ast::ExprKind::Var(v))))
    }
    Ok(())
  }

  /// Callable from `Start`, transitions to `Start`.
  /// Starts a `pat with cond` pattern, transitions to accept `pat`.
  /// When `pat` is finished, [`Pattern::with`] can be used to complete the with-pattern.
  pub fn with(&mut self, sp: &FileSpan) {
    if let Some(f) = self.pos.take() {
      let sp = sp.clone();
      self.pos = Some(Box::new(move ||
        sp!(sp, ast::ExprKind::Proj(Box::new(f()),
          sp!(sp, FieldName::Number(0))))))
    }
    self.neg = None;
  }

  /// Callable from `Start`, transitions to `Done`.
  /// Start parsing a `(pat1 | pat2 | ... | patn)` pattern, returning an `OrBuilder` that will
  /// guide the process.
  pub fn or<'a>(&mut self, sp: &'a FileSpan) -> OrBuilder<'a, T> {
    self.pos = None;
    OrBuilder { sp, neg: self.neg.take().map(Into::into), args: Some(vec![]), _mark: PhantomData }
  }

  /// Callable from `Done`. When a pattern is complete, this function should be called to
  /// push all the variables into the context for parsing the RHS of the match branch.
  pub fn prepare_rhs(&self, ba: &mut BuildAst) {
    for st in &self.posblock {
      if let ast::StmtKind::Let {lhs, ..} = &st.k {
        if let ast::TuplePatternKind::Name(_, name, v) = lhs.k {
          if name != Symbol::UNDER { ba.push(name, v) }
        }
      }
    }
  }

  /// Callable from `Done`. Finish a match branch given the pattern LHS and parsed RHS.
  pub fn finish(self, sp: &FileSpan, pat: Pattern, rhs: Spanned<T>, mb: &mut MatchBuilder<T>) {
    let PatternBuilder {posblock, negblock, uses_hyp, hyp, ..} = self;
    let rhs = sp_block(sp, posblock, rhs);
    if let Some(cond) = pat.0 {
      mb.stack.push(PreparedBranch {
        hyp: if uses_hyp {Some(hyp)} else {None},
        cond: Box::new(cond),
        tru: Box::new(rhs),
        negblock,
      });
    } else {
      mb.ready = Some(rhs)
    }
  }
}

fn binop(sp: &FileSpan, op: Binop, e1: ast::Expr, e2: ast::Expr) -> ast::Expr {
  sp!(sp, ast::ExprKind::binop(sp, op, e1, e2))
}

/// Part of the match builder state machine; this struct carries the state
/// for parsing an or pattern. Constructed by [`PatternBuilder::or`].
pub struct OrBuilder<'a, T> {
  sp: &'a FileSpan,
  args: Option<Vec<ast::Expr>>,
  neg: Option<Rc<dyn Fn() -> ast::Expr>>,
  _mark: PhantomData<T>,
}

impl<T> Debug for OrBuilder<'_, T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("OrBuilder")
      .field("sp", &self.sp)
      .field("args", &self.args)
      .field("neg", &self.neg.as_deref().map(|f| f()))
      .finish()
  }
}

impl<T: BuildMatch> OrBuilder<'_, T> {
  /// Start a new or pattern variant `pat | ...`. Transitions the pattern
  /// builder from `Done` to `Start` to accept `pat`.
  pub fn send(&mut self, pb: &mut PatternBuilder<T>) {
    pb.neg = if let (Some(f), Some(args)) = (&self.neg, &self.args) {
      let n = args.len();
      let sp = self.sp.clone();
      let f = f.clone();
      Some(Box::new(move || {
        macro_rules! proj {($e:expr, $n:expr) => {
          sp!(sp, ast::ExprKind::Proj(Box::new($e), sp!(sp, FieldName::Number($n))))
        }}
        let mut x = f();
        for _ in 0..n { x = proj!(x, 1) }
        proj!(x, 0)
      }))
    } else { None }
  }

  /// Finish an or pattern variant, storing the parsed pattern `pat` in the state.
  pub fn recv(&mut self, pat: Pattern) {
    if let Some(p) = pat.0 {
      if let Some(args) = &mut self.args { args.push(p) }
    } else { self.args = None }
  }

  /// Finish parsing an or pattern, returning the completed pattern.
  #[must_use] pub fn finish(self) -> Pattern {
    let Self {args, sp, ..} = self;
    Pattern(args.map(|args| {
      let mut e = sp!(sp, ast::ExprKind::Bool(false));
      for arg in args.into_iter().rev() {
        e = binop(sp, Binop::Or, arg, e);
      }
      e
    }))
  }
}

fn sp_block<T: BuildMatch>(span: &FileSpan, stmts: Vec<ast::Stmt>, e: Spanned<T>) -> Spanned<T> {
  if stmts.is_empty() { e } else { sp!(span, T::mk_block(stmts, e)) }
}

impl BuildAst {
  /// This function implements desugaring for chained inequalities.
  fn build_ineq(&mut self, sp: &FileSpan, args: Vec<ast::Expr>, op: Binop) -> Option<ast::Expr> {
    // Haskell pseudocode:
    // build_ineq [] = error
    // build_ineq [e1] = { e1; true }
    // build_ineq [e1, e2] = e1 < e2
    // build_ineq (e1:e2:e3:es) = { let v1 = e1; let v2 = e2; mk_and v1 v2 e3 es }
    // mk_and v0 v1 e2 es = (v0 < v1 && mk_block v1 e2 es)
    // mk_block v1 e2 [] = (v1 < e2)
    // mk_block v1 e2 (e3:es) = { let v2 = e2; mk_and v1 v2 e3 es }

    macro_rules! binop {($sp:expr, $op:expr, $e1:expr, $e2:expr) => {
      sp!($sp, ast::ExprKind::binop($sp, $op, $e1, $e2))
    }}
    macro_rules! block {($sp:expr; $($e:expr),*; $last:expr) => {
      sp!($sp, ast::ExprKind::Block(
        ast::Block {stmts: vec![$($e),*], expr: Some(Box::new($last))}))
    }}
    fn binop(sp: &FileSpan, op: Binop, v1: VarId, e2: ast::Expr) -> ast::Expr {
      binop!(sp, op, sp!(sp, ast::ExprKind::Var(v1)), e2)
    }
    fn and(sp: &FileSpan, op: Binop, v1: VarId, v2: VarId, e: ast::Expr) -> ast::Expr {
      binop!(sp, Binop::And, binop(sp, op, v1, sp!(sp, ast::ExprKind::Var(v2))), e)
    }
    let mut it = args.into_iter();
    let arg_1 = it.next()?;
    Some(if let Some(arg_2) = it.next() {
      if let Some(arg_3) = it.next() {
        fn mk_and(this: &mut BuildAst, sp: &FileSpan,
          op: Binop, v0: VarId, v1: VarId, e2: ast::Expr, mut it: std::vec::IntoIter<ast::Expr>
        ) -> ast::Expr {
          and(sp, op, v0, v1, if let Some(e3) = it.next() {
            let v2 = this.fresh_var(sp!(sp, Symbol::UNDER));
            block![sp;
              let_var(sp, sp!(sp, Symbol::UNDER), v2, e2);
              mk_and(this, sp, op, v1, v2, e3, it)]
          } else {
            binop(sp, op, v1, e2)
          })
        }
        let v_1 = self.fresh_var(sp!(sp, Symbol::UNDER));
        let v_2 = self.fresh_var(sp!(sp, Symbol::UNDER));
        block![sp;
          let_var(sp, sp!(sp, Symbol::UNDER), v_1, arg_1),
          let_var(sp, sp!(sp, Symbol::UNDER), v_2, arg_2);
          mk_and(self, sp, op, v_1, v_2, arg_3, it)]
      } else {
        binop!(sp, op, arg_1, arg_2)
      }
    } else {
      block![sp; arg_1.map_into(ast::StmtKind::Expr); sp!(sp, ast::ExprKind::Bool(true))]
    })
  }
}

fn build_lassoc1(span: &FileSpan, args: Vec<ast::Expr>, op: Binop) -> Option<ast::Expr> {
  let mut it = args.into_iter();
  let mut out = it.next()?;
  for e in it {
    out = Spanned {span: span.clone(), k: ast::ExprKind::binop(span, op, out, e)};
  }
  Some(out)
}

macro_rules! mk_funcs {
  () => {};
  ($(#[$doc:meta])* $f:ident =>
    lassoc1($zero:expr, $op:expr, |$span:pat_param, $e:pat_param| $arg:expr); $($rest:tt)*
  ) => {
    $(#[$doc])*
    #[must_use] pub fn $f(&self, span: &FileSpan, args: Vec<ast::Expr>) -> ast::Expr {
      #[allow(unused)]
      Spanned {span: span.clone(), k:
        if let Some($e) = build_lassoc1(&span, args, {use Binop::*; $op}) {
          let $span = span; $arg
        } else { use ast::ExprKind::*; $zero }
      }
    }
    mk_funcs! { $($rest)* }
  };
  ($(#[$doc:meta])* $f:ident => lassoc1($zero:expr, $op:expr); $($rest:tt)*) => {
    mk_funcs! { $(#[$doc])* $f => lassoc1($zero, $op, |_, e| return e); $($rest)* }
  };
  ($(#[$doc:meta])* $f:ident => ineq($op:expr, $s:expr); $($rest:tt)*) => {
    $(#[$doc])*
    pub fn $f(&mut self, span: &FileSpan, args: Vec<ast::Expr>) -> ast::Expr {
      self.build_ineq(&span, args, {use Binop::*; $op}).expect($s)
    }
    mk_funcs! { $($rest)* }
  };
}

impl BuildAst {
  mk_funcs! {
    /// Construct a left associative `+` expression, with `0` for an empty list.
    mk_add => lassoc1(Int(0.into()), Add);
    /// Construct a left associative `*` expression, with `1` for an empty list.
    mk_mul => lassoc1(Int(1.into()), Mul);
    /// Construct a left associative `-` expression, panicking for an empty list.
    mk_sub => lassoc1(panic!("empty subtraction"), Sub);
    /// Construct a left associative `min` expression, panicking for an empty list.
    mk_min => lassoc1(panic!("taking min of empty list"), Min);
    /// Construct a left associative `max` expression, panicking for an empty list.
    mk_max => lassoc1(panic!("taking max of empty list"), Max);
    /// Construct a left associative `&&` expression, with `true` for an empty list.
    mk_and => lassoc1(Bool(true), And);
    /// Construct a left associative `||` expression, with `false` for an empty list.
    mk_or => lassoc1(Bool(false), Or);
    /// Construct a nor expression `!((a || b) || c)`, with `true` for an empty list.
    mk_nor => lassoc1(Bool(true), Or, |sp, e| return e.not(sp));
    /// Construct a left associative bitwise `&` expression, with `-1` (all-ones) for an empty list.
    mk_bit_and => lassoc1(Int((-1).into()), BitAnd);
    /// Construct a left associative bitwise `|` expression, with `0` (all-zeros) for an empty list.
    mk_bit_or => lassoc1(Int(0.into()), BitOr);
    /// Construct a left associative bitwise `^` expression, with `0` (all-zeros) for an empty list.
    mk_bit_xor => lassoc1(Int(0.into()), BitXor);
    /// Construct a bitwise nor expression `~((a | b) | c)`, with `-1` (all-ones) for an empty list.
    mk_bit_nor => lassoc1(Int((-1).into()), BitOr, |sp, e| return e.bit_not(sp));
    /// Construct a chained `a <= b <= c` expression, panicking for an empty list.
    mk_le => ineq(Le, "empty <= expression");
    /// Construct a chained `a < b < c` expression, panicking for an empty list.
    mk_lt => ineq(Lt, "empty < expression");
    /// Construct a chained `a == b == c` expression, panicking for an empty list.
    mk_eq => ineq(Eq, "empty == expression");
    /// Construct a chained `a != b != c` expression, panicking for an empty list.
    /// (Note, this is adjacent pair disequality, not pairwise disequality.)
    mk_ne => ineq(Ne, "empty != expression");
  }
}
