//! The `(refine)` tactic, which is called by default when you give a pure proof term.
//!
//! The `(refine)` tactic is passed a lisp s-expr datum, and the interpretation of this
//! s-expr has a grammar of its own, described in [`mm1.md`].
//!
//! [`mm1.md`]: https://github.com/digama0/mm0/blob/master/mm0-hs/mm1.md#pre-expressions

use crate::{FileSpan, Span};
use super::{Elaborator, ElabError, Result};
use crate::{AtomId, TermKind, DeclKey, Modifiers,
  ObjectKind, SortId, TermId, ThmId, Type};
use super::lisp::{InferTarget, LispKind, LispRef, LispVal, Uncons, RefineSyntax,
  print::{FormatEnv, EnvDisplay}, eval::SResult};
use super::local_context::{InferSort, try_get_span, try_get_span_opt};
use super::proof::Subst;

/// The inference mode on an application, which determines which arguments are being
/// omitted and which provided explicitly.
#[derive(Copy, Clone, Debug)]
pub enum InferMode {
  /// No annotation, i.e. `(foo p1 p2)`. Here `foo` should take two hypotheses,
  /// which are proved via `p1` and `p2`.
  Regular,
  /// Fully explicit: `(! foo x y a b p1 p2)`. Here `x y a b` are the list of all variables,
  /// both bound and regular, followed by proofs of the hypotheses of theorem `foo`.
  Explicit,
  /// Bound variables only: `(!! foo x y p1 p2)`. Here `x y` are bound variables and
  /// the regular variables are omitted.
  BoundOnly
}

/// A parsed refine expression. This type is nonrecursive, meaning that `parse_refine` should
/// be called repeatedly on the subterms as we go.
#[allow(variant_size_differences)]
enum RefineExpr {
  /// An application like `(foo p1 p2)` or `(!! bar x p1)`.
  App {
    /// The span of the application.
    sp: Span,
    /// The span of the head term, `foo` or `bar` in the examples.
    sp2: Span,
    /// The infer mode (see [`InferMode`]), the prefix `!!` or `!`.
    im: InferMode,
    /// The head term or theorem.
    head: AtomId,
    /// The remainder of the term.
    u: Uncons
  },
  /// A type ascription `{e : ty}`. This is the same as `e` but where we assert that
  /// it has type `ty` (which may result in additional unification of metavariables).
  Typed {
    /// The demanded type
    ty: LispVal,
    /// The main expression
    e: LispVal
  },
  /// An elaborated or "verbatim" term. This term is assumed to be a full proof already
  /// and is not interpreted as a refine script.
  Exact(LispVal),
  /// A user procedure, which should be called in order to produce the elaborated term.
  Proc,
}

/// The type of stack elements for a refine stack. This represents a continuation that
/// expects an elaborated term or proof.
///
/// Below, we have pseudocode for each stack element, where a stack continuation is
/// a function with a number of arguments that were stored previously, and one argument that is
/// being returned from another call, and returns a value to the outer context
/// (another stack element).
#[derive(Debug)]
pub(crate) enum RStack {
  /// Top level stack element: we are expecting an elaborated proof to
  /// assign to `g`, after which we will refine `es` against the goals `gs`.
  /// ```text
  /// RStack::Goals(g, gs, es)(ret) :=
  ///   assign g <- ret
  ///   return RState::Goals(gs, es)
  /// ```
  Goals {
    /// The current goal
    g: LispVal,
    /// Later goals
    gs: std::vec::IntoIter<LispVal>,
    /// Later expressions to unify against later goals
    es: std::vec::IntoIter<LispVal>,
    /// return a value
    ret_val: bool,
  },
  /// This is not used directly by evaluation, but can be set manually. When we return
  /// to this stack element, we append this list of goals and pass the return value to the parent.
  /// ```text
  /// RStack::DeferGoals(gs)(ret) :=
  ///   goals += gs
  ///   return ret
  /// ```
  DeferGoals(Vec<LispVal>),
  /// This stack element awaits a proof of `src`, where `u` is a proof of `src = tgt`. It returns
  /// a proof of `tgt`.
  /// ```text
  /// RStack::Coerce(tgt, u)(p) :=
  ///   return (:conv u tgt p)
  /// ```
  Coerce {
    /// The elaborated target type
    tgt: LispVal,
    /// The conversion proof, possibly `#undef`
    u: LispVal
  },
  /// This is like [`Coerce`](Self::Coerce) but infers the type of `p` and uses it to determine the coercion.
  /// ```text
  /// RStack::CoerceTo(tgt)(p) :=
  ///   let src = type_of(p)
  ///   let u = coerce(src, tgt)
  ///   return (:conv u tgt p)
  /// ```
  CoerceTo(LispVal),
  /// This stack element is awaiting an elaborated target type, to match against the actual
  /// target type, used when elaborating `{p : _}: tgt`.
  /// ```text
  /// RStack::TypedAt(tgt, p)(tgt') :=
  ///   let u = unify(tgt, tgt')
  ///   let elab_p = RState::RefineProof(tgt', p)
  ///   return RStack::Coerce(tgt, u)(elab_p)
  /// ```
  TypedAt {
    /// The span of `p`
    sp: Span,
    /// The elaborated target type
    tgt: LispVal,
    /// The unelaborated proof
    p: LispVal
  },
  /// Like [`TypedAt`](Self::TypedAt) but the target type is unknown.
  /// ```text
  /// RStack::Typed(p)(tgt) :=
  ///   return RState::RefineProof(tgt, p)
  /// ```
  Typed(LispVal),
  /// An application in progress. See [`RState::RefineApp`].
  /// ```text
  /// RStack::RefineApp(tgt, t, u, args)(arg) :=
  ///   return RState::RefineApp(tgt, t, u, args ++ [arg])
  /// ```
  RefineApp {
    /// The span of the term `t`
    sp2: Span,
    /// The expected type
    tgt: InferTarget,
    /// The head term
    t: TermId,
    /// The remainder of the application
    u: Uncons,
    /// The elaborated arguments
    args: Vec<LispVal>
  },
  /// Elaborating the binders of a theorem application. See [`RState::RefineBis`].
  /// ```text
  /// RStack::RefineBis(tgt, im, t, u, args)(arg) :=
  ///   return RState::RefineBis(tgt, im, t, u, args ++ [arg])
  /// ```
  RefineBis {
    /// The span of the application
    sp: Span,
    /// The span of the theorem `t`
    sp2: Span,
    /// The expected type
    tgt: LispVal,
    /// The infer mode (see [`InferMode`])
    im: InferMode,
    /// The head theorem
    t: ThmId,
    /// The remainder of the application
    u: Uncons,
    /// The elaborated arguments
    args: Vec<LispVal>,
  },
  /// Elaborating the hypotheses of a theorem application. See `RState::RefineHyps`.
  /// ```text
  /// RStack::RefineHyps(tgt, im, t, u, args, hyps, res)(arg) :=
  ///   return RState::RefineHyps(tgt, im, t, u, args ++ [arg], hyps, res)
  /// ```
  RefineHyps {
    /// The span of the application
    sp: Span,
    /// The span of the theorem `t`
    sp2: Span,
    /// The expected type
    tgt: LispVal,
    /// The head theorem
    t: ThmId,
    /// The remainder of the application
    u: Uncons,
    /// The elaborated arguments
    args: Vec<LispVal>,
    /// The elaborated subproofs
    hyps: std::vec::IntoIter<LispVal>,
    /// The unification result
    res: RefineHypsResult,
  },
}

impl EnvDisplay for RStack {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      RStack::Goals { g, gs, es, ret_val } => write!(f,
        "Goals {{g: {}, gs: {}, es: {}, ret_val: {}}}",
        fe.to(g), fe.to(gs.as_slice()), fe.to(es.as_slice()), ret_val),
      RStack::DeferGoals(es) => write!(f,
        "DeferGoals {{es: {}}}", fe.to(es.as_slice())),
      RStack::Coerce { tgt, u } => write!(f,
        "Coerce {{tgt: {}, u: {}}}", fe.to(tgt), fe.to(u)),
      RStack::CoerceTo(tgt) => write!(f,
        "CoerceTo {{tgt: {}}}", fe.to(tgt)),
      RStack::TypedAt { tgt, p, .. } => write!(f,
        "TypedAt {{tgt: {}, p: {}}}", fe.to(tgt), fe.to(p)),
      RStack::Typed(p) => write!(f, "Typed {{p: {}}}", fe.to(p)),
      RStack::RefineApp { tgt, t, u, args, .. } => write!(f,
        "RefineApp {{\n  tgt: {},\n  {} {} -> {}}}",
        fe.to(tgt), fe.to(t), fe.to(u), fe.to(args)),
      RStack::RefineBis { tgt, im, t, u, args, .. } => write!(f,
        "RefineBis {{\n  tgt: {},\n  im: {:?},\n  {} {} -> {}}}",
        fe.to(tgt), im, fe.to(t), fe.to(u), fe.to(args)),
      RStack::RefineHyps { tgt, t, u, args, hyps, res, .. } => write!(f,
        "RefineHyps {{\n  tgt: {},\n  {} {} -> {},\n  hyps: {},\n  res: {}}}",
        fe.to(tgt), fe.to(t), fe.to(u), fe.to(args), fe.to(hyps.as_slice()), fe.to(res)),
    }
  }
}

/// The states of the state machine that implements `refine`. (Ideally we could
/// implement this with a generator or async function but we need to reflect on the stack
/// to print out user stack traces, so we need control over the call stack itself.)
///
/// Below, we have pseudocode for each state, which may call stack functions in
/// [`RStack`] as well as other state functions.
#[derive(Debug)]
pub(crate) enum RState {
  /// Initial state: we are given a sequence of goals to unify against a list
  /// of refine scripts.
  /// ```text
  /// RState::Goals(g::gs, e::es) :=
  ///   let p = RState::RefineProof(tgt, e)
  ///   return RStack::Goals(g, gs, es)(p)
  /// RState::Goals(gs, _) := goals += gs; return
  /// ```
  Goals {
    /// Later goals
    gs: std::vec::IntoIter<LispVal>,
    /// Later expressions to unify against later goals
    es: std::vec::IntoIter<LispVal>,
    /// return a value
    ret_val: bool,
  },
  /// Elaborate the unelaborated proof `p` against the target type `tgt`.
  /// ```text
  /// RState::RefineProof(tgt, '_) := return new_goal(tgt)
  /// RState::RefineProof(tgt, '(!im thm args)) :=
  ///   return RState::RefineBis(tgt, im, thm, [thm], args)
  /// RState::RefineProof(tgt, '{p : ty}) :=
  ///   let ty' = RState::RefineExpr(unknown, ty)
  ///   return RStack::TypedAt(tgt, p)(ty')
  /// RState::RefineProof(tgt, '(exact p)) := return coerce(tgt, type_of(p), p)
  /// RState::RefineProof(tgt, func) := return RState::Proc(tgt, func)
  /// ...
  /// ```
  RefineProof {
    /// The (elaborated) expected type
    tgt: LispVal,
    /// The unelaborated proof
    p: LispVal,
  },
  /// Elaborate the unelaborated term `e` against the target sort `tgt`.
  /// ```text
  /// RState::RefineExpr(tgt, '_) := return new_mvar(tgt)
  /// RState::RefineExpr(tgt, 'x) if x: ty := return coerce(tgt, ty, x)
  /// RState::RefineExpr(tgt, '(term args)) :=
  ///   return RState::RefineApp(tgt, term, [term], args)
  /// ...
  /// ```
  RefineExpr {
    /// The expected type
    tgt: InferTarget,
    /// The unelaborated term
    e: LispVal,
  },
  /// Elaborate the arguments of a term application.
  /// ```text
  /// RState::RefineApp(tgt, t, ei::es, [t, a0, ..., a(i-1)]) if i < t.args.len :=
  ///   let ai = RState::RefineExpr(t.args[i], ei)
  ///   return RStack::RefineApp(tgt, t, es, [t, a0, ..., a(i-1)])(ai)
  /// RState::RefineApp(tgt, t, [], [t, a0, ..., an]) :=
  ///   return coerce(tgt, t.ret, '(t a0 ... an))
  /// ...
  /// ```
  RefineApp {
    /// The span of `t`
    sp2: Span,
    /// The expected type
    tgt: InferTarget,
    /// The head term
    t: TermId,
    /// The unelaborated arguments
    u: Uncons,
    /// The elaborated arguments
    args: Vec<LispVal>,
  },
  /// Elaborate the (possibly) extra arguments of a completed theorem application.
  /// ```text
  /// RState::RefineArgs(tgt, ty, p, []) := return coerce(tgt, ty, p)
  /// RState::RefineArgs(tgt, ty, p, args) := return (yield RefineExtraArgs(tgt, p, args))
  /// ```
  RefineArgs {
    /// The span of the application
    sp: Span,
    /// The expected type
    tgt: LispVal,
    /// The type of `p`
    ty: LispVal,
    /// The elaborated proof
    p: LispVal,
    /// The extra arguments
    u: Uncons,
  },
  /// Elaborates the binders (bound and regular variables) of a theorem application. The
  /// behavior of this phase depends on the infer mode.
  RefineBis {
    /// The span of the application.
    sp: Span,
    /// The span of `t`.
    sp2: Span,
    /// The expected type
    tgt: LispVal,
    /// The infer mode (see [`InferMode`])
    im: InferMode,
    /// The head theorem
    t: ThmId,
    /// The remainder of the application
    u: Uncons,
    /// The elaborated arguments
    args: Vec<LispVal>,
  },
  /// Elaborates the hypotheses of a theorem application.
  RefineHyps {
    /// The span of the application.
    sp: Span,
    /// The span of `t`.
    sp2: Span,
    /// The expected type
    tgt: LispVal,
    /// The head theorem
    t: ThmId,
    /// The remainder of the application
    u: Uncons,
    /// The elaborated arguments
    args: Vec<LispVal>,
    /// The elaborated subproofs
    hyps: std::vec::IntoIter<LispVal>,
    /// The unification result
    res: RefineHypsResult,
  },
  /// Elaborates a proof `p` that is a user procedure, by calling it with
  /// a callback for calling back into `refine`. This can be used to implement
  /// tactics that are placed inline in a refine script
  /// (and sequenced with it, called in the middle of the `refine`).
  Proc {
    /// The expected type
    tgt: LispVal,
    /// The proof procedure
    p: LispVal,
  },
  /// State that pops the stack and calls a stack procedure.
  /// ```text
  /// RState::Ret(ret) := return ret
  /// ```
  Ret(LispVal),
}

impl EnvDisplay for RState {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      RState::Goals {gs, es, ..} => write!(f,
        "Goals {{gs: {}, es: {}}}", fe.to(gs.as_slice()), fe.to(es.as_slice())),
      RState::RefineProof {tgt, p} => write!(f,
        "RefineProof {{\n  tgt: {},\n  p: {}}}", fe.to(tgt), fe.to(p)),
      RState::RefineExpr {tgt, e} => write!(f,
        "RefineExpr {{\n  tgt: {},\n  e: {}}}", fe.to(tgt), fe.to(e)),
      RState::RefineApp {tgt, t, u, args, ..} => write!(f,
        "RefineApp {{\n  tgt: {},\n  {} {} -> {}}}",
        fe.to(tgt), fe.to(t), fe.to(u), fe.to(args)),
      RState::Ret(e) => write!(f, "Ret({})", fe.to(e)),
      RState::RefineArgs {tgt, ty, p, u, ..} => write!(f,
        "RefineArgs {{\n  tgt: {},\n  ty: {},\n  p: {},\n  u: {}}}",
        fe.to(tgt), fe.to(ty), fe.to(p), fe.to(u)),
      RState::RefineBis {tgt, im, t, u, args, ..} => write!(f,
        "RefineBis {{\n  tgt: {},\n  im: {:?},\n  {} {} -> {}}}",
        fe.to(tgt), im, fe.to(t), fe.to(u), fe.to(args)),
      RState::RefineHyps {tgt, t, u, args, hyps, res, ..} => write!(f,
        "RefineHyps {{\n  tgt: {},\n  {} {} -> {},\n  hyps: {},\n  res: {}}}",
        fe.to(tgt), fe.to(t), fe.to(u), fe.to(args), fe.to(hyps.as_slice()), fe.to(res)),
      RState::Proc {tgt, p} => write!(f,
        "Proc {{\n  tgt: {},\n  p: {}}}", fe.to(tgt), fe.to(p)),
    }
  }
}

/// Stores the result of unification, which is ready as soon as we read the first
/// `n` arguments of the application, if the theorem has `n` arguments.
/// If there are more arguments in the application, we go into
/// [`Extra`](RefineHypsResult::Extra) mode
/// and call the user callback `refine-extra-args` to find out how to deal with it.
#[derive(Debug)]
pub enum RefineHypsResult {
  /// The function was applied to the right number of arguments;
  /// the stored value is the conversion that is the result of unification.
  Ok(LispVal),
  /// The function was applied too many arguments; we don't know what
  /// the target type is because it doesn't match so we don't run unification
  /// and leave it to the user callback.
  Extra,
}

impl EnvDisplay for RefineHypsResult {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      RefineHypsResult::Ok(e) => write!(f, "Ok({})", fe.to(e)),
      RefineHypsResult::Extra => write!(f, "Extra"),
    }
  }
}

/// The result of the `refine` function. A regular return is [`Ret`](RefineResult::Ret),
/// but it can also yield in the middle of execution in order to call a lisp callback.
#[derive(Debug)]
#[allow(variant_size_differences)]
pub enum RefineResult {
  /// `return e`: `refine` completed successfully and this is the result.
  Ret(LispVal),
  /// `return`: `refine` completed successfully and there is no result.
  RetNone,
  /// `await (refine-extra-args tgt p args)`: we want to call the `refine-extra-args`
  /// callback to determine how to apply `args` to the proof `p`, with expected type `tgt`.
  RefineExtraArgs(LispVal, LispVal, Uncons),
  /// `await (call tgt func)`: calls `(func refine-cb tgt)` where
  /// `refine-cb` is a callback that can be used to return here.
  Proc(LispVal, LispVal),
}

impl LispVal {
  fn conv(tgt: Self, u: Self, p: Self) -> Self {
    Self::list(vec![Self::atom(AtomId::CONV), tgt, u, p])
  }
  fn unfold(t: AtomId, es: Vec<Self>, p: Self) -> Self {
    Self::list(vec![Self::atom(AtomId::UNFOLD), Self::atom(t), Self::list(es), p])
  }
  fn sym(p: Self) -> Self {
    Self::list(vec![Self::atom(AtomId::SYM), p])
  }
  fn apply_conv(c: Self, tgt: Self, p: Self) -> Self {
    if c.is_def() {Self::conv(tgt, c, p)} else {p}
  }

  fn as_mvar<T>(&self, f: impl FnOnce(&Self, &LispRef) -> T) -> Option<T> {
    fn rec<T, F: FnOnce(&LispVal, &LispRef) -> T>(e: &LispVal, f: F) -> Result<T, Option<F>> {
      match &**e {
        LispKind::Annot(_, e2) => rec(e2, f),
        LispKind::Ref(mutex) => {
          let guard = mutex.unref();
          match rec(&guard, f) {
            Ok(r) => Ok(r),
            Err(None) => Err(None),
            Err(Some(f)) => Ok(f(e, mutex))
          }
        }
        LispKind::MVar(_, _) => Err(Some(f)),
        _ => Err(None)
      }
    }
    rec(self, f).ok()
  }
}

#[derive(Debug)]
enum AssignError { Cyclic, BoundVar }

impl Elaborator {

  fn parse_refine(&mut self, fsp: &FileSpan, e: &LispVal) -> Result<RefineExpr> {
    Ok(match &*e.unwrapped_arc() {
      &LispKind::Atom(head) => {
        let sp = try_get_span(fsp, e);
        RefineExpr::App {sp, sp2: sp, im: InferMode::Regular, head, u: Uncons::nil()}
      }
      LispKind::List(_) | LispKind::DottedList(_, _) => {
        let mut u = Uncons::from(e.clone());
        let sp = try_get_span(fsp, e);
        match u.next() {
          None if e.is_list() => RefineExpr::App {sp, sp2: sp,
            im: InferMode::Regular, head: AtomId::UNDER, u: Uncons::nil()},
          None => return Err(ElabError::new_e(try_get_span(fsp, e), "refine: syntax error")),
          Some(e) => {
            let a = e.as_atom().ok_or_else(||
              ElabError::new_e(try_get_span(fsp, &e), "refine: expected an atom"))?;
            let (im, t) = match a {
              AtomId::BANG => {
                let sp2 = try_get_span_opt(fsp, e.fspan().as_ref());
                if let Some(sp2) = sp2 {
                  self.spans.insert_if(sp2, || ObjectKind::RefineSyntax(RefineSyntax::Explicit));
                }
                let t = u.next().ok_or_else(||
                  ElabError::new_e(sp2.unwrap_or(fsp.span), "!: expected at least one argument"))?;
                (InferMode::Explicit, t)
              }
              AtomId::BANG2 => {
                let sp2 = try_get_span_opt(fsp, e.fspan().as_ref());
                if let Some(sp2) = sp2 {
                  self.spans.insert_if(sp2, || ObjectKind::RefineSyntax(RefineSyntax::BoundOnly));
                }
                let t = u.next().ok_or_else(||
                  ElabError::new_e(sp2.unwrap_or(fsp.span), "!!: expected at least one argument"))?;
                (InferMode::BoundOnly, t)
              }
              AtomId::VERB => {
                let sp2 = try_get_span_opt(fsp, e.fspan().as_ref());
                if let Some(sp2) = sp2 {
                  self.spans.insert_if(sp2, || ObjectKind::RefineSyntax(RefineSyntax::Verb));
                }
                return if let (Some(e), true) = (u.next(), u.is_empty()) {
                  Ok(RefineExpr::Exact(e))
                } else {
                  Err(ElabError::new_e(sp2.unwrap_or(fsp.span), "verb: expected one argument"))
                }
              }
              AtomId::COLON => {
                let sp2 = try_get_span_opt(fsp, e.fspan().as_ref());
                if let Some(sp2) = sp2 {
                  self.spans.insert_if(sp2, || ObjectKind::RefineSyntax(RefineSyntax::Typed));
                }
                return if let (Some(e), Some(ty), true) = (u.next(), u.next(), u.is_empty()) {
                  Ok(RefineExpr::Typed {ty, e})
                } else {
                  Err(ElabError::new_e(sp2.unwrap_or(fsp.span), "':' expected two arguments"))
                }
              }
              _ => (InferMode::Regular, e)
            };
            let sp2 = try_get_span(fsp, &t);
            let head = t.as_atom().ok_or_else(|| ElabError::new_e(sp2, "refine: expected an atom"))?;
            RefineExpr::App {sp, sp2, im, head, u}
          }
        }
      }
      LispKind::Proc(_) => RefineExpr::Proc,
      _ => return Err(ElabError::new_e(try_get_span(fsp, e), "refine: syntax error")),
    })
  }

  fn new_goal(&mut self, sp: Span, ty: LispVal) -> LispVal {
    let r = LispVal::new_ref(LispVal::goal(self.fspan(sp), ty));
    self.lc.goals.push(r.clone());
    r
  }

  /// Get the sort of the term `e` (with only minimal type-checking).
  pub fn infer_target(&self, sp: Span, e: &LispVal) -> Result<InferTarget> {
    macro_rules! err {
      ($e:expr, $err:expr) => {ElabError::new_e(try_get_span(&self.fspan(sp), &$e), $err)}
    }
    Ok(match *e.unwrapped_arc() {
      LispKind::Atom(x) => match self.lc.vars.get(&x) {
        Some(&(_, InferSort::Bound(s))) => InferTarget::Bound(self.sorts[s].atom),
        Some(&(_, InferSort::Reg(s, _))) => InferTarget::Reg(self.sorts[s].atom),
        Some(&(_, InferSort::Unknown {..})) => InferTarget::Unknown,
        None => return Err(err!(e, format!("unknown variable '{}'", self.data[x].name)))
      },
      LispKind::List(_) | LispKind::DottedList(_, _) => {
        let mut u = Uncons::from(e.clone());
        let head = u.next().ok_or_else(|| err!(e, "not a term"))?;
        let a = head.as_atom().ok_or_else(|| err!(head, "expected an atom"))?;
        let tid = self.term(a).ok_or_else(||
          err!(head, format!("unknown term '{}'", self.data[a].name)))?;
        let sort = self.env.terms[tid].ret.0;
        InferTarget::Reg(self.sorts[sort].atom)
      }
      LispKind::MVar(_, it) => it,
      _ => return Err(err!(e, format!("not a proof: {}", self.print(e))))
    })
  }

  /// Get the type of the proof `e` (with only minimal type-checking).
  pub fn infer_type(&self, sp: Span, e: &LispVal) -> Result<LispVal> {
    macro_rules! err {
      ($e:expr, $err:expr) => {ElabError::new_e(try_get_span(&self.fspan(sp), &$e), $err)}
    }
    Ok(match &*e.unwrapped_arc() {
      &LispKind::Atom(h) => match self.lc.get_proof(h) {
        Some((_, e, _)) => e.clone(),
        None => return Err(err!(e, format!("unknown hypothesis '{}'", self.data[h].name)))
      },
      LispKind::List(_) | LispKind::DottedList(_, _) => {
        let mut u = Uncons::from(e.clone());
        let head = u.next().ok_or_else(|| err!(e, "not a proof"))?;
        match head.as_atom().ok_or_else(|| err!(head, "expected an atom"))? {
          AtomId::CONV => u.next().ok_or_else(|| err!(e, "bad :conv"))?,
          a => {
            let tid = self.thm(a).ok_or_else(||
              err!(head, format!("unknown theorem '{}'", self.data[a].name)))?;
            let tdata = &self.env.thms[tid];
            let num_args = tdata.args.len();
            let mut args = Vec::with_capacity(num_args);
            if !u.extend_into(num_args, &mut args) {return Err(err!(e, "not enough arguments"))}
            Subst::new(&self.env, &tdata.heap, args).subst(&tdata.ret)
          }
        }
      }
      LispKind::Goal(e) => e.clone(),
      _ => return Err(err!(e, format!("not a proof: {}", self.print(e))))
    })
  }

  /// Coerce term `e`, which has sort `s` and boundedness `bd`, to target `tgt`.
  fn coerce_term(&mut self, sp: Span, tgt: InferTarget, s: SortId, bd: bool, e: LispVal) -> Result<LispVal> {
    let tgt = match tgt {
      InferTarget::Unknown => return Ok(e),
      InferTarget::Provable if self.sorts[s].mods.contains(Modifiers::PROVABLE) => return Ok(e),
      InferTarget::Provable => *self.pe.coe_prov.get(&s).ok_or_else(||
        ElabError::new_e(sp, format!("type error: expected provable, got {}", self.print(&s))))?,
      InferTarget::Bound(_) if !bd => return Err(ElabError::new_e(sp, "type error: expected bound var, got regular")),
      InferTarget::Bound(tgt) => self.data[tgt].sort.ok_or_else(|| ElabError::new_e(sp, "bad sort"))?,
      InferTarget::Reg(tgt) => self.data[tgt].sort.ok_or_else(|| ElabError::new_e(sp, "bad sort"))?,
    };
    if s == tgt {return Ok(e)}
    let c = self.pe.coes.get(&s).and_then(|m| m.get(&tgt)).ok_or_else(||
      ElabError::new_e(sp, format!("type error: expected {}, got {}", self.print(&tgt), self.print(&s))))?;
    Ok(self.apply_coe(&Some(self.fspan(sp)), c, e))
  }

  /// Coerce proof `p`, which has type `e`, to target `tgt`.
  fn coerce_to(&mut self, sp: Span, tgt: LispVal, e: &LispVal, p: LispVal) -> Result<LispVal> {
    Ok(LispVal::apply_conv(self.unify(sp, &tgt, e)?, tgt, p))
  }

  /// Return true if `e` contains an occurrence of the metavariable `mv`.
  /// We use this before assigning `mv := e` to ensure acyclicity.
  fn occurs(&mut self, mv: &LispVal, e: &LispVal) -> bool {
    match &**e {
      LispKind::Annot(_, e) => self.occurs(mv, e),
      LispKind::Ref(m) => mv.ptr_eq(e) || m.get(|e2| self.occurs(mv, e2)),
      LispKind::List(es) => es.iter().any(|e| self.occurs(mv, e)),
      LispKind::DottedList(es, r) =>
        es.iter().any(|e| self.occurs(mv, e)) && self.occurs(mv, r),
      _ => false,
    }
  }

  /// Assign metavariable `mv` to `e` (or fail). `m` is the underlying reference of `mv`.
  /// If `sym` is false then this is the result of `mv =?= e`, otherwise it
  /// is `e =?= mv`; currently we don't use this information.
  fn assign(&mut self, _sym: bool, mv: &LispVal, m: &LispRef, e: &LispVal) -> Result<(), AssignError> {
    let e = &e.as_mvar(|e2, _| e2.clone()).unwrap_or_else(|| e.clone());
    if mv.ptr_eq(e) {return Ok(())}
    if self.occurs(mv, e) {
      Err(AssignError::Cyclic)
    } else {
      if let Some(InferTarget::Bound(_)) = mv.mvar_target() {
        if !e.unwrapped(|r| match r {
          LispKind::Atom(a) => matches!(self.lc.vars.get(a), Some((_, InferSort::Bound {..}))),
          LispKind::MVar(_, is) => is.bound(),
          _ => false,
        }) {return Err(AssignError::BoundVar)}
      }
      let mut e = e.clone();
      if e.fspan().is_none() {
        if let Some(sp) = m.get(|e2| e2.fspan()) {e = e.span(sp)}
      }
      m.get_mut(|e2| *e2 = e);
      Ok(())
    }
  }

  /// Unify expressions `e1` and `e2`. Returns a conversion proof
  /// `u: e1 = e2`, with `#undef` meaning that `e1` and `e2` are equal after unification.
  fn unify(&mut self, sp: Span, e1: &LispVal, e2: &LispVal) -> Result<LispVal> {
    self.unify1(e1, e2).map_err(|e| ElabError::new_e(sp, e))
  }

  /// Unify expressions `e1` and `e2`. Returns a conversion proof
  /// `u: e1 = e2`, with `#undef` meaning that `e1` and `e2` are equal after unification.
  fn unify1(&mut self, e1: &LispVal, e2: &LispVal) -> SResult<LispVal> {
    self.unify_core(e1, e2).map_err(|e| self.format_env().pretty(|p|
      format!("{}\n{}", p.unify_err(e1, e2).pretty(80), e)))
  }

  /// Unify expressions `e1` and `e2`. Returns a conversion proof
  /// `u: e1 = e2`, with `#undef` meaning that `e1` and `e2` are equal after unification.
  fn unify_core(&mut self, e1: &LispVal, e2: &LispVal) -> SResult<LispVal> {
    // println!("{} =?= {}", self.format_env().pp(e1, 80), self.format_env().pp(e2, 80));
    // (|| {
    if e1.ptr_eq(e2) {return Ok(LispVal::undef())}
    match e1.as_mvar(|e1, m| self.assign(false, e1, m, e2)) {
      Some(Ok(())) => return Ok(LispVal::undef()),
      Some(Err(AssignError::Cyclic)) =>
        return Err("occurs-check failed, can't build infinite assignment".into()),
      r1 => match (r1, e2.as_mvar(|e2, m| self.assign(true, e2, m, e1))) {
        (_, Some(Ok(()))) => return Ok(LispVal::undef()),
        (_, Some(Err(AssignError::Cyclic))) =>
          return Err("occurs-check failed, can't build infinite assignment".into()),
        (Some(Err(AssignError::BoundVar)), None) =>
          return Err(format!("type error: expected bound var, got {}", self.print(e2))),
        (None, Some(Err(AssignError::BoundVar))) =>
          return Err(format!("type error: expected bound var, got {}", self.print(e1))),
        (None, None) => {},
        _ => unreachable!()
      }
    }
    match (e1.as_atom(), e2.as_atom()) {
      (Some(a1), Some(a2)) if a1 == a2 => Ok(LispVal::undef()),
      (Some(a1), Some(a2)) => Err(format!(
        "variables do not match: {} != {}", self.data[a1].name, self.data[a2].name)),
      (None, None) => {
        let mut u1 = Uncons::from(e1.clone());
        let mut u2 = Uncons::from(e2.clone());
        let e_t1 = u1.next().ok_or_else(||
          format!("bad term: {}", self.print(e1)))?;
        let a_t1 = e_t1.as_atom().ok_or_else(||
          format!("bad term: {}", self.print(e1)))?;
        let a_t2 = u2.next().and_then(|a| a.as_atom()).ok_or_else(||
          format!("bad term: {}", self.print(e2)))?;
        if a_t1 == a_t2 {
          let mut cs = vec![e_t1];
          let u3 = u1.clone();
          while let (Some(x1), Some(x2)) = (u1.next(), u2.next()) {
            cs.push(self.unify_core(&x1, &x2)?);
          }
          if u1.is_empty() && u2.is_empty() {
            if cs[1..].iter().any(|c| c.is_def()) {
              for (c, x) in cs[1..].iter_mut().zip(u3) {
                if !c.is_def() {*c = x}
              }
              Ok(LispVal::list(cs))
            } else {
              Ok(LispVal::undef())
            }
          } else {
            Err(format!("bad terms: {}, {}", self.print(e1), self.print(e2)))
          }
        } else {
          let t1 = self.term(a_t1).ok_or_else(||
            format!("bad term: {}", self.print(e1)))?;
          let tdata1 = &self.terms[t1];
          let t2 = self.term(a_t2).ok_or_else(||
            format!("bad term: {}", self.print(e2)))?;
          let tdata2 = &self.terms[t2];
          macro_rules! s {() => {format!(
            "terms do not match: {} != {}", self.data[a_t1].name, self.data[a_t2].name)
          }}

          match (&tdata1.kind, &tdata2.kind) {
            (_, TermKind::Def(_)) if t1 < t2 => self.unfold(true, t2, &u2, e1).map_err(|e| format!("{}\n{}", s!(), e)),
            (TermKind::Def(_), _) => self.unfold(false, t1, &u1, e2).map_err(|e| format!("{}\n{}", s!(), e)),
            (_, TermKind::Def(_)) => self.unfold(true, t2, &u2, e1).map_err(|e| format!("{}\n{}", s!(), e)),
            _ => Err(s!())
          }
        }
      }
      _ => Err(format!(
        "variable vs term: {} != {}", self.print(e1), self.print(e2))),
    }
    // })().map(|r| {
    //   let fe = self.format_env();
    //   println!("{} =?= {}\n:= {}", fe.pp(e1, 80), fe.pp(e2, 80), fe.pp(&r, 80));
    //   r
    // })
  }

  /// Produce a proof that `(tid u1) = e2` if `sym` is false, or `e2 = (tid u1)` if `sym` is true.
  fn unfold(&mut self, sym: bool, tid: TermId, u1: &Uncons, e2: &LispVal) -> SResult<LispVal> {
    let tdata = &self.env.terms[tid];
    let a = tdata.atom;
    let nargs = tdata.args.len();
    if let TermKind::Def(Some(val)) = &tdata.kind {
      let mut args = Vec::with_capacity(nargs);
      if !u1.extend_into(nargs, &mut args) {
        return Err(format!("bad term: {}", self.print(u1)))
      }
      let e1_unfolded = Subst::new(&self.env, &val.heap, args.clone())
        .subst_mut(&mut self.lc, &val.head);
      let conv = self.unify1(&e1_unfolded, e2)?;
      let conv = LispVal::unfold(a, args, if conv.is_def() {conv} else {e1_unfolded});
      Ok(if sym {LispVal::sym(conv)} else {conv})
    } else {
      Err(format!("not a definition: {}", self.print(&a)))
    }
  }

  fn type_target(&self, ty: &Type) -> InferTarget {
    match *ty {
      Type::Bound(s) => InferTarget::Bound(self.sorts[s].atom),
      Type::Reg(s, _) => InferTarget::Reg(self.sorts[s].atom),
    }
  }

  /// Run the main `refine` state machine. The normal entry point sets
  /// `stack = []` and `active = RState::Goals {gs, es}` where `es` is the input
  /// and `gs` is the current set of goals. See the [`RState`] and [`RStack`]
  /// types for a description of the different states.
  #[allow(clippy::never_loop)]
  pub(crate) fn run_refine(&mut self,
    sp: Span,
    stack: &mut Vec<RStack>,
    mut active: RState
  ) -> Result<RefineResult> {
    let fsp = self.fspan(sp);
    'main: loop {
      // if self.check_proofs {
      //   println!("{}", self.print(&active));
      // }
      active = match active {
        RState::Goals {mut gs, mut es, ret_val} => {
          if let Some(p) = es.next() {
            while let Some(g) = gs.next() {
              if let Some(tgt) = g.goal_type() {
                stack.push(RStack::Goals {g, gs, es, ret_val});
                active = RState::RefineProof {tgt, p};
                continue 'main
              }
            }
          }
          self.lc.goals.extend(gs);
          if ret_val {
            RState::Ret(LispVal::undef())
          } else {
            assert!(stack.is_empty());
            return Ok(RefineResult::RetNone)
          }
        }
        RState::RefineProof {tgt, p} => match self.parse_refine(&fsp, &p)? {
          RefineExpr::App {sp, sp2, head: AtomId::QMARK, ..} => {
            let head = LispVal::new_ref(LispVal::goal(self.fspan(sp), tgt));
            self.spans.insert_if(sp2, || ObjectKind::proof(head.clone()));
            RState::Ret(head)
          }
          RefineExpr::App {sp, sp2, head: AtomId::UNDER, u, ..} => {
            if u.is_empty() {
              let head = self.new_goal(sp, tgt);
              self.spans.insert_if(sp2, || ObjectKind::proof(head.clone()));
              RState::Ret(head)
            } else {
              let mv = self.lc.new_mvar(InferTarget::Unknown, Some(self.fspan(sp2)));
              let head = self.new_goal(sp, mv);
              self.spans.insert_if(sp2, || ObjectKind::proof(head.clone()));
              return Ok(RefineResult::RefineExtraArgs(tgt, head, u))
            }
          }
          RefineExpr::App {sp, sp2, im, head: a, u} => {
            let head = LispVal::atom(a).span(self.fspan(sp2));
            if let Some((_, ty, _)) = self.lc.get_proof(a) {
              self.spans.insert_if(sp2, || ObjectKind::proof(head.clone()));
              RState::RefineArgs {sp, ty: ty.clone(), tgt, p: head, u}
            } else if let Some(DeclKey::Thm(t)) = self.data[a].decl {
              RState::RefineBis {sp, sp2, tgt, im, t, args: vec![head], u}
            } else {
              return Err(ElabError::new_e(sp2, format!(
                "unknown theorem/hypothesis '{}'", self.data[a].name)))
            }
          }
          RefineExpr::Typed {ty, e: q} => {
            stack.push(RStack::TypedAt {sp: try_get_span(&fsp, &p), tgt, p: q});
            RState::RefineExpr {tgt: InferTarget::Unknown, e: ty}
          }
          RefineExpr::Exact(p) => {
            let e = self.infer_type(sp, &p)?;
            RState::Ret(self.coerce_to(sp, tgt, &e, p)?)
          }
          RefineExpr::Proc => RState::Proc {tgt, p},
        },
        RState::RefineExpr {tgt, e} => match self.parse_refine(&fsp, &e) {
          Ok(RefineExpr::App {sp2, head: AtomId::UNDER, ..}) => {
            let head = self.lc.new_mvar(tgt, Some(self.fspan(sp2)));
            self.spans.insert_if(sp2, || ObjectKind::expr(head.clone()));
            RState::Ret(head)
          }
          Ok(RefineExpr::App {sp, sp2, head: a, u, ..}) => {
            let empty = u.is_empty();
            let head = LispVal::atom(a);
            self.spans.insert_if(sp2, || ObjectKind::expr(head.clone()));
            if let Some((_, is)) = if empty {self.lc.vars.get(&a)} else {None} {
              let (sort, bd) = match *is {
                InferSort::Bound(sort) => (sort, true),
                InferSort::Reg(sort, _) => (sort, false),
                InferSort::Unknown {..} => unreachable!(),
              };
              RState::Ret(self.coerce_term(sp, tgt, sort, bd, head)?)
            } else if let Some(t) = if tgt.bound() {None} else {self.term(a)} {
              RState::RefineApp {sp2, tgt, t, u, args: vec![head]}
            } else if let Some(s) = tgt.sort().filter(|_| empty) {
              let sort = self.data[s].sort.ok_or_else(|| ElabError::new_e(sp, "bad sort"))?;
              self.lc.vars.insert(a, (true, InferSort::Bound(sort)));
              RState::Ret(head)
            } else {
              return Err(ElabError::new_e(sp, format!("unknown term '{}'", self.data[a].name)))
            }
          }
          Ok(RefineExpr::Typed {ty: s, e}) => {
            let s = s.as_atom().filter(|&s| self.data[s].sort.is_some())
              .ok_or_else(|| ElabError::new_e(sp, "expected a sort"))?;
            RState::RefineExpr {
              e,
              tgt: if tgt.bound() {InferTarget::Bound(s)} else {InferTarget::Reg(s)}
            }
          }
          Ok(RefineExpr::Exact(e)) => RState::Ret(e),
          Ok(RefineExpr::Proc) => RState::Ret(e),
          Err(err) => (|| -> Result<_> {
            if let Some(proc) = &self.data[AtomId::TO_EXPR_FALLBACK].lisp {
              let proc = proc.val.clone();
              let args = vec![tgt.sort().map_or_else(LispVal::undef, LispVal::atom), e.clone()];
              if let Ok(res) = self.call_func(sp, &proc, args) {
                return Ok(RState::Ret(res))
              }
            }
            Err(err)
          })()?
        },
        RState::RefineApp {sp2, tgt: ret, t, mut u, mut args} => {
         'l: loop { // labeled block, not a loop. See rust#48594
            let tdata = &self.env.terms[t];
            for (_, ty) in &tdata.args[args.len() - 1..] {
              let tgt = self.type_target(ty);
              match u.next() {
                Some(e) => {
                  stack.push(RStack::RefineApp {sp2, tgt: ret, t, u, args});
                  break 'l RState::RefineExpr {tgt, e}
                }
                None => args.push(self.lc.new_mvar(tgt, Some(self.fspan(sp2))))
              }
            }
            let s = tdata.ret.0;
            break RState::Ret(self.coerce_term(sp, ret, s, false, LispVal::list(args))?)
          }
        }
        RState::RefineArgs {sp, tgt, ty, p, u} if u.is_empty() =>
          RState::Ret(self.coerce_to(sp, tgt, &ty, p)?),
        RState::RefineArgs {tgt, p, u, ..} =>
          return Ok(RefineResult::RefineExtraArgs(tgt, p, u)),
        RState::RefineBis {sp, sp2, tgt, im, t, mut u, mut args} => {
          'l2: loop { // labeled block, not a loop. See rust#48594
            let tdata = &self.env.thms[t];
            for (_, ty) in &tdata.args[args.len() - 1..] {
              let tgt1 = self.type_target(ty);
              let explicit = match im {
                InferMode::Regular => false,
                InferMode::Explicit => true,
                InferMode::BoundOnly => ty.bound(),
              };
              if let Some(e) = if explicit {u.next()} else {None} {
                stack.push(RStack::RefineBis {sp, sp2, tgt, im, t, u, args});
                break 'l2 RState::RefineExpr {tgt: tgt1, e}
              }
              args.push(self.lc.new_mvar(tgt1, Some(self.fspan(sp2))))
            }
            let mut subst = Subst::new(&self.env, &tdata.heap, Vec::from(&args[1..]));
            let hyps = tdata.hyps.iter().map(|(_, h)| subst.subst(h)).collect::<Vec<_>>();
            let ret = subst.subst(&tdata.ret);
            break RState::RefineHyps {
              res: if u.len() <= hyps.len() {
                RefineHypsResult::Ok(self.unify(sp2, &tgt, &ret)?)
              } else {
                RefineHypsResult::Extra
              },
              sp, sp2, tgt, t, u, args, hyps: hyps.into_iter()
            }
          }
        }
        RState::RefineHyps {sp, sp2, tgt, t, mut u, mut args, mut hyps, res} => {
          'l3: loop { // labeled block, not a loop. See rust#48594
            while let Some(h) = hyps.next() {
              if let Some(p) = u.next() {
                stack.push(RStack::RefineHyps {sp, sp2, tgt, t, u, args, hyps, res});
                break 'l3 RState::RefineProof {tgt: h, p}
              }
              args.push(self.new_goal(sp, h))
            }
            let head = LispVal::list(args);
            self.spans.insert_if(sp2, || ObjectKind::proof(head.clone()));
            break match res {
              RefineHypsResult::Ok(c) => RState::Ret(LispVal::apply_conv(c, tgt, head)),
              RefineHypsResult::Extra =>
                return Ok(RefineResult::RefineExtraArgs(tgt, head, u)),
            }
          }
        }
        RState::Proc {tgt, p} => return Ok(RefineResult::Proc(tgt, p)),
        RState::Ret(ret) => match stack.pop() {
          None => return Ok(RefineResult::Ret(ret)),
          Some(RStack::DeferGoals(mut gs)) => {
            self.lc.goals.append(&mut gs);
            RState::Ret(ret)
          }
          Some(RStack::Goals {g, gs, es, ret_val}) => {
            g.as_ref_(|e| *e = ret).expect("a goal is a ref");
            RState::Goals {gs, es, ret_val}
          }
          Some(RStack::Coerce {tgt, u}) => RState::Ret(LispVal::apply_conv(u, tgt, ret)),
          Some(RStack::CoerceTo(tgt)) => {
            let sp = try_get_span(&fsp, &ret);
            let e = self.infer_type(sp, &ret)?;
            RState::Ret(self.coerce_to(sp, tgt, &e, ret)?)
          }
          Some(RStack::TypedAt {sp, tgt, p}) => {
            stack.push(RStack::Coerce {u: self.unify(sp, &tgt, &ret)?, tgt});
            RState::RefineProof {tgt: ret, p}
          }
          Some(RStack::Typed(p)) => RState::RefineProof {tgt: ret, p},
          Some(RStack::RefineApp {sp2, tgt, t, u, mut args}) => {
            args.push(ret);
            RState::RefineApp {sp2, tgt, t, u, args}
          }
          Some(RStack::RefineBis {sp, sp2, tgt, im, t, u, mut args}) => {
            args.push(ret);
            RState::RefineBis {sp, sp2, tgt, im, t, u, args}
          }
          Some(RStack::RefineHyps {sp, sp2, tgt, t, u, mut args, hyps, res}) => {
            args.push(ret);
            RState::RefineHyps {sp, sp2, tgt, t, u, args, hyps, res}
          }
        },
      }
    }
  }
}
