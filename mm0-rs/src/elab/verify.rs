//! A non-critical verifier used to sanity check definitions in the environment.

use std::{collections::HashMap, fmt::Write, cell::Cell};

use mm0_util::{AtomId, Modifiers, SortId, TermId, ThmId, LinedString};
use mm0b_parser::MAX_BOUND_VARS;

use crate::{DeclKey, Environment, ExprNode, FormatEnv, LispVal, ProofNode, Term, TermKind, Thm, ThmKind, Type};
use super::proof::Subst;

/// If true, environment additions will be verified before going in the environmenst.
pub const VERIFY_ON_ADD: bool = true;

/// Errors that can appear during expression verification.
#[derive(Clone, Copy, Debug)]
pub enum ExprVerifyError<'a> {
  /// At `parent`: Expected sort `s1`, got `e : s2`
  SortError(&'a ExprNode, SortId, SortId),
  /// Expected bound variable, got expression
  BoundError(&'a ExprNode),
}

/// Errors that can appear during proof verification.
#[derive(Clone, Copy, Debug)]
pub enum ProofVerifyError<'a> {
  /// At `parent`: Expected sort `s1`, got `e : s2`
  SortError(Option<ThmId>, &'a ProofNode, usize, SortId, SortId),
  /// Expected bound variable, got expression
  BoundError(Option<ThmId>, &'a ProofNode, usize),
  /// Disjoint variable violation when applying theorem
  DisjointVariableViolation,
  /// Subproof `th` proved `|- e`, and was expected to prove something else
  UnifyFailure(Option<usize>, &'a ProofNode),
  /// Expected expression, got proof or conv
  ExpectedExpr(&'a ProofNode),
  /// Expected proof, got expr or conv
  ExpectedProof(&'a ProofNode),
  /// Expected conv, got expr or proof
  ExpectedConv(&'a ProofNode),
  /// Conv `c` does not prove `lhs = rhs`
  ExpectedConvSides(&'a ProofNode, &'a ProofNode),
  /// Cannot unfold a non-definition
  UnfoldNonDef,
}

/// Errors that can appear during verification.
#[derive(Clone, Copy, Debug)]
pub enum VerifyError<'a> {
  /// An error in expression validation.
  ExprVerifyError(&'a [ExprNode], &'a [ExprNode], Option<&'a ExprNode>, ExprVerifyError<'a>),
  /// An error in proof validation.
  ProofVerifyError(ProofContext<'a>, Option<&'a ProofNode>, ProofVerifyError<'a>),
  /// The visibility applied to this definition is not valid for the definition.
  InvalidVisibility,
  /// Sort `s` was referenced before it was declared.
  FwdReferenceSort(SortId),
  /// Term `t` was referenced before it was declared.
  FwdReferenceTerm(TermId),
  /// Theorem `t` was referenced before it was declared.
  FwdReferenceThm(ThmId),
  /// A variable depends on a bound variable which has not yet been declared.
  DepsOutOfBounds,
  /// Maximum number of bound variables exceeded
  MaxBoundVars,
  /// Bound variable declared in a `strict` sort
  BoundInStrictSort,
  /// Dummy variable declared in a `free` sort
  DummyInFreeSort,
  /// Term declared in a `pure` sort
  TermInPureSort,
  /// Definition or theorem uses `sorry`
  UsesSorry,
  /// Expression or proof heap has structural issues
  MalformedHeap,
  /// Expression or proof store has structural issues
  MalformedStore,
  /// Expected dependencies `deps1`, got `deps2`
  ExprDepsError(u64, u64),
  /// Dummy `a` declared more than once
  DummyDeclaredTwice(AtomId),
  /// Dummy variable in a theorem declaration
  InvalidDummy,
  /// Theorem hypothesis or conclusion not in a `provable` sort
  HypNotInProvableSort,
  /// Hypothesis `i` declared multiple times
  MultipleHyp(usize),
  /// `hyps[i]` does not point to `Hyp(i, e)`
  MalformedHyp(usize),
  /// Hypothesis `i` claims to have different types in the signature and body
  HypUnifyFailure(usize),
  /// Theorem proved `|- e` but the signature claims something else
  ThmUnifyFailure(&'a ProofNode),
}

fn expr_head(heap: &[ExprNode], e: &ExprNode) -> Option<TermId> {
  match *e {
    ExprNode::Ref(i) if i < heap.len() => expr_head(&heap[..i], &heap[i]),
    ExprNode::App(term, ..) => Some(term),
    _ => None,
  }
}

impl ExprVerifyError<'_> {
  /// Convert this error to an error message.
  pub fn render<W: Write>(&self, env: &Environment,
    heap: &[ExprNode], _store: &[ExprNode], parent: Option<&ExprNode>, w: &mut W
  ) -> std::fmt::Result {
    if let Some(term) = parent.and_then(|e| expr_head(heap, e)) {
      write!(w, "at {}: ", env.data[env.terms[term].atom].name)?
    }
    match *self {
      Self::SortError(_, s1, s2) => write!(w, "Expected sort {}, got {}",
        env.data[env.sorts[s1].atom].name, env.data[env.sorts[s2].atom].name),
      Self::BoundError(_) => write!(w, "Expected bound variable, got expression"),
    }
  }
}

fn proof_head(heap: &[ProofNode], e: &ProofNode) -> Option<DeclKey> {
  match *e {
    ProofNode::Ref(i) if i < heap.len() => proof_head(&heap[..i], &heap[i]),
    ProofNode::Thm(thm, ..) => Some(DeclKey::Thm(thm)),
    ProofNode::Term(term, ..) |
    ProofNode::Cong(term, ..) |
    ProofNode::Unfold(term, ..) => Some(DeclKey::Term(term)),
    _ => None
  }
}

impl ProofVerifyError<'_> {
  /// Convert this error to an error message.
  pub fn render<W: Write>(&self,
    env: &Environment, ctx: &ProofContext<'_>, parent: Option<&ProofNode>, w: &mut W
  ) -> std::fmt::Result {
    match parent.and_then(|e| proof_head(ctx.heap, e)) {
      Some(DeclKey::Thm(thm)) => write!(w, "at {}: ", env.data[env.thms[thm].atom].name)?,
      Some(DeclKey::Term(term)) => write!(w, "at {}: ", env.data[env.terms[term].atom].name)?,
      _ => {}
    }
    let build_heap = || {
      let mut lisp_heap = Vec::with_capacity(ctx.heap.len());
      lisp_heap.extend(ctx.args.iter().map(|&(a, _)| LispVal::atom(a.unwrap_or(AtomId::UNDER))));
      for e in &ctx.heap[lisp_heap.len()..] {
        let e = env.proof_node(ctx.hyps, &lisp_heap, &mut None, ctx.store, e);
        lisp_heap.push(e)
      }
      lisp_heap
    };
    match *self {
      Self::SortError(p, _, i, s1, s2) => {
        write!(w, "arg {}: ", i+1)?;
        if let Some(thm) = p {
          write!(w, "(in subproof for {}) ", env.data[env.thms[thm].atom].name)?
        }
        write!(w, "Expected sort {}, got {}",
          env.data[env.sorts[s1].atom].name, env.data[env.sorts[s2].atom].name)
      }
      Self::BoundError(p, _, i) => {
        write!(w, "arg {}: ", i+1)?;
        if let Some(thm) = p {
          write!(w, "(in subproof for {}) ", env.data[env.thms[thm].atom].name)?
        }
        write!(w, "Expected bound variable, got expression")
      }
      Self::DisjointVariableViolation => {
        // if let Some(e) = parent {
        //   with_format_env(env, |fe| if let Some(fe) = fe {
        //     let lisp_heap = build_heap();
        //     let p = env.proof_node(ctx.hyps, &lisp_heap, &mut None, ctx.store, e);
        //     writeln!(w, "at: {}", fe.pp(&p, 80)).unwrap()
        //   });
        // }
        write!(w, "Disjoint variable violation when applying theorem")
      },
      Self::UnifyFailure(i, proved) => with_format_env(env, |fe| if let Some(fe) = fe {
        let Some(&ProofNode::Thm(thm, p)) = parent else { unreachable!() };
        let td = &env.thms[thm];
        let lisp_heap = build_heap();
        let (_, args, _) = td.unpack_thm(&ctx.store[p..]);
        let lisp_args = args.iter()
          .map(|e| env.proof_node(ctx.hyps, &lisp_heap, &mut None, ctx.store, e)).collect::<Vec<_>>();
        let proved = env.proof_node(ctx.hyps, &lisp_heap, &mut None, ctx.store, proved);
        let mut subst = Subst::new(env, &td.heap, &td.store, lisp_args.clone());
        fe.pretty(|pp| {
          pp.verify_subst_err(i, &lisp_args, &proved, td, |e| subst.subst(e)).render_fmt(80, w)
        })
      } else {
        write!(w, "Subproof {i:?} failed to prove what it should")
      }),
      Self::ExpectedExpr(_) => write!(w, "Expected expression, got proof or conv"),
      Self::ExpectedProof(_) => write!(w, "Expected proof, got expr or conv"),
      Self::ExpectedConv(_) => write!(w, "Expected conv, got expr or proof"),
      Self::ExpectedConvSides(lhs, rhs) => with_format_env(env, |fe| if let Some(fe) = fe {
        let lisp_heap = build_heap();
        fe.pretty(|pp| {
          writeln!(w, "Conv proved the wrong thing: expected")?;
          pp.expr(&env.proof_node(ctx.hyps, &lisp_heap, &mut None, ctx.store, lhs)).render_fmt(80, w)?;
          writeln!(w, "\n  =")?;
          pp.expr(&env.proof_node(ctx.hyps, &lisp_heap, &mut None, ctx.store, rhs)).render_fmt(80, w)
        })
      } else {
        write!(w, "Conv proved the wrong thing")
      }),
      Self::UnfoldNonDef => write!(w, "Cannot unfold a non-definition"),
    }
  }
}

impl VerifyError<'_> {
  /// Convert this error to an error message.
  pub fn render<W: Write>(&self, env: &Environment, w: &mut W) -> std::fmt::Result {
    match *self {
      VerifyError::ExprVerifyError(heap, store, parent, e) => e.render(env, heap, store, parent, w),
      VerifyError::ProofVerifyError(ref ctx, parent, e) => e.render(env, ctx, parent, w),
      VerifyError::InvalidVisibility => write!(w, "invalid visibility"),
      VerifyError::FwdReferenceSort(s) => write!(w,
        "sort {} was referenced before it was declared", env.data[env.sorts[s].atom].name),
      VerifyError::FwdReferenceTerm(t) => write!(w,
        "term {} was referenced before it was declared", env.data[env.terms[t].atom].name),
      VerifyError::FwdReferenceThm(t) => write!(w,
        "theorem {} was referenced before it was declared", env.data[env.thms[t].atom].name),
      VerifyError::DepsOutOfBounds => write!(w,
        "A variable depends on a bound variable which has not yet been declared."),
      VerifyError::MaxBoundVars => write!(w,
        "Maximum number of bound variables exceeded (max {MAX_BOUND_VARS})"),
      VerifyError::BoundInStrictSort => write!(w, "Bound variable declared in a `strict` sort"),
      VerifyError::DummyInFreeSort => write!(w, "Dummy variable declared in a `free` sort"),
      VerifyError::TermInPureSort => write!(w, "Term declared in a `pure` sort"),
      VerifyError::UsesSorry => write!(w, "Definition or theorem uses `sorry`"),
      VerifyError::MalformedHeap => write!(w, "Expression or proof heap has structural issues"),
      VerifyError::MalformedStore => write!(w, "Expression or proof store has structural issues"),
      VerifyError::ExprDepsError(_, _) => write!(w, "Unaccounted dependencies"),
      VerifyError::DummyDeclaredTwice(a) => write!(w, "Dummy {} declared more than once",
        env.data[a].name),
      VerifyError::InvalidDummy => write!(w, "Dummy variable in a theorem declaration"),
      VerifyError::HypNotInProvableSort => write!(w,
        "Theorem hypothesis or conclusion not in a `provable` sort"),
      VerifyError::MultipleHyp(i) => write!(w, "Hypothesis {i} declared multiple times"),
      VerifyError::MalformedHyp(i) => write!(w, "`hyps[{i}]` does not point to `Hyp({i}, e)`"),
      VerifyError::HypUnifyFailure(i) => write!(w,
        "Hypothesis {i} claims to have different types in the signature and body"),
      VerifyError::ThmUnifyFailure(_) => write!(w,
        "Theorem proved one thing but the signature claims something else"),
    }
  }

  /// Convert this error to an error message.
  #[must_use] pub fn render_to_string(&self, env: &Environment) -> String {
    let mut s = String::new();
    self.render(env, &mut s).expect("impossible");
    s
  }
}

/// Adds a side-channel parameter to `render_to_string`.
pub fn scope_ast_source<R>(source: &LinedString, f: impl FnOnce() -> R) -> R {
  // We use a drop guard for panic safety
  struct ResetOnDrop(*const LinedString);
  impl Drop for ResetOnDrop {
    fn drop(&mut self) { SCOPED_SRC.with(|k| k.set(self.0)) }
  }
  let guard = ResetOnDrop(SCOPED_SRC.with(|k| k.replace(source)));
  let r = f();
  drop(guard);
  r
}

/// Get a [`FormatEnv`] within the scope of a `scope_ast_source` call.
pub fn with_format_env<R>(env: &Environment, f: impl FnOnce(Option<FormatEnv<'_>>) -> R) -> R {
  SCOPED_SRC.with(|k| {
    // Safety: SCOPED_SRC is only non-null within the scope of a `scope_ast_source` call, which
    // ensures that the value is still alive. We tie this to the lifetime of the `FormatEnv<'a>`
    // passed to `f`, so this function does not need to be unsafe.
    f(unsafe { k.get().as_ref() }.map(|source| FormatEnv {source, env}))
  })
}

thread_local! {
  /// A side-channel parameter passed through a thread local.
  /// See [`scope_ast_source`] and [`with_format_env`].
  static SCOPED_SRC: Cell<*const LinedString> = const { Cell::new(std::ptr::null()) };
}

/// An upper bound on the terms/theorems that can be used in a proof. Used to ensure acyclicity.
#[derive(Clone, Copy, Debug, Default)]
pub struct Bound {
  /// If Some, proof must use sorts strictly before this one; if None there is no restriction
  sort: Option<SortId>,
  /// If Some, proof must use terms strictly before this one; if None there is no restriction
  term: Option<TermId>,
  /// If Some, proof must use theorems strictly before this one; if None there is no restriction
  thm: Option<ThmId>,
}

macro_rules! vassert { ($e:expr, $v:expr) => { if !$e { return Err($v) } }}

impl Bound {
  fn check_sort<'a>(&self, s: SortId) -> Result<(), VerifyError<'a>> {
    match self.sort {
      Some(s2) if s2 <= s => Err(VerifyError::FwdReferenceSort(s)),
      _ => Ok(())
    }
  }
  fn check_term<'a>(&self, t: TermId) -> Result<(), VerifyError<'a>> {
    match self.term {
      Some(t2) if t2 <= t => Err(VerifyError::FwdReferenceTerm(t)),
      _ => Ok(())
    }
  }
  fn check_thm<'a>(&self, t: ThmId) -> Result<(), VerifyError<'a>> {
    match self.thm {
      Some(t2) if t2 <= t => Err(VerifyError::FwdReferenceThm(t)),
      _ => Ok(())
    }
  }
}

#[derive(Clone, Copy)]
enum HeapEl<'a> {
  Expr(&'a ProofNode, SortId, bool),
  Proof(&'a ProofNode, &'a ProofNode),
  Conv(&'a ProofNode),
}

impl<'a> HeapEl<'a> {
  fn as_expr(&self, ctx: &ProofContext<'a>, parent: Option<&'a ProofNode>
  ) -> Result<(&'a ProofNode, SortId, bool), VerifyError<'a>> {
    match *self {
      HeapEl::Expr(node, s, bv) => Ok((node, s, bv)),
      HeapEl::Proof(node, _) |
      HeapEl::Conv(node) => Err(VerifyError::ProofVerifyError(*ctx, parent,
        ProofVerifyError::ExpectedExpr(node))),
    }
  }

  fn as_proof(&self,
    ctx: &ProofContext<'a>, parent: Option<&'a ProofNode>
  ) -> Result<&'a ProofNode, VerifyError<'a>> {
    match *self {
      HeapEl::Proof(_, e) => Ok(e),
      HeapEl::Expr(node, ..) |
      HeapEl::Conv(node) => Err(VerifyError::ProofVerifyError(*ctx, parent,
        ProofVerifyError::ExpectedProof(node))),
    }
  }
}

#[allow(clippy::type_complexity)]
fn load_args<'a, T>(
  env: &Environment, bound: &Bound, args: &[(T, Type)]
) -> Result<(u64, Vec<(SortId, bool, u64)>), VerifyError<'a>> {
  let mut bvars = 1;
  let mut heap = vec![];
  for (_, ty) in args {
    match *ty {
      Type::Bound(s) => {
        bound.check_sort(s)?;
        vassert!(!env.sorts[s].mods.contains(Modifiers::STRICT), VerifyError::BoundInStrictSort);
        vassert!(bvars < 1 << MAX_BOUND_VARS, VerifyError::MaxBoundVars);
        heap.push((s, true, bvars));
        bvars <<= 1;
      },
      Type::Reg(s, deps) => {
        bound.check_sort(s)?;
        vassert!(deps < bvars, VerifyError::DepsOutOfBounds);
        heap.push((s, false, deps));
      }
    }
  }
  Ok((bvars, heap))
}

impl Environment {
  fn verify_expr_node<'a>(
    &self,
    bound: &Bound,
    orig_heap: &'a [ExprNode],
    store: &'a [ExprNode],
    heap: &[(SortId, bool, u64)],
    dummies: &mut Option<(HashMap<AtomId, SortId>, u64)>,
    node: &'a ExprNode
  ) -> Result<(SortId, bool, u64), VerifyError<'a>> {
    Ok(match *node {
      ExprNode::Ref(i) => heap[i],
      ExprNode::Dummy(a, s) => if let Some((dummies, bvars)) = dummies {
        bound.check_sort(s)?;
        vassert!(!self.sorts[s].mods.contains(Modifiers::STRICT), VerifyError::BoundInStrictSort);
        vassert!(!self.sorts[s].mods.contains(Modifiers::FREE), VerifyError::DummyInFreeSort);
        vassert!(dummies.insert(a, s).is_none(), VerifyError::DummyDeclaredTwice(a));
        let deps = *bvars;
        vassert!(deps < 1 << MAX_BOUND_VARS, VerifyError::MaxBoundVars);
        *bvars <<= 1;
        (s, true, deps)
      } else {
        return Err(VerifyError::InvalidDummy)
      }
      ExprNode::App(t, p) => {
        let td = &self.terms[t];
        bound.check_term(t)?;
        vassert!(p + td.args.len() <= store.len(), VerifyError::MalformedStore);
        let mut deps = vec![];
        let mut accum = 0;
        for (e, (_, ty)) in store[p..].iter().zip(&*td.args) {
          let (s, bv, mut d) = self.verify_expr_node(bound, orig_heap, store, heap, dummies, e)?;
          match *ty {
            Type::Bound(s2) => {
              vassert!(s == s2, VerifyError::ExprVerifyError(orig_heap, store, Some(node),
                ExprVerifyError::SortError(e, s2, s)));
              vassert!(bv, VerifyError::ExprVerifyError(orig_heap, store, Some(node),
                ExprVerifyError::BoundError(e)));
              deps.push(d);
            }
            Type::Reg(s2, d2) => {
              vassert!(s == s2, VerifyError::ExprVerifyError(orig_heap, store, Some(node),
                ExprVerifyError::SortError(e, s2, s)));
              for (i, &dep) in deps.iter().enumerate() {
                if d2 & (1 << i) != 0 { d &= !dep }
              }
              accum |= d;
            }
          }
        }
        if td.ret.1 != 0 {
          for (i, &dep) in deps.iter().enumerate() {
            if td.ret.1 & (1 << i) != 0 { accum |= dep }
          }
        }
        (td.ret.0, false, accum)
      }
    })
  }
}

struct Unifier<'a, 'b> {
  env: &'b Environment,
  e_heap: &'b [ExprNode],
  e_store: &'b [ExprNode],
  p_heap: &'a [ProofNode],
  p_store: &'a [ProofNode],
  tr: Vec<Option<&'a ProofNode>>,
  dummy: HashMap<AtomId, &'a ProofNode>,
}

fn unref<'a>(heap: &'a [ProofNode], pf: &'a ProofNode) -> &'a ProofNode {
  match *pf {
    ProofNode::Ref(i) if i < heap.len() => unref(&heap[..i], &heap[i]),
    _ => pf
  }
}

enum UnifyExprErr {
  UnifyFailure,
  DisjointVariableViolation,
}

impl UnifyExprErr {
  fn into_err<'a>(self, i: Option<usize>, tgt: &'a ProofNode,
    ctx: &ProofContext<'a>, parent: Option<&'a ProofNode>,
  ) -> VerifyError<'a> {
    VerifyError::ProofVerifyError(*ctx, parent, match self {
      UnifyExprErr::UnifyFailure => ProofVerifyError::UnifyFailure(i, tgt),
      UnifyExprErr::DisjointVariableViolation => ProofVerifyError::DisjointVariableViolation,
    })
  }
}

impl<'a, 'b> Unifier<'a, 'b> {
  fn new(env: &'b Environment,
    e_heap: &'b [ExprNode], e_store: &'b [ExprNode],
    p_heap: &'a [ProofNode], p_store: &'a [ProofNode],
  ) -> Self {
    Self {
      env, e_heap, e_store, p_heap, p_store,
      tr: vec![None; e_heap.len()], dummy: HashMap::new()
    }
  }

  fn unify_expr(&mut self, deps: &HashMap<*const ProofNode, u64>,
    e: &ExprNode, pf: &'a ProofNode
  ) -> Result<&'a ProofNode, UnifyExprErr> {
    match *e {
      ExprNode::Ref(i) => {
        if let Some(pf2) = self.tr[i] {
          let pf = unref(self.p_heap, pf);
          if !std::ptr::eq(pf, pf2) { return Err(UnifyExprErr::UnifyFailure) }
          Ok(pf)
        } else {
          let pf = self.unify_expr(deps, &self.e_heap[i], pf)?;
          self.tr[i] = Some(pf);
          Ok(pf)
        }
      }
      ExprNode::Dummy(a, _) => {
        let pf = unref(self.p_heap, pf);
        if let Some(pf2) = self.dummy.insert(a, pf) {
          if !std::ptr::eq(pf, pf2) { return Err(UnifyExprErr::UnifyFailure) }
        } else {
          let d = deps[&std::ptr::from_ref(pf)];
          for pf2 in &self.tr {
            if let Some(pf2) = *pf2 {
              if deps[&std::ptr::from_ref(pf2)] & d != 0 {
                return Err(UnifyExprErr::DisjointVariableViolation)
              }
            }
          }
        }
        Ok(pf)
      }
      ExprNode::App(t, p) => {
        let td = &self.env.terms[t];
        let es = td.unpack_app(&self.e_store[p..]);
        let pf = unref(self.p_heap, pf);
        match *pf {
          ProofNode::Term(term, p2) if term == t => {
            let args = td.unpack_term(&self.p_store[p2..]);
            for (e, arg) in es.iter().zip(args) {
              self.unify_expr(deps, e, arg)?;
            }
            Ok(pf)
          }
          _ => Err(UnifyExprErr::UnifyFailure)
        }
      }
    }
  }
}

/// The top level context objects within which a [`ProofNode`] is interpreted.
#[derive(Clone, Copy, Debug)]
pub struct ProofContext<'a> {
  args: &'a [(Option<AtomId>, Type)],
  hyps: &'a [(Option<AtomId>, ExprNode)],
  heap: &'a [ProofNode],
  store: &'a [ProofNode],
}
struct VerifyProof<'a, 'b> {
  env: &'b Environment,
  bound: &'b Bound,
  ctx: ProofContext<'a>,
  deps: HashMap<*const ProofNode, u64>,
  heap: Vec<HeapEl<'a>>,
  found_hyps: Box<[Option<&'a ProofNode>]>,
  dummies: HashMap<AtomId, SortId>,
  thm_parent: Option<ThmId>,
  bvars: u64,
}

impl<'a, 'b> VerifyProof<'a, 'b> {
  fn verify_proof_node(&mut self, node: &'a ProofNode) -> Result<HeapEl<'a>, VerifyError<'a>> {
    Ok(match *node {
      ProofNode::Ref(i) => self.heap[i],
      ProofNode::Dummy(a, s) => {
        self.bound.check_sort(s)?;
        let mods = self.env.sorts[s].mods;
        vassert!(!mods.contains(Modifiers::STRICT), VerifyError::BoundInStrictSort);
        vassert!(!mods.contains(Modifiers::FREE), VerifyError::DummyInFreeSort);
        vassert!(self.dummies.insert(a, s).is_none(), VerifyError::DummyDeclaredTwice(a));
        let deps = self.bvars;
        vassert!(deps < 1 << MAX_BOUND_VARS, VerifyError::MaxBoundVars);
        self.bvars <<= 1;
        self.deps.insert(node, deps);
        HeapEl::Expr(node, s, true)
      }
      ProofNode::Term(term, p) => {
        self.bound.check_term(term)?;
        let td = &self.env.terms[term];
        vassert!(p + td.args.len() <= self.ctx.store.len(), VerifyError::MalformedStore);
        let args = td.unpack_term(&self.ctx.store[p..]);
        let mut accum = 0;
        for ((i, e), (_, ty)) in args.iter().enumerate().zip(&*td.args) {
          let (pr, s, bv) = self.verify_proof_node(e)?.as_expr(&self.ctx, Some(node))?;
          accum |= self.deps[&std::ptr::from_ref(pr)];
          match *ty {
            Type::Bound(s2) => {
              vassert!(s == s2, VerifyError::ProofVerifyError(self.ctx, Some(node),
                ProofVerifyError::SortError(self.thm_parent, e, i, s2, s)));
              vassert!(bv, VerifyError::ProofVerifyError(self.ctx, Some(node),
                ProofVerifyError::BoundError(self.thm_parent, e, i)));
            }
            Type::Reg(s2, _) => {
              vassert!(s == s2, VerifyError::ProofVerifyError(self.ctx, Some(node),
                ProofVerifyError::SortError(self.thm_parent, e, i, s2, s)));
            }
          }
        }
        self.deps.insert(node, accum);
        HeapEl::Expr(node, td.ret.0, false)
      }
      ProofNode::Hyp(i, p) => {
        vassert!(p < self.ctx.store.len(), VerifyError::MalformedStore);
        let e = unref(self.ctx.heap, &self.ctx.store[p]);
        vassert!(self.found_hyps[i].replace(e).is_none(), VerifyError::MultipleHyp(i));
        HeapEl::Proof(node, e)
      }
      ProofNode::Thm(thm, p) => {
        self.bound.check_thm(thm)?;
        let td = &self.env.thms[thm];
        vassert!(p + td.args.len() + td.hyps.len() < self.ctx.store.len(),
          VerifyError::MalformedStore);
        let (res, args, subproofs) = td.unpack_thm(&self.ctx.store[p..]);
        self.thm_parent = Some(thm);
        let mut deps = vec![];
        let mut uheap = vec![];
        let mut unify = Unifier::new(self.env, &td.heap, &td.store, self.ctx.heap, self.ctx.store);
        for ((i, e), (_, ty)) in args.iter().enumerate().zip(&*td.args) {
          let (e2, s, bv) = self.verify_proof_node(e)?.as_expr(&self.ctx, Some(node))?;
          let d = self.deps[&std::ptr::from_ref(e2)];
          match *ty {
            Type::Bound(s2) => {
              vassert!(s == s2, VerifyError::ProofVerifyError(
                self.ctx, Some(node),
                ProofVerifyError::SortError(None, e, i, s2, s)));
              vassert!(bv, VerifyError::ProofVerifyError(
                self.ctx, Some(node),
                ProofVerifyError::BoundError(None, e, i)));
              for &(_, d2) in &uheap {
                vassert!(d & d2 == 0, VerifyError::ProofVerifyError(self.ctx, Some(node),
                  ProofVerifyError::DisjointVariableViolation));
              }
              deps.push(d);
            }
            Type::Reg(s2, d2) => {
              vassert!(s == s2, VerifyError::ProofVerifyError(
                self.ctx, Some(node),
                ProofVerifyError::SortError(None, e, i, s2, s)));
              for (i, &dep) in deps.iter().enumerate() {
                vassert!(d2 & (1 << i) != 0 || dep & d == 0,
                  VerifyError::ProofVerifyError(self.ctx, Some(node),
                    ProofVerifyError::DisjointVariableViolation));
              }
            }
          }
          uheap.push((e2, d));
        }
        let res = self.verify_proof_node(res)?.as_expr(&self.ctx, Some(node))?.0;
        for ((e, _), o) in uheap.into_iter().zip(&mut unify.tr) { *o = Some(e) }
        let res = unify.unify_expr(&self.deps, &td.ret, res).map_err(|e| e.into_err(
          None, res, &self.ctx, Some(node)))?;
        for (i, (arg, (_, tgt))) in subproofs.iter().zip(&*td.hyps).enumerate() {
          let h = self.verify_proof_node(arg)?.as_proof(&self.ctx, Some(node))?;
          unify.unify_expr(&self.deps, tgt, h).map_err(|e| e.into_err(
            Some(i), h, &self.ctx, Some(node)))?;
        }
        self.thm_parent = None;
        HeapEl::Proof(node, res)
      }
      ProofNode::Conv(p) => {
        vassert!(p + 3 <= self.ctx.store.len(), VerifyError::MalformedStore);
        let (tgt, conv, proof) = ProofNode::unpack_conv(&self.ctx.store[p..]);
        let lhs = unref(self.ctx.heap, tgt);
        let rhs = self.verify_proof_node(proof)?.as_proof(&self.ctx, Some(node))?;
        self.verify_conv_node(node, conv, lhs, rhs)?;
        HeapEl::Proof(node, tgt)
      }
      ProofNode::Refl(_) |
      ProofNode::Sym(_) |
      ProofNode::Cong(..) |
      ProofNode::Unfold(..) => HeapEl::Conv(node)
    })
  }

  fn verify_conv_node(&mut self,
    parent: &'a ProofNode, node: &'a ProofNode, lhs: &'a ProofNode, rhs: &'a ProofNode
  ) -> Result<(), VerifyError<'a>> {
    match *node {
      ProofNode::Ref(i) => match self.heap.get(i) {
        Some(HeapEl::Conv(_)) => self.verify_conv_node(parent, &self.ctx.heap[i], lhs, rhs)?,
        _ => return Err(VerifyError::ProofVerifyError(self.ctx, Some(parent),
          ProofVerifyError::ExpectedConv(node))),
      },
      ProofNode::Refl(p) => {
        vassert!(p < self.ctx.store.len(), VerifyError::MalformedStore);
        let e = unref(self.ctx.heap, &self.ctx.store[p]);
        vassert!(std::ptr::eq(e, lhs) && std::ptr::eq(e, rhs),
          VerifyError::ProofVerifyError(self.ctx, Some(node),
            ProofVerifyError::ExpectedConvSides(lhs, rhs)));
      }
      ProofNode::Sym(p) => {
        vassert!(p < self.ctx.store.len(), VerifyError::MalformedStore);
        self.verify_conv_node(node, &self.ctx.store[p], rhs, lhs)?
      }
      ProofNode::Cong(term, p) => {
        let td = &self.env.terms[term];
        vassert!(p + td.args.len() <= self.ctx.store.len(), VerifyError::MalformedStore);
        let args = td.unpack_term(&self.ctx.store[p..]);
        match (lhs, rhs) {
          (&ProofNode::Term(t1, p1), &ProofNode::Term(t2, p2))
          if term == t1 && term == t2 => {
            let lhss = td.unpack_term(&self.ctx.store[p1..]);
            let rhss = td.unpack_term(&self.ctx.store[p2..]);
            for ((a, l), r) in args.iter().zip(lhss).zip(rhss) {
              self.verify_conv_node(node, a, unref(self.ctx.heap, l), unref(self.ctx.heap, r))?
            }
          }
          _ => return Err(VerifyError::ProofVerifyError(self.ctx, Some(node),
            ProofVerifyError::ExpectedConvSides(lhs, rhs)))
        }
      }
      ProofNode::Unfold(term, p) => match *lhs {
        ProofNode::Term(t1, p1) if term == t1 => {
          let td = &self.env.terms[term];
          vassert!(p + td.args.len() + 2 <= self.ctx.store.len(), VerifyError::MalformedStore);
          let (sub_lhs, c, args) = td.unpack_unfold(&self.ctx.store[p..]);
          let lhss = td.unpack_term(&self.ctx.store[p1..]);
          if let TermKind::Def(Some(expr)) = &td.kind {
            let mut unify = Unifier::new(self.env,
              &expr.heap, &expr.store, self.ctx.heap, self.ctx.store);
            for ((e, e2), o) in args.iter().zip(lhss).zip(&mut unify.tr) {
              let e = unref(self.ctx.heap, e);
              vassert!(std::ptr::eq(e, unref(self.ctx.heap, e2)),
                VerifyError::ProofVerifyError(self.ctx, Some(node),
                  ProofVerifyError::ExpectedConvSides(lhs, rhs)));
              *o = Some(e)
            }
            let sub_lhs = unify.unify_expr(&self.deps, expr.head(), sub_lhs).map_err(|e| e.into_err(
              None, sub_lhs, &self.ctx, Some(node)))?;
            self.verify_conv_node(node, c, sub_lhs, rhs)?
          } else {
            return Err(VerifyError::ProofVerifyError(self.ctx, Some(node),
              ProofVerifyError::UnfoldNonDef))
          }
        }
        _ => return Err(VerifyError::ProofVerifyError(self.ctx, Some(node),
          ProofVerifyError::ExpectedConvSides(lhs, rhs)))
      }
      _ => return Err(VerifyError::ProofVerifyError(self.ctx, Some(parent),
        ProofVerifyError::ExpectedConv(node))),
    }
    Ok(())
  }
}

impl Environment {
  /// Verify that a term definition is type-correct.
  pub fn verify_termdef<'a>(&self, bound: &Bound, td: &'a Term) -> Result<(), VerifyError<'a>> {
    vassert!(match td.kind {
      TermKind::Term => td.vis.is_empty(),
      TermKind::Def(_) => (Modifiers::LOCAL | Modifiers::ABSTRACT).contains(td.vis),
    }, VerifyError::InvalidVisibility);
    let (bvars, mut e_heap) = load_args(self, bound, &td.args)?;
    bound.check_sort(td.ret.0)?;
    vassert!(td.ret.1 < bvars, VerifyError::DepsOutOfBounds);
    vassert!(!self.sorts[td.ret.0].mods.contains(Modifiers::PURE), VerifyError::TermInPureSort);
    match &td.kind {
      TermKind::Term => Ok(()),
      TermKind::Def(None) => Err(VerifyError::UsesSorry),
      TermKind::Def(Some(expr)) => {
        vassert!(e_heap.len() <= expr.heap.len(), VerifyError::MalformedHeap);
        vassert!(!expr.store.is_empty(), VerifyError::MalformedStore);
        for (i, e) in expr.heap.iter().enumerate().take(e_heap.len()) {
          vassert!(matches!(*e, ExprNode::Ref(j) if j == i), VerifyError::MalformedHeap)
        }
        let mut dummies = Some((Default::default(), bvars));
        for e in &expr.heap[e_heap.len()..] {
          e_heap.push(self.verify_expr_node(
            bound, &expr.heap, &expr.store, &e_heap, &mut dummies, e)?)
        }
        let (s, _, deps) = self.verify_expr_node(
          bound, &expr.heap, &expr.store, &e_heap, &mut dummies, expr.head())?;
        vassert!(s == td.ret.0, VerifyError::ExprVerifyError(&expr.heap, &expr.store, None,
          ExprVerifyError::SortError(expr.head(), s, td.ret.0)));
        vassert!(deps & !td.ret.1 == 0, VerifyError::ExprDepsError(deps, td.ret.1));
        Ok(())
      }
    }
  }

  /// Verify that an axiom or theorem is correct and has a proof.
  pub fn verify_thmdef<'a>(&self, bound: &Bound, td: &'a Thm) -> Result<(), VerifyError<'a>> {
    vassert!(match td.kind {
      ThmKind::Axiom => td.vis.is_empty(),
      ThmKind::Thm(_) => Modifiers::PUB.contains(td.vis),
    }, VerifyError::InvalidVisibility);
    let (bvars, mut e_heap) = load_args(self, bound, &td.args)?;
    vassert!(e_heap.len() <= td.heap.len(), VerifyError::MalformedHeap);
    for e in &td.heap[e_heap.len()..] {
      e_heap.push(self.verify_expr_node(bound, &td.heap, &td.store, &e_heap, &mut None, e)?)
    }
    for (_, hyp) in &*td.hyps {
      let (s, _, _) = self.verify_expr_node(bound, &td.heap, &td.store, &e_heap, &mut None, hyp)?;
      vassert!(self.sorts[s].mods.contains(Modifiers::PROVABLE), VerifyError::HypNotInProvableSort);
    }
    let (s, _, _) = self.verify_expr_node(bound, &td.heap, &td.store, &e_heap, &mut None, &td.ret)?;
    vassert!(self.sorts[s].mods.contains(Modifiers::PROVABLE), VerifyError::HypNotInProvableSort);
    match &td.kind {
      ThmKind::Axiom => Ok(()),
      ThmKind::Thm(None) => Err(VerifyError::UsesSorry),
      ThmKind::Thm(Some(pf)) => {
        e_heap.truncate(td.args.len());
        vassert!(e_heap.len() <= pf.heap.len() && td.hyps.len() == pf.hyps.len(),
          VerifyError::MalformedHeap);
        vassert!(!pf.store.is_empty(), VerifyError::MalformedStore);
        let mut ver = VerifyProof {
          env: self,
          bound,
          ctx: ProofContext { args: &td.args, hyps: &td.hyps, heap: &pf.heap, store: &pf.store },
          heap: vec![],
          found_hyps: vec![None; td.hyps.len()].into(),
          deps: Default::default(),
          dummies: Default::default(),
          thm_parent: None,
          bvars,
        };
        let mut hyp_unify = Unifier::new(self, &td.heap, &td.store, &pf.heap, &pf.store);
        for (i, (&(s, bv, d), e)) in e_heap.iter().zip(&*pf.heap).enumerate() {
          vassert!(matches!(*e, ProofNode::Ref(j) if j == i), VerifyError::MalformedHeap);
          hyp_unify.tr[i] = Some(e);
          ver.deps.insert(e, d);
          ver.heap.push(HeapEl::Expr(e, s, bv))
        }
        for e in &pf.heap[e_heap.len()..] {
          let el = ver.verify_proof_node(e)?;
          ver.heap.push(el)
        }
        for (i, ((_, arg), hyp)) in td.hyps.iter().zip(&*pf.hyps).enumerate() {
          ver.verify_proof_node(hyp)?;
          match *unref(&pf.heap, hyp) {
            ProofNode::Hyp(j, p) if j == i => {
              vassert!(p < pf.store.len(), VerifyError::MalformedStore);
              hyp_unify.unify_expr(&ver.deps, arg, &pf.store[p]).map_err(|e| match e {
                UnifyExprErr::UnifyFailure => VerifyError::HypUnifyFailure(i),
                UnifyExprErr::DisjointVariableViolation => VerifyError::InvalidDummy,
              })?;
            }
            _ => return Err(VerifyError::MalformedHyp(i)),
          }
        }
        let res = ver.verify_proof_node(pf.head())?.as_proof(&ver.ctx, None)?;
        hyp_unify.unify_expr(&ver.deps, &td.ret, res).map_err(|e| match e {
          UnifyExprErr::UnifyFailure => VerifyError::ThmUnifyFailure(res),
          UnifyExprErr::DisjointVariableViolation => VerifyError::InvalidDummy,
        })?;
        Ok(())
      }
    }
  }
}
