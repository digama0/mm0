//! A non-critical verifier used to sanity check definitions in the environment.

use std::{collections::HashMap, fmt::Write};

use mm0_util::{AtomId, Modifiers, SortId, TermId, ThmId};
use mm0b_parser::MAX_BOUND_VARS;

use crate::{Environment, Expr, ExprNode, Proof, ProofNode, Term, TermKind, Thm, ThmKind, Type};

/// If true, environment additions will be verified before going in the environmenst.
pub const VERIFY_ON_ADD: bool = true;

/// Errors that can appear during verification.
#[derive(Clone, Copy, Debug)]
pub enum VerifyError<'a> {
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
  /// At `parent`: Expected sort `s1`, got `e : s2`
  ExprSortError(Option<&'a ExprNode>, &'a ExprNode, SortId, SortId),
  /// At `parent`: Expected sort `s1`, got `e : s2`
  ProofSortError(Option<&'a ProofNode>, &'a ProofNode, SortId, SortId),
  /// Expected bound variable, got expression
  ExprBoundError(Option<&'a ExprNode>, &'a ExprNode),
  /// Expected bound variable, got expression
  ProofBoundError(Option<&'a ProofNode>, &'a ProofNode),
  /// Expected dependencies `deps1`, got `deps2`
  ExprDepsError(u64, u64),
  /// Dummy `a` declared more than once
  DummyDeclaredTwice(AtomId),
  /// Expected `n1` args, got `n2`
  ExprTermArgMismatch(&'a ExprNode, usize, usize),
  /// Expected `n1` args, got `n2`
  ProofTermArgMismatch(&'a ProofNode, usize, usize),
  /// Dummy variable in a theorem declaration
  InvalidDummy,
  /// Theorem hypothesis or conclusion not in a `provable` sort
  HypNotInProvableSort,
  /// Hypothesis `i` declared multiple times
  MultipleHyp(usize),
  /// `hyps[i]` does not point to `Hyp(i, e)`
  MalformedHyp(usize),
  /// Disjoint variable violation when applying theorem
  DisjointVariableViolation(&'a ProofNode),
  /// Subproof `th` proved `|- e`, and was expected to prove something else
  UnifyFailure(Option<&'a ProofNode>, &'a ProofNode, &'a ProofNode),
  /// Expected expression, got proof or conv
  ExpectedExpr(Option<&'a ProofNode>, &'a ProofNode),
  /// Expected proof, got expr or conv
  ExpectedProof(Option<&'a ProofNode>, &'a ProofNode),
  /// Expected conv, got expr or proof
  ExpectedConv(Option<&'a ProofNode>, &'a ProofNode),
  /// Conv `c` does not prove `lhs = rhs`
  ExpectedConvSides(Option<&'a ProofNode>, &'a ProofNode, &'a ProofNode, &'a ProofNode),
  /// Cannot unfold a non-definition
  UnfoldNonDef(&'a ProofNode),
  /// Hypothesis `i` claims to have different types in the signature and body
  HypUnifyFailure(usize),
  /// Theorem proved `|- e` but the signature claims something else
  ThmUnifyFailure(&'a ProofNode),
}

impl VerifyError<'_> {
  /// Convert this error to an error message.
  pub fn render(&self, env: &Environment, w: &mut impl Write) -> std::fmt::Result {
    match *self {
      VerifyError::InvalidVisibility => write!(w, "invalid visibility"),
      VerifyError::FwdReferenceSort(s) => write!(w,
        "sort {} was referenced before it was declared", env.data[env.sorts[s].atom].name),
      VerifyError::FwdReferenceTerm(t) => write!(w,
        "term {} was referenced before it was declared", env.data[env.terms[t].atom].name),
      VerifyError::FwdReferenceThm(t) => write!(w,
        "theorem {} was referenced before it was declared", env.data[env.thms[t].atom].name),
      VerifyError::DepsOutOfBounds => write!(w,
        "A variable depends on a bound variable which has not yet been declared."),
      VerifyError::MaxBoundVars => write!(w, "Maximum number of bound variables exceeded"),
      VerifyError::BoundInStrictSort => write!(w, "Bound variable declared in a `strict` sort"),
      VerifyError::DummyInFreeSort => write!(w, "Dummy variable declared in a `free` sort"),
      VerifyError::TermInPureSort => write!(w, "Term declared in a `pure` sort"),
      VerifyError::UsesSorry => write!(w, "Definition or theorem uses `sorry`"),
      VerifyError::MalformedHeap => write!(w, "Expression or proof heap has structural issues"),
      VerifyError::ExprSortError(_, _, s1, s2) |
      VerifyError::ProofSortError(_, _, s1, s2) => write!(w, "Expected sort {}, got {}",
        env.data[env.sorts[s1].atom].name, env.data[env.sorts[s2].atom].name),
      VerifyError::ExprBoundError(_, _) |
      VerifyError::ProofBoundError(_, _) => write!(w, "Expected bound variable, got expression"),
      VerifyError::ExprDepsError(_, _) => write!(w, "Unaccounted dependencies"),
      VerifyError::DummyDeclaredTwice(a) => write!(w, "Dummy {} declared more than once",
        env.data[a].name),
      VerifyError::ExprTermArgMismatch(_, n1, n2) |
      VerifyError::ProofTermArgMismatch(_, n1, n2) => write!(w, "Expected {} args, got {}", n1, n2),
      VerifyError::InvalidDummy => write!(w, "Dummy variable in a theorem declaration"),
      VerifyError::HypNotInProvableSort => write!(w,
        "Theorem hypothesis or conclusion not in a `provable` sort"),
      VerifyError::MultipleHyp(i) => write!(w, "Hypothesis {} declared multiple times", i),
      VerifyError::MalformedHyp(i) => write!(w,
        "`hyps[{i}]` does not point to `Hyp({i}, e)`", i = i),
      VerifyError::DisjointVariableViolation(_) => write!(w,
        "Disjoint variable violation when applying theorem"),
      VerifyError::UnifyFailure(_, _, _) => write!(w, "Subproof proved the wrong thing"),
      VerifyError::ExpectedExpr(_, _) => write!(w, "Expected expression, got proof or conv"),
      VerifyError::ExpectedProof(_, _) => write!(w, "Expected proof, got expr or conv"),
      VerifyError::ExpectedConv(_, _) => write!(w, "Expected conv, got expr or proof"),
      VerifyError::ExpectedConvSides(_, _, _, _) => write!(w, "Conv proved the wrong thing"),
      VerifyError::UnfoldNonDef(_) => write!(w, "Cannot unfold a non-definition"),
      VerifyError::HypUnifyFailure(i) => write!(w,
        "Hypothesis {} claims to have different types in the signature and body", i),
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
  Expr(&'a ProofNode, SortId, bool, u64),
  Proof(&'a ProofNode, &'a ProofNode),
  Conv(&'a ProofNode),
}

impl<'a> HeapEl<'a> {
  fn as_expr(&self,
    parent: Option<&'a ProofNode>
  ) -> Result<(&'a ProofNode, SortId, bool, u64), VerifyError<'a>> {
    match *self {
      HeapEl::Expr(node, s, bv, d) => Ok((node, s, bv, d)),
      HeapEl::Proof(node, _) |
      HeapEl::Conv(node) => Err(VerifyError::ExpectedExpr(parent, node)),
    }
  }

  fn as_proof(&self,
    parent: Option<&'a ProofNode>
  ) -> Result<&'a ProofNode, VerifyError<'a>> {
    match *self {
      HeapEl::Proof(_, e) => Ok(e),
      HeapEl::Expr(node, ..) |
      HeapEl::Conv(node) => Err(VerifyError::ExpectedProof(parent, node)),
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
      ExprNode::App(t, ref es) => {
        bound.check_term(t)?;
        let td = &self.terms[t];
        vassert!(td.args.len() == es.len(),
          VerifyError::ExprTermArgMismatch(node, es.len(), td.args.len()));
        let mut deps = vec![];
        let mut accum = 0;
        for (e, (_, ty)) in es.iter().zip(&*td.args) {
          let (s, bv, mut d) = self.verify_expr_node(bound, heap, dummies, e)?;
          match *ty {
            Type::Bound(s2) => {
              vassert!(s == s2, VerifyError::ExprSortError(Some(node), e, s2, s));
              vassert!(bv, VerifyError::ExprBoundError(Some(node), e));
              deps.push(d);
            }
            Type::Reg(s2, d2) => {
              vassert!(s == s2, VerifyError::ExprSortError(Some(node), e, s2, s));
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
  heap: &'b [ExprNode],
  tr: Vec<Option<&'a ProofNode>>,
  dummy: HashMap<AtomId, &'a ProofNode>,
}

fn unref<'a>(heap: &'a [ProofNode], pf: &'a ProofNode) -> &'a ProofNode {
  match *pf {
    ProofNode::Ref(i) if i < heap.len() => unref(&heap[..i], &heap[i]),
    _ => pf
  }
}

impl<'a, 'b> Unifier<'a, 'b> {
  fn new(heap: &'b [ExprNode]) -> Self {
    Self { heap, tr: vec![None; heap.len()], dummy: HashMap::new() }
  }

  fn unify_expr(&mut self,
    e: &ExprNode, heap: &'a [ProofNode], pf: &'a ProofNode
  ) -> Result<&'a ProofNode, ()> {
    match *e {
      ExprNode::Ref(i) => {
        if let Some(pf2) = self.tr[i] {
          let pf = unref(heap, pf);
          if !std::ptr::eq(pf, pf2) { return Err(()) }
          Ok(pf)
        } else {
          let pf = self.unify_expr(&self.heap[i], heap, pf)?;
          self.tr[i] = Some(pf);
          Ok(pf)
        }
      }
      ExprNode::Dummy(a, _) => {
        let pf = unref(heap, pf);
        if let Some(pf2) = self.dummy.insert(a, pf) {
          if !std::ptr::eq(pf, pf2) { return Err(()) }
        }
        Ok(pf)
      }
      ExprNode::App(t, ref es) => {
        let pf = unref(heap, pf);
        match *pf {
          ProofNode::Term { term, ref args } if term == t => {
            for (e, arg) in es.iter().zip(&**args) {
              self.unify_expr(e, heap, arg)?;
            }
            Ok(pf)
          }
          _ => Err(())
        }
      }
    }
  }
}

struct VerifyProof<'a, 'b> {
  env: &'b Environment,
  bound: &'b Bound,
  orig_heap: &'a [ProofNode],
  heap: Vec<HeapEl<'a>>,
  found_hyps: Box<[Option<&'a ProofNode>]>,
  dummies: HashMap<AtomId, SortId>,
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
        HeapEl::Expr(node, s, true, deps)
      }
      ProofNode::Term { term, ref args } => {
        self.bound.check_term(term)?;
        let td = &self.env.terms[term];
        vassert!(td.args.len() == args.len(),
          VerifyError::ProofTermArgMismatch(node, td.args.len(), args.len()));
        let mut deps = vec![];
        let mut accum = 0;
        for (e, (_, ty)) in args.iter().zip(&*td.args) {
          let (_, s, bv, d) = self.verify_proof_node(e)?.as_expr(Some(node))?;
          match *ty {
            Type::Bound(s2) => {
              vassert!(s == s2, VerifyError::ProofSortError(Some(node), e, s2, s));
              vassert!(bv, VerifyError::ProofBoundError(Some(node), e));
              deps.push(d);
            }
            Type::Reg(s2, _) => {
              vassert!(s == s2, VerifyError::ProofSortError(Some(node), e, s2, s));
              accum |= d;
            }
          }
        }
        HeapEl::Expr(node, td.ret.0, false, accum)
      }
      ProofNode::Hyp(i, ref e) => {
        let e = unref(self.orig_heap, e);
        vassert!(self.found_hyps[i].replace(e).is_none(), VerifyError::MultipleHyp(i));
        HeapEl::Proof(node, e)
      }
      ProofNode::Thm { thm, ref args, ref res } => {
        self.bound.check_thm(thm)?;
        let td = &self.env.thms[thm];
        vassert!(td.args.len() + td.hyps.len() == args.len(),
          VerifyError::ProofTermArgMismatch(node, td.args.len() + td.hyps.len(), args.len()));
        let mut deps = vec![];
        let mut uheap = vec![];
        let mut unify = Unifier::new(&td.heap);
        for (e, (_, ty)) in args.iter().zip(&*td.args) {
          let (e2, s, bv, d) = self.verify_proof_node(e)?.as_expr(Some(node))?;
          match *ty {
            Type::Bound(s2) => {
              vassert!(s == s2, VerifyError::ProofSortError(Some(node), e, s2, s));
              vassert!(bv, VerifyError::ProofBoundError(Some(node), e));
              for &(_, d2) in &uheap {
                vassert!(d & d2 == 0, VerifyError::DisjointVariableViolation(node));
              }
              deps.push(d);
            }
            Type::Reg(s2, d2) => {
              vassert!(s == s2, VerifyError::ProofSortError(Some(node), e, s2, s));
              for (i, &dep) in deps.iter().enumerate() {
                vassert!(d2 & (1 << i) != 0 || dep & d == 0,
                  VerifyError::DisjointVariableViolation(node));
              }
            }
          }
          uheap.push((e2, d));
        }
        for ((e, _), o) in uheap.into_iter().zip(&mut unify.tr) { *o = Some(e) }
        let res = unify.unify_expr(&td.ret, self.orig_heap, res)
          .map_err(|_| VerifyError::UnifyFailure(None, node, res))?;
        for (arg, (_, tgt)) in args[td.args.len()..].iter().zip(&*td.hyps) {
          let h = self.verify_proof_node(arg)?.as_proof(Some(node))?;
          unify.unify_expr(tgt, self.orig_heap, h)
            .map_err(|_| VerifyError::UnifyFailure(Some(node), arg, h))?;
        }
        HeapEl::Proof(node, res)
      }
      ProofNode::Conv(ref args) => {
        let (tgt, conv, proof) = &**args;
        let lhs = unref(self.orig_heap, tgt);
        let rhs = self.verify_proof_node(proof)?.as_proof(Some(node))?;
        self.verify_conv_node(conv, lhs, rhs)?;
        HeapEl::Proof(node, tgt)
      }
      ProofNode::Refl(_) |
      ProofNode::Sym(_) |
      ProofNode::Cong { .. } |
      ProofNode::Unfold { .. } => HeapEl::Conv(node)
    })
  }

  fn verify_conv_node(&mut self, node: &'a ProofNode, lhs: &'a ProofNode, rhs: &'a ProofNode
  ) -> Result<(), VerifyError<'a>> {
    match *node {
      ProofNode::Ref(i) => match self.heap.get(i) {
        Some(HeapEl::Conv(_)) => self.verify_conv_node(&self.orig_heap[i], lhs, rhs)?,
        _ => return Err(dbg!(VerifyError::ExpectedConv(None, node))),
      },
      ProofNode::Refl(ref e) => {
        let e = unref(self.orig_heap, e);
        vassert!(std::ptr::eq(e, lhs) && std::ptr::eq(e, rhs),
          VerifyError::ExpectedConvSides(None, node, lhs, rhs));
      }
      ProofNode::Sym(ref p) => self.verify_conv_node(p, rhs, lhs)?,
      ProofNode::Cong { term, ref args } => {
        match (lhs, rhs) {
          (ProofNode::Term { term: t1, args: lhss }, ProofNode::Term { term: t2, args: rhss })
          if term == *t1 && term == *t2 => {
            vassert!(args.len() == lhss.len(),
              VerifyError::ProofTermArgMismatch(node, lhss.len(), args.len()));
            for ((a, l), r) in args.iter().zip(&**lhss).zip(&**rhss) {
              self.verify_conv_node(a, unref(self.orig_heap, l), unref(self.orig_heap, r))?
            }
          }
          _ => return Err(VerifyError::ExpectedConvSides(None, node, lhs, rhs))
        }
      }
      ProofNode::Unfold { term, ref args, ref res } => match lhs {
        ProofNode::Term { term: t1, args: lhss } if term == *t1 => {
          vassert!(args.len() == lhss.len(),
            VerifyError::ProofTermArgMismatch(node, lhss.len(), args.len()));
          let td = &self.env.terms[term];
          if let TermKind::Def(Some(Expr { heap, head })) = &td.kind {
            let mut unify = Unifier::new(heap);
            for ((e, e2), o) in args.iter().zip(&**lhss).zip(&mut unify.tr) {
              let e = unref(self.orig_heap, e);
              vassert!(std::ptr::eq(e, unref(self.orig_heap, e2)),
                VerifyError::ExpectedConvSides(None, node, lhs, rhs));
              *o = Some(e)
            }
            let (sub_lhs, p) = &**res;
            let sub_lhs = unify.unify_expr(head, self.orig_heap, sub_lhs)
              .map_err(|_| VerifyError::UnifyFailure(None, node, sub_lhs))?;
            self.verify_conv_node(p, sub_lhs, rhs)?
          } else {
            return Err(VerifyError::UnfoldNonDef(node))
          }
        }
        _ => return Err(VerifyError::ExpectedConvSides(None, node, lhs, rhs))
      }
      _ => return Err(dbg!(VerifyError::ExpectedConv(None, node))),
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
      TermKind::Def(Some(Expr { heap, head })) => {
        vassert!(e_heap.len() <= heap.len(), VerifyError::MalformedHeap);
        for (i, e) in heap.iter().enumerate().take(e_heap.len()) {
          vassert!(matches!(*e, ExprNode::Ref(j) if j == i), VerifyError::MalformedHeap)
        }
        let mut dummies = Some((Default::default(), bvars));
        for e in &heap[e_heap.len()..] {
          e_heap.push(self.verify_expr_node(bound, &e_heap, &mut dummies, e)?)
        }
        let (s, _, deps) = self.verify_expr_node(bound, &e_heap, &mut dummies, head)?;
        vassert!(s == td.ret.0, VerifyError::ExprSortError(None, head, s, td.ret.0));
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
      e_heap.push(self.verify_expr_node(bound, &e_heap, &mut None, e)?)
    }
    for (_, hyp) in &*td.hyps {
      let (s, _, _) = self.verify_expr_node(bound, &e_heap, &mut None, hyp)?;
      vassert!(self.sorts[s].mods.contains(Modifiers::PROVABLE), VerifyError::HypNotInProvableSort);
    }
    let (s, _, _) = self.verify_expr_node(bound, &e_heap, &mut None, &td.ret)?;
    vassert!(self.sorts[s].mods.contains(Modifiers::PROVABLE), VerifyError::HypNotInProvableSort);
    match &td.kind {
      ThmKind::Axiom => Ok(()),
      ThmKind::Thm(None) => Err(VerifyError::UsesSorry),
      ThmKind::Thm(Some(Proof { heap, hyps, head })) => {
        e_heap.truncate(td.args.len());
        vassert!(e_heap.len() <= heap.len() && td.hyps.len() == hyps.len(),
          VerifyError::MalformedHeap);
        let mut ver = VerifyProof {
          env: self,
          bound,
          heap: vec![],
          orig_heap: heap,
          found_hyps: vec![None; td.hyps.len()].into(),
          dummies: Default::default(),
          bvars,
        };
        let mut hyp_unify = Unifier::new(&td.heap);
        for (i, (&(s, bv, d), e)) in e_heap.iter().zip(&**heap).enumerate() {
          vassert!(matches!(*e, ProofNode::Ref(j) if j == i), VerifyError::MalformedHeap);
          hyp_unify.tr[i] = Some(e);
          ver.heap.push(HeapEl::Expr(e, s, bv, d))
        }
        for e in &heap[e_heap.len()..] {
          let el = ver.verify_proof_node(e)?;
          ver.heap.push(el)
        }
        for (i, ((_, arg), hyp)) in td.hyps.iter().zip(&**hyps).enumerate() {
          ver.verify_proof_node(hyp)?;
          match unref(heap, hyp) {
            ProofNode::Hyp(j, p) if *j == i => {
              hyp_unify.unify_expr(arg, heap, p).map_err(|_| VerifyError::HypUnifyFailure(i))?;
            }
            _ => return Err(VerifyError::MalformedHyp(i)),
          }
        }
        let res = ver.verify_proof_node(head)?.as_proof(None)?;
        hyp_unify.unify_expr(&td.ret, heap, res).map_err(|_| VerifyError::ThmUnifyFailure(res))?;
        Ok(())
      }
    }
  }
}