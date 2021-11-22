//! The compiler lemmas we need from `compiler.mm1`
#![allow(unknown_lints)]

// Lints because of the macro heavy nature of the code
#![allow(clippy::many_single_char_names, clippy::similar_names,
  clippy::equatable_if_let, clippy::redundant_else,
  clippy::if_not_else, non_snake_case)]

// Lints because the code is not finished
#![allow(unused, clippy::unused_self, clippy::diverging_sub_expression, clippy::match_same_arms)]

#[macro_use] mod macros;
mod predefs;
mod norm_num;
mod assembler;
mod compiler;

use std::collections::HashMap;
use mm0_util::{ArcString, AtomId, FileSpan, Modifiers, SortId, Span, TermId, ThmId};
use mmcc::{Idx, Symbol};
use mmcc::proof::ElfProof;

use crate::elab::Result;
use crate::{ElabError, Elaborator, Environment, Expr, ExprNode,
  LispVal, Proof, ProofNode, Term, TermKind, Thm, ThmKind, Type};
use crate::elab::proof::{self, IDedup, ProofKind};

pub(crate) use predefs::Predefs;

trait Dedup<'a>: std::ops::Deref<Target = &'a Predefs> {
  type Node;
  type Hash;
  type Id: Idx;
  fn new(pd: &'a Predefs, args: &[(Option<AtomId>, Type)]) -> Self;
  fn add(&mut self, h: Self::Hash) -> Self::Id;
  fn get(&self, i: Self::Id) -> &Self::Hash;
  fn build0(&mut self, i: Self::Id) -> (Box<[Self::Node]>, Self::Node);
  const APP: fn(t: TermId, args: Box<[usize]>) -> Self::Hash;
  fn ref_(&mut self, k: ProofKind, i: usize) -> Self::Id;
  fn dummy(&mut self, s: crate::AtomId, sort: SortId) -> Self::Id;
  fn app(&mut self, t: TermId, args: &[Self::Id]) -> Self::Id {
    self.add(Self::APP(t, args.iter().map(|x| x.into_usize()).collect()))
  }
  fn is_app_of(&self, i: Self::Id, t: TermId) -> Option<&[usize]>;
  #[inline] fn mk_eq(&mut self, a: Self::Id, b: Self::Id) -> Self::Id {
    app!(self, a = b)
  }
  #[inline] fn do_from_usize(&self, i: usize) -> Self::Id { Idx::from_usize(i) }

  fn from_expr_node(&mut self, e: &ExprNode, refs: &[Self::Id]) -> Self::Id {
    match *e {
      ExprNode::Ref(i) if i < refs.len() => refs[i],
      ExprNode::Ref(i) => self.ref_(ProofKind::Expr, i),
      ExprNode::Dummy(s, sort) => self.dummy(s, sort),
      ExprNode::App(t, ref es) => {
        let args = es.iter().map(|e| self.from_expr_node(e, refs)).collect::<Vec<_>>();
        self.app(t, &args)
      }
    }
  }
  fn from_expr_nodes(&mut self, heap: &[ExprNode]) -> Vec<Self::Id> {
    let mut refs = Vec::with_capacity(heap.len());
    for node in heap {
      let id = self.from_expr_node(node, &refs);
      refs.push(id)
    }
    refs
  }
  fn from_expr(&mut self, e: &Expr) -> Self::Id {
    let refs = self.from_expr_nodes(&e.heap);
    self.from_expr_node(&e.head, &refs)
  }
  fn to_lisp(&self, env: &mut Environment, i: Self::Id) -> LispVal;
  fn pp(&self,
    elab: &mut Elaborator, i: Self::Id, f: &mut impl std::fmt::Write
  ) -> std::fmt::Result {
    let val = self.to_lisp(elab, i);
    elab.format_env().pretty(|p| p.expr(&val).render_fmt(80, f))
  }
}

macro_rules! make_dedup {
  ($($dedup:ident, $hash:ident, $node:ty, $id:ident, $app:ident;)*) => {$(
    #[derive(Clone, Copy, PartialEq, Eq)]
    struct $id(u32);
    impl Idx for $id {
      fn into_usize(self) -> usize { self.0 as usize }
      fn from_usize(n: usize) -> Self { Self(n as u32) }
    }
    struct $dedup<'a> {
      pd: &'a Predefs,
      de: proof::Dedup<proof::$hash>,
    }
    impl<'a> std::ops::Deref for $dedup<'a> {
      type Target = &'a Predefs;
      fn deref(&self) -> &Self::Target { &self.pd }
    }
    impl<'a> Dedup<'a> for $dedup<'a> {
      type Node = $node;
      type Hash = proof::$hash;
      type Id = $id;
      fn new(pd: &'a Predefs, args: &[(Option<AtomId>, Type)]) -> Self {
        Self { pd, de: proof::Dedup::new(args) }
      }
      fn add(&mut self, h: proof::$hash) -> $id { $id::from_usize(self.de.add_direct(h)) }
      fn ref_(&mut self, k: ProofKind, i: usize) -> Self::Id {
        self.add(proof::$hash::Ref(k, i))
      }
      fn dummy(&mut self, s: crate::AtomId, sort: SortId) -> Self::Id {
        self.add(proof::$hash::Dummy(s, sort))
      }
      fn build0(&mut self, i: $id) -> (Box<[$node]>, $node) {
        self.de.calc_use(0, [i.into_usize()]);
        let (mut ids, heap) = proof::build(&self.de);
        (heap, ids[i.into_usize()].take())
      }
      fn get(&self, i: Self::Id) -> &Self::Hash { &self.de[i.into_usize()] }
      const APP: fn(t: TermId, args: Box<[usize]>) -> Self::Hash = proof::$hash::$app;
      fn is_app_of(&self, i: Self::Id, t: TermId) -> Option<&[usize]> {
        if let proof::$hash::$app(t2, args) = self.get(i) {
          if *t2 == t { return Some(&args) }
        }
        None
      }
      fn to_lisp(&self, env: &mut Environment, i: Self::Id) -> LispVal {
        let mut builder = self.de.to_lisp_builder();
        builder.get(env, &self.de, i.into_usize())
      }
    }
  )*}
}
make_dedup! {
  ExprDedup, ExprHash, ExprNode, ExprId, App;
  ProofDedup, ProofHash, ProofNode, ProofId, Term;
}

impl ProofDedup<'_> {
  fn thm(&mut self, t: ThmId, args: &[ProofId], res: ProofId) -> ProofId {
    self.add(proof::ProofHash::Thm(t,
      args.iter().map(|x| x.into_usize()).collect(), res.into_usize()))
  }

  fn thm0(&mut self, env: &Environment, name: ThmId) -> (ProofId, ProofId) {
    let thd = &env.thms[name];
    assert!(thd.args.is_empty() && thd.hyps.is_empty());
    let refs = self.from_expr_nodes(&thd.heap);
    let concl = self.from_expr_node(&thd.ret, &refs);
    (concl, self.thm(name, &[], concl))
  }

  fn get_def0(&mut self, env: &Environment, name: TermId) -> ProofId {
    let td = &env.terms[name];
    assert!(td.args.is_empty());
    let e = if let TermKind::Def(Some(e)) = &td.kind { e } else { unreachable!("not a def") };
    self.from_expr(e)
  }

  fn refl_conv(&mut self, e: ProofId) -> ProofId {
    self.add(proof::ProofHash::Refl(e.into_usize()))
  }

  fn cong(&mut self, t: TermId, args: &[ProofId]) -> ProofId {
    self.add(proof::ProofHash::Cong(t, args.iter().map(|x| x.into_usize()).collect()))
  }

  fn conv(&mut self, tgt: ProofId, conv: ProofId, th: ProofId) -> ProofId {
    self.add(proof::ProofHash::Conv(tgt.into_usize(), conv.into_usize(), th.into_usize()))
  }

  fn unfold(&mut self, t: TermId, args: &[ProofId], conv: ProofId) -> ProofId {
    let sub_lhs = proof::ProofHash::conv_side(&mut self.de, conv.into_usize(), false);
    let lhs = self.app(t, args);
    self.add(proof::ProofHash::Unfold(t,
      args.iter().map(|x| x.into_usize()).collect(),
      lhs.into_usize(), sub_lhs.into_usize(), conv.into_usize()
    ))
  }

  fn to_expr<'a, D: Dedup<'a>>(&self, de: &mut D, e: ProofId) -> D::Id {
    match *self.get(e) {
      proof::ProofHash::Ref(ProofKind::Expr, i) if i < e.into_usize() =>
        // We assume there is no significant subterm sharing in expressions in theorem statements,
        // which is mostly true for theorem statements in the compiler.
        self.to_expr(de, ProofId::from_usize(i)),
      proof::ProofHash::Ref(ProofKind::Expr, i) =>
        de.ref_(ProofKind::Expr, i),
      proof::ProofHash::Dummy(s, sort) => de.dummy(s, sort),
      proof::ProofHash::Term(t, ref es) => {
        let args = es.iter().map(|&e| self.to_expr(de, Idx::from_usize(e))).collect::<Vec<_>>();
        de.app(t, &args)
      }
      _ => panic!("to_expr called on non-expr"),
    }
  }

  /// Get the conclusion of the provided proof term.
  fn concl(&self, e: ProofId) -> ProofId {
    match *self.get(e) {
      proof::ProofHash::Ref(ProofKind::Proof, i) => self.concl(ProofId::from_usize(i)),
      proof::ProofHash::Hyp(_, concl) |
      proof::ProofHash::Thm(_, _, concl) |
      proof::ProofHash::Conv(concl, _, _) => ProofId::from_usize(concl),
      _ => panic!("concl called on non-proof"),
    }
  }

  /// Constructs a theorem with no free variables or hypotheses.
  fn build_thm0(&mut self,
    atom: AtomId, vis: Modifiers, span: FileSpan, full: Span, thm: ProofId,
  ) -> Thm {
    let mut de = ExprDedup::new(self.pd, &[]);
    let concl = self.to_expr(&mut de, self.concl(thm));
    let (eheap, ret) = de.build0(concl);
    let (heap, head) = self.build0(thm);
    Thm {
      atom, span, full, doc: None, vis,
      args: Box::new([]), hyps: Box::new([]), heap: eheap, ret,
      kind: ThmKind::Thm(Some(Proof { heap, hyps: Box::new([]), head })),
    }
  }
}

impl ExprDedup<'_> {
  /// Constructs a definition with no parameters or dummy variables.
  fn build_def0(&mut self,
    atom: AtomId, vis: Modifiers, span: FileSpan, full: Span, e: ExprId, ret: SortId,
  ) -> Term {
    let (heap, head) = self.build0(e);
    Term {
      atom, span, vis, full, doc: None, args: Box::new([]), ret: (ret, 0),
      kind: TermKind::Def(Some(Expr { heap, head })),
    }
  }
}

#[derive(Copy, Clone, Debug)]
enum Name {
  /// `foo_content: string`: the machine code for a procedure
  ProcContent(Option<Symbol>),
  /// `foo_asm: set`: the assembly for a procedure
  ProcAsm(Option<Symbol>),
  /// `foo_asms: assemble foo_content <foo_start> <foo_end> (asmProc <foo_start> foo_asm)`:
  /// the incomplete assembly proof
  ProcAsmThm(Option<Symbol>),
  /// `foo_content: string`: The full machine code string
  Content,
  /// `foo_gctx: set`: The global context, which includes `content` and the exit proposition
  GCtx,
  /// `foo_asmd: assembled gctx <asm>`: A theorem that asserts that `content` assembles to a list of
  /// procedures, referencing the `ProcAsm` definitions,
  /// for example `assembled foo_gctx (foo_asm +asm bar_asm +asm my_const_asm)`
  AsmdThm,
  /// `asmd_lem{n}: assembled foo_gctx <asm>`: A conjunct in `AsmdThm` extracted as a lemma
  AsmdThmLemma(u32),
  /// `foo_asmd: assembled foo_gctx (asmProc <foo_start> foo_asm)`: the completed assembly proof
  ProcAsmdThm(Option<Symbol>),
}

impl std::fmt::Display for Name {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match *self {
      Name::ProcContent(None) => write!(f, "_start_content"),
      Name::ProcContent(Some(proc)) => write!(f, "{}_content", proc),
      Name::ProcAsm(None) => write!(f, "_start_asm"),
      Name::ProcAsm(Some(proc)) => write!(f, "{}_asm", proc),
      Name::ProcAsmThm(None) => write!(f, "_start_asms"),
      Name::ProcAsmThm(Some(proc)) => write!(f, "{}_asms", proc),
      Name::ProcAsmdThm(None) => write!(f, "_start_asmd"),
      Name::ProcAsmdThm(Some(proc)) => write!(f, "{}_asmd", proc),
      Name::Content => write!(f, "content"),
      Name::GCtx => write!(f, "gctx"),
      Name::AsmdThm => write!(f, "asmd"),
      Name::AsmdThmLemma(n) => write!(f, "asmd_lem{}", n),
    }
  }
}

struct Mangler {
  module: ArcString,
}

impl Mangler {
  fn mangle(&self, env: &mut Environment, name: Name) -> AtomId {
    env.get_atom(format!("_mmc_{}_{}", self.module.as_str(), name).as_bytes())
  }
}

pub(crate) fn render_proof(
  pd: &Predefs, elab: &mut Elaborator, sp: Span,
  name: AtomId, proof: &ElfProof<'_>
) -> Result<()> {
  let mangler = Mangler {
    module: elab.data[name].name.clone(),
  };
  let fsp = elab.fspan(sp);
  let mut proc_asm = HashMap::new();
  let gctx = assembler::assemble_proof(elab, pd, &mut proc_asm, &mangler, proof, &fsp, sp)?;
  std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
    compiler::compile_proof(elab, pd, &proc_asm, &mangler, proof, &fsp, sp, gctx)
  })).unwrap_or_else(|e| Err(ElabError::new_e(sp, "panicked")))?;
  // elab.report(ElabError::info(sp, format!("{:#?}", proof)));
  Ok(())
}
