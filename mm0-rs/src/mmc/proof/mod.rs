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

use std::collections::HashMap;
use std::marker::PhantomData;
use mm0_util::{ArcString, AtomId, FileSpan, Modifiers, SortId, Span, TermId, ThmId};
use mmcc::{Idx, Symbol, intern};
use mmcc::proof::{AssemblyBlocks, AssemblyItem, ElfProof, Inst, Proc};

use crate::elab::Result;
use crate::{DeclKey, ElabError, Elaborator, Environment, Expr, ExprNode, Proof, ProofNode, Remap, Remapper, Term, TermKind, Thm, ThmKind, Type};
use crate::elab::proof::{self, IDedup, ProofKind};
use self::norm_num::{HexCache, Num};

pub(crate) use predefs::Predefs;

trait Dedup<'a>: std::ops::Deref<Target = &'a Predefs> {
  type Node;
  type Hash;
  type Id: Idx;
  fn new(pd: &'a Predefs, args: &[(Option<AtomId>, Type)]) -> Self;
  fn add(&mut self, h: Self::Hash) -> Self::Id;
  fn reuse(&mut self, i: Self::Id) -> Self::Id;
  fn add_r(&mut self, h: Self::Hash) -> Self::Id {
    let i = self.add(h);
    self.reuse(i)
  }
  fn get(&self, i: Self::Id) -> &Self::Hash;
  fn build0(&self, i: Self::Id) -> (Box<[Self::Node]>, Self::Node);
  const APP: fn(t: TermId, args: Box<[usize]>) -> Self::Hash;
  fn ref_(&mut self, k: ProofKind, i: usize) -> Self::Id;
  fn dummy(&mut self, s: crate::AtomId, sort: SortId) -> Self::Id;
  fn app1(&mut self, t: TermId, args: &[Self::Id]) -> Self::Id {
    self.add(Self::APP(t, args.iter().map(|x| x.into_usize()).collect()))
  }
  fn app(&mut self, t: TermId, args: &[Self::Id]) -> Self::Id {
    self.add_r(Self::APP(t, args.iter().map(|x| x.into_usize()).collect()))
  }
  fn is_app_of(&self, i: Self::Id, t: TermId) -> Option<&[usize]>;
  #[inline] fn mk_eq(&mut self, a: Self::Id, b: Self::Id) -> Self::Id {
    app!(self, a = b)
  }
  #[inline] fn do_from_usize(&self, i: usize) -> Self::Id { Idx::from_usize(i) }
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
      cache: HashMap<ThmId, $id>,
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
        Self { pd, de: proof::Dedup::new(args), cache: Default::default() }
      }
      fn add(&mut self, h: proof::$hash) -> $id { $id::from_usize(self.de.add_direct(h)) }
      fn reuse(&mut self, i: $id) -> $id { $id::from_usize(self.de.reuse(i.into_usize())) }
      fn ref_(&mut self, k: ProofKind, i: usize) -> Self::Id {
        self.add(proof::$hash::Ref(k, i))
      }
      fn dummy(&mut self, s: crate::AtomId, sort: SortId) -> Self::Id {
        self.add(proof::$hash::Dummy(s, sort))
      }
      fn build0(&self, i: $id) -> (Box<[$node]>, $node) {
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

  fn thm_r(&mut self, t: ThmId, args: &[ProofId], res: ProofId) -> ProofId {
    self.add_r(proof::ProofHash::Thm(t,
      args.iter().map(|x| x.into_usize()).collect(), res.into_usize()))
  }

  fn thm_app(&mut self, th: ThmId, args: &[ProofId], t: TermId, es: &[ProofId]) -> ProofId {
    let res = self.app1(t, es);
    self.thm(th, args, res)
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

  fn cache(&mut self, t: ThmId, res: impl FnOnce(&mut Self) -> ProofId) -> ProofId {
    if let Some(&id) = self.cache.get(&t) { return id }
    let res = res(self);
    let th = self.thm(t, &[], res);
    *self.cache.entry(t).or_insert(th)
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
  fn build_thm0(&self,
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
  fn build_def0(&self,
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
  /// `foo_asmd: assemble foo_content <foo_start> <foo_end> (asmProc <foo_start> foo_asm)`:
  /// the assembly proof
  ProcAsmThm(Option<Symbol>),
  /// `content: string`: The full machine code string
  Content,
  /// `asmd: assembled content <asm>`: A theorem that asserts that `content` assembles to a list of
  /// procedures, referencing the `ProcAsm` definitions,
  /// for example `assembled content (foo_asm +asm bar_asm +asm my_const_asm)`
  AsmdThm,
}

impl std::fmt::Display for Name {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match *self {
      Name::ProcContent(None) => write!(f, "_start_content"),
      Name::ProcContent(Some(proc)) => write!(f, "{}_content", proc),
      Name::ProcAsm(None) => write!(f, "_start_asm"),
      Name::ProcAsm(Some(proc)) => write!(f, "{}_asm", proc),
      Name::ProcAsmThm(None) => write!(f, "_start_asmd"),
      Name::ProcAsmThm(Some(proc)) => write!(f, "{}_asmd", proc),
      Name::Content => write!(f, "content"),
      Name::AsmdThm => write!(f, "asmd"),
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
  assembler::assemble_proof(&mut elab.env, pd, &mut proc_asm, &mangler, proof, &fsp, sp)?;
  elab.report(ElabError::info(sp, format!("{:#?}", proof)));
  Ok(())
}
