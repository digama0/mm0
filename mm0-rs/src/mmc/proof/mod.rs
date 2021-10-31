//! The compiler lemmas we need from `compiler.mm1`
#![allow(unknown_lints)]

// Lints because of the macro heavy nature of the code
#![allow(clippy::many_single_char_names, clippy::similar_names,
  clippy::equatable_if_let, clippy::redundant_else, non_snake_case)]

// Lints because the code is not finished
#![allow(unused, clippy::unused_self, clippy::diverging_sub_expression, clippy::match_same_arms)]

#[macro_use] mod macros;
mod predefs;
mod norm_num;
mod assembler;

use std::collections::HashMap;
use std::marker::PhantomData;
use mm0_util::{AtomId, FileSpan, Modifiers, Span, TermId, ThmId};
use mmcc::Idx;
use mmcc::proof::{AssemblyBlocks, AssemblyItem, ElfProof, Inst, Proc};

use crate::elab::Result;
use crate::mmc::proof::assembler::{BuildAssemblyProc, assemble_proc};
use crate::{DeclKey, ElabError, Elaborator, Environment, ExprNode, Proof, ProofNode,
  Remap, Remapper, Thm, ThmKind, Type};
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
    struct $id(usize);
    impl Idx for $id {
      fn into_usize(self) -> usize { self.0 }
      fn from_usize(n: usize) -> Self { Self(n) }
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
      fn add(&mut self, h: proof::$hash) -> $id { $id(self.de.add_direct(h)) }
      fn reuse(&mut self, i: $id) -> $id { $id(self.de.reuse(i.0)) }
      fn build0(&self, i: $id) -> (Box<[$node]>, $node) {
        let (mut ids, heap) = proof::build(&self.de);
        (heap, ids[i.0].take())
      }
      fn get(&self, i: Self::Id) -> &Self::Hash { &self.de[i.0] }
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
    self.add(proof::ProofHash::Thm(t, args.iter().map(|x| x.0).collect(), res.0))
  }
  fn thm_r(&mut self, t: ThmId, args: &[ProofId], res: ProofId) -> ProofId {
    self.add_r(proof::ProofHash::Thm(t, args.iter().map(|x| x.0).collect(), res.0))
  }
  fn thm_app(&mut self, th: ThmId, args: &[ProofId], t: TermId, es: &[ProofId]) -> ProofId {
    let res = self.app1(t, es);
    self.thm(th, args, res)
  }
  fn to_expr(&self, de: &mut ExprDedup<'_>, e: ProofId) -> ExprId {
    let e = match *self.get(e) {
      proof::ProofHash::Ref(ProofKind::Expr, i) if i < e.0 =>
        // We assume there is no significant subterm sharing in expressions in theorem statements,
        // which is mostly true for theorem statements in the compiler.
        return self.to_expr(de, ProofId(i)),
      proof::ProofHash::Ref(ProofKind::Expr, i) =>
        proof::ExprHash::Ref(ProofKind::Expr, i),
      proof::ProofHash::Dummy(s, sort) => proof::ExprHash::Dummy(s, sort),
      proof::ProofHash::Term(t, ref es) =>
        proof::ExprHash::App(t, es.iter().map(|&e| self.to_expr(de, ProofId(e)).0).collect()),
      _ => panic!("to_expr called on non-expr"),
    };
    de.add(e)
  }

  /// Get the conclusion of the provided proof term.
  fn concl(&self, e: ProofId) -> ProofId {
    match *self.get(e) {
      proof::ProofHash::Ref(ProofKind::Proof, i) => self.concl(ProofId(i)),
      proof::ProofHash::Hyp(_, concl) |
      proof::ProofHash::Thm(_, _, concl) |
      proof::ProofHash::Conv(concl, _, _) => ProofId(concl),
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
      atom, span, full, doc: None,
      vis,
      args: Box::new([]),
      hyps: Box::new([]),
      heap: eheap, ret,
      kind: ThmKind::Thm(Some(Proof { heap, hyps: Box::new([]), head })),
    }
  }
}

pub(crate) fn render_proof(
  pd: &Predefs, elab: &mut Elaborator, sp: Span,
  name: AtomId, proof: &ElfProof<'_>
) -> Result<()> {
  let name_str = elab.data[name].name.clone();
  let name_str = name_str.as_str();
  macro_rules! atom {($lit:literal $(, $e:expr)*) => {
    elab.get_atom(format!(concat!("{}_", $lit), name_str $(, $e)*).as_bytes())
  }}

  let mut proc_asm = HashMap::new();

  for item in proof.assembly() {
    match item {
      AssemblyItem::Proc(proc) => {
        let name = proc.name();
        let name = *proc_asm.entry(name).or_insert_with(|| match name {
          Some(name) => atom!("{}_asm", name),
          None => atom!("_start_asm"),
        });
        let asm_thm = elab.env
          .add_thm(assemble_proc(pd, name, &proc, elab.fspan(sp), sp))
          .map_err(|e| e.into_elab_error(sp))?;
        todo!()
      }
      AssemblyItem::Const(_) |
      AssemblyItem::Padding(_, _) => todo!(),
    }
  }
  elab.report(ElabError::info(sp, format!("{:#?}", proof)));
  Ok(())
}
