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
use std::fmt::Display;
use std::sync::Arc;
use mm0_util::{ArcString, AtomId, FileSpan, Modifiers, SortId, Span, TermId, ThmId};
use mmcc::{Idx, Symbol};
use mmcc::proof::ElfProof;

use crate::elab::Result;
use crate::elab::verify::scope_ast_source;
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

  #[allow(clippy::wrong_self_convention)]
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

  #[allow(clippy::wrong_self_convention)]
  fn from_expr_nodes(&mut self, heap: &[ExprNode]) -> Vec<Self::Id> {
    let mut refs = Vec::with_capacity(heap.len());
    for node in heap {
      let id = self.from_expr_node(node, &refs);
      refs.push(id)
    }
    refs
  }

  #[allow(clippy::wrong_self_convention)]
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
    impl $id {
      const INVALID: Self = Self(u32::MAX);
    }
    impl Default for $id {
      fn default() -> Self { Self::INVALID }
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

  /// Apply a theorem `name` with no arguments or hypotheses, returning `(concl, |- concl)`
  fn thm0(&mut self, env: &Environment, name: ThmId) -> (ProofId, ProofId) {
    let thd = &env.thms[name];
    assert!(thd.args.is_empty() && thd.hyps.is_empty());
    let refs = self.from_expr_nodes(&thd.heap);
    let concl = self.from_expr_node(&thd.ret, &refs);
    (concl, self.thm(name, &[], concl))
  }

  /// Unfold a definition `name` with no arguments, returning the unfolded definition.
  /// (It does not construct a proof, but this expression can be used in an `Unfold` proof.)
  fn get_def0(&mut self, env: &Environment, name: TermId) -> ProofId {
    let td = &env.terms[name];
    assert!(td.args.is_empty());
    let e = if let TermKind::Def(Some(e)) = &td.kind { e } else { unreachable!("not a def") };
    self.from_expr(e)
  }

  fn refl_conv(&mut self, e: ProofId) -> ProofId {
    self.add(proof::ProofHash::Refl(e.into_usize()))
  }

  fn sym(&mut self, conv: ProofId) -> ProofId {
    self.add(proof::ProofHash::Sym(conv.into_usize()))
  }

  fn cong(&mut self, t: TermId, args: &[ProofId]) -> ProofId {
    self.add(proof::ProofHash::Cong(t, args.iter().map(|x| x.into_usize()).collect()))
  }

  /// `conv(tgt, conv, th)` is a proof of `|- tgt` if `th: src` and `conv: tgt = src`.
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
    atom: AtomId, vis: Modifiers, span: FileSpan, full: Span, doc: Option<Arc<str>>, thm: ProofId,
  ) -> Thm {
    let mut de = ExprDedup::new(self.pd, &[]);
    let concl = self.to_expr(&mut de, self.concl(thm));
    let (eheap, ret) = de.build0(concl);
    let (heap, head) = self.build0(thm);
    Thm {
      atom, span, full, doc, vis,
      args: Box::new([]), hyps: Box::new([]), heap: eheap, ret,
      kind: ThmKind::Thm(Some(Proof { heap, hyps: Box::new([]), head })),
    }
  }
}

impl ExprDedup<'_> {
  /// Constructs a definition with no parameters or dummy variables.
  #[allow(clippy::too_many_arguments)]
  fn build_def0(&mut self,
    atom: AtomId, vis: Modifiers, span: FileSpan, full: Span, doc: Option<Arc<str>>,
    e: ExprId, ret: SortId,
  ) -> Term {
    let (heap, head) = self.build0(e);
    Term {
      atom, span, vis, full, doc, args: Box::new([]), ret: (ret, 0),
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
  /// `foo_ok: okProc foo_gctx <foo_start> <foo_args> <foo_ret> <foo_clob> <foo_se>`:
  /// the correctness proof for a regular function
  ProcOkThm(Symbol),
  /// `_start_ok: okStart foo_gctx <foo_start>`: the correctness proof for the `_start` entry point
  StartOkThm,
}

impl Display for Name {
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
      Name::ProcOkThm(proc) => write!(f, "{}_ok", proc),
      Name::StartOkThm => write!(f, "_start_ok"),
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
  fn get_data(&self, env: &mut Environment, name: Name) -> (AtomId, Arc<str>) {
    (env.get_atom(format!("{}", self.mangle(name)).as_bytes()), self.as_doc(name).into())
  }

  fn mangle(&self, name: Name) -> impl Display + '_ {
    struct S<'a>(&'a str, Name);
    impl Display for S<'_> {
      fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "_mmc_{}_{}", self.0, self.1)
      }
    }
    S(self.module.as_str(), name)
  }

  fn as_doc(&self, name: Name) -> String {
    struct ProcName(Option<Symbol>);
    impl Display for ProcName {
      fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
          None => write!(f, "the start procedure"),
          Some(proc) => write!(f, "the procedure `{}`", proc)
        }
      }
    }
    match name {
      Name::ProcContent(proc) => format!("The machine code for {}.", ProcName(proc)),

      Name::ProcAsm(proc) => format!("The assembly listing for {}.", ProcName(proc)),

      Name::ProcAsmThm(proc) => format!("The incomplete assembly proof for {}. \
        This theorem has the form `assemble content start end (asmProc start asm)`, \
        and it asserts that `content` is a string of length exactly `end - start`, \
        and (assuming `end e. u64`) the string is the result of assembling `asm` at `start..end`. \
        The assumption `end e. u64` will later be discharged in `{}`.",
        ProcName(proc), self.mangle(Name::ProcAsmdThm(proc))),

      Name::Content => "The full machine code string for the executable.".to_owned(),

      Name::GCtx => "The global context, which contains data used by every procedure. \
        It has the form `mkGCtx content result`, where `content` is the assembled binary and \
        `result` is the exit proposition, \
        i.e. the property that must be true on any successful run.".to_owned(),

      Name::AsmdThm => format!("This theorem has the form `assembled gctx asm`, where:\n\n\
        * `gctx` is the global context (`{}` in this case)\n\
        * `asm` is the collection of all assembled procedures, connected by `++asm`.\n\n\
        It asserts that all procedures assemble to their final location.",
        self.mangle(Name::GCtx)),

      Name::AsmdThmLemma(_) => format!("A lemma in the derivation of the assembly theorems \
        for the procedures. It has the same form as {} but for a subset of the procedures.",
        Name::AsmdThm),

      Name::ProcAsmdThm(proc) => format!("The completed assembly proof for {}. \
        This theorem has the form `assembled gctx (asmProc start asm)`, where:\n\n\
        * `gctx` is the global context (`{}` in this case)\n\
        * `start` is the entry point of the function\n\
        * `asm` is the assembly for this procedure.",
        ProcName(proc), self.mangle(Name::GCtx)),

      Name::ProcOkThm(proc) => format!("The correctness theorem for {}. \
        This theorem has the form `okProc gctx start args ret clob se`, where:\n\
        \n\
        * `gctx` is the global context (`{}` in this case)\n\
        * `start` is the entry point of the function\n\
        * `args` is the specification of the function arguments\n\
        * `ret` is the specification of the function returns\n\
        * `clob` is the specification of the function clobbers\n\
        * `se` is `T.` if the function has side effects, else `F.`\n\
        \n\
        It asserts that (in the context of executing the binary specified by `gctx`), \
        if the program jumps to location `start`, and the arguments `args` are loaded \
        according to the specification, then the program will safely execute and return \
        output according to the specification `ret`, \
        possibly also clobbering registers in `clob`. \
        If `se` is false then the function does not perform any side-effects, which means \
        that it can even be executed in a 'ghost' context to derive logical propositions.",
        ProcName(Some(proc)), self.mangle(Name::GCtx)),

      Name::StartOkThm => format!("The correctness theorem for {}. \
        This theorem has the form `okStart gctx start`, where:\n\
        \n\
        * `gctx` is the global context (`{}` in this case)\n\
        * `start` is the entry point of the function\n\
        \n\
        It asserts that (in the context of executing the binary specified by `gctx`), \
        if the program jumps to location `start`, then the program will safely execute \
        and satisfy the global exit proposition (or fail).",
        ProcName(None), self.mangle(Name::GCtx)),
    }
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
  scope_ast_source(&elab.ast.source.clone(), || {
    let gctx = assembler::assemble_proof(elab, pd, &mut proc_asm, &mangler, proof, &fsp, sp)?;
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
      compiler::compile_proof(elab, pd, &proc_asm, &mangler, proof, &fsp, sp, gctx)
    })).unwrap_or_else(|e| Err(ElabError::new_e(sp, "panicked")))
  })?;
  // elab.report(ElabError::info(sp, format!("{:#?}", proof)));
  Ok(())
}
