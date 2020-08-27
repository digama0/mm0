//! Debug formatting for mm0-rs items. Follows the API set out by the `print` and `pretty`
//! modules. 
use std::collections::HashMap;
use std::cell::RefCell;
use std::{fmt::{self}};
use shoebill::{ Printer, Doclike, DocPtr };
use shoebill::ron::{ RonStruct, RonSequence, RonTuple, RonOption, RonResult };
use super::{LispVal, LispKind, print::FormatEnv,
  super::{
    environment::{DeclKey, NotaInfo, AtomData, AtomID, SortID, TermID, ThmID, Term, Thm, Type, Sort, Expr }, }};
use crate::util::{ FileSpan, FileRef, Span };

/// Debug counterpart to the `Print` struct`.
pub struct DebugPrint<'a, D : ?Sized> {
  fe : FormatEnv<'a>,
  e : &'a D
}

/// DebugPrint items can be put in formatters using `{:?}`
impl<'a, D: EnvDebug + ?Sized> fmt::Debug for DebugPrint<'a, D> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.e.dbg(self.fe, f) }
}

impl<'a> FormatEnv<'a> {
  /// The debug counterpart to `FormatEnv::pretty()`
  pub fn debug<T>(self, f : impl for<'b> FnOnce(FormatEnv<'b>, &'b mut Printer<'b>) -> T) -> T {
    f(self, &mut Printer::new())
  }

  /// The debug counterpart to `FormatEnv::to()`
  pub fn to_debug<D : ?Sized>(self, e : &'a D) -> DebugPrint<'a, D> {
    DebugPrint {fe : self, e}
  }
}

impl EnvDebug for NotaInfo {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
      let mut ron = RonStruct::new();
      ron.add_field("span", self.span.dbg_aux(fe, p));
      ron.add_field("term", self.term.dbg_aux(fe, p));
      ron.add_field("nargs", self.nargs.dbg_aux(fe, p));
      ron.add_field("rassoc", self.rassoc.dbg_aux(fe, p));
      ron.add_field("lits", self.lits.dbg_aux(fe, p));
      ron.to_doc(p)
  }
}


impl EnvDebug for DeclKey {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
      let mut ron = RonTuple::new();
      ron.add_name("DeclKey");
      match self {
          DeclKey::Term(term_id) => {
              ron.add_name("Term");
              ron.add_field(term_id.dbg_aux(fe, p));
          },
          DeclKey::Thm(thm_id) => {
              ron.add_name("Thm");
              ron.add_field(thm_id.dbg_aux(fe, p));
          }
      }
      ron.to_doc(p)
  }
}

impl EnvDebug for SortID {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    match self {
      SortID(n) => {
        let sort = &fe.sorts[*self];
        let mut ron = RonStruct::new();
        ron.add_name("Sort");
        ron.add_field("sort_id", n.to_string());
        // Calling atom_id.dbg_aux(..) recursively here will loop and blow the stack.
        match sort.atom {
          AtomID(id) => ron.add_field("atom_id", id.to_string())
        }
        ron.add_field("name", sort.name.to_string());
        ron.add_field("span", sort.span.dbg_aux(fe, p));
        ron.add_field("full", sort.full.dbg_aux(fe, p));
        ron.add_field("mods", sort.mods.to_string());
        ron.to_doc(p)
      }
    }
  }
}

impl EnvDebug for Sort {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
      let mut ron = RonStruct::new();
      ron.add_name("Sort");
      match self.atom {
        AtomID(id) => ron.add_field("atom_id", id.to_string())
      }
      ron.add_field("name", self.name.to_string());
      ron.add_field("span", self.span.dbg_aux(fe, p));
      ron.add_field("full", self.full.dbg_aux(fe, p));
      ron.add_field("mods", self.mods.to_string());
      ron.to_doc(p)
  }
}

impl EnvDebug for Span {
  fn dbg_aux<'a>(
    &self, 
    _ : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    format!("{:#?}", self).alloc(p)
  }
}

impl EnvDebug for FileSpan {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonStruct::new();
    ron.add_name("FileSpan");
    ron.add_field("file", self.file.dbg_aux(fe, p));
    ron.add_field("span", self.span.dbg_aux(fe, p));
    ron.to_doc(p)
  }
}

impl EnvDebug for FileRef {
  fn dbg_aux<'a>(
    &self, 
    _ : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonStruct::new();
    ron.add_name("FileRef");
    ron.add_field("url", self.url().to_string());
    ron.add_field("path", self.path().display().to_string());
    ron.add_field("rel", self.rel().to_string());
    ron.to_doc(p)
  }
}

impl EnvDebug for Type {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonTuple::new();
    ron.add_name("Type");
    match self {
      Type::Bound(sort_id) => {
        ron.add_name("Bound");
        ron.add_field(sort_id.dbg_aux(fe, p));

      },
      Type::Reg(sort_id, n) => {
        ron.add_name("Reg");
        ron.add_field(sort_id.dbg_aux(fe, p));
        ron.add_field(n.to_string());
      }
    }
    ron.to_doc(p)
  }
}

impl EnvDebug for Expr {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonStruct::new();
    ron.add_name("Expr");
    ron.add_field("heap", self.heap.dbg_aux(fe, p));
    ron.add_field("head", self.head.dbg_aux(fe, p));
    ron.to_doc(p)
  }
}

impl EnvDebug for TermID {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let term = &fe.terms[*self];
    let mut ron = RonStruct::new();
    ron.add_field("atom", term.atom.dbg_aux(fe, p));
    ron.add_field("span", term.span.dbg_aux(fe, p));
    ron.add_field("vis", term.vis.to_string());
    ron.add_field("full", term.full.dbg_aux(fe, p));
    ron.add_field("args", term.args.dbg_aux(fe, p));
    ron.add_field("ret", term.ret.dbg_aux(fe, p));
    ron.add_field("val", term.val.dbg_aux(fe, p));
    ron.to_doc(p)
  }
}

impl EnvDebug for Term {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonStruct::new();
    match self.atom {
      AtomID(id) => ron.add_field("atom_id", id.to_string())
    }
    ron.add_field("span", self.span.dbg_aux(fe, p));
    ron.add_field("vis", self.vis.to_string());
    ron.add_field("full", self.full.dbg_aux(fe, p));
    ron.add_field("args", self.args.dbg_aux(fe, p));
    ron.add_field("ret", self.ret.dbg_aux(fe, p));
    ron.add_field("val", self.val.dbg_aux(fe, p));
    ron.to_doc(p)
  }
}

impl EnvDebug for crate::elab::environment::Proof {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonStruct::new();
    ron.add_name("Proof");
    ron.add_field("heap", self.heap.dbg_aux(fe, p));
    ron.add_field("hyps", self.hyps.dbg_aux(fe, p));
    ron.add_field("head", self.head.dbg_aux(fe, p));
    ron.to_doc(p)
  }
}

impl EnvDebug for ThmID {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let thm = &fe.thms[*self];
    let mut ron = RonStruct::new();
    ron.add_name("Thm");
    match thm.atom {
      AtomID(id) => ron.add_field("atom_id", id.to_string())
    }
    ron.add_field("span", thm.span.dbg_aux(fe, p));
    ron.add_field("vis", thm.vis.to_string());
    ron.add_field("full", thm.full.dbg_aux(fe, p));
    ron.add_field("args", thm.args.dbg_aux(fe, p));
    ron.add_field("heap", thm.heap.dbg_aux(fe, p));
    ron.add_field("hyps", thm.hyps.dbg_aux(fe, p));
    ron.add_field("ret", thm.ret.dbg_aux(fe, p));
    ron.add_field("proof", thm.proof.dbg_aux(fe, p));
    ron.to_doc(p)
  }
}

impl EnvDebug for Thm {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonStruct::new();
    ron.add_name("Thm");
    match self.atom {
      AtomID(id) => ron.add_field("atom_id", id.to_string())
    }
    ron.add_field("span", self.span.dbg_aux(fe, p));
    ron.add_field("vis", self.vis.to_string());
    ron.add_field("full", self.full.dbg_aux(fe, p));
    ron.add_field("args", self.args.dbg_aux(fe, p));
    ron.add_field("heap", self.heap.dbg_aux(fe, p));
    ron.add_field("hyps", self.hyps.dbg_aux(fe, p));
    ron.add_field("ret", self.ret.dbg_aux(fe, p));
    ron.add_field("proof", self.proof.dbg_aux(fe, p));
    ron.to_doc(p)
  }
}

impl EnvDebug for crate::elab::environment::ProofNode {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    match self {
      crate::elab::environment::ProofNode::Ref(n) => {
        let mut ron = RonTuple::new();
        ron.add_name("ProofNode::Ref");
        ron.add_field(n.to_string());
        ron.to_doc(p)
      }
      crate::elab::environment::ProofNode::Dummy(atom_id, sort_id) => {
        let mut ron = RonTuple::new();
        ron.add_name("ProofNode::Dummy");
        ron.add_field(atom_id.dbg_aux(fe, p));
        ron.add_field(sort_id.dbg_aux(fe, p));
        ron.to_doc(p)
      }
      crate::elab::environment::ProofNode::Term { term, args } => {
        let mut ron = RonStruct::new();
        ron.add_name("ProofNode::Dummy");
        ron.add_field("term", term.dbg_aux(fe, p));
        ron.add_field("args", args.as_ref().dbg_aux(fe, p));
        ron.to_doc(p)
      }
      crate::elab::environment::ProofNode::Hyp(n, pnode) => {
        let mut ron = RonTuple::new();
        ron.add_name("ProofNode::Hyp");
        ron.add_field(n.to_string());
        ron.add_field(pnode.dbg_aux(fe, p));
        ron.to_doc(p)
      }
      crate::elab::environment::ProofNode::Thm { thm, args, res } => {
        let mut ron = RonStruct::new();
        ron.add_name("ProofNode::Thm");
        ron.add_field("thm", thm.dbg_aux(fe, p));
        ron.add_field("args", args.as_ref().dbg_aux(fe, p));
        ron.add_field("res", res.as_ref().dbg_aux(fe, p));
        ron.to_doc(p)
      }
      crate::elab::environment::ProofNode::Conv(triple) => {
        let mut ron = RonTuple::new();
        ron.add_name("ProofNode::Conv");
        ron.add_field(triple.as_ref().dbg_aux(fe, p));
        ron.to_doc(p)
      }
      crate::elab::environment::ProofNode::Refl(pnode) => {
        let mut ron = RonTuple::new();
        ron.add_name("ProofNode::Refl");
        ron.add_field(pnode.dbg_aux(fe, p));
        ron.to_doc(p)
      }
      crate::elab::environment::ProofNode::Sym(pnode) => {
        let mut ron = RonTuple::new();
        ron.add_name("ProofNode::Sym");
        ron.add_field(pnode.dbg_aux(fe, p));
        ron.to_doc(p)
      }
      crate::elab::environment::ProofNode::Cong { term, args } => {
        let mut ron = RonStruct::new();
        ron.add_name("ProofNode::Cong");
        ron.add_field("term", term.dbg_aux(fe, p));
        ron.add_field("args", args.as_ref().dbg_aux(fe, p));
        ron.to_doc(p)
      }

      crate::elab::environment::ProofNode::Unfold { term, args, res } => {
        let mut ron = RonStruct::new();
        ron.add_name("ProofNode::Unfold");
        ron.add_field("term", term.dbg_aux(fe, p));
        ron.add_field("args", args.as_ref().dbg_aux(fe, p));
        ron.add_field("res", res.as_ref().dbg_aux(fe, p));
        ron.to_doc(p)
      }
    }
  }
}

impl EnvDebug for crate::elab::environment::ExprNode {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonTuple::new();
    ron.add_name("ExprNode");
    match self {
      crate::elab::environment::ExprNode::Ref(n) => {
        ron.add_name("Ref");
        ron.add_field(n.to_string());
      }
      crate::elab::environment::ExprNode::Dummy(atom_id, sort_id) => {
        ron.add_name("Dummy");
        ron.add_field(atom_id.dbg_aux(fe, p));
        ron.add_field(sort_id.dbg_aux(fe, p));
      }
      crate::elab::environment::ExprNode::App(term_id, nodes) => {
        ron.add_name("App");
        ron.add_field(term_id.dbg_aux(fe, p));
        ron.add_field(nodes.dbg_aux(fe, p));
      }
    }
    ron.to_doc(p)
  }
}

impl EnvDebug for AtomData {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
      let mut ron = RonStruct::new();
      ron.add_name("AtomData");
      ron.add_field("name", self.name.to_string());
      ron.add_field("sort", self.sort.dbg_aux(fe, p));
      ron.add_field("lisp", self.lisp.dbg_aux(fe, p));
      ron.add_field("graveyard", self.graveyard.as_deref().dbg_aux(fe, p));
      ron.to_doc(p)
  }


}

impl EnvDebug for AtomID {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    match self {
      AtomID(n) => {
        let atom_data = &fe.data[*self];
        let mut ron = RonStruct::new();
        ron.add_name("AtomData");
        ron.add_field("atom_id", n.to_string());
        ron.add_field("name", atom_data.name.to_string());
        ron.add_field("sort", atom_data.sort.dbg_aux(fe, p));
        ron.add_field("lisp", atom_data.lisp.dbg_aux(fe, p));
        ron.add_field("graveyard", atom_data.graveyard.as_deref().dbg_aux(fe, p));
        ron.to_doc(p)
      }
    }
  }
}

impl EnvDebug for crate::mmc::parser::Invariant {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonStruct::new();
    ron.add_name("Invariant");
    ron.add_field("name", self.name.dbg_aux(fe, p));
    ron.add_field("ghost", self.ghost.dbg_aux(fe, p));
    ron.add_field("ty", self.ty.dbg_aux(fe, p));
    ron.add_field("val", self.val.dbg_aux(fe, p));
    ron.to_doc(p)
  }
}

impl EnvDebug for crate::mmc::parser::Pattern {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonTuple::new();
    ron.add_name("Pattern");
    match self {
      crate::mmc::parser::Pattern::VarOrConst(atom_idx) => {
        ron.add_name("VarOrConst");
        ron.add_field(atom_idx.dbg_aux(fe, p));
      },
      crate::mmc::parser::Pattern::Number(bigint) => {
        ron.add_name("Number");
        ron.add_field(bigint.to_string());
      },
      crate::mmc::parser::Pattern::Hyped(atom_id, boxpat) => {
        ron.add_name("Hyped");
        ron.add_field(atom_id.dbg_aux(fe, p));
        ron.add_field(boxpat.dbg_aux(fe, p));
      },
      crate::mmc::parser::Pattern::With(boxtup) => {
        ron.add_name("With");
        ron.add_field(boxtup.dbg_aux(fe, p));
      },
      crate::mmc::parser::Pattern::Or(boxpat) => {
        ron.add_name("Or");
        ron.add_field(boxpat.dbg_aux(fe, p));
      },
    }
    ron.to_doc(p)
  }
}

impl EnvDebug for crate::mmc::parser::TuplePattern {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonTuple::new();
    ron.add_name("TuplePattern");
    match self {
      crate::mmc::parser::TuplePattern::Name(atom_id, op_filespan) => {
        ron.add_name("Name");
        ron.add_field(atom_id.dbg_aux(fe, p));
        ron.add_field(op_filespan.dbg_aux(fe, p));
      }
      crate::mmc::parser::TuplePattern::Typed(boxtp, lispval) => {
        ron.add_name("Typed");
        ron.add_field(boxtp.dbg_aux(fe, p));
        ron.add_field(lispval.dbg_aux(fe, p));
      }
      crate::mmc::parser::TuplePattern::Tuple(boxtp) => {
        ron.add_name("Tuple");
        ron.add_field(boxtp.dbg_aux(fe, p));
      }
    }
    ron.to_doc(p)
  }
}

impl EnvDebug for crate::mmc::parser::Expr {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    match self {
      crate::mmc::parser::Expr::Nil => {
        let mut ron = RonTuple::new();
        ron.add_name("Expr::Nil");
        ron.to_doc(p)
      },
      crate::mmc::parser::Expr::Var(atom_id)=> {
        let mut ron = RonTuple::new();
        ron.add_name("Expr::Var");
        ron.add_field(atom_id.dbg_aux(fe, p));
        ron.to_doc(p)
      },
      crate::mmc::parser::Expr::Number(bigint)=> {
        let mut ron = RonTuple::new();
        ron.add_name("Expr::Number");
        ron.add_field(bigint.to_string());
        ron.to_doc(p)
      },
      crate::mmc::parser::Expr::Let { ghost, lhs, rhs } => {
        let mut ron = RonStruct::new();
        ron.add_name("Expr::Let");
        ron.add_field("ghost", ghost.dbg_aux(fe, p));
        ron.add_field("lhs", lhs.dbg_aux(fe, p));
        ron.add_field("rhs", rhs.dbg_aux(fe, p));
        ron.to_doc(p)
      },
      crate::mmc::parser::Expr::Call { f, args, variant } => {
        let mut ron = RonStruct::new();
        ron.add_name("Expr::Call");
        ron.add_field("f", f.dbg_aux(fe, p));
        ron.add_field("args", args.dbg_aux(fe, p));
        ron.add_field("variant", variant.dbg_aux(fe, p));
        ron.to_doc(p)
      },
      crate::mmc::parser::Expr::Entail(lispval, boxexpr) => {
        let mut ron = RonTuple::new();
        ron.add_name("Expr::Entail");
        ron.add_field(lispval.dbg_aux(fe, p));
        ron.add_field(boxexpr.dbg_aux(fe, p));
        ron.to_doc(p)
      },
      crate::mmc::parser::Expr::Block(block) => {
        let mut ron = RonTuple::new();
        ron.add_name("Expr::Block");
        ron.add_field(block.dbg_aux(fe, p));
        ron.to_doc(p)
      },
      crate::mmc::parser::Expr::Label { name, args, variant, body } => {
        let mut ron = RonStruct::new();
        ron.add_name("Expr::Label");
        ron.add_field("name", name.dbg_aux(fe, p));
        ron.add_field("args", args.dbg_aux(fe, p));
        ron.add_field("variant", variant.dbg_aux(fe, p));
        ron.add_field("body", body.dbg_aux(fe, p));
        ron.to_doc(p)
      },
      crate::mmc::parser::Expr::If(boxtriple) => {
        let mut ron = RonTuple::new();
        ron.add_name("Expr::If");
        ron.add_field(boxtriple.as_ref().dbg_aux(fe, p));
        ron.to_doc(p)
      },
      crate::mmc::parser::Expr::Switch(boxexpr, boxarr) => {
        let mut ron = RonTuple::new();
        ron.add_name("Expr::Switch");
        ron.add_field(boxexpr.as_ref().dbg_aux(fe, p));
        ron.add_field(boxarr.dbg_aux(fe, p));
        ron.to_doc(p)
      },
      crate::mmc::parser::Expr::While { hyp, cond, var, invar, body } => {
        let mut ron = RonStruct::new();
        ron.add_name("Expr::While");
        ron.add_field("hyp", hyp.dbg_aux(fe, p));
        ron.add_field("cond", cond.dbg_aux(fe, p));
        ron.add_field("var", var.dbg_aux(fe, p));
        ron.add_field("invar", invar.dbg_aux(fe, p));
        ron.add_field("body", body.dbg_aux(fe, p));
        ron.to_doc(p)
      },
      crate::mmc::parser::Expr::Hole(fspan) => {
        let mut ron = RonTuple::new();
        ron.add_name("Expr::Hole");
        ron.add_field(fspan.dbg_aux(fe, p));
        ron.to_doc(p)
      },
    }
  }
}

impl EnvDebug for crate::mmc::parser::Block {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonStruct::new();
    ron.add_name("Block");
    ron.add_field("muts", self.muts.as_ref().dbg_aux(fe, p));
    ron.add_field("stmts", self.stmts.as_ref().dbg_aux(fe, p));
    ron.to_doc(p)
  }
}

impl EnvDebug for crate::mmc::parser::VariantType {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonTuple::new();
    ron.add_name("VariantType");
    match self {
      crate::mmc::parser::VariantType::Down => { ron.add_name("Down"); },
      crate::mmc::parser::VariantType::UpLt(lisp_val) => {
        ron.add_name("UpLt");
        ron.add_field(lisp_val.dbg_aux(fe, p));
      }
      crate::mmc::parser::VariantType::UpLe(lisp_val) => {
        ron.add_name("UpLe");
        ron.add_field(lisp_val.dbg_aux(fe, p));
      }
    }
    ron.to_doc(p)
  }
}

impl EnvDebug for &crate::elab::frozen::FrozenLispVal {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonTuple::new();
    ron.add_name("FrozenLispVal");
    match self {
      crate::elab::frozen::FrozenLispVal(lispval) => { 
        ron.add_field(lispval.dbg_aux(fe, p));
        ron.to_doc(p)
      }
    }
  }
}

impl EnvDebug for &crate::elab::frozen::FrozenLispRef {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonTuple::new();
    ron.add_name("FrozenLispRef");
    match self {
      crate::elab::frozen::FrozenLispRef(lispref) => { 
        ron.add_field(lispref.dbg_aux(fe, p));
        ron.to_doc(p)
      }
    }
  }
}

impl EnvDebug for &crate::elab::frozen::FrozenProc {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonTuple::new();
    ron.add_name("FrozenProc");
    match self {
      crate::elab::frozen::FrozenProc(proc_) => { 
        ron.add_field(proc_.dbg_aux(fe, p));
        ron.to_doc(p)
      }
    }
  }
}

impl EnvDebug for LispVal {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    match self {
      LispVal(rc_lisp_kind) => {
        let mut ron = RonTuple::new();
        ron.add_name("LispVal");
        ron.add_field(rc_lisp_kind.dbg_aux(fe, p));
        ron.to_doc(p)
      }
    }
  }
}

impl EnvDebug for crate::elab::lisp::LispRef {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonTuple::new();
    ron.add_name("LispRef");
    match self {
      crate::elab::lisp::LispRef(refcell_lisp_val) => { 
        ron.add_field(refcell_lisp_val.dbg_aux(fe, p)); 
      }
    }
    ron.to_doc(p)
  }
}

impl EnvDebug for crate::elab::lisp::InferTarget {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonTuple::new();
    ron.add_name("InferTarget");
    match self {
      crate::elab::lisp::InferTarget::Unknown => { ron.add_name("Unknown"); },
      crate::elab::lisp::InferTarget::Provable => { ron.add_name("Provable"); },
      crate::elab::lisp::InferTarget::Bound(atom_id) => {
        ron.add_name("Bound");
        ron.add_field(atom_id.dbg_aux(fe, p));
      },
      crate::elab::lisp::InferTarget::Reg(atom_id) => {
        ron.add_name("Reg");
        ron.add_field(atom_id.dbg_aux(fe, p));
      }
    }
    ron.to_doc(p)
  }
}

impl EnvDebug for crate::elab::lisp::ProcPos {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonTuple::new();
    ron.add_name("ProcPos");
    match self {
      crate::elab::lisp::ProcPos::Named(fspan, span, atom_id) => {
        ron.add_name("Named");
        ron.add_field(fspan.dbg_aux(fe, p));
        ron.add_field(span.dbg_aux(fe, p));
        ron.add_field(atom_id.dbg_aux(fe, p));
      },
      crate::elab::lisp::ProcPos::Unnamed(fspan) => {
        ron.add_name("Unnamed");
        ron.add_field(fspan.dbg_aux(fe, p));
      }
    }
    ron.to_doc(p)
  }
}

impl EnvDebug for LispKind {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonTuple::new();
    match self {
      LispKind::Atom(atom_id) => { 
        ron.add_name("LispKind::Atom");
        ron.add_field(atom_id.dbg_aux(fe, p)); 
      },
      LispKind::List(lisp_vals) => { 
        ron.add_name("LispKind::List");
        ron.add_field(lisp_vals.dbg_aux(fe, p)); 
      },
      LispKind::DottedList(lisp_vals, lisp_val) => { 
        ron.add_name("LispKind::DottedList");
        ron.add_field(lisp_vals.dbg_aux(fe, p)); 
        ron.add_field(lisp_val.dbg_aux(fe, p));
      },
      LispKind::Annot(annot, lisp_val) => {
        ron.add_name("LispKind::Annot");
        ron.add_field(annot.dbg_aux(fe, p));
        ron.add_field(lisp_val.dbg_aux(fe, p));
      },
      LispKind::Number(bigint) => {
        ron.add_name("LispKind::Number");
        ron.add_field(bigint.to_string());
      },
      LispKind::String(arcstring) => {
        ron.add_name("LispKind::String");
        ron.add_field(arcstring.to_string());
      },
      LispKind::Bool(b) => {
        ron.add_name("LispKind::Bool");
        ron.add_field(b.to_string());
      },
      LispKind::Syntax(syntax) => {
        ron.add_name("LispKind::Syntax");
        ron.add_field(syntax.dbg_aux(fe, p));
      },
      LispKind::Undef => {
        ron.add_name("LispKind::Undef");
      },
      LispKind::Proc(proc_) => {
        ron.add_name("LispKing::Proc");
        ron.add_field(proc_.dbg_aux(fe, p));
      }
      LispKind::AtomMap(id_val_map) => {
        ron.add_name("LispKind::AtomMap");
        ron.add_field(id_val_map.dbg_aux(fe, p));
      },
      LispKind::Ref(lisp_ref) => {
        ron.add_name("LispKind::LispRef");
        ron.add_field(lisp_ref.dbg_aux(fe, p));
      },
      LispKind::MVar(usz, infer_target) => {
        ron.add_name("LispKind::MVar");
        ron.add_field(usz.to_string());
        ron.add_field(infer_target.dbg_aux(fe, p));
      },
      LispKind::Goal(lisp_val) => {
        ron.add_name("LispKind::Goal");
        ron.add_field(lisp_val.dbg_aux(fe, p));
      }
    }
    ron.to_doc(p)

  }
}


impl EnvDebug for crate::elab::lisp::Annot {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonTuple::new();
    ron.add_name("Annot");

    match self {
      crate::elab::lisp::Annot::Span(filespan) => { 
        ron.add_name("Span");
        ron.add_field(filespan.dbg_aux(fe, p)); 
      }
    }
    ron.to_doc(p)
  }
}

impl EnvDebug for crate::mmc::nameck::Type {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonTuple::new();
    ron.add_name("Type");
    match self {
      crate::mmc::nameck::Type::Prim(primtype) => {
        ron.add_name("Prim");
        ron.add_field(primtype.dbg_aux(fe, p));
      },
      crate::mmc::nameck::Type::Unchecked => {
        ron.add_name("Proc");
      },
    }
    ron.to_doc(p)
  }
}


impl EnvDebug for crate::mmc::nameck::Entity {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonTuple::new();
    ron.add_name("Entity");
    match self {
      crate::mmc::nameck::Entity::Type(type_) => {
        ron.add_name("Type");
        ron.add_field(type_.dbg_aux(fe, p));
      },
      crate::mmc::nameck::Entity::Op(operator) => {
        ron.add_name("Op");
        ron.add_field(operator.dbg_aux(fe, p));
      },
      crate::mmc::nameck::Entity::Global(globaltc) => {
        ron.add_name("Global");
        ron.add_field(globaltc.dbg_aux(fe, p));
      },
      crate::mmc::nameck::Entity::Const(globaltc) => {
        ron.add_name("Const");
        ron.add_field(globaltc.dbg_aux(fe, p));
      }
    }
    ron.to_doc(p)
  }
}

impl EnvDebug for crate::mmc::parser::Proc {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonStruct::new();
    ron.add_name("Proc");
    ron.add_field("kind", self.kind.dbg_aux(fe, p));
    ron.add_field("name", self.name.dbg_aux(fe, p));
    ron.add_field("span", self.span.dbg_aux(fe, p));
    ron.add_field("args", self.args.dbg_aux(fe, p));
    ron.add_field("rets", self.rets.dbg_aux(fe, p));
    ron.add_field("variant", self.variant.dbg_aux(fe, p));
    ron.add_field("body", self.body.dbg_aux(fe, p));
    ron.to_doc(p)

  }
}

impl EnvDebug for crate::mmc::parser::Arg {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonStruct::new();
    ron.add_field("name", self.name.dbg_aux(fe, p));
    ron.add_field("ghost", self.ghost.dbg_aux(fe, p));
    ron.add_field("ty", self.ty.dbg_aux(fe, p));
    ron.to_doc(p)
  }
}

impl EnvDebug for crate::mmc::nameck::Operator {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonTuple::new();
    ron.add_name("Operator");
    match self {
      crate::mmc::nameck::Operator::Prim(primproc) => {
        ron.add_name("Prim");
        ron.add_field(primproc.dbg_aux(fe, p));
      },
      crate::mmc::nameck::Operator::Proc(arc_proc, proctc) => {
        ron.add_name("Proc");
        ron.add_field(arc_proc.as_ref().dbg_aux(fe, p));
        ron.add_field(proctc.dbg_aux(fe, p));
      },
    }
    ron.to_doc(p)
  }
}

impl<A : EnvDebug> EnvDebug for crate::mmc::predef::PredefMap<A> {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonTuple::new();
    ron.add_name("PredefMap");
    match self {
      crate::mmc::predef::PredefMap(arr) => { 
        let mut seq = RonSequence::new();
        seq.add_field(arr[0].dbg_aux(fe, p));
        ron.add_field(seq.to_doc(p));
      }
    }
    ron.to_doc(p)
  }
}

impl EnvDebug for crate::mmc::Compiler {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonStruct::new();
    ron.add_name("Compiler");
    ron.add_field("keywords", self.keywords.dbg_aux(fe, p));
    ron.add_field("names", self.names.dbg_aux(fe, p));
    ron.add_field("predef", self.predef.dbg_aux(fe, p));
    ron.to_doc(p)
  }
}

impl EnvDebug for crate::elab::lisp::parser::IR {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonTuple::new();
    ron.add_name("IR");
    match self {
      crate::elab::lisp::parser::IR::Local(n) => {
        ron.add_name("Local");
        ron.add_field(n.to_string());
      },
      crate::elab::lisp::parser::IR::Global(span, atom_id) => {
        ron.add_name("Global");
        ron.add_field(span.dbg_aux(fe, p));
        ron.add_field(atom_id.dbg_aux(fe, p));
      },
      crate::elab::lisp::parser::IR::Const(lisp_val) => {
        ron.add_name("Const");
        ron.add_field(lisp_val.dbg_aux(fe, p));
      },
      crate::elab::lisp::parser::IR::List(span, boxir) => {
        ron.add_name("List");
        ron.add_field(span.dbg_aux(fe, p));
        ron.add_field(boxir.as_ref().dbg_aux(fe, p));
      },
      crate::elab::lisp::parser::IR::DottedList(boxir1, boxir2) => {
        ron.add_name("DottedList");
        ron.add_field(boxir1.as_ref().dbg_aux(fe, p));
        ron.add_field(boxir2.as_ref().dbg_aux(fe, p));
      },
      crate::elab::lisp::parser::IR::App(span1, span2, boxir1, boxir2) => {
        ron.add_name("App");
        ron.add_field(span1.dbg_aux(fe, p));
        ron.add_field(span2.dbg_aux(fe, p));
        ron.add_field(boxir1.as_ref().dbg_aux(fe, p));
        ron.add_field(boxir2.as_ref().dbg_aux(fe, p));
      },
      crate::elab::lisp::parser::IR::If(boxir_triple) => {
        ron.add_name("If");
        ron.add_field(boxir_triple.as_ref().dbg_aux(fe, p));
      },
      crate::elab::lisp::parser::IR::Focus(span, boxir) => {
        ron.add_name("Focus");
        ron.add_field(span.dbg_aux(fe, p));
        ron.add_field(boxir.as_ref().dbg_aux(fe, p));
      },
      crate::elab::lisp::parser::IR::Def(usz, option_triple, boxir) => {
        ron.add_name("Def");
        ron.add_field(usz.dbg_aux(fe, p));
        ron.add_field(option_triple.as_ref().dbg_aux(fe, p));
        ron.add_field(boxir.as_ref().dbg_aux(fe, p));
      },
      crate::elab::lisp::parser::IR::Eval(bl, boxir) => {
        ron.add_name("Eval");
        ron.add_field(bl.dbg_aux(fe, p));
        ron.add_field(boxir.as_ref().dbg_aux(fe, p));
      },
      crate::elab::lisp::parser::IR::Lambda(span, usz, proc_spec, arc_ir) => {
        ron.add_name("Lambda");
        ron.add_field(span.dbg_aux(fe, p));
        ron.add_field(usz.dbg_aux(fe, p));
        ron.add_field(proc_spec.dbg_aux(fe, p));
        ron.add_field(arc_ir.as_ref().dbg_aux(fe, p));
      },
      crate::elab::lisp::parser::IR::Match(span, boxir, box_branch_arr) => {
        ron.add_name("Match");
        ron.add_field(span.dbg_aux(fe, p));
        ron.add_field(boxir.as_ref().dbg_aux(fe, p));
        ron.add_field(box_branch_arr.as_ref().dbg_aux(fe, p));
      },
    }
    ron.to_doc(p)
  }
}

impl EnvDebug for crate::elab::lisp::Proc {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    match self {
      crate::elab::lisp::Proc::Builtin(builtin_proc) => {
        let mut ron = RonTuple::new();
        ron.add_name("Proc::Builtin");
        ron.add_field(builtin_proc.dbg_aux(fe, p));
        ron.to_doc(p)
      }
      crate::elab::lisp::Proc::Lambda { pos, env, spec, code } => {
        let mut ron = RonStruct::new();
        ron.add_name("Proc::Lambda");
        ron.add_field("pos", pos.dbg_aux(fe, p));
        ron.add_field("env", env.as_ref().dbg_aux(fe, p));
        ron.add_field("spec", spec.dbg_aux(fe, p));
        ron.add_field("code", code.dbg_aux(fe, p));
        ron.to_doc(p)
      }
      crate::elab::lisp::Proc::MatchCont(wrapped_bool) => {
        let mut ron = RonTuple::new();
        ron.add_name("Proc::MatchCont");
        ron.add_field(wrapped_bool.get().dbg_aux(fe, p));
        ron.to_doc(p)
      }
      crate::elab::lisp::Proc::RefineCallback => {
        let mut ron = RonTuple::new();
        ron.add_name("Proc::RefineCallback");
        ron.to_doc(p)
      }
      crate::elab::lisp::Proc::ProofThunk(atom_id, refcell) => {
        let mut ron = RonTuple::new();
        ron.add_name("Proc::ProofThunk");
        ron.add_field(atom_id.dbg_aux(fe, p));
        ron.add_field(refcell.dbg_aux(fe, p));
        ron.to_doc(p)
      }
      crate::elab::lisp::Proc::MMCCompiler(refcell_compiler) => {
        let mut ron = RonTuple::new();
        ron.add_name("Proc::MMCCompiler");
        ron.add_field(refcell_compiler.dbg_aux(fe, p));
        ron.to_doc(p)
      }
    }
  }
}

impl EnvDebug for crate::elab::lisp::parser::Pattern {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonTuple::new();
    ron.add_name("Pattern");
    match self {
      crate::elab::lisp::parser::Pattern::Skip => {
        ron.add_name("Skip");
      },
      crate::elab::lisp::parser::Pattern::Atom(n) => {
        ron.add_name("Atom");
        ron.add_field(n.to_string());
      },
      crate::elab::lisp::parser::Pattern::QuoteAtom(atom_id) => {
        ron.add_name("QuoteAtom");
        ron.add_field(atom_id.dbg_aux(fe, p));
      },
      crate::elab::lisp::parser::Pattern::String(arc_string) => {
        ron.add_name("String");
        ron.add_field(arc_string.to_string());
      },
      crate::elab::lisp::parser::Pattern::Bool(bl) => {
        ron.add_name("Bool");
        ron.add_field(bl.dbg_aux(fe, p));
      },
      crate::elab::lisp::parser::Pattern::Undef => {
        ron.add_name("Undef");
      },
      crate::elab::lisp::parser::Pattern::Number(bigint) => {
        ron.add_name("Number");
        ron.add_field(bigint.to_string());
      },
      crate::elab::lisp::parser::Pattern::MVar(opt_box_pat_pat) => {
        ron.add_name("MVar");
        ron.add_field(opt_box_pat_pat.as_ref().map(|b| b.as_ref()).dbg_aux(fe, p));
      },
      crate::elab::lisp::parser::Pattern::Goal(boxpat) => {
        ron.add_name("Goal");
        ron.add_field(boxpat.as_ref().dbg_aux(fe, p));
      },
      crate::elab::lisp::parser::Pattern::DottedList(boxpat1, boxpat2) => {
        ron.add_name("DottedList");
        ron.add_field(boxpat1.as_ref().dbg_aux(fe, p));
        ron.add_field(boxpat2.as_ref().dbg_aux(fe, p));
      },
      crate::elab::lisp::parser::Pattern::List(boxpat, opt_usize) => {
        ron.add_name("List");
        ron.add_field(boxpat.as_ref().dbg_aux(fe, p));
        ron.add_field(opt_usize.dbg_aux(fe, p));
      },
      crate::elab::lisp::parser::Pattern::And(boxpat) => {
        ron.add_name("And");
        ron.add_field(boxpat.as_ref().dbg_aux(fe, p));
      },
      crate::elab::lisp::parser::Pattern::Or(boxpat) => {
        ron.add_name("Or");
        ron.add_field(boxpat.as_ref().dbg_aux(fe, p));
      },
      crate::elab::lisp::parser::Pattern::Not(boxpat) => {
        ron.add_name("Not");
        ron.add_field(boxpat.as_ref().dbg_aux(fe, p));
      },
      crate::elab::lisp::parser::Pattern::Test(span, boxpat, boxir) => {
        ron.add_name("Test");
        ron.add_field(span.dbg_aux(fe, p));
        ron.add_field(boxpat.as_ref().dbg_aux(fe, p));
        ron.add_field(boxir.as_ref().dbg_aux(fe, p));
      },
      crate::elab::lisp::parser::Pattern::QExprAtom(atom_id) => {
        ron.add_name("QExprAtom");
        ron.add_field(atom_id.dbg_aux(fe, p));
      },
    }
    ron.to_doc(p)
  }
}

impl EnvDebug for crate::elab::lisp::parser::Branch {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonStruct::new();
    ron.add_name("Branch");
    ron.add_field("vars", self.vars.dbg_aux(fe, p));
    ron.add_field("cont", self.cont.dbg_aux(fe, p));
    ron.add_field("pat", self.pat.dbg_aux(fe, p));
    ron.add_field("eval", self.eval.dbg_aux(fe, p));
    ron.to_doc(p)
  }
}

impl<A : EnvDebug> EnvDebug for Box<[A]> {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    self.as_ref().dbg_aux(fe, p)
  }
}


impl<A : EnvDebug> EnvDebug for RefCell<A> {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    match self.try_borrow() {
      Ok(x) => x.dbg_aux(fe, p),
      Err(_) => "_mutably borrowed RefCell_".alloc(p)
    }
  }
}


impl<A : EnvDebug> EnvDebug for Box<A> {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    self.as_ref().dbg_aux(fe, p)
  }
}

impl<A : EnvDebug> EnvDebug for &Box<A> {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    self.as_ref().dbg_aux(fe, p)
  }
}

impl<A : EnvDebug, E : EnvDebug> EnvDebug for Result<A, E> {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let ron = RonResult::new(
      self.as_ref().map(|x| x.dbg_aux(fe, p)).map_err(|e| e.dbg_aux(fe, p))
    );
    ron.to_doc(p)
  }
}

impl EnvDebug for crate::elab::lisp::Syntax {}
impl EnvDebug for crate::mmc::parser::Keyword {}
impl EnvDebug for crate::mmc::parser::ProcKind {}
impl EnvDebug for crate::mmc::nameck::GlobalTC {}
impl EnvDebug for crate::mmc::nameck::PrimProc {}
impl EnvDebug for crate::mmc::nameck::PrimType {}
impl EnvDebug for crate::mmc::nameck::ProcTC {}
impl EnvDebug for crate::elab::lisp::BuiltinProc {}
impl EnvDebug for crate::elab::lisp::ProcSpec {}
impl EnvDebug for crate::parser::ast::Prec {}
impl EnvDebug for crate::elab::environment::Literal {}
impl EnvDebug for u32 {}
impl EnvDebug for u64 {}
impl EnvDebug for usize {}
impl EnvDebug for bool {}
impl EnvDebug for std::sync::atomic::AtomicBool {}


impl<A : EnvDebug> EnvDebug for Vec<A> {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonSequence::new();
    for elem in self.iter() {
      ron.add_field(elem.dbg_aux(fe, p));
    }
    ron.to_doc(p)
  }
}

impl<A : EnvDebug> EnvDebug for &[A] {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonSequence::new();
    for elem in self.iter() {
      ron.add_field(elem.dbg_aux(fe, p));
    }
    ron.to_doc(p)
  }
}

impl<A : EnvDebug> EnvDebug for Option<A> {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let inner = self.as_ref().map(|a| a.dbg_aux(fe, p));
    RonOption::new(inner).to_doc(p)
  }
}

impl<A : EnvDebug, B : EnvDebug> EnvDebug for &(A, B) {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let l = self.0.dbg_aux(fe, p);
    let r = self.1.dbg_aux(fe, p);
    let mut ron = RonTuple::new();
    ron.add_field(l);
    ron.add_field(r);
    ron.to_doc(p)
  }
}

impl<A : EnvDebug, B : EnvDebug, C : EnvDebug> EnvDebug for &(A, B, C) {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let a = self.0.dbg_aux(fe, p);
    let b = self.1.dbg_aux(fe, p);
    let c = self.2.dbg_aux(fe, p);
    let mut ron = RonTuple::new();
    ron.add_field(a);
    ron.add_field(b);
    ron.add_field(c);
    ron.to_doc(p)
  }
}

impl<A : EnvDebug, B : EnvDebug, C : EnvDebug, D : EnvDebug> EnvDebug for (A, B, C, D) {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let a = self.0.dbg_aux(fe, p);
    let b = self.1.dbg_aux(fe, p);
    let c = self.2.dbg_aux(fe, p);
    let d = self.3.dbg_aux(fe, p);
    let mut ron = RonTuple::new();
    ron.add_field(a);
    ron.add_field(b);
    ron.add_field(c);
    ron.add_field(d);
    ron.to_doc(p)
  }
}

impl<A : EnvDebug, B : EnvDebug> EnvDebug for (A, B) {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let l = self.0.dbg_aux(fe, p);
    let r = self.1.dbg_aux(fe, p);
    let mut ron = RonTuple::new();
    ron.add_field(l);
    ron.add_field(r);
    ron.to_doc(p)
  }
}

impl<K : EnvDebug, V : EnvDebug> EnvDebug for HashMap<K, V> {
  fn dbg_aux<'a>(
    &self, 
    fe : FormatEnv<'a>,
    p : &mut Printer<'a>, 
  ) -> DocPtr<'a> {
    let mut ron = RonStruct::new();
    for (k, v) in self.iter() {
      ron.add_field(k.dbg_aux(fe, p), v.dbg_aux(fe, p));
    }
    ron.to_doc(p)
  }
}

/// Companion to `EnvDisplay`
pub trait EnvDebug : std::fmt::Debug {
  /// Companion to std::fmt::Debug that allows for extra arguments. Companion to `EnvDisplay`
  fn dbg(&self, fe : FormatEnv<'_>, f : &mut fmt::Formatter<'_>) -> fmt::Result {
    fe.debug(|fe, pr| {
      write!(f, "{}", self.dbg_aux(fe, pr).render(80, pr))
    })
  }

  /// The default implementation is just to use the type's std::fmt::Debug 
  /// representation, since there's a fair number of types (like enums whose variants are all
  /// nullary items) whose Debug representation is already their EnvDebug representation.
  fn dbg_aux<'a>(
    &self, 
    _fe : FormatEnv<'a>,
    p : &mut Printer<'a>
  ) -> DocPtr<'a> {
    format!("{:#?}", self).alloc(p)
  }
}



