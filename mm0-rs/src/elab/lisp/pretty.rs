use std::ops::Deref;
use std::collections::HashMap;
use std::cell::RefCell;
use std::{mem, fmt::{self, Write}};
use std::borrow::Cow;
use pretty::{DocAllocator, Doc, RefDoc, Arena};
use itertools::Itertools;
use super::{LispVal, LispKind, Uncons, print::FormatEnv,
  super::{
    environment::{Prec, DeclKey, Literal,
      Environment, NotaInfo, AtomData, AtomID, TermID, Term, Thm, Type},
    math_parser::APP_PREC}};

#[derive(Copy, Clone, Debug)]
struct PP<'a> {
  left: bool,
  right: bool,
  small: bool,
  doc: RefDoc<'a, ()>,
}

impl<'a> PP<'a> {
  fn token(alloc: &'a Arena<'a, ()>, env: &Environment, tk: &'a str) -> PP<'a> {
    PP {
      // A right delimiter like ')' has a token boundary on its left side,
      // and vice versa. This ensures that `x ( y ) z` gets notated as `x (y) z`
      left: env.pe.delims_r.get(*tk.as_bytes().first().unwrap()),
      right: env.pe.delims_l.get(*tk.as_bytes().last().unwrap()),
      small: true,
      doc: alloc.alloc(Doc::text(tk)),
    }
  }

  fn word(alloc: &'a Arena<'a, ()>, data: impl Into<Cow<'a, str>>) -> PP<'a> {
    PP {
      left: false,
      right: false,
      small: true,
      doc: alloc.alloc(Doc::text(data)),
    }
  }
}

impl LispKind {
  fn small(&self) -> bool {
    match self {
      LispKind::List(es) => es.is_empty(),
      LispKind::DottedList(_, _) |
      LispKind::AtomMap(_) |
      LispKind::Goal(_) => false,
      LispKind::Atom(_) |
      LispKind::MVar(_, _) |
      LispKind::Proc(_) |
      LispKind::Number(_) |
      LispKind::String(_) |
      LispKind::Bool(_) |
      LispKind::Syntax(_) |
      LispKind::Undef => true,
      LispKind::Annot(_, e) => e.small(),
      LispKind::Ref(m) => m.get().small(),
    }
  }
}

pub struct Pretty<'a> {
  fe: FormatEnv<'a>,
  alloc: &'a Arena<'a, ()>,
  hash: RefCell<HashMap<*const LispKind, (Prec, PP<'a>)>>,
  lparen: PP<'a>,
  rparen: PP<'a>,
}

const NIL: RefDoc<'static, ()> = RefDoc(&Doc::Nil);
const HARDLINE: RefDoc<'static, ()> = RefDoc(&Doc::Line);
const SPACE: RefDoc<'static, ()> = RefDoc(&Doc::BorrowedText(" "));
const LINE: RefDoc<'static, ()> = RefDoc(&Doc::FlatAlt(HARDLINE, SPACE));
const LINE_: RefDoc<'static, ()> = RefDoc(&Doc::FlatAlt(HARDLINE, NIL));
const SOFTLINE: RefDoc<'static, ()> = RefDoc(&Doc::Group(LINE));
const SOFTLINE_: RefDoc<'static, ()> = RefDoc(&Doc::Group(LINE_));

fn covariant<'a>(from: RefDoc<'static, ()>) -> RefDoc<'a, ()> {
  unsafe {mem::transmute(from)}
}

impl<'a> Pretty<'a> {
  pub fn nil() -> RefDoc<'a, ()> {covariant(NIL)}
  // fn hardline() -> RefDoc<'a, ()> {covariant(HARDLINE)}
  // fn space() -> RefDoc<'a, ()> {covariant(SPACE)}
  fn line() -> RefDoc<'a, ()> {covariant(LINE)}
  // fn line_() -> RefDoc<'a, ()> {covariant(LINE_)}
  fn softline() -> RefDoc<'a, ()> {covariant(SOFTLINE)}
  fn softline_() -> RefDoc<'a, ()> {covariant(SOFTLINE_)}

  fn new(fe: FormatEnv<'a>, alloc: &'a Arena<'a, ()>) -> Pretty<'a> {
    Pretty {
      lparen: PP::token(&alloc, fe.env, "("),
      rparen: PP::token(&alloc, fe.env, ")"),
      fe, alloc, hash: RefCell::new(HashMap::new())
    }
  }

  fn token(&'a self, tk: &'a str) -> PP<'a> { PP::token(&self.alloc, &self.fe, tk) }
  fn word(&'a self, data: &'a str) -> PP<'a> { PP::word(&self.alloc, data) }

  fn alloc(&'a self, doc: Doc<'a, RefDoc<'a, ()>, ()>) -> RefDoc<'a, ()> {
    self.alloc.alloc(doc)
  }

  fn append_doc(&'a self, a: RefDoc<'a, ()>, b: RefDoc<'a, ()>) -> RefDoc<'a, ()> {
    self.alloc(Doc::Append(a, b))
  }

  fn append_with(&'a self, a: PP<'a>, sp: RefDoc<'a, ()>, b: PP<'a>) -> PP<'a> {
    let doc = self.append_doc(self.append_doc(a.doc, sp), b.doc);
    PP {left: a.left, right: b.right, small: false, doc}
  }

  fn append(&'a self, a: PP<'a>, b: PP<'a>) -> PP<'a> {
    let sp = if a.right || b.left {Self::softline_()} else {Self::softline()};
    self.append_with(a, sp, b)
  }

  fn group(&'a self, a: PP<'a>) -> PP<'a> {
    let PP {left, right, small, doc} = a;
    PP {left, right, small, doc: self.alloc(Doc::Group(doc))}
  }

  fn nest(&'a self, i: isize, a: PP<'a>) -> PP<'a> {
    let PP {left, right, small, doc} = a;
    PP {left, right, small, doc: self.alloc(Doc::Nest(i, doc))}
  }

  fn expr_paren(&'a self, e: &LispVal, p: Prec) -> PP<'a> {
    let (q, doc) = self.pp_expr(e);
    if p > q {
      self.append(self.append(self.lparen, doc), self.rparen)
    } else {doc}
  }

  fn app(&'a self, mut head: PP<'a>, mut es: impl Iterator<Item=PP<'a>>) -> PP<'a> {
    while let Some(mut doc) = es.next() {
      if doc.small {
        head = self.append_with(head, Self::softline(), doc);
      } else {
        loop {
          head = self.append_with(head, Self::line(), doc);
          doc = if let Some(doc) = es.next() {doc} else {return head}
        }
      }
    }
    head
  }

  fn lit(&'a self, lit: &'a Literal, args: &[LispVal]) -> PP<'a> {
    match lit {
      &Literal::Var(i, p) => self.expr_paren(&args[i], p),
      Literal::Const(tk) => self.token(tk),
    }
  }

  fn infixl(&'a self, t: TermID, info: &'a NotaInfo, args: Vec<LispVal>) -> Option<PP<'a>> {
    if let Literal::Var(i, q) = info.lits[0] {
      let doc = match self.get_term_args(&args[i]) {
        Some((_, t2, args2)) if t == t2 => self.infixl(t, info, args2),
        _ => None,
      }.unwrap_or_else(|| self.group(self.expr_paren(&args[i], q)));
      let mut doc = self.append_with(doc, Self::softline(), self.lit(&info.lits[1], &args));
      let (last, most) = info.lits[2..].split_last()?;
      for lit in most {doc = self.append(doc, self.group(self.lit(&lit, &args)))}
      Some(self.append_with(doc, Self::line(), self.group(self.lit(&last, &args))))
    } else {None}
  }

  fn infixr(&'a self, t: TermID, info: &'a NotaInfo, args: Vec<LispVal>) -> Option<PP<'a>> {
    let doc = self.lit(&info.lits[0], &args);
    let mut doc = self.append_with(doc, Self::softline(), self.lit(&info.lits[1], &args));
    if let (&Literal::Var(i, q), most) = info.lits[2..].split_last()? {
      for lit in most {doc = self.append(doc, self.group(self.lit(&lit, &args)))}
      let end = match self.get_term_args(&args[i]) {
        Some((_, t2, args2)) if t == t2 => self.infixr(t, info, args2),
        _ => None,
      }.unwrap_or_else(|| self.group(self.expr_paren(&args[i], q)));
      Some(self.append_with(doc, Self::line(), end))
    } else {None}
  }

  fn get_term_args(&'a self, e: &LispVal) -> Option<(&'a AtomData, TermID, Vec<LispVal>)> {
    let mut u = Uncons::from(e.clone());
    let env = self.fe.env;
    let a = u.next()?.as_atom()?;
    let ad = &env.data[a];
    let t = if let Some(DeclKey::Term(t)) = ad.decl {t} else {None?};
    let mut args = vec![];
    let nargs = env.terms[t].args.len();
    if !u.exactly(nargs) {None?}
    u.extend_into(nargs, &mut args);
    Some((ad, t, args))
  }

  fn pp_expr(&'a self, e: &LispVal) -> (Prec, PP<'a>) {
    let p: *const LispKind = e.deref();
    if let Some(v) = self.hash.borrow().get(&p) {return v.clone()}
    let v = (|| Some({
      let env = self.fe.env;
      let (ad, t, args) = self.get_term_args(e)?;
      if let Some(&(coe, ref fix)) = env.pe.decl_nota.get(&t) {
        if coe {return Some(self.pp_expr(&args[0]))}
        if let Some(&(ref tk, infix)) = fix.first() {
          let doc = if infix {
            let info = &env.pe.infixes[tk];
            let doc = if info.rassoc.unwrap() {
              self.infixr(t, info, args)?
            } else {
              self.infixl(t, info, args)?
            };
            self.group(self.nest(2, doc))
          } else {
            let info = &env.pe.prefixes[tk];
            let mut doc = self.token(tk);
            for lit in &info.lits {
              doc = self.append(doc, self.lit(lit, &args))
            }
            doc
          };
          return Some((env.pe.consts[tk].1, doc))
        }
      }
      (APP_PREC, self.group(self.nest(2, self.app(self.word(&ad.name),
        args.iter().map(|e| self.expr_paren(e, Prec::Max))))))
    }))().unwrap_or_else(|| (Prec::Max, PP {
      left: false, right: false, small: e.small(),
      doc: self.pp_lisp(e)
    }));
    self.hash.borrow_mut().entry(p).or_insert(v).clone()
  }

  pub fn expr(&'a self, e: &LispVal) -> RefDoc<'a, ()> {
    let mut doc = self.expr_paren(e, Prec::Prec(0)).doc;
    if let Doc::Group(doc2) = *doc {doc = doc2}
    let doc = self.append_doc(self.alloc(Doc::text("$ ")),
      self.append_doc(doc, self.alloc(Doc::text(" $"))));
    self.alloc(Doc::Group(doc))
  }

  fn get_thm_args(&'a self, u: &mut Uncons, args: &mut Vec<LispVal>) -> Option<(&'a AtomData, &'a Thm)> {
    let env = self.fe.env;
    let a = u.next()?.as_atom()?;
    let ad = &env.data[a];
    let t = if let Some(DeclKey::Thm(t)) = ad.decl {t} else {None?};
    let td = &env.thms[t];
    let n = td.args.len();
    if !u.extend_into(n, args) {None?}
    for _ in 0..n {u.next();}
    Some((ad, td))
  }

  fn app_doc(&'a self, mut head: RefDoc<'a, ()>, mut es: impl Iterator<Item=(bool, RefDoc<'a, ()>)>) -> RefDoc<'a, ()> {
    while let Some((small, mut doc)) = es.next() {
      if small {
        head = self.append_doc(head, self.append_doc(Self::softline(), doc));
      } else {
        loop {
          head = self.append_doc(head, self.append_doc(Self::line(), doc));
          doc = if let Some((_, doc)) = es.next() {doc} else {return head}
        }
      }
    }
    head
  }

  pub fn pp_lisp(&'a self, e: &LispVal) -> RefDoc<'a, ()> {
    e.unwrapped(|r| match r {
      LispKind::List(_) | LispKind::DottedList(_, _) => {
        let mut u = Uncons::from(e.clone());
        let mut args = vec![];
        let mut doc = if let Some((ad, td)) = self.get_thm_args(&mut u, &mut args) {
          let doc = self.alloc(Doc::BorrowedText(&ad.name));
          let doc = self.app_doc(doc, td.args.iter().zip(&args).map(|((_, ty), e)| {
            match ty {
              Type::Bound(_) => (true, self.pp_lisp(e)),
              Type::Reg(_, _) => (e.small(), self.expr_paren(e, Prec::Max).doc),
            }
          }));
          self.alloc(Doc::Group(doc))
        } else {
          let mut u = Uncons::from(e.clone());
          if let Some(e) = u.next() { self.pp_lisp(&e) }
          else if u.exactly(0) { return self.alloc(Doc::text("()")) }
          else { return self.pp_lisp(&u.as_lisp()) }
        };
        for e in &mut u {
          doc = self.append_doc(doc, self.append_doc(Self::line(), self.pp_lisp(&e)));
        }
        if !u.exactly(0) {
          doc = self.append_doc(doc,
            self.append_doc(self.alloc(Doc::text(" .")),
              self.append_doc(Self::line(), self.pp_lisp(&u.as_lisp()))));
        }
        let doc = self.append_doc(self.lparen.doc, self.append_doc(doc, self.rparen.doc));
        self.alloc(Doc::Group(self.alloc(Doc::Nest(2, doc))))
      }
      _ => self.alloc(Doc::text(format!("{}", self.fe.to(e)))),
    })
  }

  fn dep_type(bvs: &[AtomID], ds: u64, fe: FormatEnv, f: &mut impl fmt::Write) -> fmt::Result {
    let mut i = 1;
    for x in bvs {
      if ds & i != 0 {write!(f, " {}", fe.to(x))?}
      i *= 2;
    }
    Ok(())
  }

  fn grouped_binders(&'a self, mut doc: RefDoc<'a, ()>,
    bis: &[(Option<AtomID>, Type)], bvs: &mut Vec<AtomID>) -> RefDoc<'a, ()> {
    let mut rest = bis;
    loop {
      let mut it = rest.iter();
      let ty = match it.next() {
        None => return doc,
        Some((_, ty)) => ty,
      };
      let (bis1, bis2) = rest.split_at(it.position(|(_, ty2)| ty != ty2).map_or(rest.len(), |x| x + 1));
      let mut buf = String::new();
      match ty {
        &Type::Bound(s) => {
          write!(buf, "{{{}: {}}}", bis1.iter().map(|(a, _)| {
            bvs.push(a.unwrap_or(AtomID::UNDER));
            self.fe.to(a)
          }).format(" "), self.fe.to(&s)).unwrap();
        }
        &Type::Reg(s, ds) => {
          write!(buf, "({}: {}",
            bis1.iter().map(|(a, _)| self.fe.to(a)).format(" "),
            self.fe.to(&s)).unwrap();
          Self::dep_type(bvs, ds, self.fe, &mut buf).unwrap();
          write!(buf, ")").unwrap();
        }
      }
      doc = self.append_doc(doc, self.append_doc(Self::softline(),
        self.alloc(Doc::text(buf))));
      rest = bis2;
    }
  }

  pub fn term(&'a self, t: &Term) -> RefDoc<'a, ()> {
    let buf = format!("{}{} {}", t.vis,
      if t.val.is_some() {"def"} else {"term"},
      self.fe.to(&t.atom));
    let doc = self.alloc(Doc::text(buf));
    let mut bvs = vec![];
    let doc = self.grouped_binders(doc, &t.args, &mut bvs);
    let doc = self.append_doc(doc, self.alloc(Doc::text(":")));
    let doc = self.alloc(Doc::Group(doc));
    let mut buf = format!("{}", self.fe.to(&t.ret.0));
    Self::dep_type(&bvs, t.ret.1, self.fe, &mut buf).unwrap();
    buf += ";";
    self.append_doc(doc, self.append_doc(Self::softline(),
      self.alloc(Doc::text(buf))))
  }

  pub fn hyps_and_ret(&'a self, mut doc: RefDoc<'a, ()>,
      hs: impl Iterator<Item=LispVal>, ret: &LispVal) -> RefDoc<'a, ()> {
    for e in hs {
      doc = self.append_doc(doc,
        self.append_doc(self.expr(&e),
          self.append_doc(self.alloc(Doc::text(" >")),
            Self::line())));
    }
    self.append_doc(doc, self.expr(ret))
  }

  pub fn thm(&'a self, t: &Thm) -> RefDoc<'a, ()> {
    let buf = format!("{}{} {}", t.vis,
      if t.proof.is_some() {"theorem"} else {"axiom"},
      self.fe.to(&t.atom));
    let doc = self.alloc(Doc::text(buf));
    let mut bvs = vec![];
    let doc = self.grouped_binders(doc, &t.args, &mut bvs);
    let doc = self.append_doc(doc, self.alloc(Doc::text(":")));
    let doc = self.append_doc(self.alloc(Doc::Group(doc)), Self::line());
    let mut bvs = Vec::new();
    let mut heap = Vec::new();
    self.fe.binders(&t.args, &mut heap, &mut bvs);
    for e in &t.heap[heap.len()..] {
      let e = self.fe.expr_node(&heap, &mut None, e);
      heap.push(e)
    }
    let doc = self.hyps_and_ret(doc,
      t.hyps.iter().map(|(_, e)| self.fe.expr_node(&heap, &mut None, e)),
      &self.fe.expr_node(&heap, &mut None, &t.ret));
    let doc = self.append_doc(doc, self.alloc(Doc::text(";")));
    self.alloc(Doc::Group(self.alloc(Doc::Nest(2, doc))))
  }

  pub fn unify_err(&'a self, e1: &LispVal, e2: &LispVal) -> RefDoc<'a, ()> {
    let doc = self.append_doc(RefDoc(&Doc::BorrowedText("failed to unify:")), Self::line());
    let doc = self.append_doc(doc, self.expr_paren(e1, Prec::Prec(0)).doc);
    let doc = self.append_doc(doc, self.alloc(Doc::Nest(2,
      self.append_doc(Self::line(), RefDoc(&Doc::BorrowedText("=?="))))));
    let doc = self.append_doc(doc, Self::line());
    let doc = self.append_doc(doc, self.expr_paren(e2, Prec::Prec(0)).doc);
    self.alloc(Doc::Group(doc))
  }
}

pub struct PPExpr<'a> {
  fe: FormatEnv<'a>,
  e: &'a LispVal,
  width: usize,
}

impl<'a> FormatEnv<'a> {
  pub fn pretty<T>(self, f: impl for<'b> FnOnce(&'b Pretty<'b>) -> T) -> T {
    f(&Pretty::new(self, &Arena::new()))
  }

  pub fn pp(self, e: &'a LispVal, width: usize) -> PPExpr<'a> {
    PPExpr {fe: self, e, width}
  }
}

impl<'a> fmt::Display for PPExpr<'a> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    self.fe.pretty(|p| p.expr_paren(self.e, Prec::Max).doc.render_fmt(self.width, f))
  }
}
