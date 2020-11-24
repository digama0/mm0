//! Pretty printer for math formulas and lisp terms.
//!
//! The main interface is the [`FormatEnv::pretty`] function, which provides a
//! [`Pretty`] arena on which various methods exist to print different kinds of object.

use std::collections::HashMap;
use std::cell::RefCell;
use std::{mem, fmt::{self, Write}};
use std::borrow::Cow;
use pretty::{DocAllocator, Doc, RefDoc, Arena};
use itertools::Itertools;
use super::{LispVal, LispKind, Uncons, print::FormatEnv,
  super::{
    environment::{Prec, DeclKey, Literal, TermKind, ThmKind,
      Environment, NotaInfo, AtomData, AtomID, TermID, Term, Thm, Type},
    math_parser::APP_PREC}};

#[derive(Copy, Clone, Debug)]
struct PP<'a> {
  left: bool,
  right: bool,
  small: bool,
  doc: RefDoc<'a, ()>,
}

impl<'a> From<PP<'a>> for RefDoc<'a, ()> {
  fn from(doc: PP<'a>) -> RefDoc<'a, ()> { doc.doc }
}

impl<'a> PP<'a> {
  fn token(alloc: &'a Arena<'a, ()>, env: &Environment, tk: &'a str) -> PP<'a> {
    PP {
      // A right delimiter like ')' has a token boundary on its left side,
      // and vice versa. This ensures that `x ( y ) z` gets notated as `x (y) z`
      left: env.pe.delims_r.get(*tk.as_bytes().first().expect("empty delimiter")),
      right: env.pe.delims_l.get(*tk.as_bytes().last().expect("empty delimiter")),
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
      LispKind::Ref(m) => m.get(|e| e.small()),
    }
  }
}

type PrettyCache<'a> = (LispVal, (Prec, PP<'a>));

/// A state object for constructing pretty printing nodes `PP<'a>`.
/// All pretty printing nodes will be tied to the lifetime of the struct.
pub struct Pretty<'a> {
  fe: FormatEnv<'a>,
  alloc: &'a Arena<'a, ()>,
  hash: RefCell<HashMap<*const LispKind, PrettyCache<'a>>>,
  lparen: PP<'a>,
  rparen: PP<'a>,
}

impl fmt::Debug for Pretty<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "Pretty") }
}

const NIL: RefDoc<'static, ()> = RefDoc(&Doc::Nil);
const HARDLINE: RefDoc<'static, ()> = RefDoc(&Doc::Line);
const SPACE: RefDoc<'static, ()> = RefDoc(&Doc::BorrowedText(" "));
const LINE: RefDoc<'static, ()> = RefDoc(&Doc::FlatAlt(HARDLINE, SPACE));
const LINE_: RefDoc<'static, ()> = RefDoc(&Doc::FlatAlt(HARDLINE, NIL));
const SOFTLINE: RefDoc<'static, ()> = RefDoc(&Doc::Group(LINE));
const SOFTLINE_: RefDoc<'static, ()> = RefDoc(&Doc::Group(LINE_));

#[allow(clippy::useless_transmute)]
fn covariant<'a>(from: RefDoc<'static, ()>) -> RefDoc<'a, ()> {
  unsafe {mem::transmute(from)}
}

impl<'a> Pretty<'a> {
  /// The empty string `""` as a [`RefDoc`].
  #[must_use] pub fn nil() -> RefDoc<'a, ()> {covariant(NIL)}
  // fn hardline() -> RefDoc<'a, ()> {covariant(HARDLINE)}
  // fn space() -> RefDoc<'a, ()> {covariant(SPACE)}
  fn line() -> RefDoc<'a, ()> {covariant(LINE)}
  // fn line_() -> RefDoc<'a, ()> {covariant(LINE_)}
  fn softline() -> RefDoc<'a, ()> {covariant(SOFTLINE)}
  fn softline_() -> RefDoc<'a, ()> {covariant(SOFTLINE_)}

  fn new(fe: FormatEnv<'a>, alloc: &'a Arena<'a, ()>) -> Pretty<'a> {
    Pretty {
      lparen: PP::token(alloc, fe.env, "("),
      rparen: PP::token(alloc, fe.env, ")"),
      fe, alloc, hash: RefCell::new(HashMap::new())
    }
  }

  fn token(&'a self, tk: &'a [u8]) -> PP<'a> {
    PP::token(self.alloc, &self.fe, unsafe {std::str::from_utf8_unchecked(tk)})
  }
  fn word(&'a self, data: &'a [u8]) -> PP<'a> {
    PP::word(self.alloc, unsafe {std::str::from_utf8_unchecked(data)})
  }

  fn alloc(&'a self, doc: Doc<'a, RefDoc<'a, ()>, ()>) -> RefDoc<'a, ()> {
    self.alloc.alloc(doc)
  }

  fn append_doc(&'a self, a: impl Into<RefDoc<'a, ()>>, b: impl Into<RefDoc<'a, ()>>) -> RefDoc<'a, ()> {
    self.alloc(Doc::Append(a.into(), b.into()))
  }

  fn append_with(&'a self, a: PP<'a>, sp: RefDoc<'a, ()>, b: PP<'a>) -> PP<'a> {
    let doc = self.append_doc(self.append_doc(a, sp), b);
    PP {left: a.left, right: b.right, small: false, doc}
  }

  fn append(&'a self, a: PP<'a>, b: PP<'a>) -> PP<'a> {
    let sp = if a.right || b.left {Self::softline_()} else {Self::softline()};
    self.append_with(a, sp, b)
  }

  fn group(&'a self, PP {left, right, small, doc}: PP<'a>) -> PP<'a> {
    PP {left, right, small, doc: self.alloc(Doc::Group(doc))}
  }

  fn nest(&'a self, i: isize, PP {left, right, small, doc}: PP<'a>) -> PP<'a> {
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

  fn infixl(&'a self, t: TermID, info: &'a NotaInfo, args: &[LispVal]) -> Option<PP<'a>> {
    if let Literal::Var(i, q) = info.lits[0] {
      let doc = match self.get_term_args(&args[i]) {
        Some((_, t2, args2)) if t == t2 => self.infixl(t, info, &args2),
        _ => None,
      }.unwrap_or_else(|| self.group(self.expr_paren(&args[i], q)));
      let mut doc = self.append_with(doc, Self::softline(), self.lit(&info.lits[1], args));
      if let Some((last, most)) = info.lits[2..].split_last() {
        for lit in most {doc = self.append(doc, self.group(self.lit(lit, args)))}
        doc = self.append_with(doc, Self::line(), self.group(self.lit(last, args)))
      };
      Some(doc)
    } else {None}
  }

  fn infixr(&'a self, t: TermID, info: &'a NotaInfo, args: &[LispVal]) -> Option<PP<'a>> {
    let doc = self.lit(&info.lits[0], args);
    let mut doc = self.append_with(doc, Self::softline(), self.lit(&info.lits[1], args));
    if let (&Literal::Var(i, q), most) = info.lits[2..].split_last()? {
      for lit in most {doc = self.append(doc, self.group(self.lit(lit, args)))}
      let end = match self.get_term_args(&args[i]) {
        Some((_, t2, args2)) if t == t2 => self.infixr(t, info, &args2),
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
    let p: *const LispKind = &**e;
    if let Some(v) = self.hash.borrow().get(&p) {return v.1}
    let v = (|| Some({
      let env = self.fe.env;
      let (ad, t, args) = self.get_term_args(e)?;
      if let Some(&(coe, ref fix)) = env.pe.decl_nota.get(&t) {
        if coe {return Some(self.pp_expr(&args[0]))}
        if let Some(&(ref tk, infix)) = fix.first() {
          let doc = if infix {
            let info = &env.pe.infixes[tk];
            let doc = if info.rassoc.expect("infix notation has no associativity") {
              self.infixr(t, info, &args)?
            } else {
              self.infixl(t, info, &args)?
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
    self.hash.borrow_mut().entry(p).or_insert_with(|| (e.clone(), v)).1
  }

  /// Pretty-prints a math formula surrounded by `$` delimiters, as in `$ 2 + 2 = 4 $`.
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

  /// Pretty-prints a lisp expression.
  pub fn pp_lisp(&'a self, e: &LispVal) -> RefDoc<'a, ()> {
    e.unwrapped(|r| match r {
      LispKind::List(_) | LispKind::DottedList(_, _) => {
        let mut u = Uncons::from(e.clone());
        let mut args = vec![];
        let mut doc = if let Some((ad, td)) = self.get_thm_args(&mut u, &mut args) {
          let doc = self.alloc(Doc::BorrowedText(ad.name.as_str()));
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
          else { return self.pp_lisp(&u.into()) }
        };
        for e in &mut u {
          doc = self.append_doc(doc, self.append_doc(Self::line(), self.pp_lisp(&e)));
        }
        if !u.exactly(0) {
          doc = self.append_doc(doc,
            self.append_doc(self.alloc(Doc::text(" .")),
              self.append_doc(Self::line(), self.pp_lisp(&u.into()))));
        }
        let doc = self.append_doc(self.lparen, self.append_doc(doc, self.rparen));
        self.alloc(Doc::Group(self.alloc(Doc::Nest(2, doc))))
      }
      _ => self.alloc(Doc::text(format!("{}", self.fe.to(e)))),
    })
  }

  fn dep_type(bvars: &[AtomID], ds: u64, fe: FormatEnv<'_>, f: &mut impl fmt::Write) -> fmt::Result {
    let mut i = 1;
    for x in bvars {
      if ds & i != 0 {write!(f, " {}", fe.to(x))?}
      i *= 2;
    }
    Ok(())
  }

  fn grouped_binders(&'a self, mut doc: RefDoc<'a, ()>,
    bis: &[(Option<AtomID>, Type)], bvars: &mut Vec<AtomID>) -> RefDoc<'a, ()> {
    let mut rest = bis;
    loop {
      let mut it = rest.iter();
      let ty = match it.next() {
        None => return doc,
        Some((_, ty)) => ty,
      };
      let (bis1, bis2) = rest.split_at(it.position(|(_, ty2)| ty != ty2).map_or(rest.len(), |x| x + 1));
      let mut buf = String::new();
      match *ty {
        Type::Bound(s) => {
          write!(buf, "{{{}: {}}}", bis1.iter().map(|(a, _)| {
            bvars.push(a.unwrap_or(AtomID::UNDER));
            self.fe.to(a)
          }).format(" "), self.fe.to(&s)).expect("writing to a String");
        }
        Type::Reg(s, ds) => {
          write!(buf, "({}: {}",
            bis1.iter().map(|(a, _)| self.fe.to(a)).format(" "),
            self.fe.to(&s)).expect("writing to a String");
          Self::dep_type(bvars, ds, self.fe, &mut buf).expect("writing to a Vec");
          write!(buf, ")").expect("writing to a String");
        }
      }
      doc = self.append_doc(doc, self.append_doc(Self::softline(),
        self.alloc(Doc::text(buf))));
      rest = bis2;
    }
  }

  /// Pretty-prints a `term` or `def` declaration, for example
  /// `def foo (x y: nat): nat = $ x + y $;`.
  pub fn term(&'a self, t: &Term) -> RefDoc<'a, ()> {
    let buf = format!("{}{} {}", t.vis,
      if matches!(t.kind, TermKind::Term) {"term"} else {"def"},
      self.fe.to(&t.atom));
    let doc = self.alloc(Doc::text(buf));
    let mut bvars = vec![];
    let doc = self.grouped_binders(doc, &t.args, &mut bvars);
    let doc = self.append_doc(doc, self.alloc(Doc::text(":")));
    let doc = self.alloc(Doc::Group(doc));
    let mut buf = format!("{}", self.fe.to(&t.ret.0));
    Self::dep_type(&bvars, t.ret.1, self.fe, &mut buf).expect("writing to a String");
    buf += ";";
    self.append_doc(doc, self.append_doc(Self::softline(),
      self.alloc(Doc::text(buf))))
  }

  /// Pretty-prints the hypotheses and return of an `axiom` or `theorem`, for example
  /// `$ a $ > $ a -> b $ > $ b $`. This is appended to the input `doc` on the right.
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

  /// Pretty-prints an `axiom` or `theorem` declaration, for example
  /// `theorem mp (a b: wff): $ a $ > $ a -> b $ > $ b $;`.
  /// The proof of the theorem is omitted.
  pub fn thm(&'a self, t: &Thm) -> RefDoc<'a, ()> {
    let buf = format!("{}{} {}", t.vis,
      if matches!(t.kind, ThmKind::Axiom) {"axiom"} else {"theorem"},
      self.fe.to(&t.atom));
    let doc = self.alloc(Doc::text(buf));
    let mut bvars = vec![];
    let doc = self.grouped_binders(doc, &t.args, &mut bvars);
    let doc = self.append_doc(doc, self.alloc(Doc::text(":")));
    let doc = self.append_doc(self.alloc(Doc::Group(doc)), Self::line());
    let mut bvars = Vec::new();
    let mut heap = Vec::new();
    self.fe.binders(&t.args, &mut heap, &mut bvars);
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

  /// Pretty-prints a unification error, as `failed to unify: e1 =?= e2`.
  pub fn unify_err(&'a self, e1: &LispVal, e2: &LispVal) -> RefDoc<'a, ()> {
    let doc = self.append_doc(RefDoc(&Doc::BorrowedText("failed to unify:")), Self::line());
    let doc = self.append_doc(doc, self.expr_paren(e1, Prec::Prec(0)));
    let doc = self.append_doc(doc, self.alloc(Doc::Nest(2,
      self.append_doc(Self::line(), RefDoc(&Doc::BorrowedText("=?="))))));
    let doc = self.append_doc(doc, Self::line());
    let doc = self.append_doc(doc, self.expr_paren(e2, Prec::Prec(0)));
    self.alloc(Doc::Group(doc))
  }
}

/// A struct that can be used to display a [`LispVal`] representing a math expression.
#[derive(Debug)]
pub struct PPExpr<'a> {
  fe: FormatEnv<'a>,
  e: &'a LispVal,
  width: usize,
}

impl<'a> FormatEnv<'a> {
  /// Construct a `Pretty<'a>` object, and use it within the scope of the input function `f`.
  pub fn pretty<T>(self, f: impl for<'b> FnOnce(&'b Pretty<'b>) -> T) -> T {
    f(&Pretty::new(self, &Arena::new()))
  }

  /// Pretty-print an expression at the given display width. The returned struct implements
  /// [`Display`](fmt::Display) and can be used to print to a writer.
  #[must_use] pub fn pp(self, e: &'a LispVal, width: usize) -> PPExpr<'a> {
    PPExpr {fe: self, e, width}
  }
}

impl<'a> fmt::Display for PPExpr<'a> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.fe.pretty(|p| p.expr_paren(self.e, Prec::Prec(0)).doc.render_fmt(self.width, f))
  }
}
