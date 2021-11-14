//! Pretty printer for math formulas and lisp terms.
//!
//! The main interface is the [`FormatEnv::pretty`] function, which provides a
//! [`Pretty`] arena on which various methods exist to print different kinds of object.

use std::collections::HashMap;
use std::cell::RefCell;
use std::{mem, fmt};
use std::borrow::Cow;
use pretty::DocAllocator;
use itertools::Itertools;
use crate::{LispVal, LispKind, Uncons, FormatEnv,
  Prec, DeclKey, Literal, TermKind, ThmKind, Modifiers,
  Environment, NotaInfo, AtomData, AtomId, TermId, ThmId, SortId, Thm, Type,
  APP_PREC};

/// The possible annotations around subparts of a pretty printed display.
/// These are ignored under usual printing settings, but they are used in
/// HTML printing for coloring and to provide more detailed information.
#[derive(Clone, Copy, Debug)]
pub enum Annot {
  /// These are the sort modifiers, e.g. `strict provable` in `strict provable sort foo;`
  SortModifiers(Modifiers),
  /// This is the visibility modifier, e.g. `pub` or `local`.
  Visibility(Modifiers),
  /// This is a keyword, like `axiom` or `sort`.
  Keyword,
  /// This is a sort name, like `foo` in `sort foo;`.
  SortName(SortId),
  /// This is a term/def name, like `foo` in `term foo: nat;`.
  TermName(TermId),
  /// This is an axiom/theorem name, like `foo` in `axiom foo: $ 1 + 1 = 2 $;`.
  ThmName(ThmId),
}

type Doc<'a> = pretty::Doc<'a, RefDoc<'a>, Annot>;
type RefDoc<'a> = pretty::RefDoc<'a, Annot>;
type Arena<'a> = pretty::Arena<'a, Annot>;

#[derive(Copy, Clone, Debug)]
pub(crate) struct Pp<'a> {
  left: bool,
  right: bool,
  small: bool,
  pub(crate) doc: RefDoc<'a>,
}

impl<'a> From<Pp<'a>> for RefDoc<'a> {
  fn from(doc: Pp<'a>) -> RefDoc<'a> { doc.doc }
}

impl<'a> Pp<'a> {
  fn token(alloc: &'a Arena<'a>, env: &Environment, tk: &'a str) -> Pp<'a> {
    Pp {
      // A right delimiter like ')' has a token boundary on its left side,
      // and vice versa. This ensures that `x ( y ) z` gets notated as `x (y) z`
      left: env.pe.delims_r.get(*tk.as_bytes().first().expect("empty delimiter")),
      right: env.pe.delims_l.get(*tk.as_bytes().last().expect("empty delimiter")),
      small: true,
      doc: alloc.alloc(Doc::text(tk)),
    }
  }

  fn word(alloc: &'a Arena<'a>, data: impl Into<Cow<'a, str>>) -> Pp<'a> {
    Pp {
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
      LispKind::DottedList(..) |
      LispKind::AtomMap(..) |
      LispKind::Goal(..) => false,
      LispKind::Atom(..) |
      LispKind::MVar(..) |
      LispKind::Proc(..) |
      LispKind::Number(..) |
      LispKind::String(..) |
      LispKind::Bool(..) |
      LispKind::Syntax(..) |
      LispKind::Undef => true,
      LispKind::Annot(_, e) => e.small(),
      LispKind::Ref(m) => m.get(|e| e.small()),
    }
  }
}

type PrettyCache<'a> = (LispVal, (Prec, Pp<'a>));

/// A state object for constructing pretty printing nodes `PP<'a>`.
/// All pretty printing nodes will be tied to the lifetime of the struct.
pub struct Pretty<'a> {
  fe: FormatEnv<'a>,
  pub(crate) alloc: &'a Arena<'a>,
  hash: RefCell<HashMap<*const LispKind, PrettyCache<'a>>>,
  lparen: Pp<'a>,
  rparen: Pp<'a>,
}

impl fmt::Debug for Pretty<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "Pretty") }
}

// Previously named str!, which breaks doc links. See rust#81633
macro_rules! s {($s:expr) => {pretty::RefDoc(&pretty::Doc::BorrowedText($s))}}

const NIL: RefDoc<'static> = pretty::RefDoc(&Doc::Nil);
const HARDLINE: RefDoc<'static> = pretty::RefDoc(&Doc::Line);
const SPACE: RefDoc<'static> = s!(" ");
const LINE: RefDoc<'static> = pretty::RefDoc(&pretty::Doc::FlatAlt(HARDLINE, SPACE));
const LINE_: RefDoc<'static> = pretty::RefDoc(&pretty::Doc::FlatAlt(HARDLINE, NIL));
const SOFTLINE: RefDoc<'static> = pretty::RefDoc(&pretty::Doc::Group(LINE));
const SOFTLINE_: RefDoc<'static> = pretty::RefDoc(&pretty::Doc::Group(LINE_));

fn covariant<'a>(from: RefDoc<'static>) -> RefDoc<'a> {
  #[allow(clippy::useless_transmute)]
  unsafe {mem::transmute(from)}
}

impl<'a> Pretty<'a> {
  /// The empty string `""` as a [`RefDoc`](pretty::RefDoc).
  #[must_use] pub fn nil() -> RefDoc<'a> {covariant(NIL)}
  // fn hardline() -> RefDoc<'a> {covariant(HARDLINE)}
  fn space() -> RefDoc<'a> {covariant(SPACE)}
  fn line() -> RefDoc<'a> {covariant(LINE)}
  // fn line_() -> RefDoc<'a> {covariant(LINE_)}
  fn softline() -> RefDoc<'a> {covariant(SOFTLINE)}
  fn softline_() -> RefDoc<'a> {covariant(SOFTLINE_)}

  fn new(fe: FormatEnv<'a>, alloc: &'a Arena<'a>) -> Pretty<'a> {
    Pretty {
      lparen: Pp::token(alloc, fe.env, "("),
      rparen: Pp::token(alloc, fe.env, ")"),
      fe, alloc, hash: RefCell::new(HashMap::new())
    }
  }

  fn token(&'a self, tk: &'a [u8]) -> Pp<'a> {
    Pp::token(self.alloc, &self.fe, unsafe {std::str::from_utf8_unchecked(tk)})
  }
  fn word(&'a self, data: &'a [u8]) -> Pp<'a> {
    Pp::word(self.alloc, unsafe {std::str::from_utf8_unchecked(data)})
  }

  pub(crate) fn alloc(&'a self, doc: Doc<'a>) -> RefDoc<'a> {
    self.alloc.alloc(doc)
  }

  pub(crate) fn append_doc(&'a self, a: impl Into<RefDoc<'a>>, b: impl Into<RefDoc<'a>>) -> RefDoc<'a> {
    self.alloc(Doc::Append(a.into(), b.into()))
  }

  pub(crate) fn annot(&'a self, a: Annot, doc: impl Into<RefDoc<'a>>) -> RefDoc<'a> {
    self.alloc(Doc::Annotated(a, doc.into()))
  }

  pub(crate) fn append_annot(&'a self,
      doc1: impl Into<RefDoc<'a>>, a: Annot, doc: impl Into<RefDoc<'a>>) -> RefDoc<'a> {
    self.append_doc(doc1, self.annot(a, doc))
  }

  fn append_with(&'a self, a: Pp<'a>, sp: RefDoc<'a>, b: Pp<'a>) -> Pp<'a> {
    let (left, right) = (a.left, b.right);
    let doc = self.append_doc(self.append_doc(a, sp), b);
    Pp {left, right, small: false, doc}
  }

  fn append(&'a self, a: Pp<'a>, b: Pp<'a>) -> Pp<'a> {
    let sp = if a.right || b.left {Self::softline_()} else {Self::softline()};
    self.append_with(a, sp, b)
  }

  fn group(&'a self, Pp {left, right, small, doc}: Pp<'a>) -> Pp<'a> {
    Pp {left, right, small, doc: self.alloc(Doc::Group(doc))}
  }

  fn nest(&'a self, i: isize, Pp {left, right, small, doc}: Pp<'a>) -> Pp<'a> {
    Pp {left, right, small, doc: self.alloc(Doc::Nest(i, doc))}
  }

  fn expr_paren(&'a self, e: &LispVal, p: Prec) -> Pp<'a> {
    let (q, doc) = self.pp_expr(e);
    if p > q {
      self.append(self.append(self.lparen, doc), self.rparen)
    } else {doc}
  }

  fn app(&'a self, mut head: Pp<'a>, mut es: impl Iterator<Item=Pp<'a>>) -> Pp<'a> {
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

  fn lit(&'a self, lit: &'a Literal, args: &[LispVal]) -> Pp<'a> {
    match lit {
      &Literal::Var(i, p) => self.expr_paren(&args[i], p),
      Literal::Const(tk) => self.token(tk),
    }
  }

  fn infixl(&'a self, t: TermId, info: &'a NotaInfo, args: &[LispVal]) -> Option<Pp<'a>> {
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

  fn infixr(&'a self, t: TermId, info: &'a NotaInfo, args: &[LispVal]) -> Option<Pp<'a>> {
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

  fn get_term_args(&'a self, e: &LispVal) -> Option<(&'a AtomData, TermId, Vec<LispVal>)> {
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

  /// Pretty-prints a math formula, returning the highest precedence
  /// for which this expression would not need brackets.
  pub(crate) fn pp_expr(&'a self, e: &LispVal) -> (Prec, Pp<'a>) {
    let p: *const LispKind = &**e;
    if let Some(&(_, v1)) = self.hash.borrow().get(&p) {return v1}
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
      if args.is_empty() {
        (Prec::Max, self.word(&ad.name))
      } else {
        (APP_PREC, self.group(self.nest(2, self.app(self.word(&ad.name),
          args.iter().map(|e| self.expr_paren(e, Prec::Max))))))
      }
    }))().unwrap_or_else(|| (Prec::Max, Pp {
      left: false, right: false, small: e.small(),
      doc: self.pp_lisp(e)
    }));
    self.hash.borrow_mut().entry(p).or_insert_with(|| (e.clone(), v)).1
  }

  /// Pretty-prints a math formula surrounded by delimiters.
  pub fn expr_delimited(&'a self, e: &LispVal, left: &'a str, right: &'a str) -> RefDoc<'a> {
    let mut doc = self.expr_paren(e, Prec::Prec(0)).doc;
    if let Doc::Group(doc2) = *doc {doc = doc2}
    let doc = self.append_doc(self.alloc(Doc::text(left)),
      self.append_doc(doc, self.alloc(Doc::text(right))));
    self.alloc(Doc::Group(doc))
  }

  /// Pretty-prints a math formula surrounded by `$` delimiters, as in `$ 2 + 2 = 4 $`.
  pub fn expr(&'a self, e: &LispVal) -> RefDoc<'a> {
    self.expr_delimited(e, "$ ", " $")
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

  fn app_doc(&'a self, mut head: RefDoc<'a>, mut es: impl Iterator<Item=(bool, RefDoc<'a>)>) -> RefDoc<'a> {
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
  pub fn pp_lisp(&'a self, e: &LispVal) -> RefDoc<'a> {
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
          else if u.exactly(0) { return s!("()") }
          else { return self.pp_lisp(&u.into()) }
        };
        for e in &mut u {
          doc = self.append_doc(doc, self.append_doc(Self::line(), self.pp_lisp(&e)));
        }
        if !u.exactly(0) {
          doc = self.append_doc(doc,
            self.append_doc(s!(" ."),
              self.append_doc(Self::line(), self.pp_lisp(&u.into()))));
        }
        let doc = self.append_doc(self.lparen, self.append_doc(doc, self.rparen));
        self.alloc(Doc::Group(self.alloc(Doc::Nest(2, doc))))
      }
      _ => self.alloc(Doc::text(format!("{}", self.fe.to(e)))),
    })
  }

  fn dep_type(&'a self, bvars: &[AtomId], ds: u64, mut doc: RefDoc<'a>) -> RefDoc<'a> {
    let mut i = 1;
    for x in bvars {
      if ds & i != 0 {
        let rhs = Doc::text(format!(" {}", self.fe.to(x)));
        doc = self.append_doc(doc, self.alloc(rhs));
      }
      i *= 2;
    }
    doc
  }

  fn grouped_binders(&'a self, mut doc: RefDoc<'a>,
    bis: &[(Option<AtomId>, Type)], bvars: &mut Vec<AtomId>) -> RefDoc<'a> {
    let mut rest = bis;
    loop {
      let mut it = rest.iter();
      let ty = match it.next() {
        None => return doc,
        Some((_, ty)) => ty,
      };
      let (bis1, bis2) = rest.split_at(it.position(|(_, ty2)| ty != ty2).map_or(rest.len(), |x| x + 1));
      let mut buf = Self::nil();
      match *ty {
        Type::Bound(s) => {
          buf = self.append_doc(buf, s!("{"));
          let lhs = format!("{}", bis1.iter().map(|(a, _)| {
            bvars.push(a.unwrap_or(AtomId::UNDER));
            self.fe.to(a)
          }).format(" "));
          buf = self.append_doc(buf, self.alloc(Doc::text(lhs)));
          buf = self.append_doc(buf, s!(": "));
          buf = self.append_annot(buf, Annot::SortName(s),
            self.alloc(Doc::text(self.fe.env.sorts[s].name.to_string())));
          buf = self.append_doc(buf, s!("}"));
        }
        Type::Reg(s, ds) => {
          buf = self.append_doc(buf, s!("("));
          let lhs = format!("{}", bis1.iter().map(|(a, _)| self.fe.to(a)).format(" "));
          buf = self.append_doc(buf, self.alloc(Doc::text(lhs)));
          buf = self.append_doc(buf, s!(": "));
          buf = self.append_annot(buf, Annot::SortName(s),
            self.alloc(Doc::text(self.fe.env.sorts[s].name.to_string())));
          buf = self.dep_type(bvars, ds, buf);
          buf = self.append_doc(buf, s!(")"));
        }
      }
      doc = self.append_doc(doc, self.append_doc(Self::softline(), buf));
      rest = bis2;
    }
  }

  /// Pretty-prints a `term` or `def` declaration, for example
  /// `def foo (x y: nat): nat = $ x + y $;`.
  pub fn term(&'a self, tid: TermId, show_def: bool) -> RefDoc<'a> {
    let t = &self.fe.env.terms[tid];
    let mut doc = self.annot(Annot::Keyword,
      if matches!(t.kind, TermKind::Term) {s!("term")} else {s!("def")});
    if !t.vis.is_empty() {
      doc = self.append_doc(self.annot(Annot::Visibility(t.vis),
        self.alloc(Doc::text(t.vis.to_string()))), doc);
    }
    let doc = self.append_doc(doc, Self::space());
    let doc = self.append_annot(doc, Annot::TermName(tid),
      self.alloc(Doc::text(format!("{}", self.fe.to(&t.atom)))));
    let mut bvars = vec![];
    let doc = self.grouped_binders(doc, &t.args, &mut bvars);
    let doc = self.append_doc(doc, s!(":"));
    let doc = self.alloc(Doc::Group(doc));
    let mut buf = self.annot(
      Annot::SortName(t.ret.0),
      self.alloc(Doc::text(self.fe.env.sorts[t.ret.0].name.to_string()))
    );
    buf = self.dep_type(&bvars, t.ret.1, buf);
    if let (true, TermKind::Def(Some(expr))) = (show_def, &t.kind) {
      buf = self.append_doc(buf, s!(" ="));
      let doc = self.append_doc(doc, self.append_doc(Self::softline(), buf));
      let mut bvars = Vec::new();
      let mut heap = Vec::new();
      self.fe.binders(&t.args, &mut heap, &mut bvars);
      for e in &expr.heap[heap.len()..] {
        let e = self.fe.expr_node(&heap, &mut None, e);
        heap.push(e)
      }
      let val = &self.fe.expr_node(&heap, &mut None, &expr.head);
      let doc = self.append_doc(doc, self.append_doc(Self::line(),
        self.expr_delimited(val, "$ ", " $;")));
      self.alloc(Doc::Group(doc))
    } else {
      buf = self.append_doc(buf, s!(";"));
      self.append_doc(doc, self.append_doc(Self::softline(), buf))
    }
  }

  /// Pretty-prints the hypotheses and return of an `axiom` or `theorem`, for example
  /// `$ a $ > $ a -> b $ > $ b $`. This is appended to the input `doc` on the right.
  pub fn hyps_and_ret(&'a self, mut doc: RefDoc<'a>,
      hs: impl Iterator<Item=LispVal>, ret: &LispVal) -> RefDoc<'a> {
    for e in hs {
      doc = self.append_doc(doc,
        self.append_doc(self.expr(&e),
          self.append_doc(s!(" >"), Self::line())));
    }
    self.append_doc(doc, self.expr(ret))
  }

  /// Pretty print a sort, with annotations.
  /// Basic form is just `<modifiers> sort <name>;`
  pub fn sort(&'a self, sid: SortId) -> RefDoc<'a> {
    let s = &self.fe.env.sorts[sid];
    let mut doc = self.annot(Annot::SortModifiers(s.mods),
      self.alloc(Doc::text(s.mods.to_string())));
    doc = self.append_annot(doc, Annot::Keyword, s!("sort"));
    doc = self.append_doc(doc, Self::space());
    doc = self.append_annot(doc, Annot::SortName(sid),
      self.alloc(Doc::text(s.name.as_str())));
    self.append_doc(doc, s!(";"))
  }

  /// Pretty-prints an `axiom` or `theorem` declaration, for example
  /// `theorem mp (a b: wff): $ a $ > $ a -> b $ > $ b $;`.
  /// The proof of the theorem is omitted.
  pub fn thm(&'a self, tid: ThmId) -> RefDoc<'a> {
    let t = &self.fe.env.thms[tid];
    let doc = self.annot(Annot::Visibility(t.vis),
      self.alloc(Doc::text(t.vis.to_string())));
    let doc = self.append_annot(doc, Annot::Keyword,
      if matches!(t.kind, ThmKind::Axiom) {s!("axiom")} else {s!("theorem")});
    let doc = self.append_doc(doc, Self::space());
    let doc = self.append_annot(doc, Annot::ThmName(tid),
      self.alloc(Doc::text(format!("{}", self.fe.to(&t.atom)))));
    let mut bvars = vec![];
    let doc = self.grouped_binders(doc, &t.args, &mut bvars);
    let doc = self.append_doc(doc, s!(":"));
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
    let doc = self.append_doc(doc, s!(";"));
    self.alloc(Doc::Group(self.alloc(Doc::Nest(2, doc))))
  }

  /// Pretty-prints a unification error, as `failed to unify: e1 =?= e2`.
  pub fn unify_err(&'a self, e1: &LispVal, e2: &LispVal) -> RefDoc<'a> {
    let doc = self.append_doc(s!("failed to unify:"), Self::line());
    let doc = self.append_doc(doc, self.expr_paren(e1, Prec::Prec(0)));
    let doc = self.append_doc(doc, self.alloc(Doc::Nest(2,
      self.append_doc(Self::line(), s!("=?=")))));
    let doc = self.append_doc(doc, Pretty::line());
    let doc = self.append_doc(doc, self.expr_paren(e2, Prec::Prec(0)));
    self.alloc(Doc::Group(doc))
  }
}

/// A struct that can be used to display a [`LispVal`] representing a math expression.
#[derive(Debug)]
pub struct PpExpr<'a> {
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
  #[must_use] pub fn pp(self, e: &'a LispVal, width: usize) -> PpExpr<'a> {
    PpExpr {fe: self, e, width}
  }
}

impl<'a> fmt::Display for PpExpr<'a> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.fe.pretty(|p| p.pp_expr(self.e).1.doc.render_fmt(self.width, f))
  }
}
