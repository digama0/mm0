//! Pretty printer for math formulas and lisp terms.
//!
//! The main interface is the [`FormatEnv::pretty`] function, which provides a
//! [`Pretty`] arena on which various methods exist to print different kinds of object.

use std::collections::HashMap;
use std::cell::RefCell;
use std::{mem, fmt};
use std::borrow::Cow;
use mm0_util::ArcString;
use pretty::DocAllocator;
use itertools::Itertools;
use if_chain::if_chain;
use crate::{LispVal, LispKind, Uncons, FormatEnv,
  Prec, DeclKey, Literal, TermKind, ThmKind, Modifiers,
  Environment, NotaInfo, AtomData, AtomId, TermId, ThmId, SortId, Thm, Type,
  APP_PREC, ExprNode};

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
  /// This is a precedence, like `23` or `max`.
  Prec,
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
      doc: alloc.alloc(Doc::BorrowedText(tk)),
    }
  }

  fn word(alloc: &'a Arena<'a>, data: impl Into<Cow<'a, str>>) -> Pp<'a> {
    Pp {
      left: false,
      right: false,
      small: true,
      doc: alloc.text(data).into_doc(),
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
const HARDLINE: RefDoc<'static> = pretty::RefDoc(&Doc::Hardline);
const SPACE: RefDoc<'static> = s!(" ");
const LINE: RefDoc<'static> = pretty::RefDoc(&pretty::Doc::FlatAlt(HARDLINE, SPACE));
const LINE_: RefDoc<'static> = pretty::RefDoc(&pretty::Doc::FlatAlt(HARDLINE, NIL));
const SOFTLINE: RefDoc<'static> = pretty::RefDoc(&pretty::Doc::Group(LINE));
const SOFTLINE_: RefDoc<'static> = pretty::RefDoc(&pretty::Doc::Group(LINE_));

fn covariant<'a>(from: RefDoc<'static>) -> RefDoc<'a> {
  #[allow(clippy::useless_transmute)]
  // Safety: `RefDoc` is actually covariant. Rust is unable to prove this because of the
  // Doc::Column and Doc::Nesting variants, which contain
  // &'a (dyn Fn(usize) -> RefDoc<'a, _> + 'a), which is covariant
  // in 'a even though rust doesn't try to reason about the changing return type.
  unsafe { mem::transmute(from) }
}

impl<'a> Pretty<'a> {
  /// The empty string `""` as a [`RefDoc`](pretty::RefDoc).
  #[must_use] pub fn nil() -> RefDoc<'a> {covariant(NIL)}
  fn hardline() -> RefDoc<'a> {covariant(HARDLINE)}
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
    // Safety: Tokens come from the ASCII text
    Pp::token(self.alloc, &self.fe, unsafe { std::str::from_utf8_unchecked(tk) })
  }
  fn word(&'a self, data: &'a [u8]) -> Pp<'a> {
    // Safety: Words come from the ASCII text
    Pp::word(self.alloc, unsafe { std::str::from_utf8_unchecked(data) })
  }

  pub(crate) fn alloc(&'a self, doc: Doc<'a>) -> RefDoc<'a> {
    self.alloc.alloc(doc)
  }

  pub(crate) fn text(&'a self, data: impl Into<Cow<'a, str>>) -> RefDoc<'a> {
    self.alloc.text(data).into_doc()
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

  fn append_lit(&'a self, doc: Pp<'a>, lit: &'a Literal, args: &[LispVal]) -> Pp<'a> {
    let doc2 = self.lit(lit, args);
    // HACK to make `a, b` look better as a binop
    let punct = matches!(lit, Literal::Const(tk) if matches!(&**tk, b"," | b";" | b"." | b":"));
    let sp = if punct && (doc.right || doc2.left) {Self::softline_()} else {Self::softline()};
    self.append_with(doc, sp, self.lit(lit, args))
  }

  fn infixl(&'a self, t: TermId, info: &'a NotaInfo, args: &[LispVal]) -> Option<Pp<'a>> {
    if let Literal::Var(i, q) = info.lits[0] {
      let doc = match self.get_term_args(&args[i]) {
        Some((_, t2, args2)) if t == t2 => self.infixl(t, info, &args2),
        _ => None,
      }.unwrap_or_else(|| self.group(self.expr_paren(&args[i], q)));
      let mut doc = self.append_lit(doc, &info.lits[1], args);
      if let Some((last, most)) = info.lits[2..].split_last() {
        for lit in most {doc = self.append(doc, self.group(self.lit(lit, args)))}
        doc = self.append_with(doc, Self::line(), self.group(self.lit(last, args)))
      };
      Some(doc)
    } else {None}
  }

  fn infixr(&'a self, t: TermId, info: &'a NotaInfo, args: &[LispVal]) -> Option<Pp<'a>> {
    let doc = self.lit(&info.lits[0], args);
    let mut doc = self.append_lit(doc, &info.lits[1], args);
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
    let Some(DeclKey::Term(t)) = ad.decl else { return None };
    let mut args = vec![];
    let nargs = env.terms[t].args.len();
    if !u.exactly(nargs) { return None }
    u.extend_into(nargs, &mut args);
    Some((ad, t, args))
  }

  /// Pretty-prints a math formula, returning the highest precedence
  /// for which this expression would not need brackets.
  pub(crate) fn pp_expr(&'a self, e: &LispVal) -> (Prec, Pp<'a>) {
    let p: *const LispKind = &**e;
    if let Some(&(_, v1)) = self.hash.borrow().get(&p) { return v1 }
    let v = (|| Some({
      let env = self.fe.env;
      let (ad, t, args) = self.get_term_args(e)?;
      if let Some(&(coe, ref fix)) = env.pe.decl_nota.get(&t) {
        if coe { return Some(self.pp_expr(&args[0])) }
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

  /// Pretty-prints a math formula without delimiters, as in `2 + 2 = 4`.
  pub fn expr_no_delim(&'a self, e: &LispVal) -> RefDoc<'a> {
    self.expr_paren(e, Prec::Prec(0)).doc
  }

  /// Pretty-prints a math formula surrounded by delimiters.
  pub fn expr_delimited(&'a self, e: &LispVal, left: &'a str, right: &'a str) -> RefDoc<'a> {
    let mut doc = self.expr_no_delim(e);
    if let Doc::Group(doc2) = *doc {doc = doc2}
    let doc = self.append_doc(self.text(left), self.append_doc(doc, self.text(right)));
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
      _ => self.text(format!("{}", self.fe.to(e))),
    })
  }

  fn dep_type(&'a self, bvars: &[AtomId], ds: u64, mut doc: RefDoc<'a>) -> RefDoc<'a> {
    let mut i = 1;
    for x in bvars {
      if ds & i != 0 {
        let rhs = format!(" {}", self.fe.to(x));
        doc = self.append_doc(doc, self.text(rhs));
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
      let Some((_, ty)) = it.next() else { return doc };
      let (bis1, bis2) = rest.split_at(it.position(|(_, ty2)| ty != ty2).map_or(rest.len(), |x| x + 1));
      let mut buf = Self::nil();
      match *ty {
        Type::Bound(s) => {
          buf = self.append_doc(buf, s!("{"));
          let lhs = format!("{}", bis1.iter().map(|(a, _)| {
            bvars.push(a.unwrap_or(AtomId::UNDER));
            self.fe.to(a)
          }).format(" "));
          buf = self.append_doc(buf, self.text(lhs));
          buf = self.append_doc(buf, s!(": "));
          buf = self.append_annot(buf, Annot::SortName(s),
            self.text(self.fe.env.sorts[s].name.to_string()));
          buf = self.append_doc(buf, s!("}"));
        }
        Type::Reg(s, ds) => {
          buf = self.append_doc(buf, s!("("));
          let lhs = format!("{}", bis1.iter().map(|(a, _)| self.fe.to(a)).format(" "));
          buf = self.append_doc(buf, self.text(lhs));
          buf = self.append_doc(buf, s!(": "));
          buf = self.append_annot(buf, Annot::SortName(s),
            self.text(self.fe.env.sorts[s].name.to_string()));
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
        self.text(t.vis.to_string())), doc);
    }
    let doc = self.append_doc(doc, Self::space());
    let doc = self.append_annot(doc, Annot::TermName(tid),
      self.text(format!("{}", self.fe.to(&t.atom))));
    let mut bvars = vec![];
    let doc = self.grouped_binders(doc, &t.args, &mut bvars);
    let doc = self.append_doc(doc, s!(":"));
    let doc = self.alloc(Doc::Group(doc));
    let mut buf = self.annot(
      Annot::SortName(t.ret.0),
      self.text(self.fe.env.sorts[t.ret.0].name.to_string())
    );
    buf = self.dep_type(&bvars, t.ret.1, buf);
    if let (true, TermKind::Def(Some(expr))) = (show_def, &t.kind) {
      buf = self.append_doc(buf, s!(" ="));
      let doc = self.append_doc(doc, self.append_doc(Self::softline(), buf));
      let mut bvars = Vec::new();
      let mut heap = Vec::new();
      self.fe.binders(&t.args, &mut heap, &mut bvars);
      for e in &expr.heap[heap.len()..] {
        let e = self.fe.expr_node(&heap, &mut None, &expr.store, e);
        heap.push(e)
      }
      let val = &self.fe.expr_node(&heap, &mut None, &expr.store, expr.head());
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
      self.text(s.mods.to_string()));
    doc = self.append_annot(doc, Annot::Keyword, s!("sort"));
    doc = self.append_doc(doc, Self::space());
    doc = self.append_annot(doc, Annot::SortName(sid),
      self.text(s.name.as_str()));
    self.append_doc(doc, s!(";"))
  }

  /// Pretty print a coercion declaration, with annotations, that is:
  ///`coercion <name>: <sort> > <sort>;`.
  /// Panics if the term is not a coercion.
  pub fn coercion(&'a self, tid: TermId) -> RefDoc<'a> {
    let t = &self.fe.env.terms[tid];
    let doc = self.annot(Annot::Keyword, s!("coercion"));
    let doc = self.append_doc(doc, Self::space());
    let doc = self.append_annot(doc, Annot::TermName(tid),
      self.text(format!("{}", self.fe.to(&t.atom))));
    let doc = self.append_doc(doc, s!(": "));
    let [(_, Type::Reg(ty, 0))] = *t.args else { panic!("not a coercion") };
    let doc = self.append_annot(doc, Annot::SortName(ty),
      self.text(self.fe.env.sorts[ty].name.to_string()));
    let doc = self.append_doc(doc, s!(" > "));
    let doc = self.append_annot(doc, Annot::SortName(t.ret.0),
      self.text(self.fe.env.sorts[t.ret.0].name.to_string()));
    self.append_doc(doc, s!(";"))
  }

  /// Pretty print a simple notation declaration, with annotations, that is:
  ///`infix <name>: $<const>$ prec <n>;`.
  pub fn simple_nota(&'a self,
    tid: TermId, kw: RefDoc<'a>, tk: &ArcString, prec: Prec
  ) -> RefDoc<'a> {
    let t = &self.fe.env.terms[tid];
    let doc = self.annot(Annot::Keyword, kw);
    let doc = self.append_doc(doc, Self::space());
    let doc = self.append_annot(doc, Annot::TermName(tid),
      self.text(format!("{}", self.fe.to(&t.atom))));
    let doc = self.append_doc(doc, s!(": $"));
    let doc = self.append_annot(doc, Annot::TermName(tid), self.text(format!("{tk}")));
    let doc = self.append_doc(doc, s!("$ "));
    let doc = self.append_annot(doc, Annot::Keyword, s!("prec"));
    let doc = self.append_doc(doc, Self::space());
    let doc = self.append_annot(doc, Annot::Prec, self.text(format!("{prec}")));
    self.append_doc(doc, s!(";"))
  }

  /// Print a constant notation literal like `($e.$:23)`.
  fn const_lit(&'a self, tk: &ArcString) -> RefDoc<'a> {
    let doc = self.text(format!("${tk}$:"));
    let doc = self.append_annot(doc, Annot::Prec,
      self.text(format!("{}", self.fe.env.pe.consts[tk].1)));
    self.append_doc(self.append_doc(self.lparen, doc), self.rparen)
  }

  /// Pretty print a notation declaration, with annotations, e.g.
  /// `notation foo (x y: nat): nat = ($FOO$:2) x ($,$:max) y: <n> rassoc;`.
  pub fn notation(&'a self, nota: &NotaInfo, prefix: Option<&ArcString>) -> RefDoc<'a> {
    if let Some(tk) = prefix {
      let prec = self.fe.env.pe.consts[tk].1;
      if nota.is_prefix(prec) {
        return self.simple_nota(nota.term, s!("prefix"), tk, prec)
      }
    } else if let Some((rassoc, tk, prec)) = nota.is_infix() {
      let kw = if rassoc {s!("infixr")} else {s!("infixl")};
      return self.simple_nota(nota.term, kw, tk, Prec::Prec(prec))
    }
    let t = &self.fe.env.terms[nota.term];
    let doc = self.annot(Annot::Keyword, s!("notation"));
    let doc = self.append_doc(doc, Self::space());
    let doc = self.append_annot(doc, Annot::TermName(nota.term),
      self.text(format!("{}", self.fe.to(&t.atom))));
    let mut bvars = vec![];
    let doc = self.grouped_binders(doc, &t.args, &mut bvars);
    let doc = self.append_doc(doc, s!(":"));
    let doc = self.alloc(Doc::Group(doc));
    let doc = self.append_doc(doc, Self::softline());
    let doc = self.append_annot(doc, Annot::SortName(t.ret.0),
      self.text(self.fe.env.sorts[t.ret.0].name.to_string()));
    let doc = self.dep_type(&bvars, t.ret.1, doc);
    let doc = self.append_doc(doc, s!(" ="));
    let doc = self.alloc(Doc::Group(doc));
    let mut buf = None;
    let mut push_doc = |doc| match buf {
      Some(ref mut buf) => *buf = self.append_doc(*buf, self.append_doc(Self::softline(), doc)),
      None => buf = Some(doc),
    };
    if let Some(tk) = prefix { push_doc(self.const_lit(tk)) }
    for lit in &nota.lits {
      push_doc(match lit {
        &Literal::Var(i, _) => {
          let a = t.args[i].0.unwrap_or(AtomId::UNDER);
          self.text(self.fe.env.data[a].name.to_string())
        }
        Literal::Const(tk) => self.const_lit(tk)
      })
    }
    let mut buf = buf.expect("bad notation");
    if_chain! {
      if prefix.is_none();
      if let Some(&Literal::Var(_, prec1)) = nota.lits.first();
      if let Some(&Literal::Var(_, prec2)) = nota.lits.last();
      if let Some(rassoc) = nota.rassoc;
      then {
        let doc = self.append_doc(doc, s!(":"));
        let doc = self.alloc(Doc::Group(doc));
        let doc = self.append_doc(doc, Self::line());
        let doc = self.append_annot(doc, Annot::Prec,
          self.text(format!("{}", if rassoc {prec2} else {prec1})));
        let doc = self.append_doc(doc, Self::space());
        buf = self.append_annot(doc, Annot::Keyword, if rassoc {s!("rassoc")} else {s!("lassoc")});
      }
    }
    let buf = self.alloc(Doc::Group(self.append_doc(buf, s!(";"))));
    let doc = self.append_doc(doc, self.append_doc(Self::line(), buf));
    self.alloc(Doc::Group(doc))
  }

  /// Pretty-prints a `term` or `def` declaration, followed by any applicable notations for it.
  pub fn term_and_notations(&'a self, tid: TermId, show_def: bool) -> RefDoc<'a> {
    let mut doc = self.term(tid, show_def);
    if let Some(&(coe, ref fix)) = self.fe.env.pe.decl_nota.get(&tid) {
      if coe {
        doc = self.append_doc(doc, self.append_doc(Self::hardline(), self.coercion(tid)))
      }
      for &(ref tk, infix) in fix {
        let (prefix, nota) = if infix {
          (None, &self.fe.env.pe.infixes[tk])
        } else {
          (Some(tk), &self.fe.env.pe.prefixes[tk])
        };
        doc = self.append_doc(doc, self.append_doc(Self::hardline(), self.notation(nota, prefix)))
      }
    }
    doc
  }

  /// Pretty-prints an `axiom` or `theorem` declaration, for example
  /// `theorem mp (a b: wff): $ a $ > $ a -> b $ > $ b $;`.
  /// The proof of the theorem is omitted.
  pub fn thm(&'a self, tid: ThmId) -> RefDoc<'a> {
    let t = &self.fe.env.thms[tid];
    let doc = self.annot(Annot::Visibility(t.vis), self.text(t.vis.to_string()));
    let doc = self.append_annot(doc, Annot::Keyword,
      if matches!(t.kind, ThmKind::Axiom) {s!("axiom")} else {s!("theorem")});
    let doc = self.append_doc(doc, Self::space());
    let doc = self.append_annot(doc, Annot::ThmName(tid),
      self.text(format!("{}", self.fe.to(&t.atom))));
    let mut bvars = vec![];
    let doc = self.grouped_binders(doc, &t.args, &mut bvars);
    let doc = self.append_doc(doc, s!(":"));
    let doc = self.append_doc(self.alloc(Doc::Group(doc)), Self::line());
    let mut bvars = Vec::new();
    let mut heap = Vec::new();
    self.fe.binders(&t.args, &mut heap, &mut bvars);
    for e in &t.heap[heap.len()..] {
      let e = self.fe.expr_node(&heap, &mut None, &t.store, e);
      heap.push(e)
    }
    let doc = self.hyps_and_ret(doc,
      t.hyps.iter().map(|(_, e)| self.fe.expr_node(&heap, &mut None, &t.store, e)),
      &self.fe.expr_node(&heap, &mut None, &t.store, &t.ret));
    let doc = self.append_doc(doc, s!(";"));
    self.alloc(Doc::Group(self.alloc(Doc::Nest(2, doc))))
  }

  /// Pretty-prints a unification error, as `failed to unify: e1 =?= e2`.
  pub fn unify_err(&'a self, e1: &LispVal, e2: &LispVal) -> RefDoc<'a> {
    let doc = self.append_doc(s!("failed to unify:"), Self::line());
    let doc = self.append_doc(doc, self.expr_no_delim(e1));
    let doc = self.append_doc(doc, self.alloc(Doc::Nest(2,
      self.append_doc(Self::line(), s!("=?=")))));
    let doc = self.append_doc(doc, Self::line());
    let doc = self.append_doc(doc, self.expr_no_delim(e2));
    self.alloc(Doc::Group(doc))
  }

  /// Pretty prints a verification error that looks like:
  /// ```text
  /// Subproof 2 of
  ///   (foo x y): $ A $ > $ B $ > $ C $
  /// proved
  ///   $ B' $
  /// but was supposed to prove
  ///   $ B $
  /// ```
  pub fn verify_subst_err(&'a self,
    i: Option<usize>, lisp_args: &[LispVal], proved: &LispVal, td: &Thm,
    mut subst: impl FnMut(&ExprNode) -> LispVal,
  ) -> RefDoc<'a> {
    let mut args1 = vec![LispVal::atom(td.atom)];
    args1.extend(lisp_args.iter().cloned());
    let subst_hyps = td.hyps.iter()
      .map(|(_, e)| self.expr(&subst(e))).collect::<Box<[_]>>();
    let subst_ret = self.expr(&subst(&td.ret));
    let (msg1, e1, e2) = if let Some(i) = i {
      (self.text(format!("Subproof {} of", i+1)), self.expr(proved), subst_hyps[i])
    } else {
      (s!("Theorem application"), subst_ret, self.expr(proved))
    };

    let doc = self.expr_no_delim(&LispVal::list(args1));
    let doc = self.append_doc(self.alloc(Doc::Group(doc)), s!(":"));
    let mut doc = self.append_doc(doc, Self::line());
    for &e in &*subst_hyps {
      doc = self.append_doc(doc, self.append_doc(e, self.append_doc(s!(" >"), Self::line())));
    }
    let doc = self.alloc(Doc::Group(self.append_doc(doc, subst_ret)));
    let msg = self.alloc(Doc::Nest(2, self.append_doc(msg1, self.append_doc(Self::line(), doc))));
    let msg1 = s!("proved");
    let msg = self.append_doc(self.append_doc(msg, Self::line()),
      self.alloc(Doc::Nest(2, self.append_doc(msg1, self.append_doc(Self::line(), e1)))));
    let msg1 = s!("but was supposed to prove");
    self.append_doc(self.append_doc(msg, Self::line()),
      self.alloc(Doc::Nest(2, self.append_doc(msg1, self.append_doc(Self::line(), e2)))))
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
