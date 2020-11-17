//! The lisp parser, which takes (already parsed) s-exprs and puts them into an
//! intermediate representation suitable for interpretation (doing as many
//! static checks as we can beforehand).

use std::ops::{Deref, DerefMut};
use std::sync::Arc;
use std::collections::HashMap;
use num::{BigInt, ToPrimitive};
use itertools::Itertools;
use crate::parser::ast::{SExpr, SExprKind, Atom};
use crate::util::ArcString;
use super::super::{AtomID, Span, DocComment, Elaborator, ElabError, ObjectKind};
use super::*;
use super::super::math_parser::{QExpr, QExprKind};
use super::print::{FormatEnv, EnvDisplay};

/// The intermediate representation for "compiled" lisp functions.
/// We will do interpretation/evaluation directly on this data structure.
#[derive(Debug, EnvDebug, DeepSizeOf)]
pub enum IR {
  /// Access variable number `n` in the context
  Local(usize),
  /// Access a global declaration named `a`
  Global(Span, AtomID),
  /// Return a `LispVal` literally
  Const(LispVal),
  /// The `(list)` function: evaluate the list of arguments,
  /// and then create a list from the results.
  List(Span, Box<[IR]>),
  /// The `(cons)` function: evaluate the list of arguments, then the last argument,
  /// and then create a dotted list from the results.
  DottedList(Box<[IR]>, Box<IR>),
  /// Function application: evaluate the first argument to produce a procedure,
  /// evaluate the list of arguments, then call the procedure with the list of results.
  App(Span, Span, Box<IR>, Box<[IR]>),
  /// The `(if c t f)` syntax form: evaluate the condition `c`, and if the result is
  /// truthy evaluate `t`, else evaluate `f`, and return the result.
  If(Box<(IR, IR, IR)>),
  /// The `(focus es)` syntax form. This should be a regular function, but it does some
  /// preparation work before it starts executing the list of arguments.
  Focus(Span, Box<[IR]>),
  /// The `(def x e)` syntax form. Call the argument, and extend the context with the result.
  /// The `usize` argument indicates the number of the variable that was just declared,
  /// but it is only there for sanity checking - there is only one valid value for this field.
  /// The argument `(sp1, sp2, a)` has `sp1` as the full span of the `(def)` and `sp2` as
  /// the span of the variable `a`.
  ///
  /// (Some definitions are added by the compiler and have no source text.)
  Def(usize, Option<(Span, Span, Option<DocComment>, AtomID)>, Box<IR>),
  /// * `keep = true`: The `(begin es)` syntax form.
  ///   Evaluate the list of arguments, and return the last one.
  ///
  ///   Most places in the surface syntax that allow begin-lists, like `(def x foo bar)`,
  ///   elaborate to essentially `Def(x, Eval(false, true, [foo, bar]))`.
  ///
  /// * `keep = false`: The `(def _ es)` syntax form.
  ///   Evaluate the list of arguments, and return `#undef`. Unlike `(def x es)`,
  ///   this does not extend the context, i.e. it does not bind any variables.
  Eval(bool, Box<[IR]>),
  /// A tail recursion barrier. This is needed in letrec compilation in order to prop up
  /// the weak references to the functions.
  NoTailRec,
  /// The `(fn xs e)` syntax form. Create a closure from the current context, and return
  /// it, using the provided `ProcSpec` and code. It can later be called by the `App` instruction.
  Lambda(Span, usize, ProcSpec, Arc<IR>),
  /// The `(match e bs)` syntax form. Evaluate `e`, and then match it against the branches.
  Match(Span, Box<IR>, Box<[Branch]>),
}

impl<'a> EnvDisplay for IR {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      &IR::Local(i) => write!(f, "x{}", i),
      &IR::Global(_, a) => a.fmt(fe, f),
      IR::Const(e) => e.fmt(fe, f),
      IR::List(_, es) => write!(f, "(list {})", es.iter().map(|ir| fe.to(ir)).format(" ")),
      IR::DottedList(es, r) => write!(f, "(cons {})",
        es.iter().chain(Some(&**r)).map(|ir| fe.to(ir)).format(" ")),
      IR::App(_, _, e, es) => write!(f, "({})",
        Some(&**e).into_iter().chain(&**es).map(|ir| fe.to(ir)).format(" ")),
      IR::If(es) => write!(f, "(if {} {} {})",
        fe.to(&es.0), fe.to(&es.1), fe.to(&es.2)),
      IR::Focus(_, es) => write!(f, "(focus {})", es.iter().map(|ir| fe.to(ir)).format(" ")),
      IR::NoTailRec => write!(f, "(no-tail-rec)"),
      IR::Def(n, a, e) => write!(f, "(def {}:{} {})",
        n, fe.to(&a.as_ref().map_or(AtomID::UNDER, |&(_, _, _, a)| a)), fe.to(e)),
      IR::Eval(false, es) => write!(f, "(def _ {})", es.iter().map(|ir| fe.to(ir)).format(" ")),
      IR::Eval(true, es) => write!(f, "(begin {})", es.iter().map(|ir| fe.to(ir)).format(" ")),
      IR::Lambda(_, n, sp, e) => {
        write!(f, "(lambda {}:", n)?;
        match sp {
          ProcSpec::Exact(n) => write!(f, "{}", n)?,
          ProcSpec::AtLeast(n) => write!(f, "{}+", n)?,
        }
        write!(f, " {})", fe.to(e))
      }
      IR::Match(_, e, bs) => write!(f, "(match {} {})", fe.to(e), fe.to(&**bs))
    }
  }
}

impl IR {
  fn eval(es: impl Into<Box<[IR]>>) -> IR {
    let es: Box<[IR]> = es.into();
    match es.len() {
      0 => IR::Const(LispVal::undef()),
      1 => es.into_vec().swap_remove(0),
      _ => IR::Eval(true, es)
    }
  }

  fn builtin_app(sp1: Span, sp2: Span, f: BuiltinProc, es: Box<[IR]>) -> IR {
    IR::App(sp1, sp2, Box::new(IR::Const(LispVal::proc(Proc::Builtin(f)))), es)
  }

  fn new_ref(sp1: Span, sp2: Span, e: IR) -> IR {
    IR::builtin_app(sp1, sp2, BuiltinProc::NewRef, Box::new([e]))
  }
  fn set_weak(sp1: Span, sp2: Span, e1: IR, e2: IR) -> IR {
    IR::builtin_app(sp1, sp2, BuiltinProc::SetWeak, Box::new([e1, e2]))
  }
  fn match_fn_body(sp: Span, i: usize, brs: Box<[Branch]>) -> IR {
    IR::Match(sp, Box::new(IR::Local(i)), brs)
  }

  /// The span of a code segment.
  pub fn span(&self) -> Option<Span> {
    match self {
      &IR::Global(sp, _) |
      &IR::List(sp, _) |
      &IR::App(sp, _, _, _) |
      &IR::Focus(sp, _) |
      &IR::Lambda(sp, _, _, _) |
      &IR::Match(sp, _, _) => Some(sp),
      _ => None
    }
  }
}

/// A single match branch. Branches can look like:
///
/// * `[pat eval]`: Matches the input against the pattern, binding variables that are used in `eval`.
/// * `[pat (=> cont) eval]`: same thing, but `cont` is bound to a delimited continuation
///   that can be used to jump to the next case (essentially indicating that the branch fails to
///   apply even after the pattern succeeds).
#[derive(Debug, EnvDebug, DeepSizeOf)]
pub struct Branch {
  /// The number of variables in the pattern. The context for `eval` is extended by this many variables
  /// regardless of the input at runtime. For example the pattern `(or ('foo a _) ('bar _ b))` will
  /// always bind variables `a` and `b` (so `vars = 2` here), and the one that is not matched in a
  /// given case will be `#undef`.
  pub vars: usize,
  /// True if the branch includes `(=> cont)`, in which case the context will be extended by the
  /// branch failure continuation.
  pub cont: bool,
  /// The pattern to match against.
  pub pat: Pattern,
  /// The expression to evaluate with the result of the match.
  pub eval: Box<IR>,
}

impl<'a> EnvDisplay for Branch {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    if self.cont {
      write!(f, "[{} (=> _) {}]", fe.to(&self.pat), fe.to(&self.eval))
    } else {
      write!(f, "[{} {}]", fe.to(&self.pat), fe.to(&self.eval))
    }
  }
}

/// A pattern, used in `match`. Patterns match against an input expression, and bind
/// a compile-time known set of variables that can be referred to in the branch expression.
/// Patterns are matched from left to right; later patterns will clobber the
/// bindings of earlier patterns if variable names are reused.
#[derive(Debug, EnvDebug, DeepSizeOf)]
pub enum Pattern {
  /// The `_` pattern. Matches anything, binds nothing.
  Skip,
  /// The `x` pattern. Matches anything, binds the variable `x`.
  /// The number here is the index of the variable that will be bound.
  Atom(usize),
  /// The `'foo` pattern. Matches the literal atom `foo`, binds nothing.
  QuoteAtom(AtomID),
  /// The `"foo"` pattern. Matches the literal string `"foo"`, binds nothing.
  String(ArcString),
  /// The `#t` or `#f` pattern. Matches a boolean value, binds nothing.
  Bool(bool),
  /// The `#undef` pattern. Matches `#undef`, binds nothing.
  Undef,
  /// The `123` pattern. Matches the number `123`, binds nothing.
  Number(BigInt),
  /// The `(mvar)` or `(mvar bd s)` pattern. `(mvar)` matches metavars with unknown type,
  /// `(mvar bd s)` matches a metavar with known type, matching the boundedness and sort
  /// against patterns `bd` ans `s`.
  MVar(MVarPattern),
  /// The `(goal p)` pattern. Matches a goal with type matched against `p`.
  Goal(Box<Pattern>),
  /// The `(p1 p2 ... pn . p)` pattern. Matches an `n`-fold cons cell,
  /// or a list of length at least `n`, matching the parts against the `p`'s.
  DottedList(Box<[Pattern]>, Box<Pattern>),
  /// * With `dot = None`: The `(p1 p2 ... pn)` pattern.
  ///   Matches a list of length `n`, matching the elements against `p1, ..., pn`.
  /// * With `dot = Some(k)`: The `(p1 p2 ... pn __ k)` pattern.
  ///   Matches a proper list of length at least `n + k`,
  ///   matching the first `n` elements against `p1, ..., pn`.
  List(Box<[Pattern]>, Option<usize>),
  /// The `(and ps)` pattern. Matches the input against each `p` in turn, succeeding
  /// if all patterns match.
  And(Box<[Pattern]>),
  /// The `(or ps)` pattern. Matches the input against each `p`, succeeding if any pattern matches.
  Or(Box<[Pattern]>),
  /// The `(not ps)` pattern. Matches the input against each `p`,
  /// succeeding if none of the patterns match. Binds nothing.
  Not(Box<[Pattern]>),
  /// The `(? f ps)` pattern. The expression `f` is evaluated in the context of the `match`,
  /// resulting in a procedure, and then `(f e)` is called, where `e` is the input.
  /// If this function returns truthy, then it acts like `(and ps)`, otherwise the pattern fails.
  Test(Span, Box<IR>, Box<[Pattern]>),
  /// The `$foo$` pattern. This is equivalent to `(or 'foo ('foo))`.
  QExprAtom(AtomID),
}

/// The `(mvar)` patterns, which match a metavariable of different kinds.
#[derive(Debug, EnvDebug, DeepSizeOf)]
pub enum MVarPattern {
  /// The `(mvar)` pattern, which matches metavars with unknown type.
  Unknown,
  /// The `(mvar ...)` pattern, which matches metavars with any type.
  Any,
  /// The `(mvar bd s)` pattern, which matches a metavar with known type,
  /// matching the boundedness and sort against patterns `bd` ans `s`.
  Simple(Box<(Pattern, Pattern)>)
}

impl<'a> EnvDisplay for Pattern {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      &Pattern::Skip => write!(f, "_"),
      &Pattern::Atom(i) => write!(f, "x{}", i),
      Pattern::QuoteAtom(a) => write!(f, "'{}", fe.to(a)),
      Pattern::String(s) => write!(f, "{:?}", s),
      Pattern::Bool(true) => write!(f, "#t"),
      Pattern::Bool(false) => write!(f, "#f"),
      Pattern::Undef => write!(f, "#undef"),
      Pattern::Number(n) => write!(f, "{}", n),
      Pattern::MVar(MVarPattern::Unknown) => write!(f, "(mvar)"),
      Pattern::MVar(MVarPattern::Any) => write!(f, "(mvar ...)"),
      Pattern::MVar(MVarPattern::Simple(p)) => write!(f, "(mvar {} {})", fe.to(&p.0), fe.to(&p.1)),
      Pattern::Goal(p) => write!(f, "(goal {})", fe.to(p)),
      Pattern::DottedList(es, r) => write!(f, "({} . {})",
        es.iter().map(|ir| fe.to(ir)).format(" "), fe.to(r)),
      Pattern::List(es, None) => write!(f, "({})",
        es.iter().map(|ir| fe.to(ir)).format(" ")),
      Pattern::List(es, Some(0)) => write!(f, "({} ...)",
        es.iter().map(|ir| fe.to(ir)).format(" ")),
      Pattern::List(es, Some(n)) => write!(f, "({} __ {})",
        es.iter().map(|ir| fe.to(ir)).format(" "), n),
      Pattern::And(es) => write!(f, "(and {})", es.iter().map(|ir| fe.to(ir)).format(" ")),
      Pattern::Or(es) => write!(f, "(or {})", es.iter().map(|ir| fe.to(ir)).format(" ")),
      Pattern::Not(es) => write!(f, "(not {})", es.iter().map(|ir| fe.to(ir)).format(" ")),
      Pattern::Test(_, ir, p) => write!(f, "(? {} {})", fe.to(&**ir), fe.to(&**p)),
      Pattern::QExprAtom(a) => write!(f, "${}$", fe.to(a)),
    }
  }
}

impl Remap for IR {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      &IR::Local(i) => IR::Local(i),
      &IR::Global(sp, a) => IR::Global(sp, a.remap(r)),
      IR::Const(v) => IR::Const(unsafe { v.freeze() }.remap(r)),
      IR::List(sp, v) => IR::List(*sp, v.remap(r)),
      IR::DottedList(v, e) => IR::DottedList(v.remap(r), e.remap(r)),
      &IR::App(s, t, ref e, ref es) => IR::App(s, t, e.remap(r), es.remap(r)),
      IR::If(e) => IR::If(e.remap(r)),
      IR::NoTailRec => IR::NoTailRec,
      IR::Focus(sp, e) => IR::Focus(*sp, e.remap(r)),
      &IR::Def(n, ref a, ref e) => IR::Def(n,
        a.as_ref().map(|&(sp1, sp2, ref doc, a)| (sp1, sp2, doc.clone(), a.remap(r))),
        e.remap(r)),
      &IR::Eval(b, ref e) => IR::Eval(b, e.remap(r)),
      &IR::Lambda(sp, n, spec, ref e) => IR::Lambda(sp, n, spec, e.remap(r)),
      &IR::Match(sp, ref e, ref br) => IR::Match(sp, e.remap(r), br.remap(r)),
    }
  }
}

impl Remap for Branch {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    Self {
      vars: self.vars,
      cont: self.cont,
      pat: self.pat.remap(r),
      eval: self.eval.remap(r)
    }
  }
}

impl Remap for Pattern {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      Pattern::Skip => Pattern::Skip,
      &Pattern::Atom(i) => Pattern::Atom(i),
      Pattern::QuoteAtom(a) => Pattern::QuoteAtom(a.remap(r)),
      Pattern::String(s) => Pattern::String(s.clone()),
      &Pattern::Bool(b) => Pattern::Bool(b),
      Pattern::Undef => Pattern::Undef,
      Pattern::Number(i) => Pattern::Number(i.clone()),
      Pattern::MVar(p) => Pattern::MVar(p.remap(r)),
      Pattern::Goal(p) => Pattern::Goal(p.remap(r)),
      Pattern::DottedList(v, e) => Pattern::DottedList(v.remap(r), e.remap(r)),
      &Pattern::List(ref es, n) => Pattern::List(es.remap(r), n),
      Pattern::And(es) => Pattern::And(es.remap(r)),
      Pattern::Or(es) => Pattern::Or(es.remap(r)),
      Pattern::Not(es) => Pattern::Not(es.remap(r)),
      &Pattern::Test(sp, ref ir, ref es) => Pattern::Test(sp, ir.remap(r), es.remap(r)),
      Pattern::QExprAtom(a) => Pattern::QExprAtom(a.remap(r)),
    }
  }
}

impl Remap for MVarPattern {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      MVarPattern::Unknown => MVarPattern::Unknown,
      MVarPattern::Any => MVarPattern::Any,
      MVarPattern::Simple(p) => MVarPattern::Simple(p.remap(r)),
    }
  }
}

impl IR {
  fn unconst(cs: Vec<IR>) -> Result<Vec<LispVal>, Vec<IR>> {
    if cs.iter().all(|c| matches!(c, IR::Const(_))) {
      Ok(cs.into_iter().map(|c|
        if let IR::Const(v) = c {v}
        else {unsafe {std::hint::unreachable_unchecked()}}).collect())
    } else {Err(cs)}
  }
  fn list(fsp: FileSpan, cs: Vec<IR>) -> IR {
    match IR::unconst(cs) {
      Ok(es) => IR::Const(LispVal::list(es).span(fsp)),
      Err(cs) => IR::List(fsp.span, cs.into())
    }
  }
  fn dotted_list(sp: Span, mut cs: Vec<IR>, c: IR) -> IR {
    if cs.is_empty() {return c}
    match c {
      IR::Const(e) => match e.deref() {
        LispKind::List(es) => {
          cs.extend(es.iter().map(|e| IR::Const(e.clone())));
          IR::List(sp, cs.into())
        }
        LispKind::DottedList(es, e) => {
          cs.extend(es.iter().map(|e| IR::Const(e.clone())));
          IR::DottedList(cs.into(), Box::new(IR::Const(e.clone())))
        }
        _ => match IR::unconst(cs) {
          Ok(es) => IR::Const(LispVal::dotted_list(es, e)),
          Err(cs) => IR::DottedList(cs.into(), Box::new(IR::Const(e)))
        }
      },
      IR::List(_, cs2) => {
        cs.extend(cs2.into_vec());
        IR::List(sp, cs.into())
      }
      IR::DottedList(cs2, c) => {
        cs.extend(cs2.into_vec());
        IR::DottedList(cs.into(), c)
      }
      _ => IR::DottedList(cs.into(), Box::new(c))
    }
  }
}

struct LocalCtx {
  names: HashMap<AtomID, Vec<usize>>,
  ctx: Vec<AtomID>,
}

impl LocalCtx {
  fn new() -> Self { Self {names: HashMap::new(), ctx: vec![]} }
  fn len(&self) -> usize { self.ctx.len() }
  fn get(&self, x: AtomID) -> Option<usize> {
    self.names.get(&x).and_then(|v| v.last().cloned())
  }
  fn push(&mut self, x: AtomID) -> usize {
    let old = self.ctx.len();
    if x != AtomID::UNDER { self.names.entry(x).or_insert_with(Vec::new).push(old) }
    self.ctx.push(x);
    old
  }
  fn push_list(&mut self, xs: &[AtomID]) -> usize {
    let old = self.ctx.len();
    for &x in xs { self.push(x); }
    old
  }
  fn get_or_push(&mut self, x: AtomID) -> usize {
    self.get(x).unwrap_or_else(|| self.push(x))
  }

  fn pop(&mut self) {
    let x = self.ctx.pop().unwrap();
    if x != AtomID::UNDER {self.names.get_mut(&x).unwrap().pop();}
  }
  fn restore(&mut self, n: usize) {
    while self.ctx.len() > n { self.pop() }
  }
}

struct LispParser<'a> {
  elab: &'a mut Elaborator,
  ctx: LocalCtx,
}
impl<'a> Deref for LispParser<'a> {
  type Target = Elaborator;
  fn deref(&self) -> &Elaborator { self.elab }
}
impl<'a> DerefMut for LispParser<'a> {
  fn deref_mut(&mut self) -> &mut Elaborator { self.elab }
}

enum Item<'a> {
  List(&'a [SExpr]),
  DottedList(&'a [SExpr], &'a SExpr),
}

type Var<'a> = (Span, AtomID, Vec<Item<'a>>);

impl<'a> LispParser<'a> {
  fn def_var<'c>(&mut self, mut e: &'c SExpr) -> Result<Var<'c>, ElabError> {
    let mut stack = vec![];
    loop {
      match &e.k {
        &SExprKind::Atom(a) => break Ok((e.span, self.parse_atom(e.span, a)?, stack)),
        SExprKind::List(xs) if !xs.is_empty() =>
          {stack.push(Item::List(&xs[1..])); e = &xs[0]}
        SExprKind::DottedList(xs, y) if !xs.is_empty() =>
          {stack.push(Item::DottedList(&xs[1..], y)); e = &xs[0]}
        _ => return Err(ElabError::new_e(e.span, "def: invalid spec"))
      }
    }
  }

  fn def_ir(&mut self, sp: Span, es: &[SExpr], stack: Vec<Item<'_>>) -> Result<Vec<IR>, ElabError> {
    for e in stack.iter().rev() {
      match e {
        Item::List(xs) => {
          let xs = self.parse_idents(xs)?;
          self.ctx.push_list(&xs);
        }
        Item::DottedList(xs, y) => {
          let xs = self.parse_idents(xs)?;
          self.ctx.push_list(&xs);
          let y = self.parse_ident(y)?;
          self.ctx.push(y);
        }
      }
    }
    let mut len = self.ctx.len();
    let mut ir = self.exprs(false, es)?;
    for e in stack {
      ir = match e {
        Item::List(xs) => {
          len -= xs.len();
          vec![IR::Lambda(sp, len, ProcSpec::Exact(xs.len()), IR::eval(ir).into())]
        }
        Item::DottedList(xs, _) => {
          len -= xs.len() + 1;
          vec![IR::Lambda(sp, len, ProcSpec::AtLeast(xs.len()), IR::eval(ir).into())]
        }
      }
    }
    self.ctx.restore(len);
    Ok(ir)
  }

  fn def(&mut self, e: &SExpr, es: &[SExpr]) -> Result<(Span, AtomID, Vec<IR>), ElabError> {
    let (sp, x, stack) = self.def_var(e)?;
    let ir = self.def_ir(sp, es, stack)?;
    if self.ctx.len() == 0 {
      self.spans.insert(sp, ObjectKind::Global(x));
    }
    Ok((sp, x, ir))
  }
}

impl<'a> LispParser<'a> {
  fn parse_ident_or_syntax(&mut self, sp: Span, a: Atom) -> Result<AtomID, Syntax> {
    match Syntax::parse(self.ast.clone().span(sp), a) {
      Ok(s) => Err(s),
      Err(s) => Ok(self.get_atom(s))
    }
  }

  fn parse_atom(&mut self, sp: Span, a: Atom) -> Result<AtomID, ElabError> {
    self.parse_ident_or_syntax(sp, a).map_err(|_|
      ElabError::new_e(sp, "keyword in invalid position"))
  }

  fn parse_ident(&mut self, e: &SExpr) -> Result<AtomID, ElabError> {
    if let SExprKind::Atom(a) = e.k {
      self.parse_atom(e.span, a)
    } else {
      Err(ElabError::new_e(e.span, "expected an identifier"))
    }
  }

  fn parse_idents(&mut self, es: &[SExpr]) -> Result<Vec<AtomID>, ElabError> {
    let mut xs = vec![];
    for e in es {xs.push(self.parse_ident(e)?)}
    Ok(xs)
  }

  fn qexpr(&mut self, e: QExpr) -> Result<IR, ElabError> {
    match e.k {
      QExprKind::IdentApp(sp, es) => {
        let head = IR::Const(LispVal::atom(
          self.elab.env.get_atom(self.ast.clone().span(sp))).span(self.fspan(sp)));
        if es.is_empty() {Ok(head)} else {
          let mut cs = vec![head];
          for e in es.into_vec() { cs.push(self.qexpr(e)?) }
          Ok(IR::list(self.fspan(e.span), cs))
        }
      }
      QExprKind::App(sp, t, es) => {
        let a = self.terms[t].atom;
        let mut cs = vec![IR::Const(LispVal::atom(a).span(self.fspan(sp)))];
        for e in es.into_vec() { cs.push(self.qexpr(e)?) }
        Ok(IR::list(self.fspan(e.span), cs))
      }
      QExprKind::Unquote(e) => {
        if self.mm0_mode {
          self.report(ElabError::warn(e.span, "(MM0 mode) unquotation not allowed"))
        }
        self.expr(false, &e)
      }
    }
  }

  fn exprs(&mut self, quote: bool, es: &[SExpr]) -> Result<Vec<IR>, ElabError> {
    let mut cs = vec![];
    for e in es { cs.push(self.expr(quote, e)?) }
    Ok(cs)
  }

  fn let_var<'c>(&mut self, e: &'c SExpr) -> Result<(Var<'c>, &'c [SExpr]), ElabError> {
    match &e.k {
      SExprKind::List(es) if !es.is_empty() => Ok((self.def_var(&es[0])?, &es[1..])),
      _ => Err(ElabError::new_e(e.span, "let: invalid spec"))
    }
  }

  fn let_(&mut self, rec: bool, es: &[SExpr]) -> Result<IR, ElabError> {
    if es.is_empty() {return Ok(IR::Const(LispVal::undef()))}
    let ls = if let SExprKind::List(ls) = &es[0].k {ls} else {
      return Err(ElabError::new_e(es[0].span, "let: invalid spec"))
    };
    let mut cs = vec![];
    if rec {
      let mut ds = Vec::with_capacity(ls.len());
      for l in ls {
        let ((sp, x, stk), e2) = self.let_var(l)?;
        let n = self.ctx.push(x);
        let sps = if x == AtomID::UNDER {None} else {Some((l.span, sp, None, x))};
        cs.push(IR::Def(n, sps.clone(),
          Box::new(IR::new_ref(sp, sp, IR::Const(LispVal::undef())))));
        ds.push((sp, x, stk, e2, n, sps));
      }
      for (sp, x, stk, e2, n, sps) in ds {
        let mut v = self.def_ir(sp, e2, stk)?;
        if let Some(r) = v.pop() {
          cs.extend(v);
          let m = self.ctx.push(x);
          cs.push(IR::Def(m, sps, r.into()));
          cs.push(IR::set_weak(sp, sp, IR::Local(n), IR::Local(m)));
        }
      }
      cs.push(IR::NoTailRec);
    } else {
      for l in ls {
        let ((sp, x, stk), e2) = self.let_var(l)?;
        let v = self.def_ir(sp, e2, stk)?;
        if x == AtomID::UNDER {
          cs.push(IR::Eval(false, v.into()))
        } else {
          cs.push(IR::Def(self.ctx.push(x), Some((l.span, sp, None, x)), IR::eval(v).into()))
        }
      }
    }
    for e in &es[1..] { cs.push(self.expr(false, e)?) }
    Ok(IR::Eval(true, cs.into()))
  }

  fn list_pattern(&mut self, ctx: &mut LocalCtx, code: &mut Vec<IR>,
      quote: bool, mut es: &[SExpr]) -> Result<Pattern, ElabError> {
    let mut pfx = vec![];
    let pat = loop {
      match es {
        [] => return Ok(Pattern::List(pfx.into(), None)),
        &[SExpr {span, k: SExprKind::Atom(a)}, ref e] if quote =>
          if self.ast.span_atom(span, a) == b"unquote" {
            break self.pattern(ctx, code, false, e)?
          },
        _ if quote => {},
        [head, args @ ..] => if let SExprKind::Atom(a) = head.k {
          match self.ast.span_atom(head.span, a) {
            b"quote" => match args {
              [e] => break self.pattern(ctx, code, true, e)?,
              _ => return Err(ElabError::new_e(head.span, "expected one argument")),
            },
            b"mvar" => match args {
              [] => break Pattern::MVar(MVarPattern::Unknown),
              &[SExpr {span, k: SExprKind::Atom(a)}]
                if matches!(self.ast.span_atom(span, a), b"___" | b"...") =>
                break Pattern::MVar(MVarPattern::Any),
              [bd, s] => {
                let bd = self.pattern(ctx, code, quote, bd)?;
                let s = self.pattern(ctx, code, quote, s)?;
                break Pattern::MVar(MVarPattern::Simple(Box::new((bd, s))))
              }
              _ => return Err(ElabError::new_e(head.span, "expected zero or two arguments")),
            },
            b"goal" => match args {
              [e] => break Pattern::Goal(Box::new(self.pattern(ctx, code, quote, e)?)),
              _ => return Err(ElabError::new_e(head.span, "expected one argument")),
            },
            b"and" => break Pattern::And(self.patterns(ctx, code, quote, args)?),
            b"or" => break Pattern::Or(self.patterns(ctx, code, quote, args)?),
            b"not" => break Pattern::Not(self.patterns(ctx, code, quote, args)?),
            b"?" => match args {
              [test, rest @ ..] => {
                let p = self.ctx.len();
                let ir = self.expr(false, test)?;
                self.ctx.restore(p);
                let rest = self.patterns(ctx, code, quote, rest)?;
                break Pattern::Test(test.span, Box::new(ir), rest)
              },
              _ => return Err(ElabError::new_e(head.span, "expected at least one argument")),
            }
            b"cons" => match args {
              [] => return Err(ElabError::new_e(head.span, "expected at least one argument")),
              [es @ .., e] => break Pattern::DottedList(
                self.patterns(ctx, code, quote, es)?,
                self.pattern(ctx, code, quote, e)?.into())
            },
            b"___" | b"..." => match args {
              [] => return Ok(Pattern::List(pfx.into(), Some(0))),
              _ => return Err(ElabError::new_e(head.span, "expected nothing after '...'")),
            },
            b"__" => match *args {
              [SExpr {span, k: SExprKind::Number(ref n)}] =>
                return Ok(Pattern::List(pfx.into(), Some(n.to_usize().ok_or_else(||
                  ElabError::new_e(span, "number out of range"))?))),
              _ => return Err(ElabError::new_e(head.span, "expected number after '__'")),
            },
            _ => {}
          }
        }
      }
      pfx.push(self.pattern(ctx, code, quote, &es[0])?);
      es = &es[1..];
    };
    Ok(if pfx.is_empty() {pat} else {Pattern::DottedList(pfx.into(), pat.into())})
  }

  fn qexpr_pattern(&mut self, ctx: &mut LocalCtx, code: &mut Vec<IR>, e: QExpr) -> Result<Pattern, ElabError> {
    match e.k {
      QExprKind::IdentApp(sp, es) => {
        let head = match self.ast.clone().span(sp) {
          b"_" => Pattern::Skip,
          s if es.is_empty() => Pattern::QExprAtom(self.elab.env.get_atom(s)),
          s => Pattern::QuoteAtom(self.elab.env.get_atom(s)),
        };
        if es.is_empty() {Ok(head)} else {
          let mut cs = vec![head];
          for e in es.into_vec() { cs.push(self.qexpr_pattern(ctx, code, e)?) }
          Ok(Pattern::List(cs.into(), None))
        }
      }
      QExprKind::App(_, t, es) => {
        let x = self.terms[t].atom;
        if es.is_empty() {
          Ok(Pattern::QExprAtom(x))
        } else {
          let mut cs = vec![Pattern::QExprAtom(x)];
          for e in es.into_vec() { cs.push(self.qexpr_pattern(ctx, code, e)?) }
          Ok(Pattern::List(cs.into(), None))
        }
      }
      QExprKind::Unquote(e) => self.pattern(ctx, code, false, &e)
    }
  }


  fn patterns(&mut self, ctx: &mut LocalCtx, code: &mut Vec<IR>,
      quote: bool, es: &[SExpr]) -> Result<Box<[Pattern]>, ElabError> {
    let mut ps = vec![];
    for e in es {ps.push(self.pattern(ctx, code, quote, e)?)}
    Ok(ps.into())
  }

  fn pattern(&mut self, ctx: &mut LocalCtx, code: &mut Vec<IR>,
      quote: bool, e: &SExpr) -> Result<Pattern, ElabError> {
    match &e.k {
      &SExprKind::Atom(a) => Ok(
        if quote {
          Pattern::QuoteAtom(self.elab.env.get_atom(self.elab.ast.span_atom(e.span, a)))
        } else {
          let x = self.parse_atom(e.span, a)?;
          if x == AtomID::UNDER {Pattern::Skip}
          else {Pattern::Atom(ctx.get_or_push(x))}
        }
      ),
      SExprKind::DottedList(es, e) => Ok(Pattern::DottedList(
        self.patterns(ctx, code, quote, es)?,
        self.pattern(ctx, code, quote, e)?.into())),
      SExprKind::Number(n) => Ok(Pattern::Number(n.clone().into())),
      SExprKind::String(s) => Ok(Pattern::String(s.clone())),
      &SExprKind::Bool(b) => Ok(Pattern::Bool(b)),
      SExprKind::Undef => Ok(Pattern::Undef),
      SExprKind::DocComment(_, e) => self.pattern(ctx, code, quote, e),
      SExprKind::List(es) => self.list_pattern(ctx, code, quote, es),
      &SExprKind::Formula(f) => {
        let q = self.parse_formula(f)?;
        self.qexpr_pattern(ctx, code, q)
      }
    }
  }

  fn branch(&mut self, code: &mut Vec<IR>, e: &SExpr) -> Result<Branch, ElabError> {
    let (e, mut es) = match &e.k {
      SExprKind::List(es) if !es.is_empty() => (&es[0], &es[1..]),
      _ => return Err(ElabError::new_e(e.span, "match: improper syntax"))
    };
    let mut cont = AtomID::UNDER;
    if let Some(e2) = es.get(0) {
      if let SExprKind::List(v) = &e2.k {
        if let [SExpr {span, k: SExprKind::Atom(a)}, ref x] = **v {
          if let b"=>" = self.ast.span_atom(span, a) {
            cont = self.parse_ident(x)?;
            es = &es[1..];
          }
        }
      }
    }
    let mut ctx = LocalCtx::new();
    let pat = self.pattern(&mut ctx, code, false, e)?;
    let vars = ctx.ctx.len();
    let start = self.ctx.push_list(&ctx.ctx);
    if cont != AtomID::UNDER {self.ctx.push(cont);}
    let eval = Box::new(IR::eval(self.exprs(false, es)?));
    self.ctx.restore(start);
    Ok(Branch {pat, vars, cont: cont != AtomID::UNDER, eval})
  }
  fn branches(&mut self, code: &mut Vec<IR>, es: &[SExpr]) -> Result<Box<[Branch]>, ElabError> {
    let mut bs = vec![];
    for e in es { bs.push(self.branch(code, e)?) }
    Ok(bs.into())
  }
  fn match_(&mut self, es: &[SExpr], f: impl FnOnce(Box<[Branch]>) -> IR) -> Result<IR, ElabError> {
    let mut code = vec![];
    let m = self.branches(&mut code, es)?;
    if code.is_empty() {
      Ok(f(m))
    } else {
      code.push(f(m));
      Ok(IR::Eval(true, code.into()))
    }
  }

  fn eval_atom(&mut self, sp: Span, x: AtomID) -> IR {
    match self.ctx.get(x) {
      None => {
        self.spans.insert(sp, ObjectKind::Global(x));
        IR::Global(sp, x)
      },
      Some(i) => IR::Local(i)
    }
  }

  fn expr(&mut self, quote: bool, e: &SExpr) -> Result<IR, ElabError> {
    self.expr_doc(String::new(), quote, e)
  }

  fn expr_doc(&mut self, mut doc: String, quote: bool, e: &SExpr) -> Result<IR, ElabError> {
    macro_rules! span {($sp:expr, $e:expr) => {{$e.span(self.fspan($sp))}}}
    let mut restore = Some(self.ctx.len());
    let res = match &e.k {
      &SExprKind::Atom(a) => if quote {
        Ok(IR::Const(span!(e.span,
          match self.parse_ident_or_syntax(e.span, a) {
            Ok(x) => LispVal::atom(x),
            Err(s) => LispVal::syntax(s),
          }
        )))
      } else {
        Ok(match self.parse_atom(e.span, a)? {
          AtomID::UNDER => IR::Const(span!(e.span, LispVal::atom(AtomID::UNDER))),
          x => self.eval_atom(e.span, x),
        })
      },
      SExprKind::DottedList(es, e) => {
        if !quote {
          return Err(ElabError::new_e(e.span, "cannot evaluate an improper list"))
        }
        let mut cs = vec![];
        for e in es {
          if let SExprKind::Atom(a) = es[0].k {
            if let Ok(Syntax::Unquote) = Syntax::parse(self.ast.span(e.span), a) {
              return Err(ElabError::new_e(e.span, "cannot evaluate an improper list"))
            }
          }
          cs.push(self.expr(quote, e)?)
        }
        Ok(IR::dotted_list(e.span, cs, self.expr(true, e)?))
      }
      SExprKind::Number(n) => Ok(IR::Const(LispVal::number(n.clone().into()))),
      SExprKind::String(s) => Ok(IR::Const(LispVal::string(s.clone()))),
      &SExprKind::Bool(b) => Ok(IR::Const(LispVal::bool(b))),
      SExprKind::Undef => Ok(IR::Const(LispVal::undef())),
      SExprKind::DocComment(doc2, e) => {
        // push an extra newline to separate multiple doc comments
        if !doc.is_empty() {doc.push('\n');}
        doc.push_str(doc2);
        return self.expr_doc(doc, quote, e)
      }
      SExprKind::List(es) if es.is_empty() => Ok(IR::Const(span!(e.span, LispVal::nil()))),
      SExprKind::List(es) => if quote {
        let mut cs = vec![];
        let mut it = es.iter();
        Ok(loop {
          if let Some(arg) = it.next() {
            if let SExprKind::Atom(a) = arg.k {
              if let Ok(Syntax::Unquote) = Syntax::parse(self.ast.span(arg.span), a) {
                let r = it.next().ok_or_else(||
                  ElabError::new_e(arg.span, "expected at least one argument"))?;
                break IR::dotted_list(e.span, cs, self.expr(false, r)?)
              } else {cs.push(self.expr(true, arg)?)}
            } else {cs.push(self.expr(true, arg)?)}
          } else {break IR::list(self.fspan(e.span), cs)}
        })
      } else if let SExprKind::Atom(a) = es[0].k {
        match self.parse_ident_or_syntax(es[0].span, a) {
          Ok(AtomID::UNDER) => return Err(ElabError::new_e(es[0].span, "'_' is not a function")),
          Ok(x) =>
            Ok(IR::App(e.span, es[0].span,
              Box::new(self.eval_atom(es[0].span, x)), self.exprs(false, &es[1..])?.into())),
          Err(stx) => {
            self.spans.insert_if(es[0].span, || ObjectKind::Syntax(stx));
            match stx {
              Syntax::Begin => Ok(IR::Eval(true, self.exprs(false, &es[1..])?.into())),
              Syntax::Define if es.len() < 2 => return Err(
                ElabError::new_e(es[0].span, "expected at least one argument")),
              Syntax::Define =>
                Ok(match self.def(&es[1], &es[2..])? {
                  (_, AtomID::UNDER, cs) => IR::Eval(false, cs.into()),
                  (sp, x, cs) => {
                    restore = None;
                    let doc = if doc.is_empty() {None} else {Some(doc.into())};
                    IR::Def(self.ctx.push(x), Some((e.span, sp, doc, x)), IR::eval(cs).into())
                  }
                }),
              Syntax::Lambda if es.len() < 2 => return Err(
                ElabError::new_e(es[0].span, "expected at least one argument")),
              Syntax::Lambda => match &es[1].k {
                SExprKind::List(xs) => {
                  let xs = self.parse_idents(xs)?;
                  Ok(IR::Lambda(es[0].span, self.ctx.push_list(&xs), ProcSpec::Exact(xs.len()),
                    IR::eval(self.exprs(false, &es[2..])?).into()))
                }
                SExprKind::DottedList(xs, y) => {
                  let xs = self.parse_idents(xs)?;
                  let y = self.parse_ident(y)?;
                  let n = self.ctx.push_list(&xs);
                  self.ctx.push(y);
                  Ok(IR::Lambda(es[0].span, n, ProcSpec::AtLeast(xs.len()),
                    IR::eval(self.exprs(false, &es[2..])?).into()))
                }
                _ => {
                  let x = self.parse_ident(&es[1])?;
                  Ok(IR::Lambda(es[0].span, self.ctx.push(x), ProcSpec::AtLeast(0),
                    IR::eval(self.exprs(false, &es[2..])?).into()))
                }
              },
              Syntax::Quote if es.len() < 2 => return Err(
                ElabError::new_e(es[0].span, "expected at least one argument")),
              Syntax::Quote => self.expr(true, &es[1]),
              Syntax::Unquote if es.len() < 2 => return Err(
                ElabError::new_e(es[0].span, "expected at least one argument")),
              Syntax::Unquote => self.expr(false, &es[1]),
              Syntax::If if 3 <= es.len() && es.len() <= 4 => Ok(IR::If(Box::new((
                self.expr(false, &es[1])?,
                self.expr(false, &es[2])?,
                if let Some(e) = es.get(3) {
                  self.ctx.restore(restore.unwrap());
                  self.expr(false, e)?
                } else { IR::Const(LispVal::undef()) }
              )))),
              Syntax::If => return Err(
                ElabError::new_e(es[0].span, "expected two or three arguments")),
              Syntax::Focus => Ok(IR::Focus(es[0].span, self.exprs(false, &es[1..])?.into())),
              Syntax::Let => self.let_(false, &es[1..]),
              Syntax::Letrec => self.let_(true, &es[1..]),
              Syntax::Match if es.len() < 2 => return Err(
                ElabError::new_e(es[0].span, "expected at least one argument")),
              Syntax::Match => {
                let e = self.expr(false, &es[1])?;
                self.ctx.restore(restore.unwrap());
                self.match_(&es[2..], |m| IR::Match(es[0].span, Box::new(e), m))
              },
              Syntax::MatchFn => {
                let i = self.ctx.push(AtomID::UNDER);
                Ok(IR::Lambda(es[0].span, i, ProcSpec::Exact(1),
                  Arc::new(self.match_(&es[1..], |m| IR::match_fn_body(es[0].span, i, m))?)))
              }
              Syntax::MatchFns => {
                let i = self.ctx.push(AtomID::UNDER);
                Ok(IR::Lambda(es[0].span, i, ProcSpec::AtLeast(0),
                  Arc::new(self.match_(&es[1..], |m| IR::match_fn_body(es[0].span, i, m))?)))
              }
            }
          }
        }
      } else {
        Ok(IR::App(e.span, es[0].span, Box::new(self.expr(false, &es[0])?),
          self.exprs(false, &es[1..])?.into()))
      },
      &SExprKind::Formula(f) => {let q = self.parse_formula(f)?; self.qexpr(q)}
    };
    if let Some(old) = restore { self.ctx.restore(old) }
    res
  }
}

impl Elaborator {
  /// Parse a lisp `SExpr` from the surface syntax into an `IR` object suitable for evaluation.
  pub fn parse_lisp(&mut self, e: &SExpr) -> Result<IR, ElabError> {
    self.parse_lisp_doc(e, String::new())
  }

  /// Parse a lisp `SExpr` from the surface syntax into an `IR` object suitable for evaluation.
  /// The `doc` argument is an additional doc string, if applicable.
  pub fn parse_lisp_doc(&mut self, e: &SExpr, doc: String) -> Result<IR, ElabError> {
    LispParser {elab: &mut *self, ctx: LocalCtx::new()}.expr_doc(doc, false, e)
  }

  /// Parse a `QExpr`, the result of parsing a math formula,
  /// into an `IR` object suitable for evaluation. (Usually this will be a `IR::Const`,
  /// but `QExpr`'s can contain antiquotations which require evaluation.)
  pub fn parse_qexpr(&mut self, e: QExpr) -> Result<IR, ElabError> {
    LispParser {elab: &mut *self, ctx: LocalCtx::new()}.qexpr(e)
  }
}