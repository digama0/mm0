//! The lisp parser, which takes (already parsed) s-exprs and puts them into an
//! intermediate representation suitable for interpretation (doing as many
//! static checks as we can beforehand).

use std::ops::{Deref, DerefMut};
use std::sync::Arc;
use std::collections::HashMap;
use num::{BigInt, ToPrimitive};
use crate::ast::{SExpr, SExprKind, Atom};
use crate::ArcString;
use super::super::{AtomId, Span, DocComment, Elaborator, ElabError, ObjectKind};
use super::{BuiltinProc, FileSpan, LispKind, LispVal, PatternSyntax, Proc, ProcSpec,
  Remap, Remapper, Syntax};
use super::super::math_parser::{QExpr, QExprKind};
use super::print::{FormatEnv, EnvDisplay};

/// The intermediate representation for "compiled" lisp functions.
/// We will do interpretation/evaluation directly on this data structure.
#[derive(Clone, Debug, EnvDebug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum Ir {
  /// Drop `n` elements from the stack. `[a0, ..., an] -> []`
  Drop(usize),
  /// Drop `n` elements from the stack, skipping the top element. `[a1, ..., an, v] -> [v]`
  DropAbove(usize),
  /// Push `#undef`. `[] -> [#undef]`
  Undef,
  /// Copy the top element on the stack. `[v] -> [v, v]`
  Dup,
  /// Assert that the the context has size `n`. (This is only here for sanity checking -
  /// there is only one valid value for this field, which can be determined statically.)
  /// Does not touch the stack.
  AssertScope(usize),
  /// Restore the context to size `n`, by dropping elements from the context.
  /// Does not touch the stack.
  EndScope(usize),
  /// Access variable number `n` in the context. `[] -> [v_n]`
  Local(usize),
  /// Access a global declaration named `a`. `[] -> [global[a]]`
  Global(Span, AtomId),
  /// Return a [`LispVal`] literally. `[] -> [c]`
  Const(LispVal),
  /// The `(list)` function: create a list from the last `n` results on the stack.
  /// `[a1, ..., an] -> [(a1 ... an)]`
  List(Span, usize),
  /// The `(cons)` function: create a dotted list from the last `n+1` results on the stack.
  /// `[a1, ..., an, a(n+1)] -> [(a1 ... an . a(n+1))]`
  DottedList(usize),
  /// Function application: given `1 + n` results on the stack, where the first argument
  /// is a procedure and the following `n` are the arguments, call the procedure
  /// and put the result on the stack.
  /// * `app: [f, a1, ..., an] -> [f(a1, ..., an)]`
  /// * `tail-app: [ret, ..., f, a1, ..., an] -> [ret, f(a1, ..., an)]`
  App(bool, Box<(Span, Span)>, usize),
  /// Function application: given `n` arguments on the stack, call the builtin procedure `f`
  /// and put the result on the stack.
  /// * `app: [a1, ..., an] -> [f(a1, ..., an)]`
  /// * `tail-app: [ret, ..., a1, ..., an] -> [ret, f(a1, ..., an)]`
  BuiltinApp(bool, BuiltinProc, Box<(Span, Span)>, usize),
  /// A constant-propagated arity error in a builtin application.
  ArityError(Span, ProcSpec),
  /// Applies the head of the stack to the element under it. `[x, f] -> [f(x)]`
  AppHead(Span),
  /// Pop the last result on the stack; if it is truthy then continue, else jump
  /// to the indicated location in the procedure.
  /// `[#t] -> [] (and ip += 1)`, or `[#f] -> [] (and ip = tgt)`
  JumpUnless(usize),
  /// Jump unconditionally to the indicated location. `ip = tgt`, does not touch the stack.
  /// Only used for forward jumps.
  Jump(usize),
  /// The initializer for the `(focus es)` syntax form.
  /// Takes the goals out of the state and puts them in a `focus` node on the stack.
  /// `[] -> (focus lc.goals)`, `set lc.goals = []`
  FocusStart(Span),
  /// Fail if there are goals remaining. Part of the `(focus es)` macro.
  /// * If no closer, assert `lc.goals = []`, then `[(focus gs)] -> [], lc.goals := gs`
  /// * If closer is set, then jump to self, `[(focus gs)] -> [(focus gs)]` and evaluate `closer()`
  /// * If stack does not have `focus` on the head:
  ///   assert `lc.goals = []`, then `[(focus gs), e] -> [], lc.goals := gs`.
  ///   (This is the second execution of this instruction after the loop in (2),
  ///   and bypasses the closer check so that we don't evaluate the closer multiple times.)
  FocusFinish,
  /// The `(set-merge-strategy)` function, which is a macro because it directly binds
  /// to a global name. `[e] -> []`
  SetMergeStrategy(Span, AtomId),
  /// The `(def x e)` syntax form, not at global scope. Get the argument from the stack,
  /// and extend the context with the result. `[e] -> []`, assert `n` is the context length.
  LocalDef(usize),
  /// The `(def x e)` syntax form at global scope. Get the argument from the stack,
  /// and store it as a global definition with the given name. `[e] -> []`
  GlobalDef(Span, Span, AtomId),
  /// Set the doc comment for a variable. Does not touch the stack.
  SetDoc(DocComment, AtomId),
  /// The `(fn xs e)` syntax form. Create a closure from the current context, and return
  /// it, using the provided [`ProcSpec`] and code. It can later be called by the
  /// [`App`](Self::App) instruction.
  /// The `u8` is `u8::MAX` if the lambda is unnamed; else it is a forward reference
  /// to a `GlobalDef` with the name information. `[] -> [lambda spec [code...]]`
  Lambda(u8, Box<(Span, ProcSpec, Arc<[Ir]>)>),
  /// Start a match branch. Push `n` variables to the match context,
  /// to store the values of variables to match.
  /// The second usize is the address of the next branch.
  /// The option is set if we need a match continuation.
  /// `[e] -> [(branch e), e]`, transitions to pattern mode (see `Ir::Pattern*` instructions)
  Branch(usize, usize, Option<usize>),
  /// Resume after a `PatternTestPause` instruction.
  /// * `[(pause vars), #t] -> []`, transition to pattern mode
  /// * `[(pause vars), #f] -> []`, transition to pattern mode and throw
  TestPatternResume,
  /// End a match, throwing a "match failed" error.
  /// `[e] -> error "match failed: e"`
  BranchFail(Span),
  /// Implementation of `map` function.
  /// * `[(map-proc-2 [args...]), e] -> [(map-proc-2 [args..., e])]` and loop
  /// * `[f, (map-proc-1 (a1 . u1) ... (an . un)), (map-proc-2 args)] ->
  ///    [f, (map-proc-1 u1' ... un'), (map-proc-2 args)]` and loop and evaluate `f(a1, ..., an)`
  /// * `[f, (map-proc-1 () ... ()), (map-proc-2 args)] -> [(args)]`
  Map,
  /// Implementation of `have` function. `[h, p] -> [#undef]`,
  /// adds `h := p` as a hypothesis to the state.
  Have,
  /// Implementation of `refine` function. `[(refine rstack), e] -> refine(rstack, ret(e))`
  RefineResume,
  /// Call refine with the last argument on the stack, if not `#undef`.
  /// Part of the `(focus es)` macro.
  /// If the bool is true (shown as `refine`), this returns the result of the refine,
  /// else (shown as `refine-goal`) it drops the result.
  /// * `refine-goal: [#undef] -> []`
  /// * `refine: [#undef] -> [#undef]`
  /// * `refine-goal: [e] -> refine(e, goals(gs, [e], ret_val = false)`
  /// * `refine: [e] -> refine(e, goals(gs, [e], ret_val = true)`
  RefineGoal(bool),
  /// Receive the result of a callback in the `add-thm` function.
  /// `[(add-thm ap), ret] -> [#undef]` and evaluate `ap.finish(ret)`.
  AddThm,
  /// Implementation of `merge-map` inner loop.
  /// * `[(merge-map {map, k: Some(k), ..}), ret] -> [(merge-map {map', k: None})]` and loop,
  ///   where `map' = map.insert(k, ret)`
  /// * `[(merge-map {it, k: None, ..})] -> [(merge-map {it, k: Some(k)})]` and loop
  ///   and call `apply_merge(oldv, newv)`, if `it.next() = Some((k, oldv, newv))`
  /// * `[(merge-map {it, k: None, map, ..})] -> [map]` if `it.next() = None`
  MergeMap,

  /// A pattern that always returns the given result.
  /// * `PatternResult(false) := fail`
  /// * `PatternResult(true) := skip`
  /// * `skip: [e] -> []`
  /// * `fail: [e] -> []` and throw
  PatternResult(bool),
  /// The `x` pattern. Matches anything, binds the variable `x`.
  /// The number here is the index of the variable that will be bound.
  /// * `[e] -> []` and store `x_i := e` to the pattern context
  PatternAtom(usize),
  /// The `'foo` pattern. Matches the literal atom `foo`, binds nothing.
  /// * `[e] -> []` and throw unless `e = 'foo`
  PatternQuoteAtom(AtomId),
  /// The `"foo"` pattern. Matches the literal string `"foo"`, binds nothing.
  /// * `[e] -> []` and throw unless `e = "foo"`
  PatternString(ArcString),
  /// The `#t` or `#f` pattern. Matches a boolean value, binds nothing.
  /// * `[e] -> []` and throw unless `e = #t` or `#f` resp.
  PatternBool(bool),
  /// The `#undef` pattern. Matches `#undef`, binds nothing.
  /// * `[e] -> []` and throw unless `e = #undef` resp.
  PatternUndef,
  /// The `123` pattern. Matches the number `123`, binds nothing.
  /// * `[e] -> []` and throw unless `e = 123` (or other given number).
  PatternNumber(BigInt),
  /// The `(mvar)` or `(mvar bd s)` pattern. `(mvar)` matches metavars with unknown type,
  /// `(mvar bd s)` matches a metavar with known type, matching the boundedness and sort
  /// against patterns `bd` ans `s`.
  /// * `unknown: [e] -> []` and throw unless `e = (mvar)`.
  /// * `any: [e] -> []` and throw unless `e = (mvar)` or `(mvar bd s)` for some `bd, s`.
  /// * `simple: [e] -> [bd, s]` if `e = (mvar bd s)`, or throw.
  PatternMVar(MVarPattern),
  /// The `(goal p)` pattern. Matches a goal with type matched against `p`.
  /// * `[e] -> [g]` if `e = (goal g)`, or throw.
  PatternGoal,
  /// The `(p1 p2 ... pn . p)` pattern. Matches an `n`-fold cons cell,
  /// or a list of length at least `n`, matching the parts against the `p`'s.
  /// * `[e] -> [a1, ..., an, a(n+1)]` if `e = (a1 ... an . a(n+1))`, or throw.
  PatternDottedList(usize),
  /// * With `dot = None`: The `(p1 p2 ... pn)` pattern.
  ///   Matches a list of length `n`, matching the elements against `p1, ..., pn`.
  ///   * `[e] -> [a1, ..., an]` if `e = (a1 ... an)`, or throw.
  /// * With `dot = Some(k)`: The `(p1 p2 ... pn __ k)` pattern.
  ///   Matches a proper list of length at least `n + k`,
  ///   matching the first `n` elements against `p1, ..., pn`.
  ///   * `[e] -> [a1, ..., an]` if `e = (a1 ... an . a(n+1))`
  ///     where `a(n+1)` is a list of length at least `k`, or throw.
  PatternList(usize, Option<usize>),
  /// Start a pattern try-block.
  /// Jump to the first location on success and the second location on failure.
  /// * Used normally, `[(try ok err)] -> []` and jump to `ok`
  /// * If currently throwing, items are popped off the stack;
  ///   if `(try ok err)` is encountered then stop throwing and jump to `err`
  PatternTry(usize, usize),
  /// Exit pattern mode temporarily to evaluate an expression.
  /// * `[e] -> [e, (pause vars), e]` and exit pattern mode
  PatternTestPause,
  /// The `$foo$` pattern. This is equivalent to `(or 'foo ('foo))`.
  /// * `[e] -> []` and throw unless `e = 'foo` or `e = '(foo)`, where `'foo` is the given atom.
  PatternQExprAtom(AtomId),
}

// make sure that `Ir` doesn't get too big
#[cfg(all(target_arch = "x86_64", target_pointer_width = "64"))]
const _: [(); 40] = [(); std::mem::size_of::<Ir>()];

impl Ir {
  const fn drop(keep: bool, n: usize) -> Ir {
    if keep { Ir::DropAbove(n) } else { Ir::Drop(n) }
  }

  fn fmt_list(code: &[Ir], depth: usize, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    for (i, ir) in code.iter().enumerate() {
      for _ in 0..depth { f.write_str("  ")? }
      write!(f, "{i}: ")?;
      ir.fmt1(depth, fe, f)?;
      writeln!(f, ";")?;
    }
    Ok(())
  }

  fn fmt1(&self, depth: usize, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match *self {
      Ir::Drop(n) => write!(f, "drop {n}"),
      Ir::DropAbove(n) => write!(f, "drop-above {n}"),
      Ir::Undef => write!(f, "undef"),
      Ir::Dup => write!(f, "dup"),
      Ir::AssertScope(n) => write!(f, "assert-scope {n}"),
      Ir::EndScope(n) => write!(f, "end-scope {n}"),
      Ir::Local(n) => write!(f, "local x{n}"),
      Ir::Global(_, a) => write!(f, "global {}", fe.to(&a)),
      Ir::Const(ref e) => write!(f, "const {}", fe.to(e)),
      Ir::List(_, n) => write!(f, "list {n}"),
      Ir::DottedList(n) => write!(f, "dotted-list {n}"),
      Ir::App(false, _, n) => write!(f, "app {n}"),
      Ir::App(true, _, n) => write!(f, "tail-app {n}"),
      Ir::BuiltinApp(false, p, _, n) => write!(f, "app {p} {n}"),
      Ir::BuiltinApp(true, p, _, n) => write!(f, "tail-app {p} {n}"),
      Ir::ArityError(_, spec) => write!(f, "error {:?}", spec.arity_error()),
      Ir::AppHead(_) => write!(f, "app-head"),
      Ir::JumpUnless(ip) => write!(f, "jump-unless -> {ip}"),
      Ir::Jump(ip) => write!(f, "jump -> {ip}"),
      Ir::FocusStart(_) => write!(f, "focus-start"),
      Ir::RefineGoal(false) => write!(f, "refine-goal"),
      Ir::RefineGoal(true) => write!(f, "refine"),
      Ir::FocusFinish => write!(f, "focus-finish"),
      Ir::SetMergeStrategy(_, a) => write!(f, "set-merge-strategy {}", fe.to(&a)),
      Ir::LocalDef(n) => write!(f, "def x{n}"),
      Ir::GlobalDef(_, _, a) => write!(f, "def {}", fe.to(&a)),
      Ir::SetDoc(_, a) => write!(f, "set-doc _ {}", fe.to(&a)),
      Ir::Lambda(n, ref args) => {
        write!(f, "lambda{} ", if n == u8::MAX {""} else {"-global"})?;
        match args.1 {
          ProcSpec::Exact(n) => writeln!(f, "{n} [")?,
          ProcSpec::AtLeast(n) => writeln!(f, "{n}+ [")?,
        }
        Self::fmt_list(&args.2, depth + 1, fe, f)?;
        for _ in 0..depth { f.write_str("  ")? }
        write!(f, "]")
      }
      Ir::Branch(n, ip, None) => write!(f, "branch {n} -> {ip}"),
      Ir::Branch(n, ip, Some(_)) => write!(f, "branch-cont {n} -> {ip}"),
      Ir::TestPatternResume => write!(f, "test-resume"),
      Ir::BranchFail(_) => write!(f, "branch-fail"),
      Ir::Map => write!(f, "map"),
      Ir::Have => write!(f, "have"),
      Ir::RefineResume => write!(f, "refine-resume"),
      Ir::AddThm => write!(f, "add-thm"),
      Ir::MergeMap => write!(f, "merge-map"),
      Ir::PatternResult(false) => write!(f, "> fail"),
      Ir::PatternResult(true) => write!(f, "> skip"),
      Ir::PatternAtom(n) => write!(f, "> var {n}"),
      Ir::PatternQuoteAtom(a) => write!(f, "> '{}", fe.to(&a)),
      Ir::PatternString(ref s) => write!(f, "> \"{s}\""),
      Ir::PatternBool(b) => write!(f, "> #{b}"),
      Ir::PatternUndef => write!(f, "> #undef"),
      Ir::PatternNumber(ref n) => write!(f, "> {n}"),
      Ir::PatternMVar(MVarPattern::Unknown) => write!(f, "> (mvar)"),
      Ir::PatternMVar(MVarPattern::Any) => write!(f, "> (mvar ..)"),
      Ir::PatternMVar(MVarPattern::Simple) => write!(f, "> (mvar _ _)"),
      Ir::PatternGoal => write!(f, "> (goal _)"),
      Ir::PatternDottedList(n) => write!(f, "> (cons {n} _)"),
      Ir::PatternList(n, None) => write!(f, "> (list {n})"),
      Ir::PatternList(n, Some(k)) => write!(f, "> (list {n} __ {k})"),
      Ir::PatternTry(ip1, ip2) => write!(f, "> try(ok -> {ip1}, err -> {ip2})"),
      Ir::PatternTestPause => write!(f, "> test-pause"),
      Ir::PatternQExprAtom(a) => write!(f, "> ${}$", fe.to(&a)),
    }
  }
}

impl EnvDisplay for Ir {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.fmt1(0, fe, f)
  }
}

/// A formatter for [`Ir`] lists.
#[derive(Clone, Copy, Debug, EnvDebug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct IrList<'a>(pub usize, pub &'a [Ir]);

impl EnvDisplay for IrList<'_> {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    Ir::fmt_list(self.1, self.0, fe, f)
  }
}

/// The `(mvar)` patterns, which match a metavariable of different kinds.
#[derive(Clone, Copy, Debug, EnvDebug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum MVarPattern {
  /// The `(mvar)` pattern, which matches metavars with unknown type.
  Unknown,
  /// The `(mvar ...)` pattern, which matches metavars with any type.
  Any,
  /// The `(mvar bd s)` pattern, which matches a metavar with known type,
  /// matching the boundedness and sort against patterns `bd` ans `s`.
  Simple,
}

impl Remap for Ir {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      &Ir::Global(sp, a) => Ir::Global(sp, a.remap(r)),
      // Safety: The input Ir is already frozen
      Ir::Const(v) => Ir::Const(unsafe { v.freeze() }.remap(r)),
      &Ir::SetMergeStrategy(sp, a) => Ir::SetMergeStrategy(sp, a.remap(r)),
      &Ir::GlobalDef(sp, sp2, a) => Ir::GlobalDef(sp, sp2, a.remap(r)),
      &Ir::Lambda(name, ref args) => Ir::Lambda(name, Box::new((args.0, args.1, args.2.remap(r)))),
      &Ir::PatternQuoteAtom(a) => Ir::PatternQuoteAtom(a.remap(r)),
      &Ir::PatternQExprAtom(a) => Ir::PatternQExprAtom(a.remap(r)),
      _ => self.clone()
    }
  }
}

struct LocalCtx {
  names: HashMap<AtomId, Vec<usize>>,
  ctx: Vec<AtomId>,
}

impl LocalCtx {
  fn new() -> Self { Self {names: HashMap::new(), ctx: vec![]} }
  fn len(&self) -> usize { self.ctx.len() }
  fn get(&self, x: AtomId) -> Option<usize> {
    Some(*self.names.get(&x)?.last()?)
  }
  fn push(&mut self, x: AtomId) -> usize {
    let old = self.ctx.len();
    if x != AtomId::UNDER { self.names.entry(x).or_insert_with(Vec::new).push(old) }
    self.ctx.push(x);
    old
  }
  fn push_list(&mut self, xs: &[AtomId]) -> usize {
    let old = self.ctx.len();
    for &x in xs { self.push(x); }
    old
  }
  fn get_or_push(&mut self, x: AtomId) -> usize {
    self.get(x).unwrap_or_else(|| self.push(x))
  }

  fn pop(&mut self) {
    let x = self.ctx.pop().expect("context underflow");
    if x != AtomId::UNDER {self.names.get_mut(&x).expect("missing name").pop();}
  }
  fn restore(&mut self, n: usize) {
    while self.ctx.len() > n { self.pop() }
  }
}

struct LispParser<'a> {
  elab: &'a mut Elaborator,
  ctx: LocalCtx,
  code: Vec<Ir>,
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

type Var<'a> = (Span, AtomId, Vec<Item<'a>>);

#[derive(Clone, Copy)]
enum ExprsCtx {
  App,
  Eval(bool, bool),
  Focus,
}

#[derive(Clone, Copy)]
#[allow(clippy::struct_excessive_bools)]
struct ExprCtx {
  quote: bool,
  mask_def: bool,
  keep: bool,
  tail: bool,
  global: bool,
}

impl ExprCtx {
  const EVAL: Self = Self::eval(true);
  const DROP: Self = Self::eval(false);
  const fn eval(keep: bool) -> Self {
    Self { quote: false, mask_def: false, keep, global: false, tail: false }
  }
  const fn quote(self, quote: bool) -> Self { Self { quote, ..self } }
  const fn global(self, global: bool) -> Self { Self { global, ..self } }
  const fn tail(self, tail: bool) -> Self { Self { tail, ..self } }
  const fn mask_def(self) -> Self { Self { mask_def: true, ..self } }
}

impl<'a> LispParser<'a> {
  fn new(elab: &'a mut Elaborator) -> Self {
    Self { elab, ctx: LocalCtx::new(), code: vec![] }
  }

  fn push_def(&mut self,
    global: bool, span: Span, full: Span, doc: Option<DocComment>, x: AtomId
  ) {
    if global && x != AtomId::UNDER {
      for (i, ir) in self.code.iter_mut().rev().enumerate() {
        match ir {
          Ir::AssertScope(_) | Ir::EndScope(_) => {}
          Ir::Lambda(name, _) => {
            if let Ok(i) = i.try_into() { *name = i }
            break
          }
          _ => break
        }
      }
      self.code.push(Ir::GlobalDef(span, full, x));
      if let Some(doc) = doc {
        self.code.push(Ir::SetDoc(doc, x))
      }
    } else {
      let n = self.ctx.push(x);
      self.code.push(Ir::LocalDef(n));
    }
  }

  fn push_lambda(&mut self, sp: Span, n: usize, spec: ProcSpec, code: Arc<[Ir]>) {
    self.code.push(Ir::AssertScope(n));
    self.code.push(Ir::Lambda(u8::MAX, Box::new((sp, spec, code))))
  }

  fn restore(&mut self, n: usize) {
    if n < self.ctx.len() {
      self.code.push(Ir::EndScope(n));
      self.ctx.restore(n)
    }
  }

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

  fn def_ir(&mut self,
    sp: Span, keep: bool, tail: bool, es: &[SExpr], stack: Vec<Item<'_>>
  ) -> Result<(), ElabError> {
    let lambdas = stack.len();
    if !keep && lambdas != 0 { return Ok(()) }
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
    if lambdas == 0 {
      self.exprs(ExprsCtx::Eval(keep, tail), es)?;
      self.restore(len)
    } else {
      let mut orig = std::mem::take(&mut self.code);
      self.exprs(ExprsCtx::Eval(true, true), es)?;
      for (i, e) in stack.into_iter().enumerate() {
        let mut code = if i == lambdas - 1 { std::mem::take(&mut orig) } else { vec![] };
        std::mem::swap(&mut self.code, &mut code);
        match e {
          Item::List(xs) => {
            len -= xs.len();
            self.push_lambda(sp, len, ProcSpec::Exact(xs.len()), code.into())
          }
          Item::DottedList(xs, _) => {
            len -= xs.len() + 1;
            self.push_lambda(sp, len, ProcSpec::AtLeast(xs.len()), code.into())
          }
        }
      }
      self.ctx.restore(len)
    }
    Ok(())
  }

  fn def(&mut self, global: bool, tail: bool, e: &SExpr, es: &[SExpr]) -> Result<(Span, AtomId), ElabError> {
    let (sp, x, stack) = self.def_var(e)?;
    self.spans.insert(sp, if global {
      ObjectKind::Global(true, !stack.is_empty(), x)
    } else {
      ObjectKind::LispVar(true, !stack.is_empty(), x)
    });
    self.def_ir(sp, x != AtomId::UNDER, tail, es, stack)?;
    Ok((sp, x))
  }
}

impl<'a> LispParser<'a> {
  fn pop_builtin(&mut self) -> Option<BuiltinProc> {
    let Some(Ir::Const(v)) = self.code.last() else { return None };
    let p = v.unwrapped(|e|
      if let LispKind::Proc(Proc::Builtin(p)) = *e { Some(p) } else { None })?;
    self.code.pop();
    Some(p)
  }

  fn new_patch(&mut self) -> usize {
    let n = self.code.len();
    self.code.push(Ir::Undef);
    n
  }

  fn finish_patch(&mut self, n: usize, ir: impl FnOnce(usize) -> Ir) {
    let here = self.code.len();
    self.code[n] = ir(here)
  }

  fn list(&mut self, fsp: FileSpan, n: usize) {
    if self.code[self.code.len() - n..].iter().all(|ir| matches!(ir, Ir::Const(_))) {
      let args = self.code.drain(self.code.len() - n..).map(|ir| {
        let Ir::Const(e) = ir else { unreachable!() };
        e
      }).collect::<Box<[_]>>();
      self.code.push(Ir::Const(LispVal::list(args).span(fsp)));
    } else {
      self.code.push(Ir::List(fsp.span, n));
    }
  }

  fn dotted_list(&mut self, sp: Span, n: usize) {
    if n == 0 { return }
    if matches!(self.code.last(), Some(Ir::Const(_))) {
      let Some(Ir::Const(e)) = self.code.pop() else { unreachable!() };
      match &*e {
        LispKind::List(es) => {
          self.code.extend(es.iter().map(|e| Ir::Const(e.clone())));
          self.code.push(Ir::List(sp, n + es.len()))
        }
        LispKind::DottedList(es, e) => {
          self.code.extend(es.iter().map(|e| Ir::Const(e.clone())));
          self.code.push(Ir::Const(e.clone()));
          self.code.push(Ir::DottedList(n + es.len()))
        }
        _ => if self.code[self.code.len() - n..].iter().all(|ir| matches!(ir, Ir::Const(_))) {
          let args = self.code.drain(self.code.len() - n..).map(|ir| {
            let Ir::Const(e) = ir else { unreachable!() };
            e
          }).collect::<Box<[_]>>();
          self.code.push(Ir::Const(LispVal::dotted_list(args, e)))
        } else {
          self.code.push(Ir::Const(e));
          self.code.push(Ir::DottedList(n))
        }
      }
    } else {
      self.code.push(Ir::DottedList(n))
    }
  }

  fn parse_ident_or_syntax(&mut self, sp: Span, a: Atom) -> Result<AtomId, Syntax> {
    match Syntax::parse(self.ast.clone().span(sp), a) {
      Ok(s) => Err(s),
      Err(s) => Ok(self.get_atom(s))
    }
  }

  fn parse_atom(&mut self, sp: Span, a: Atom) -> Result<AtomId, ElabError> {
    self.parse_ident_or_syntax(sp, a).map_err(|_|
      ElabError::new_e(sp, "keyword in invalid position"))
  }

  fn parse_ident_raw(&mut self, e: &SExpr) -> Result<AtomId, ElabError> {
    if let SExprKind::Atom(a) = e.k {
      self.parse_atom(e.span, a)
    } else {
      Err(ElabError::new_e(e.span, "expected an identifier"))
    }
  }

  fn parse_ident(&mut self, e: &SExpr) -> Result<AtomId, ElabError> {
    let x = self.parse_ident_raw(e)?;
    self.spans.insert(e.span, ObjectKind::LispVar(true, false, x));
    Ok(x)
  }

  fn parse_idents(&mut self, es: &[SExpr]) -> Result<Vec<AtomId>, ElabError> {
    let mut xs = vec![];
    for e in es {xs.push(self.parse_ident(e)?)}
    Ok(xs)
  }

  fn qexpr(&mut self, keep: bool, e: QExpr) -> Result<(), ElabError> {
    let fsp = self.fspan(e.span);
    match e.k {
      QExprKind::IdentApp(sp, es) => {
        if keep {
          self.code.push(Ir::Const(LispVal::atom(
            self.elab.env.get_atom(self.ast.clone().span(sp))).span(self.fspan(sp))));
        }
        if !es.is_empty() {
          let n = es.len();
          for e in es.into_vec() { self.qexpr(keep, e)? }
          if keep { self.list(fsp, n + 1) }
        }
      }
      QExprKind::App(sp, t, es) => {
        let a = self.terms[t].atom;
        if keep {
          self.code.push(Ir::Const(LispVal::atom(a).span(self.fspan(sp))));
        }
        let n = es.len();
        for e in es.into_vec() { self.qexpr(keep, e)? }
        if keep { self.list(fsp, n + 1) }
      }
      QExprKind::Unquote(e) => {
        if self.mm0_mode {
          self.report(ElabError::warn(e.span, "(MM0 mode) unquotation not allowed"))
        }
        self.expr(ExprCtx::eval(keep), &e)?;
      }
    }
    Ok(())
  }

  fn exprs(&mut self, ctx: ExprsCtx, es: &[SExpr]) -> Result<usize, ElabError> {
    match ctx {
      ExprsCtx::Eval(keep, tail) => {
        if let [es @ .., last] = es {
          for e in es {
            self.expr(ExprCtx::DROP, e)?;
          }
          self.expr(ExprCtx::eval(keep).tail(tail), last)?;
        } else if keep {
          self.code.push(Ir::Undef);
        }
        Ok(keep.into())
      }
      ExprsCtx::App => {
        let mut n = 0;
        for e in es {
          if self.expr(ExprCtx::EVAL, e)? {
            n += 1;
          } else {
            assert!(matches!(self.code.pop(), Some(Ir::Undef)));
          }
        }
        Ok(n)
      }
      ExprsCtx::Focus => {
        for e in es {
          if self.expr(ExprCtx::EVAL, e)? {
            if matches!(self.code.last(), Some(Ir::Undef)) {
              self.code.pop();
            } else {
              self.code.push(Ir::RefineGoal(false));
            }
          }
        }
        self.code.push(Ir::FocusFinish);
        Ok(0)
      }
    }
  }

  fn let_var<'c>(&mut self, e: &'c SExpr) -> Result<(Var<'c>, &'c [SExpr]), ElabError> {
    match &e.k {
      SExprKind::List(es) if !es.is_empty() => {
        let (sp, x, stk) = self.def_var(&es[0])?;
        self.spans.insert(sp, ObjectKind::LispVar(true, !stk.is_empty(), x));
        Ok(((sp, x, stk), &es[1..]))
      }
      _ => Err(ElabError::new_e(e.span, "let: invalid spec"))
    }
  }

  fn let_(&mut self, mut rec: bool, keep: bool, tail: bool, es: &[SExpr]) -> Result<(), ElabError> {
    if es.is_empty() {
      if keep { self.code.push(Ir::Undef) }
      return Ok(())
    }
    let SExprKind::List(ls) = &es[0].k else {
      return Err(ElabError::new_e(es[0].span, "let: invalid spec"))
    };
    rec &= !ls.is_empty();
    if rec {
      let mut ds = Vec::with_capacity(ls.len());
      for l in ls {
        let ((sp, x, stk), e2) = self.let_var(l)?;
        let n = self.ctx.push(x);
        self.code.push(Ir::Undef);
        self.code.push(Ir::BuiltinApp(false, BuiltinProc::NewRef, Box::new((sp, sp)), 1));
        self.code.push(Ir::LocalDef(n));
        ds.push((sp, x, stk, e2, n));
      }
      for (sp, x, stk, e2, n) in ds {
        self.code.push(Ir::Local(n));
        self.def_ir(sp, true, false, e2, stk)?;
        self.code.push(Ir::BuiltinApp(false, BuiltinProc::SetWeak, Box::new((sp, sp)), 2));
        let m = self.ctx.push(x);
        self.code.push(Ir::LocalDef(m));
      }
    } else {
      for l in ls {
        let ((sp, x, stk), e2) = self.let_var(l)?;
        self.def_ir(sp, x != AtomId::UNDER, false, e2, stk)?;
        if x == AtomId::UNDER {
          self.code.push(Ir::Drop(1));
          self.code.push(Ir::Undef);
        } else {
          let n = self.ctx.push(x);
          self.code.push(Ir::LocalDef(n))
        }
      }
    }
    self.exprs(ExprsCtx::Eval(keep, tail && !rec), &es[1..])?;
    Ok(())
  }

  fn finish_dotted_list_pattern(&mut self,
    ctx: &mut LocalCtx, quote: bool, pfx: &[SExpr]
  ) -> Result<(), ElabError> {
    if !pfx.is_empty() {
      self.code.push(Ir::PatternDottedList(pfx.len()));
      for e in pfx { self.pattern(ctx, quote, e)? }
    }
    Ok(())
  }

  fn list_pattern(&mut self,
    ctx: &mut LocalCtx, quote: bool, es: &[SExpr]
  ) -> Result<(), ElabError> {
    let mut pfx = 0;
    macro_rules! finish {($e:expr) => {{
      self.finish_dotted_list_pattern(ctx, quote, &es[..pfx])?;
      { $e }
      return Ok(())
    }}}
    loop {
      match es[pfx..] {
        [] => {
          self.code.push(Ir::PatternList(pfx, None));
          for e in &es[..pfx] { self.pattern(ctx, quote, e)? }
          return Ok(())
        }
        [SExpr {span, k: SExprKind::Atom(a)}, ref e] if quote =>
          if self.ast.span_atom(span, a) == b"unquote" {
            finish!(self.pattern(ctx, false, e)?)
          }
        _ if quote => {},
        [ref head, ref args @ ..] => if let SExprKind::Atom(a) = head.k {
          match self.ast.span_atom(head.span, a) {
            b"quote" => {
              self.spans.insert(head.span, ObjectKind::Syntax(Syntax::Quote));
              if let [e] = args { finish!(self.pattern(ctx, true, e)?) }
              return Err(ElabError::new_e(head.span, "expected one argument"))
            }
            b"mvar" => {
              self.spans.insert(head.span, ObjectKind::PatternSyntax(PatternSyntax::MVar));
              match args {
                [] => finish!(self.code.push(Ir::PatternMVar(MVarPattern::Unknown))),
                &[SExpr {span, k: SExprKind::Atom(a)}]
                if matches!(self.ast.span_atom(span, a), b"___" | b"...") =>
                  finish!(self.code.push(Ir::PatternMVar(MVarPattern::Any))),
                [bd, s] => finish!({
                  self.code.push(Ir::PatternMVar(MVarPattern::Simple));
                  self.pattern(ctx, quote, bd)?;
                  self.pattern(ctx, quote, s)?;
                }),
                _ => return Err(ElabError::new_e(head.span, "expected zero or two arguments")),
              }
            }
            b"goal" => {
              self.spans.insert(head.span, ObjectKind::PatternSyntax(PatternSyntax::Goal));
              if let [e] = args {
                finish!({
                  self.code.push(Ir::PatternGoal);
                  self.pattern(ctx, quote, e)?
                })
              }
              return Err(ElabError::new_e(head.span, "expected one argument"))
            },
            b"and" => finish!({
              self.spans.insert(head.span, ObjectKind::PatternSyntax(PatternSyntax::And));
              self.patterns_and(ctx, args)?
            }),
            b"or" => finish!({
              self.spans.insert(head.span, ObjectKind::PatternSyntax(PatternSyntax::Or));
              self.patterns_or(ctx, args)?
            }),
            b"not" => finish!({
              self.spans.insert(head.span, ObjectKind::PatternSyntax(PatternSyntax::Not));
              let patch = self.new_patch();
              self.patterns_and(ctx, args)?;
              self.finish_patch(patch, |ip| Ir::PatternTry(ip, ip + 1));
              self.code.push(Ir::PatternResult(false))
            }),
            b"?" => {
              self.spans.insert(head.span, ObjectKind::PatternSyntax(PatternSyntax::Test));
              if let [test, tail @ ..] = args {
                finish!({
                  self.code.push(Ir::PatternTestPause);
                  self.expr(ExprCtx::EVAL.mask_def(), test)?;
                  if let Some(p) = self.pop_builtin() {
                    self.code.push(Ir::BuiltinApp(false, p, Box::new((test.span, test.span)), 1));
                  } else {
                    self.code.push(Ir::AppHead(test.span));
                  }
                  self.code.push(Ir::TestPatternResume);
                  self.patterns_and(ctx, tail)?
                })
              }
              return Err(ElabError::new_e(head.span, "expected at least one argument"))
            }
            b"cons" => {
              self.spans.insert(head.span, ObjectKind::PatternSyntax(PatternSyntax::Cons));
              if let [es2 @ .., e] = args {
                if es2.len() + pfx != 0 {
                  self.code.push(Ir::PatternDottedList(es2.len() + pfx));
                  for e in &es[..pfx] { self.pattern(ctx, quote, e)? }
                  for e in es2 { self.pattern(ctx, quote, e)? }
                }
                self.pattern(ctx, quote, e)?;
                return Ok(())
              }
              return Err(ElabError::new_e(head.span, "expected at least one argument"))
            }
            b"___" | b"..." => {
              self.spans.insert(head.span, ObjectKind::PatternSyntax(PatternSyntax::Rest));
              if args.is_empty() {
                self.code.push(Ir::PatternList(pfx, Some(0)));
                for e in &es[..pfx] { self.pattern(ctx, quote, e)? }
                return Ok(())
              }
              return Err(ElabError::new_e(head.span, "expected nothing after '...'"))
            }
            b"__" => {
              self.spans.insert(head.span, ObjectKind::PatternSyntax(PatternSyntax::RestN));
              if let [SExpr {span, k: SExprKind::Number(ref n)}] = *args {
                self.code.push(Ir::PatternList(pfx, Some(n.to_usize().ok_or_else(||
                  ElabError::new_e(span, "number out of range"))?)));
                for e in &es[..pfx] { self.pattern(ctx, quote, e)? }
                return Ok(())
              }
              return Err(ElabError::new_e(head.span, "expected number after '__'"))
            }
            _ => {}
          }
        }
      }
      pfx += 1;
    }
  }

  fn patterns_and(&mut self, ctx: &mut LocalCtx, args: &[SExpr]) -> Result<(), ElabError> {
    if let [args @ .., last] = args {
      for e in args {
        self.code.push(Ir::Dup);
        self.pattern(ctx, false, e)?;
      }
      self.pattern(ctx, false, last)
    } else {
      self.code.push(Ir::PatternResult(true));
      Ok(())
    }
  }

  fn patterns_or(&mut self, ctx: &mut LocalCtx, args: &[SExpr]) -> Result<(), ElabError> {
    match args {
      [] => self.code.push(Ir::PatternResult(false)),
      [e] => self.pattern(ctx, false, e)?,
      [args @ .., last] => {
        let mut jumps = vec![];
        for e in args {
          self.code.push(Ir::Dup);
          let patch = self.new_patch();
          self.pattern(ctx, false, e)?;
          jumps.push((patch, self.code.len()));
        }
        self.code.push(Ir::Dup);
        self.pattern(ctx, false, last)?;
        for (j, end) in jumps { self.finish_patch(j, |ip| Ir::PatternTry(ip, end)) }
        self.code.push(Ir::PatternResult(true));
      }
    }
    Ok(())
  }

  fn qexpr_pattern(&mut self, ctx: &mut LocalCtx, e: QExpr) -> Result<(), ElabError> {
    match e.k {
      QExprKind::IdentApp(sp, es) => {
        let head = match self.ast.clone().span(sp) {
          b"_" => Ir::PatternResult(true),
          s if es.is_empty() => Ir::PatternQExprAtom(self.elab.env.get_atom(s)),
          s => Ir::PatternQuoteAtom(self.elab.env.get_atom(s)),
        };
        match es.len() {
          0 => self.code.push(head),
          n => {
            self.code.push(Ir::PatternList(n + 1, None));
            self.code.push(head);
            for e in es.into_vec() { self.qexpr_pattern(ctx, e)? }
          }
        }
      }
      QExprKind::App(_, t, es) => {
        let x = self.terms[t].atom;
        match es.len() {
          0 => self.code.push(Ir::PatternQExprAtom(x)),
          n => {
            self.code.push(Ir::PatternList(n + 1, None));
            self.code.push(Ir::PatternQExprAtom(x));
            for e in es.into_vec() { self.qexpr_pattern(ctx, e)? }
          }
        }
      }
      QExprKind::Unquote(e) => self.pattern(ctx, false, &e)?
    }
    Ok(())
  }

  fn pattern(&mut self, ctx: &mut LocalCtx, quote: bool, e: &SExpr) -> Result<(), ElabError> {
    match &e.k {
      &SExprKind::Atom(a) => if quote {
        self.code.push(Ir::PatternQuoteAtom(
          self.elab.env.get_atom(self.elab.ast.span_atom(e.span, a))))
      } else {
        let x = self.parse_atom(e.span, a)?;
        if x == AtomId::UNDER {
          self.code.push(Ir::PatternResult(true))
        } else {
          self.spans.insert(e.span, ObjectKind::LispVar(true, false, x));
          self.code.push(Ir::PatternAtom(ctx.get_or_push(x)))
        }
      }
      SExprKind::DottedList(es, e) => {
        self.code.push(Ir::PatternDottedList(es.len()));
        for e in es { self.pattern(ctx, quote, e)? }
        self.pattern(ctx, quote, e)?;
      }
      SExprKind::Number(n) => self.code.push(Ir::PatternNumber(n.clone().into())),
      SExprKind::String(s) => self.code.push(Ir::PatternString(s.clone())),
      &SExprKind::Bool(b) => self.code.push(Ir::PatternBool(b)),
      SExprKind::Undef => self.code.push(Ir::PatternUndef),
      SExprKind::DocComment(_, e) => self.pattern(ctx, quote, e)?,
      SExprKind::List(es) => self.list_pattern(ctx, quote, es)?,
      &SExprKind::Formula(f) => {
        let q = self.parse_formula(f)?;
        self.qexpr_pattern(ctx, q)?
      }
    }
    Ok(())
  }

  fn branch(&mut self, keep: bool, tail: bool, e: &SExpr) -> Result<usize, ElabError> {
    let patch1 = self.new_patch();
    let (e, mut es) = match &e.k {
      SExprKind::List(es) if !es.is_empty() => (&es[0], &es[1..]),
      _ => return Err(ElabError::new_e(e.span, "match: improper syntax"))
    };
    let mut cont = AtomId::UNDER;
    if let Some(e2) = es.get(0) {
      if let SExprKind::List(v) = &e2.k {
        if let [SExpr {span, k: SExprKind::Atom(a)}, ref x] = **v {
          if self.ast.span_atom(span, a) == b"=>" {
            cont = self.parse_ident(x)?;
            es = &es[1..];
          }
        }
      }
    }
    let mut ctx = LocalCtx::new();
    self.pattern(&mut ctx, false, e)?;
    let vars = ctx.ctx.len();
    let start = self.ctx.push_list(&ctx.ctx);
    let cont = (cont != AtomId::UNDER).then(|| self.ctx.push(cont));
    self.exprs(ExprsCtx::Eval(keep, tail && cont.is_none()), es)?;
    if cont.is_some() { self.code.push(Ir::drop(keep, 1)) }
    self.restore(start);
    let patch3 = self.new_patch();
    self.finish_patch(patch1, |ip| Ir::Branch(vars, ip, cont));
    Ok(patch3)
  }

  fn match_(&mut self, keep: bool, tail: bool, sp: Span, es: &[SExpr]) -> Result<(), ElabError> {
    let mut patches = vec![];
    for e in es { patches.push(self.branch(keep, tail, e)?) }
    self.code.push(Ir::BranchFail(sp));
    for patch in patches { self.finish_patch(patch, Ir::Jump) }
    Ok(())
  }

  fn eval_atom(&mut self, keep: bool, sp: Span, x: AtomId) -> bool {
    match self.ctx.get(x) {
      None => {
        if keep {
          // Preload the value, if it exists; else look it up at run time
          let data = &self.data[x];
          if let Some(data) = &data.lisp {
            let val = data.val.clone();
            self.code.push(Ir::Const(val))
          } else if let Some(p) = BuiltinProc::from_bytes(&data.name) {
            self.code.push(Ir::Const(LispVal::proc(Proc::Builtin(p))))
          } else {
            self.code.push(Ir::Global(sp, x))
          }
        }
        false
      },
      Some(i) => {
        if keep { self.code.push(Ir::Local(i)) }
        true
      }
    }
  }

  fn expr(&mut self, ctx: ExprCtx, e: &SExpr) -> Result<bool, ElabError> {
    self.expr_doc(String::new(), ctx, e)
  }

  fn expr_doc(&mut self, mut doc: String, ctx: ExprCtx, e: &SExpr) -> Result<bool, ElabError> {
    macro_rules! span {($sp:expr, $e:expr) => {{$e.span(self.fspan($sp))}}}
    macro_rules! push_const {($e:expr) => {
      if ctx.keep { let e = $e; self.code.push(Ir::Const(e)) }
    }}
    let restore = self.ctx.len();
    match &e.k {
      &SExprKind::Atom(a) => if ctx.quote {
        push_const!(span!(e.span,
          match self.parse_ident_or_syntax(e.span, a) {
            Ok(x) => LispVal::atom(x),
            Err(s) => LispVal::syntax(s),
          }
        ))
      } else {
        match self.parse_atom(e.span, a)? {
          AtomId::UNDER => push_const!(span!(e.span, LispVal::atom(AtomId::UNDER))),
          x => {
            if self.eval_atom(ctx.keep, e.span, x) {
              self.spans.insert(e.span, ObjectKind::LispVar(false, false, x));
            } else {
              self.spans.insert(e.span, ObjectKind::Global(false, false, x));
            }
          }
        }
      }
      SExprKind::DottedList(es, e) => {
        if !ctx.quote {
          return Err(ElabError::new_e(e.span, "cannot evaluate an improper list"))
        }
        for e in es {
          if let SExprKind::Atom(a) = es[0].k {
            if Syntax::parse(self.ast.span(e.span), a) == Ok(Syntax::Unquote) {
              return Err(ElabError::new_e(e.span, "cannot evaluate an improper list"))
            }
          }
          self.expr(ExprCtx::EVAL.quote(true), e)?;
        }
        self.expr(ExprCtx::EVAL.quote(true), e)?;
        self.dotted_list(e.span, es.len());
      }
      SExprKind::Number(n) => push_const!(span!(e.span, LispVal::number(n.clone().into()))),
      SExprKind::String(s) => push_const!(span!(e.span, LispVal::string(s.clone()))),
      &SExprKind::Bool(b) => push_const!(span!(e.span, LispVal::bool(b))),
      SExprKind::Undef => push_const!(span!(e.span, LispVal::undef())),
      SExprKind::DocComment(doc2, e) => {
        // push an extra newline to separate multiple doc comments
        if !doc.is_empty() {doc.push('\n');}
        doc.push_str(doc2);
        return self.expr_doc(doc, ctx, e)
      }
      SExprKind::List(es) if es.is_empty() => push_const!(span!(e.span, LispVal::nil())),
      SExprKind::List(es) => if ctx.quote {
        let mut size = 0;
        let mut it = es.iter();
        loop {
          if let Some(arg) = it.next() {
            if let SExprKind::Atom(a) = arg.k {
              if Syntax::parse(self.ast.span(arg.span), a) == Ok(Syntax::Unquote) {
                let r = it.next().ok_or_else(||
                  ElabError::new_e(arg.span, "expected at least one argument"))?;
                self.expr(ExprCtx::eval(ctx.keep), r)?;
                if ctx.keep { self.dotted_list(e.span, size) }
                break
              }
            }
            size += 1;
            self.expr(ExprCtx::eval(ctx.keep).quote(true), arg)?;
          } else {
            if ctx.keep { let fsp = self.fspan(e.span); self.list(fsp, size) }
            break
          }
        }
      } else if let SExprKind::Atom(a) = es[0].k {
        match self.parse_ident_or_syntax(es[0].span, a) {
          Ok(AtomId::UNDER) => return Err(ElabError::new_e(es[0].span, "'_' is not a function")),
          Ok(x) => {
            let mut local = self.eval_atom(true, es[0].span, x);
            let p = self.pop_builtin();
            let n = self.exprs(ExprsCtx::App, &es[1..])?;
            if let Some(p) = p {
              local = false;
              let spec = p.spec();
              if spec.valid(n) {
                self.code.push(Ir::BuiltinApp(ctx.tail, p, Box::new((e.span, es[0].span)), n));
              } else {
                self.code.push(Ir::ArityError(e.span, spec));
              }
            } else {
              self.code.push(Ir::App(ctx.tail, Box::new((e.span, es[0].span)), n));
            };
            self.spans.insert(es[0].span, if local {
              ObjectKind::LispVar(false, true, x)
            } else {
              ObjectKind::Global(false, true, x)
            });
            if !ctx.keep { self.code.push(Ir::Drop(1)) }
          }
          Err(stx) => {
            self.spans.insert_if(Some(es[0].span), || ObjectKind::Syntax(stx));
            match stx {
              Syntax::Begin => { self.exprs(ExprsCtx::Eval(ctx.keep, ctx.tail), &es[1..])?; }
              Syntax::Define if es.len() < 2 => return Err(
                ElabError::new_e(es[0].span, "expected at least one argument")),
              Syntax::Define => {
                let (sp, x) = self.def(
                  !ctx.mask_def && ctx.global, ctx.tail && !ctx.keep, &es[1], &es[2..])?;
                if x != AtomId::UNDER && !ctx.mask_def {
                  let doc = if doc.is_empty() {None} else {Some(doc.into())};
                  self.push_def(ctx.global, e.span, sp, doc, x);
                }
                if ctx.keep { self.code.push(Ir::Undef) }
                if ctx.mask_def { self.restore(restore) }
                return Ok(false)
              }
              Syntax::Lambda if es.len() < 2 => return Err(
                ElabError::new_e(es[0].span, "expected at least one argument")),
              Syntax::Lambda => if ctx.keep {
                let orig = std::mem::take(&mut self.code);
                match &es[1].k {
                  SExprKind::List(xs) => {
                    let xs = self.parse_idents(xs)?;
                    let n = self.ctx.push_list(&xs);
                    self.exprs(ExprsCtx::Eval(true, true), &es[2..])?;
                    let code = std::mem::replace(&mut self.code, orig).into();
                    self.push_lambda(es[0].span, n, ProcSpec::Exact(xs.len()), code)
                  }
                  SExprKind::DottedList(xs, y) => {
                    let xs = self.parse_idents(xs)?;
                    let y = self.parse_ident(y)?;
                    let n = self.ctx.push_list(&xs);
                    self.ctx.push(y);
                    self.exprs(ExprsCtx::Eval(true, true), &es[2..])?;
                    let code = std::mem::replace(&mut self.code, orig).into();
                    self.push_lambda(es[0].span, n, ProcSpec::AtLeast(xs.len()), code)
                  }
                  _ => {
                    let x = self.parse_ident(&es[1])?;
                    let n = self.ctx.push(x);
                    self.exprs(ExprsCtx::Eval(true, true), &es[2..])?;
                    let code = std::mem::replace(&mut self.code, orig).into();
                    self.push_lambda(es[0].span, n, ProcSpec::AtLeast(0), code)
                  }
                }
              }
              Syntax::Quote if es.len() < 2 => return Err(
                ElabError::new_e(es[0].span, "expected at least one argument")),
              Syntax::Quote => { self.expr(ExprCtx::eval(ctx.keep).quote(true), &es[1])?; }
              Syntax::Unquote if es.len() < 2 => return Err(
                ElabError::new_e(es[0].span, "expected at least one argument")),
              Syntax::Unquote => { self.expr(ExprCtx::eval(ctx.keep), &es[1])?; }
              Syntax::If if 3 <= es.len() && es.len() <= 4 => {
                self.expr(ExprCtx::EVAL.mask_def(), &es[1])?;
                let patch1 = self.new_patch();
                self.expr(ExprCtx::eval(ctx.keep).mask_def(), &es[2])?;
                let patch2 = self.new_patch();
                self.finish_patch(patch1, Ir::JumpUnless);
                match es.get(3) {
                  None => if ctx.keep { self.code.push(Ir::Undef) },
                  Some(e) => { self.expr(ExprCtx::eval(ctx.keep).mask_def(), e)?; }
                }
                self.finish_patch(patch2, Ir::Jump);
              }
              Syntax::If => return Err(
                ElabError::new_e(es[0].span, "expected two or three arguments")),
              Syntax::Focus => {
                self.code.push(Ir::FocusStart(es[0].span));
                self.exprs(ExprsCtx::Focus, &es[1..])?;
              }
              Syntax::Let => self.let_(false, ctx.keep, ctx.tail, &es[1..])?,
              Syntax::Letrec => self.let_(true, ctx.keep, ctx.tail, &es[1..])?,
              Syntax::SetMergeStrategy if 2 <= es.len() && es.len() <= 3 => {
                let a = self.parse_ident_raw(&es[1])?;
                self.spans.insert(es[1].span, ObjectKind::Global(false, false, a));
                if let Some(e) = es.get(2) { self.expr(ExprCtx::EVAL, e)?; }
                else { self.code.push(Ir::Undef) }
                self.code.push(Ir::SetMergeStrategy(es[0].span, a));
                if ctx.keep { self.code.push(Ir::Undef) }
              }
              Syntax::SetMergeStrategy => return Err(
                ElabError::new_e(es[0].span, "expected one or two arguments")),
              Syntax::Match if es.len() < 2 => return Err(
                ElabError::new_e(es[0].span, "expected at least one argument")),
              Syntax::Match => {
                self.expr(ExprCtx::EVAL.mask_def(), &es[1])?;
                self.match_(ctx.keep, ctx.tail, es[0].span, &es[2..])?
              }
              Syntax::MatchFn | Syntax::MatchFns => {
                let spec = match stx {
                  Syntax::MatchFn => ProcSpec::Exact(1),
                  Syntax::MatchFns => ProcSpec::AtLeast(0),
                  _ => unreachable!()
                };
                let i = self.ctx.push(AtomId::UNDER);
                let orig = std::mem::take(&mut self.code);
                self.code.push(Ir::Local(i));
                self.match_(true, true, es[0].span, &es[1..])?;
                let code = std::mem::replace(&mut self.code, orig).into();
                self.push_lambda(es[0].span, i, spec, code);
              }
            }
          }
        }
      } else {
        self.expr(ExprCtx::EVAL.mask_def(), &es[0])?;
        let n = self.exprs(ExprsCtx::App, &es[1..])?;
        self.code.push(Ir::App(ctx.tail, Box::new((e.span, es[0].span)), n));
        if !ctx.keep { self.code.push(Ir::Drop(1)) }
      },
      &SExprKind::Formula(f) => {
        let q = self.parse_formula(f)?;
        self.qexpr(ctx.keep, q)?
      }
    };
    self.restore(restore);
    Ok(true)
  }
}

impl Elaborator {
  /// Parse a lisp `SExpr` from the surface syntax into an `IR` object suitable for evaluation.
  pub fn parse_lisp(&mut self, global: bool, e: &SExpr) -> Result<Vec<Ir>, ElabError> {
    self.parse_lisp_doc(global, e, String::new())
  }

  /// Parse a lisp `SExpr` from the surface syntax into an `IR` object suitable for evaluation.
  /// The `doc` argument is an additional doc string, if applicable.
  pub fn parse_lisp_doc(&mut self, global: bool, e: &SExpr, doc: String) -> Result<Vec<Ir>, ElabError> {
    let mut p = LispParser::new(self);
    p.expr_doc(doc, ExprCtx::EVAL.global(global), e)?;
    Ok(p.code)
  }

  /// Parse and evaluate a lisp expression being used as a proof. Essentially the same
  /// as evaluating `(refine e)` where `e` is the input expression.
  pub fn parse_refine_lisp(&mut self, e: &SExpr) -> Result<Vec<Ir>, ElabError> {
    let mut p = LispParser::new(self);
    p.expr(ExprCtx::EVAL.mask_def(), e)?;
    p.code.push(Ir::RefineGoal(true));
    Ok(p.code)
  }

  /// Parse a `QExpr`, the result of parsing a math formula,
  /// into an `IR` object suitable for evaluation. (Usually this will be a `IR::Const`,
  /// but `QExpr`'s can contain antiquotations which require evaluation.)
  pub fn parse_qexpr(&mut self, e: QExpr) -> Result<Vec<Ir>, ElabError> {
    let mut p = LispParser::new(self);
    p.qexpr(true, e)?;
    Ok(p.code)
  }
}
