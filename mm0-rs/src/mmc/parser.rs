//! The MMC parser, which takes lisp literals and maps them to MMC AST.
use std::mem;
use std::sync::Arc;
use std::collections::HashMap;
use num::BigInt;
use crate::util::{Span, FileSpan};
use crate::elab::{Result, ElabError,
  environment::{AtomID, Environment},
  lisp::{LispKind, LispVal, Uncons, print::FormatEnv},
  local_context::try_get_span};

/// An argument to a function.
#[derive(Debug)]
pub struct Arg {
  /// The name of the argument, if not `_`.
  pub name: Option<(FileSpan, AtomID)>,
  /// True if the argument is a ghost variable (computationally irrelevant).
  pub ghost: bool,
  /// The (unparsed) type of the argument.
  pub ty: LispVal,
}

impl PartialEq<Arg> for Arg {
  fn eq(&self, other: &Arg) -> bool {
    let b = match (&self.name, &other.name) {
      (None, None) => true,
      (&Some((_, a)), &Some((_, b))) => a == b,
      _ => false
    };
    b && self.ghost == other.ghost && self.ty == other.ty
  }
}
impl Eq for Arg {}

/// The type of variant, or well founded order that recursions decrease.
#[derive(PartialEq, Eq, Debug)]
pub enum VariantType {
  /// This variant is a nonnegative natural number which decreases to 0.
  Down,
  /// This variant is a natural number or integer which increases while
  /// remaining less than this constant.
  UpLt(LispVal),
  /// This variant is a natural number or integer which increases while
  /// remaining less than or equal to this constant.
  UpLe(LispVal)
}

/// A variant is a pure expression, together with a
/// well founded order that decreases on all calls.
pub type Variant = (LispVal, VariantType);

/// An invariant is a local variable in a loop, that is passed as an argument
/// on recursive calls.
#[derive(Debug)]
pub struct Invariant {
  /// The variable name.
  pub name: AtomID,
  /// True if the variable is ghost (computationally irrelevant).
  pub ghost: bool,
  /// The type of the variable, or none for inferred.
  pub ty: Option<LispVal>,
  /// The initial value of the variable.
  pub val: Option<Expr>,
}

/// A block is a local scope. Like functions, this requires explicit importing
/// of variables from external scope if they will be mutated after the block.
#[derive(Debug)]
pub struct Block {
  /// The list of variables that will be updated by the block. Variables
  /// in external scope that are not in this list are treated as read only.
  pub muts: Box<[AtomID]>,
  /// The statements of the block.
  pub stmts: Box<[Expr]>
}

/// A tuple pattern, which destructures the results of assignments from functions with
/// mutiple return values, as well as explicit tuple values and structs.
#[derive(Debug)]
pub enum TuplePattern {
  /// A variable binding, or `_` for an ignored binding.
  Name(AtomID, Option<FileSpan>),
  /// A type ascription. The type is unparsed.
  Typed(Box<TuplePattern>, LispVal),
  /// A tuple, with the given arguments.
  Tuple(Box<[TuplePattern]>),
}

/// A pattern, the left side of a switch statement.
#[derive(Debug)]
pub enum Pattern {
  /// A variable binding, unless this is the name of a constant in which case
  /// it is a constant value.
  VarOrConst(AtomID),
  /// A numeric literal.
  Number(BigInt),
  /// A hypothesis pattern, which binds the first argument to a proof that the
  /// scrutinee satisfies the pattern argument.
  Hyped(AtomID, Box<Pattern>),
  /// A pattern guard: Matches the inner pattern, and then if the expression returns
  /// true, this is also considered to match.
  With(Box<(Pattern, Expr)>),
  /// A disjunction of patterns.
  Or(Box<[Pattern]>),
}

/// An expression or statement. A block is a list of expressions.
#[derive(Debug)]
pub enum Expr {
  /// A `()` literal.
  Nil,
  /// A variable reference.
  Var(AtomID),
  /// A number literal.
  Number(BigInt),
  /// A let binding.
  Let {
    /// True if the `rhs` expression should not be evaluated,
    /// and all variables in the declaration should be considered ghost.
    ghost: bool,
    /// A tuple pattern, containing variable bindings.
    lhs: TuplePattern,
    /// The expression to evaluate, or `None` for uninitialized.
    rhs: Option<Box<Expr>>,
  },
  /// A function call (or something that looks like one at parse time).
  Call {
    /// The function to call.
    f: AtomID,
    /// The function arguments.
    args: Box<[Expr]>,
    /// The variant, if needed.
    variant: Option<Variant>,
  },
  /// An entailment proof, which takes a proof of `P1 * ... * Pn => Q` and expressions proving
  /// `P1, ..., Pn` and is a hypothesis of type `Q`.
  Entail(LispVal, Box<[Expr]>),
  /// A block scope.
  Block(Block),
  /// A label, which looks exactly like a local function but has no independent stack frame.
  /// They are called like regular functions but can only appear in tail position.
  Label {
    /// The name of the label
    name: AtomID,
    /// The arguments of the label
    args: Box<[Arg]>,
    /// The variant, for recursive calls
    variant: Option<Variant>,
    /// The code that is executed when you jump to the label
    body: Block,
  },
  /// An if-then-else expression (at either block or statement level). The initial atom names
  /// a hypothesis that the expression is true in one branch and false in the other.
  If(Box<(Option<AtomID>, Expr, Expr, Expr)>),
  /// A switch (pattern match) statement, given the initial expression and a list of match arms.
  Switch(Box<Expr>, Box<[(Pattern, Expr)]>),
  /// A while loop.
  While {
    /// A hypothesis that the condition is true in the loop and false after it.
    hyp: Option<AtomID>,
    /// The loop condition.
    cond: Box<Expr>,
    /// The variant, which must decrease on every round around the loop.
    var: Option<Variant>,
    /// The invariants, which must be supplied on every round around the loop.
    invar: Box<[Invariant]>,
    /// The body of the loop.
    body: Block,
  },
  /// A hole `_`, which is a compile error but queries the compiler to provide a type context.
  Hole(FileSpan),
}

/// A procedure kind, which defines the different kinds of function-like declarations.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum ProcKind {
  /// A (pure) function, which generates a logic level function as well as code. (Body required.)
  Func,
  /// A procedure, which is opaque except for its type. (Body provided.)
  Proc,
  /// A precedure declaration, used for forward declarations. (Body not provided.)
  ProcDecl,
  /// An intrinsic declaration, which is only here to put the function declaration in user code.
  /// The compiler will ensure this matches an existing intrinsic, and intrinsics cannot be
  /// called until they are declared using an `intrinsic` declaration.
  Intrinsic,
}

/// A procedure (or function or intrinsic), a top level item similar to function declarations in C.
#[derive(Debug)]
pub struct Proc {
  /// The type of declaration: `func`, `proc`, `proc` with no body, or `intrinsic`.
  pub kind: ProcKind,
  /// The name of the procedure.
  pub name: AtomID,
  /// The span of the procedure name.
  pub span: Option<FileSpan>,
  /// The arguments of the procedure.
  pub args: Box<[Arg]>,
  /// The return values of the procedure. (Functions and procedures return multiple values in MMC.)
  pub rets: Box<[Arg]>,
  /// The variant, used for recursive functions.
  pub variant: Option<Variant>,
  /// The body of the procedure.
  pub body: Block,
}

impl Proc {
  /// Checks if this proc equals `other`, ignoring the `body` and `kind` fields.
  /// (This is how we validate a proc against a proc decl.)
  pub fn eq_decl(&self, other: &Proc) -> bool {
    self.name == other.name &&
    self.args == other.args &&
    self.rets == other.rets &&
    self.variant == other.variant &&
    self.body.muts == other.body.muts
  }
}

/// A field of a struct.
#[derive(Debug)]
pub struct Field {
  /// The name of the field.
  pub name: AtomID,
  /// True if the field is computationally irrelevant.
  pub ghost: bool,
  /// The type of the field (unparsed).
  pub ty: LispVal,
}

/// A top level program item. (A program AST is a list of program items.)
#[derive(Debug)]
pub enum AST {
  /// A procedure, behind an Arc so it can be cheaply copied.
  Proc(Arc<Proc>),
  /// A global variable declaration.
  Global {
    /// The variable(s) being declared
    lhs: TuplePattern,
    /// The value of the declaration
    rhs: Option<Box<Expr>>,
  },
  /// A constant declaration.
  Const {
    /// The constant(s) being declared
    lhs: TuplePattern,
    /// The value of the declaration
    rhs: Box<Expr>,
  },
  /// A type definition.
  Typedef {
    /// The name of the newly declared type
    name: AtomID,
    /// The span of the name
    span: Option<FileSpan>,
    /// The arguments of the type declaration, for a parametric type
    args: Box<[Arg]>,
    /// The value of the declaration (another type)
    val: LispVal,
  },
  /// A structure definition.
  Struct {
    /// The name of the structure
    name: AtomID,
    /// The span of the name
    span: Option<FileSpan>,
    /// The parameters of the type
    args: Box<[Arg]>,
    /// The fields of the structure
    fields: Box<[Field]>,
  },
}

impl AST {
  /// Make a new `AST::Proc`.
  pub fn proc(p: Proc) -> AST { AST::Proc(Arc::new(p)) }
}

macro_rules! make_keywords {
  {$($(#[$attr:meta])* $x:ident: $e:expr,)*} => {
    make_keywords! {@IMPL $($(#[$attr])* $x concat!("The keyword `", $e, "`.\n"), $e,)*}
  };
  {@IMPL $($(#[$attr:meta])* $x:ident $doc0:expr, $e:expr,)*} => {
    /// The type of MMC keywords, which are atoms with a special role in the MMC parser.
    #[derive(Debug, PartialEq, Eq, Copy, Clone)]
    pub enum Keyword { $(#[doc=$doc0] $(#[$attr])* $x),* }

    impl Environment {
      /// Make the initial MMC keyword map in the given environment.
      pub fn make_keywords(&mut self) -> HashMap<AtomID, Keyword> {
        let mut atoms = HashMap::new();
        $(atoms.insert(self.get_atom($e), Keyword::$x);)*
        atoms
      }
    }
  }
}

make_keywords! {
  Add: "+",
  Arrow: "=>",
  Begin: "begin",
  Colon: ":",
  ColonEq: ":=",
  Const: "const",
  Entail: "entail",
  Func: "func",
  Finish: "finish",
  Ghost: "ghost",
  Global: "global",
  Intrinsic: "intrinsic",
  Invariant: "invariant",
  If: "if",
  Le: "<=",
  Lt: "<",
  Mut: "mut",
  Or: "or",
  Proc: "proc",
  Struct: "struct",
  Switch: "switch",
  Typedef: "typedef",
  Variant: "variant",
  While: "while",
  With: "with",
}

/// The parser, which has no real state of its own but needs access to the
/// formatting environment for printing, and the keyword list.
#[derive(Debug)]
pub struct Parser<'a> {
  /// The formatting environment.
  pub fe: FormatEnv<'a>,
  /// The keyword list.
  pub kw: &'a HashMap<AtomID, Keyword>,
  /// The base file span, for error reporting.
  pub fsp: FileSpan,
}

fn head_atom(e: &LispVal) -> Option<(AtomID, Uncons)> {
  let mut u = Uncons::from(e.clone());
  Some((u.next()?.as_atom()?, u))
}

impl<'a> Parser<'a> {
  fn try_get_span(&self, e: &LispVal) -> Span {
    try_get_span(&self.fsp, &e)
  }
  fn try_get_fspan(&self, e: &LispVal) -> FileSpan {
    FileSpan { file: self.fsp.file.clone(), span: self.try_get_span(e) }
  }

  fn head_keyword(&self, e: &LispVal) -> Option<(Keyword, Uncons)> {
    let mut u = Uncons::from(e.clone());
    Some((*self.kw.get(&u.next()?.as_atom()?)?, u))
  }

  fn parse_variant(&self, e: &LispVal) -> Option<(LispVal, VariantType)> {
    if let Some((Keyword::Variant, mut u)) = self.head_keyword(e) {
      Some((u.next()?, match u.next() {
        None => VariantType::Down,
        Some(e) => match *self.kw.get(&e.as_atom()?)? {
          Keyword::Lt => VariantType::UpLt(u.next()?),
          Keyword::Le => VariantType::UpLe(u.next()?),
          _ => None?
        }
      }))
    } else {None}
  }

  fn parse_arg1(&self, e: LispVal, ghost: bool) -> Result<Arg> {
    if let Some((AtomID::COLON, mut u)) = head_atom(&e) {
      match (u.next(), u.next(), u.is_empty()) {
        (Some(ea), Some(ty), true) => {
          let a = ea.as_atom().ok_or_else(||
            ElabError::new_e(self.try_get_span(&ea), "argument syntax error: expecting function name"))?;
          let name = if a == AtomID::UNDER {None} else {
            Some((self.try_get_fspan(&ea), a))
          };
          Ok(Arg { ghost, name, ty })
        }
        _ => Err(ElabError::new_e(self.try_get_span(&e), "syntax error in function arg"))
      }
    } else {Ok(Arg { ghost, name: None, ty: e })}
  }

  fn parse_arg(&self, e: LispVal, args: &mut Vec<Arg>, muts: Option<&mut Vec<AtomID>>) -> Result<()> {
    match (self.head_keyword(&e), muts) {
      (Some((Keyword::Ghost, u)), _) => for e in u {
        args.push(self.parse_arg1(e, true)?)
      }
      (Some((Keyword::Mut, u)), Some(muts)) => for e in u {
        muts.push(e.as_atom().ok_or_else(||
          ElabError::new_e(self.try_get_span(&e), "mut: expected an atom"))?)
      }
      _ => args.push(self.parse_arg1(e, false)?)
    }
    Ok(())
  }

  fn parse_tuple_pattern(&self, e: LispVal) -> Result<TuplePattern> {
    Ok(match &*e.unwrapped_arc() {
      &LispKind::Atom(a) => TuplePattern::Name(a, e.fspan()),
      LispKind::List(_) | LispKind::DottedList(_, _) => {
        if let Some((Keyword::Colon, mut u)) = self.head_keyword(&e) {
          if let (Some(e), Some(ty), true) = (u.next(), u.next(), u.is_empty()) {
            return Ok(TuplePattern::Typed(Box::new(self.parse_tuple_pattern(e)?), ty))
          }
          return Err(ElabError::new_e(self.try_get_span(&e), "':' syntax error"))
        }
        let mut args = vec![];
        for e in Uncons::from(e) {args.push(self.parse_tuple_pattern(e)?)}
        TuplePattern::Tuple(args.into_boxed_slice())
      }
      _ => return Err(ElabError::new_e(self.try_get_span(&e),
        format!("tuple pattern syntax error: {}", self.fe.to(&e))))
    })
  }

  fn parse_pattern(&self, e: LispVal) -> Result<Pattern> {
    Ok(match &*e.unwrapped_arc() {
      &LispKind::Atom(a) => Pattern::VarOrConst(a),
      LispKind::List(_) | LispKind::DottedList(_, _) => match self.head_keyword(&e) {
        Some((Keyword::Colon, mut u)) =>
          if let (Some(h), Some(p), true) = (u.next(), u.next(), u.is_empty()) {
            let h = h.as_atom().ok_or_else(||
              ElabError::new_e(self.try_get_span(&h), "expecting hypothesis name"))?;
            Pattern::Hyped(h, Box::new(self.parse_pattern(p)?))
          } else {
            return Err(ElabError::new_e(self.try_get_span(&e), "':' syntax error"))
          },
        Some((Keyword::Or, u)) => {
          let mut args = vec![];
          for e in u {args.push(self.parse_pattern(e)?)}
          Pattern::Or(args.into_boxed_slice())
        }
        Some((Keyword::With, mut u)) =>
          if let (Some(p), Some(g), true) = (u.next(), u.next(), u.is_empty()) {
            Pattern::With(Box::new((self.parse_pattern(p)?, self.parse_expr(g)?)))
          } else {
            return Err(ElabError::new_e(self.try_get_span(&e), "'with' syntax error"))
          },
        _ => return Err(ElabError::new_e(self.try_get_span(&e), "pattern syntax error"))
      }
      LispKind::Number(n) => Pattern::Number(n.clone()),
      _ => return Err(ElabError::new_e(self.try_get_span(&e), "pattern syntax error"))
    })
  }

  fn parse_decl(&self, e: LispVal) -> Result<(TuplePattern, Option<Box<Expr>>)> {
    if let Some((Keyword::ColonEq, mut u)) = self.head_keyword(&e) {
      if let (Some(lhs), Some(rhs), true) = (u.next(), u.next(), u.is_empty()) {
        Ok((self.parse_tuple_pattern(lhs)?, Some(Box::new(self.parse_expr(rhs)?))))
      } else {
        Err(ElabError::new_e(self.try_get_span(&e), "decl: syntax error"))
      }
    } else {
      Ok((self.parse_tuple_pattern(e)?, None))
    }
  }

  fn parse_invariant_decl(&self, ghost: bool, e: LispVal) -> Result<Invariant> {
    match self.parse_decl(e.clone())? {
      (TuplePattern::Typed(v, ty), val) => if let TuplePattern::Name(name, _) = *v {
        return Ok(Invariant {name, ghost, ty: Some(ty), val: val.map(|v| *v)})
      },
      (TuplePattern::Name(name, _), val) =>
        return Ok(Invariant {name, ghost, ty: None, val: val.map(|v| *v)}),
      _ => {}
    }
    Err(ElabError::new_e(self.try_get_span(&e), "while: unexpected invariant"))
  }

  fn parse_expr(&self, e: LispVal) -> Result<Expr> {
    Ok(match &*e.unwrapped_arc() {
      &LispKind::Atom(AtomID::UNDER) => Expr::Hole(self.try_get_fspan(&e)),
      &LispKind::Atom(a) => Expr::Var(a),
      LispKind::List(_) | LispKind::DottedList(_, _) => match self.head_keyword(&e) {
        Some((Keyword::Ghost, mut u)) =>
          if let (Some(e), true) = (u.next(), u.is_empty()) {
            let (lhs, rhs) = self.parse_decl(e)?;
            Expr::Let {ghost: true, lhs, rhs}
          } else {
            return Err(ElabError::new_e(self.try_get_span(&e), "ghost: syntax error"))
          },
        Some((Keyword::Colon, _)) |
        Some((Keyword::ColonEq, _)) => {
          let (lhs, rhs) = self.parse_decl(e)?;
          Expr::Let {ghost: false, lhs, rhs}
        }
        Some((Keyword::If, mut u)) =>
          if let (Some(cond), Some(tru)) = (u.next(), u.next()) {
            let (hyp, cond) = match self.head_keyword(&cond) {
              Some((Keyword::Colon, mut u)) =>
                if let (Some(h), Some(cond), true) = (u.next(), u.next(), u.is_empty()) {
                  let h = h.as_atom().ok_or_else(||
                    ElabError::new_e(self.try_get_span(&h), "expecting hypothesis name"))?;
                  (if h == AtomID::UNDER {None} else {Some(h)}, cond)
                } else {
                  return Err(ElabError::new_e(self.try_get_span(&cond), "':' syntax error"))
                },
              _ => (None, cond),
            };
            let (cond, tru) = (self.parse_expr(cond)?, self.parse_expr(tru)?);
            let fal = match u.next() {
              Some(fal) if u.is_empty() => self.parse_expr(fal)?,
              None => Expr::Nil,
              _ => return Err(ElabError::new_e(self.try_get_span(&e), "if: syntax error")),
            };
            Expr::If(Box::new((hyp, cond, tru, fal)))
          } else {
            return Err(ElabError::new_e(self.try_get_span(&e), "if: syntax error"))
          },
        Some((Keyword::Switch, mut u)) => {
          let c = self.parse_expr(u.next().ok_or_else(||
            ElabError::new_e(self.try_get_span(&e), "switch: syntax error"))?)?;
          let mut branches = vec![];
          for e in u {
            if let Some((Keyword::Arrow, mut u)) = self.head_keyword(&e) {
              if let (Some(p), Some(e), true) = (u.next(), u.next(), u.is_empty()) {
                branches.push((self.parse_pattern(p)?, self.parse_expr(e)?));
              } else {
                return Err(ElabError::new_e(self.try_get_span(&e), "switch: syntax error"))
              }
            } else {
              return Err(ElabError::new_e(self.try_get_span(&e), "switch: syntax error"))
            }
          }
          Expr::Switch(Box::new(c), branches.into_boxed_slice())
        }
        Some((Keyword::While, mut u)) => {
          let c = u.next().ok_or_else(||
            ElabError::new_e(self.try_get_span(&e), "while: syntax error"))?;
          let (hyp, c) = if let Some((Keyword::Invariant, mut u)) = self.head_keyword(&c) {
            if let (Some(h), Some(c), true) = (u.next().and_then(|a| a.as_atom()), u.next(), u.is_empty()) {
              (Some(h), c)
            } else {
              return Err(ElabError::new_e(self.try_get_span(&e), "while: bad pattern"))
            }
          } else {(None, c)};
          let c = self.parse_expr(c)?;
          let mut invar = vec![];
          let mut muts = vec![];
          let mut var = None;
          let mut body = vec![];
          while let Some(e) = u.next() {
            if let Some(v) = self.parse_variant(&e) {
              if mem::replace(&mut var, Some(v)).is_some() {
                return Err(ElabError::new_e(self.try_get_span(&e), "while: two variants"))
              }
            } else if let Some((Keyword::Invariant, u)) = self.head_keyword(&e) {
              for e in u {
                match self.head_keyword(&e) {
                  Some((Keyword::Mut, u)) => for e in u {
                    muts.push(e.as_atom().ok_or_else(||
                      ElabError::new_e(self.try_get_span(&e), "mut: expected an atom"))?)
                  },
                  Some((Keyword::Ghost, u)) => for e in u {
                    invar.push(self.parse_invariant_decl(true, e)?)
                  },
                  _ => invar.push(self.parse_invariant_decl(false, e)?),
                }
              }
            } else {
              body.push(self.parse_expr(e)?);
              break
            }
          }
          for e in u {body.push(self.parse_expr(e)?)}
          Expr::While {
            hyp, cond: Box::new(c), var,
            invar: invar.into_boxed_slice(),
            body: Block { muts: muts.into(), stmts: body.into_boxed_slice() }
          }
        }
        Some((Keyword::Begin, mut u)) => {
          let mut muts = vec![];
          let mut body = vec![];
          while let Some(e) = u.next() {
            if let Some((Keyword::Mut, u)) = self.head_keyword(&e) {
              for e in u {
                muts.push(e.as_atom().ok_or_else(||
                  ElabError::new_e(self.try_get_span(&e), "mut: expected an atom"))?)
              }
            } else {
              body.push(self.parse_expr(e)?);
              break
            }
          }
          for e in u {body.push(self.parse_expr(e)?)}
          Expr::Block(Block {muts: muts.into(), stmts: body.into_boxed_slice()})
        }
        Some((Keyword::Entail, mut u)) => {
          let mut last = u.next().ok_or_else(||
            ElabError::new_e(self.try_get_span(&e), "entail: expected proof"))?;
          let mut args = vec![];
          for e in u {
            args.push(self.parse_expr(mem::replace(&mut last, e))?)
          }
          Expr::Entail(last, args.into_boxed_slice())
        }
        _ => {
          let mut u = Uncons::from(e);
          match u.next() {
            None => Expr::Nil,
            Some(e) => match self.head_keyword(&e) {
              Some((Keyword::Begin, mut u1)) => {
                let name = u1.next().and_then(|e| e.as_atom()).ok_or_else(||
                  ElabError::new_e(self.try_get_span(&e), "label: expected label name"))?;
                let mut args = vec![];
                let mut muts = vec![];
                let mut variant = None;
                for e in u1 {
                  if let Some(v) = self.parse_variant(&e) {
                    if mem::replace(&mut variant, Some(v)).is_some() {
                      return Err(ElabError::new_e(self.try_get_span(&e), "label: two variants"))
                    }
                  } else {
                    self.parse_arg(e, &mut args, Some(&mut muts))?
                  }
                }
                let mut body = vec![];
                for e in u {body.push(self.parse_expr(e)?)}
                Expr::Label {
                  name, args: args.into(), variant,
                  body: Block {muts: muts.into(), stmts: body.into_boxed_slice()}
                }
              }
              _ => {
                let f = e.as_atom().ok_or_else(||
                  ElabError::new_e(self.try_get_span(&e), "only variables can be called like functions"))?;
                let mut args = vec![];
                let mut variant = None;
                for e in u {
                  if let Some(v) = self.parse_variant(&e) {
                    if mem::replace(&mut variant, Some(v)).is_some() {
                      return Err(ElabError::new_e(self.try_get_span(&e), "call: two variants"))
                    }
                  } else {
                    args.push(self.parse_expr(e)?)
                  }
                }
                Expr::Call {f, args: args.into(), variant}
              }
            }
          }
        }
      },
      LispKind::Number(n) => Expr::Number(n.clone()),
      _ => return Err(ElabError::new_e(self.try_get_span(&e), "unknown expression"))
    })
  }

  fn parse_proc(&self, mut kind: ProcKind, mut u: Uncons) -> Result<Proc> {
    let e = match u.next() {
      None => return Err(ElabError::new_e(self.try_get_span(&u.into()), "func/proc: syntax error")),
      Some(e) => e,
    };
    let mut muts = vec![];
    let mut args = vec![];
    let mut rets = vec![];
    let (name, span) = match &*e.unwrapped_arc() {
      &LispKind::Atom(a) => (a, e.fspan()),
      LispKind::List(_) | LispKind::DottedList(_, _) => {
        let mut u = Uncons::from(e.clone());
        let e = u.next().ok_or_else(||
          ElabError::new_e(self.try_get_span(&e), "func/proc syntax error: expecting function name"))?;
        let name = e.as_atom().ok_or_else(||
          ElabError::new_e(self.try_get_span(&e), "func/proc syntax error: expecting an atom"))?;
        while let Some(e) = u.next() {
          if let Some(AtomID::COLON) = e.as_atom() { break }
          self.parse_arg(e, &mut args, Some(&mut muts))?
        }
        for e in u { self.parse_arg(e, &mut rets, None)? }
        (name, e.fspan())
      }
      _ => return Err(ElabError::new_e(self.try_get_span(&e), "func/proc: syntax error"))
    };
    let mut body = vec![];
    let variant = if let Some(e) = u.next() {
      match kind {
        ProcKind::Intrinsic => return Err(
          ElabError::new_e(self.try_get_span(&e), "intrinsic: unexpected body")),
        ProcKind::ProcDecl => kind = ProcKind::Proc,
        _ => {}
      }
      let v = self.parse_variant(&e);
      if v.is_none() {body.push(self.parse_expr(e)?)}
      for e in u {body.push(self.parse_expr(e)?)}
      v
    } else {None};
    Ok(Proc {
      name, span,
      args: args.into_boxed_slice(),
      rets: rets.into_boxed_slice(),
      variant,
      kind,
      body: Block {muts: muts.into(), stmts: body.into_boxed_slice()}
    })
  }

  fn parse_name_and_args(&self, e: LispVal) -> Result<(AtomID, Option<FileSpan>, Vec<Arg>)> {
    let mut args = vec![];
    let (name, sp) = match &*e.unwrapped_arc() {
      &LispKind::Atom(a) => (a, e.fspan()),
      LispKind::List(_) | LispKind::DottedList(_, _) => {
        let mut u = Uncons::from(e.clone());
        let e = u.next().ok_or_else(|| ElabError::new_e(self.try_get_span(&e), "typedef: syntax error"))?;
        let a = e.as_atom().ok_or_else(|| ElabError::new_e(self.try_get_span(&e), "typedef: expected an atom"))?;
        for e in u { self.parse_arg(e, &mut args, None)? }
        (a, e.fspan())
      },
      _ => return Err(ElabError::new_e(self.try_get_span(&e), "typedef: syntax error"))
    };
    Ok((name, sp, args))
  }

  fn parse_field(&self, ghost: bool, e: LispVal) -> Result<Field> {
    if let Some((Keyword::Colon, mut u)) = self.head_keyword(&e) {
      if let (Some(name), Some(ty), true) = (u.next().and_then(|e| e.as_atom()), u.next(), u.is_empty()) {
        Ok(Field {ghost, name, ty})
      } else {
        Err(ElabError::new_e(self.try_get_span(&e), "struct: syntax error"))
      }
    } else {
      Err(ElabError::new_e(self.try_get_span(&e), "struct: syntax error"))
    }
  }

  /// Parses the input lisp literal `e` into a list of top level items and appends them to `ast`.
  pub fn parse_ast(&self, ast: &mut Vec<AST>, e: &LispVal) -> Result<()> {
    let mut u = Uncons::from(e.clone());
    while let Some(e) = u.next() {
      match self.head_keyword(&e) {
        Some((Keyword::Proc, u)) => ast.push(AST::proc(self.parse_proc(ProcKind::ProcDecl, u)?)),
        Some((Keyword::Func, u)) => ast.push(AST::proc(self.parse_proc(ProcKind::Func, u)?)),
        Some((Keyword::Intrinsic, u)) => ast.push(AST::proc(self.parse_proc(ProcKind::Intrinsic, u)?)),
        Some((Keyword::Global, u)) => for e in u {
          let (lhs, rhs) = self.parse_decl(e)?;
          ast.push(AST::Global {lhs, rhs})
        },
        Some((Keyword::Const, u)) => for e in u {
          if let (lhs, Some(rhs)) = self.parse_decl(e.clone())? {
            ast.push(AST::Const {lhs, rhs})
          } else {
            return Err(ElabError::new_e(self.try_get_span(&e), "const: definition is required"))
          }
        },
        Some((Keyword::Typedef, mut u)) =>
          if let (Some(e), Some(val), true) = (u.next(), u.next(), u.is_empty()) {
            let (name, span, args) = self.parse_name_and_args(e)?;
            ast.push(AST::Typedef {name, span, args: args.into(), val});
          } else {
            return Err(ElabError::new_e(self.try_get_span(&e), "typedef: syntax error"))
          },
        Some((Keyword::Struct, mut u)) => {
          let e = u.next().ok_or_else(||
            ElabError::new_e(self.try_get_span(&e), "struct: expecting name"))?;
          let (name, span, args) = self.parse_name_and_args(e)?;
          let mut fields = vec![];
          for e in u {
            if let Some((Keyword::Ghost, u)) = self.head_keyword(&e) {
              for e in u {fields.push(self.parse_field(true, e)?)}
            }
            fields.push(self.parse_field(false, e)?);
          }
          ast.push(AST::Struct {name, span, args: args.into(), fields: fields.into()});
        }
        _ => return Err(ElabError::new_e(self.try_get_span(&e), "MMC: unknown top level item"))
      }
    }
    if !u.is_empty() {
      return Err(ElabError::new_e(self.try_get_span(&e), "MMC: syntax error"))
    }
    Ok(())
  }
}
