// This module may become a plugin in the future, but for now let's avoid the complexity
// of dynamic loading.

use std::collections::hash_map::HashMap;
use crate::util::{Span, FileSpan};
use crate::elab::{
  Result, Elaborator, ElabError,
  environment::{AtomID, Environment, Remap},
  lisp::{LispKind, LispVal, Uncons, LispRemapper},
  local_context::try_get_span};

struct Arg {
  ghost: bool,
  name: Option<(FileSpan, AtomID)>,
  ty: LispVal,
}

enum VariantType {
  Down,
  UpLt(LispVal),
  UpLe(LispVal)
}

struct Block {
  muts: Box<[AtomID]>,
  stmts: Box<[Expr]>
}

enum TuplePattern {
  Name(AtomID),
  Typed(Box<TuplePattern>, LispVal),
  Tuple(Box<[TuplePattern]>),
}

enum Expr {
  Hole(FileSpan),
  Let {ghost: bool, lhs: TuplePattern, rhs: Option<Box<Expr>>},
}

struct Proc {
  pure: bool,
  intrinsic: bool,
  name: AtomID,
  args: Box<[Arg]>,
  rets: Box<[Arg]>,
  variant: Option<(LispVal, VariantType)>,
  body: Block,
}

enum AST {
  Proc(Proc),
  Global {lhs: TuplePattern, rhs: Option<Box<Expr>>},
  Const {lhs: TuplePattern, rhs: Box<Expr>},
}


macro_rules! make_keywords {
  {$($x:ident: $e:expr,)*} => {
    #[derive(Debug, PartialEq, Eq, Copy, Clone)]
    enum Keyword { $($x),* }

    impl Environment {
      fn make_keywords(&mut self) -> HashMap<AtomID, Keyword> {
        let mut atoms = HashMap::new();
        $(atoms.insert(self.get_atom($e), Keyword::$x);)*
        atoms
      }
    }
  }
}

make_keywords! {
  Add: "+",
  And: "and",
  Assert: "assert",
  Array: "array",
  BAnd: "band",
  Bool: "bool",
  BNot: "bnot",
  BOr: "bor",
  BXor: "bxor",
  I8: "i8",
  I16: "i16",
  I32: "i32",
  I64: "i64",
  Colon: ":",
  ColonEq: ":=",
  Const: "const",
  Entail: "entail",
  Func: "func",
  Finish: "finish",
  Ghost: "ghost",
  Global: "global",
  Index: "index",
  Intrinsic: "intrinsic",
  Invariant: "invariant",
  Le: "<=",
  List: "list",
  Lt: "<",
  Mut: "mut",
  Not: "not",
  Or: "or",
  Own: "own",
  Proc: "proc",
  Pun: "pun",
  Ref: "&",
  RefMut: "&mut",
  Slice: "slice",
  TypeofBang: "typeof!",
  Typeof: "typeof",
  U8: "u8",
  U16: "u16",
  U32: "u32",
  U64: "u64",
  Union: "union",
  Variant: "variant",
}

impl<R> Remap<R> for Keyword {
  fn remap(&self, _: &mut R) -> Self { *self }
}

pub struct Compiler {
  keywords: HashMap<AtomID, Keyword>,
}

impl std::fmt::Debug for Compiler {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    write!(f, "#<mmc-compiler>")
  }
}

impl Remap<LispRemapper> for Compiler {
  fn remap(&self, r: &mut LispRemapper) -> Self {
    Compiler { keywords: self.keywords.remap(r) }
  }
}

struct Parser<'a> {
  elab: &'a mut Elaborator,
  kw: &'a HashMap<AtomID, Keyword>,
  fsp: &'a FileSpan,
}

fn head_atom(e: &LispVal) -> Option<(AtomID, Uncons)> {
  let mut u = Uncons::from(e.clone());
  Some((u.next()?.as_atom()?, u))
}

impl<'a> Parser<'a> {
  fn try_get_span(&self, e: &LispVal) -> Span {
    try_get_span(self.fsp, &e)
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

  fn parse_arg1(&mut self, e: LispVal, ghost: bool) -> Result<Arg> {
    if let Some((AtomID::COLON, mut u)) = head_atom(&e) {
      match (u.next(), u.next(), u.exactly(0)) {
        (Some(ea), Some(ty), true) => {
          let a = ea.as_atom().ok_or_else(||
            ElabError::new_e(self.try_get_span(&ea), "argument syntax error: expecting function name"))?;
          let name = if a == AtomID::UNDER {None} else {
            Some((self.try_get_fspan(&ea), a))
          };
          Ok(Arg { ghost, name, ty })
        }
        _ => Err(ElabError::new_e(self.try_get_span(&e), "syntax error in function arg"))?
      }
    } else {Ok(Arg { ghost, name: None, ty: e })}
  }

  fn parse_arg(&mut self, e: LispVal, args: &mut Vec<Arg>, muts: Option<&mut Vec<AtomID>>) -> Result<()> {
    Ok(match (self.head_keyword(&e), muts) {
      (Some((Keyword::Ghost, u)), _) => for e in u {
        args.push(self.parse_arg1(e, true)?)
      }
      (Some((Keyword::Mut, u)), Some(muts)) => for e in u {
        muts.push(e.as_atom().ok_or_else(||
          ElabError::new_e(self.try_get_span(&e), "mut: expected an atom"))?)
      }
      _ => args.push(self.parse_arg1(e, false)?)
    })
  }

  fn parse_tuple_pattern(&self, e: LispVal) -> Result<TuplePattern> {
    Ok(match &*e.unwrapped_arc() {
      &LispKind::Atom(a) => TuplePattern::Name(a),
      LispKind::List(_) | LispKind::DottedList(_, _) => {
        if let Some((Keyword::Colon, mut u)) = self.head_keyword(&e) {
          if let (Some(e), Some(ty), true) = (u.next(), u.next(), u.exactly(0)) {
            return Ok(TuplePattern::Typed(Box::new(self.parse_tuple_pattern(e)?), ty))
          }
          Err(ElabError::new_e(self.try_get_span(&e), "':' syntax error"))?
        }
        let mut args = vec![];
        for e in Uncons::from(e) {args.push(self.parse_tuple_pattern(e)?)}
        TuplePattern::Tuple(args.into_boxed_slice())
      }
      _ => Err(ElabError::new_e(self.try_get_span(&e), "tuple pattern syntax error"))?
    })
  }

  fn parse_decl(&mut self, e: LispVal) -> Result<(TuplePattern, Option<Box<Expr>>)> {
    if let Some((Keyword::ColonEq, mut u)) = self.head_keyword(&e) {
      if let (Some(lhs), Some(rhs), true) = (u.next(), u.next(), u.exactly(0)) {
        Ok((self.parse_tuple_pattern(lhs)?, Some(Box::new(self.parse_expr(rhs)?))))
      } else {
        Err(ElabError::new_e(self.try_get_span(&e), "decl: syntax error"))
      }
    } else {
      Ok((self.parse_tuple_pattern(e)?, None))
    }
  }

  fn parse_expr(&mut self, e: LispVal) -> Result<Expr> {
    Ok(match &*e.unwrapped_arc() {
      &LispKind::Atom(AtomID::UNDER) => Expr::Hole(self.try_get_fspan(&e)),
      LispKind::List(_) | LispKind::DottedList(_, _) => match self.head_keyword(&e) {
        Some((Keyword::Ghost, mut u)) =>
          if let (Some(e), true) = (u.next(), u.exactly(0)) {
            let (lhs, rhs) = self.parse_decl(e)?;
            Expr::Let {ghost: true, lhs, rhs}
          } else {
            Err(ElabError::new_e(self.try_get_span(&e), "ghost: syntax error"))?
          },
        Some((Keyword::Colon, _)) |
        Some((Keyword::ColonEq, _)) => {
          let (lhs, rhs) = self.parse_decl(e)?;
          Expr::Let {ghost: false, lhs, rhs}
        }
        _ => Err(ElabError::new_e(self.try_get_span(&e), "unknown expression"))?
      },
      _ => Err(ElabError::new_e(self.try_get_span(&e), "unknown expression"))?
    })
  }

  fn parse_proc(&mut self, pure: bool, intrinsic: bool, mut u: Uncons) -> Result<Proc> {
    let e = match u.next() {
      None => return Err(ElabError::new_e(self.try_get_span(&u.as_lisp()), "func/proc: syntax error")),
      Some(e) => e,
    };
    let mut muts = vec![];
    let mut args = vec![];
    let mut rets = vec![];
    let name = match &*e.unwrapped_arc() {
      &LispKind::Atom(a) => a,
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
        while let Some(e) = u.next() { self.parse_arg(e, &mut rets, None)? }
        name
      },
      _ => Err(ElabError::new_e(self.try_get_span(&e), "func/proc: syntax error"))?
    };
    let mut body = vec![];
    Ok(Proc {
      pure, intrinsic, name,
      args: args.into_boxed_slice(),
      rets: rets.into_boxed_slice(),
      variant: if let Some(e) = u.next() {
        if intrinsic {
          Err(ElabError::new_e(self.try_get_span(&e), "intrinsic: unexpected body"))?
        }
        let v = self.parse_variant(&e);
        if v.is_none() {body.push(self.parse_expr(e)?)}
        for e in u {body.push(self.parse_expr(e)?)}
        v
      } else {None},
      body: Block {muts: muts.into(), stmts: body.into_boxed_slice()}
    })
  }

  fn parse_ast(&mut self, e: &LispVal) -> Result<Vec<AST>> {
    let mut u = Uncons::from(e.clone());
    let mut ast = vec![];
    while let Some(e) = u.next() {
      match self.head_keyword(&e) {
        Some((Keyword::Proc, u)) => ast.push(AST::Proc(self.parse_proc(false, false, u)?)),
        Some((Keyword::Func, u)) => ast.push(AST::Proc(self.parse_proc(true, false, u)?)),
        Some((Keyword::Intrinsic, u)) => ast.push(AST::Proc(self.parse_proc(false, true, u)?)),
        Some((Keyword::Global, u)) => for e in u {
          let (lhs, rhs) = self.parse_decl(e)?;
          ast.push(AST::Global {lhs, rhs})
        },
        Some((Keyword::Const, u)) => for e in u {
          if let (lhs, Some(rhs)) = self.parse_decl(e.clone())? {
            ast.push(AST::Const {lhs, rhs})
          } else {
            Err(ElabError::new_e(self.try_get_span(&e), "const: definition is required"))?
          }
        },
        _ => Err(ElabError::new_e(self.try_get_span(&e), "MMC: unknown top level item"))?
      }
    }
    if !u.exactly(0) {
      Err(ElabError::new_e(self.try_get_span(&e), "MMC: syntax error"))?
    }
    Ok(ast)
  }
}

impl Compiler {
  pub fn new(e: &mut Elaborator) -> Compiler {
    Compiler {keywords: e.env.make_keywords()}
  }

  pub fn add(&mut self, elab: &mut Elaborator, fsp: &FileSpan, e: &LispVal) -> Result<()> {
    let _ast = Parser {elab, kw: &self.keywords, fsp}.parse_ast(e)?;
    Ok(())
  }

  pub fn finish(&mut self, elab: &mut Elaborator, fsp: &FileSpan, a1: AtomID, a2: AtomID) -> Result<()> {
    Ok(())
  }

  pub fn call(&mut self, elab: &mut Elaborator, sp: Span, args: Vec<LispVal>) -> Result<LispVal> {
    let fsp = elab.fspan(sp);
    let mut it = args.into_iter();
    let e = it.next().unwrap();
    match e.as_atom().and_then(|a| self.keywords.get(&a)) {
      Some(Keyword::Add) => {
        for e in it { self.add(elab, &fsp, &e)? }
        Ok(LispVal::undef())
      }
      Some(Keyword::Finish) => {
        let a1 = it.next().and_then(|e| e.as_atom()).ok_or_else(||
          ElabError::new_e(fsp.span, "mmc-finish: syntax error"))?;
        let a2 = it.next().and_then(|e| e.as_atom()).ok_or_else(||
          ElabError::new_e(fsp.span, "mmc-finish: syntax error"))?;
        for e in it { self.add(elab, &fsp, &e)? }
        self.finish(elab, &fsp, a1, a2)?;
        Ok(LispVal::undef())
      }
      _ => Err(ElabError::new_e(fsp.span,
        format!("mmc-compiler: unknown subcommand '{}'", elab.format_env().to(&e))))?
    }
  }
}