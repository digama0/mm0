//! Build the mid-level IR from HIR
#![allow(unused)]

use std::borrow::{Borrow, Cow};
use std::{cell::RefCell, rc::Rc, fmt::Debug, hash::{Hash, Hasher}, mem, ops::Index};
use std::result::Result as StdResult;
use std::convert::{TryFrom, TryInto};
use bumpalo::Bump;
use std::collections::HashMap;
use hir::{Context, ContextNext};
use itertools::Itertools;
use num::Signed;
use types::IntTy;
use crate::{AtomId, FileSpan, FormatEnv, LispVal, lisp::print::alphanumber, u32_as_usize};
use super::{Compiler, parser::try_get_fspan, types};
use types::{Binop, BinopType, FieldName, Mm0ExprNode, Size, Spanned, Unop, VarId, hir, mir};
use hir::GenId;
use types::entity::{Entity, ConstTc, GlobalTc, ProcTy, ProcTc, TypeTc, TypeTy};
use super::union_find::{UnifyCtx, UnifyKey, UnificationTable};
#[allow(clippy::wildcard_imports)] use super::types::ty::*;

struct BuildMir<'m> {
  compiler: &'m mut Compiler,
  alloc: &'m Bump,
}

impl<'m> BuildMir<'m> {
  fn new(compiler: &'m mut Compiler, alloc: &'m Bump) -> Self {
    Self { compiler, alloc }
  }

  fn lower_item<'a>(&mut self, it: hir::Item<'a>) {
    match it.k {
      hir::ItemKind::Proc { kind, name, tyargs, args, rets, variant, body } => {
      }
      hir::ItemKind::Global { lhs, rhs } => {}
      hir::ItemKind::Const { lhs, rhs } => {}
      hir::ItemKind::Typedef { name, tyargs, args, val } => {}
    }
  }
}