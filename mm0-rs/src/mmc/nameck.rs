//! MMC name resolution pass.
use std::collections::{HashMap, hash_map::Entry};
use crate::elab::{Result, ElabError, environment::AtomId};
use crate::util::FileSpan;
use super::{Compiler, types};
use types::Spanned;
use types::entity::{ConstTc, Entity, GlobalTc, ProcTc, TypeTc};
use types::parse::{Item, ItemKind};

impl Compiler {
  /// Add a reservation (an [`Unchecked`](ProcTc::Unchecked)) to the [`Entity`] entry
  /// for this item, also ensuring that the item's name has not already been used.
  /// (This way, even if the elaboration of the item fails, we still know that it exists so
  /// that downstream code isn't totally broken.)
  pub fn reserve_names(names: &mut HashMap<AtomId, Entity>, item: &Item) -> Result<()> {
    fn add_item(names: &mut HashMap<AtomId, Entity>,
      name: AtomId, span: &FileSpan, val: impl FnOnce() -> Entity
    ) -> Result<()> {
      match names.entry(name) {
        Entry::Vacant(e) => { e.insert(val()); Ok(()) }
        Entry::Occupied(e) => if let Some(sp2) = e.get().span() {
          Err(ElabError::with_info(span,
            "an item by this name has already been declared".into(),
            vec![(sp2.clone(), "previously declared here".into())]))
        } else {
          Err(ElabError::new_e(span, "this name is reserved for a primitive operator"))
        }
      }
    }
    match &item.k {
      ItemKind::Proc(proc) => add_item(names, proc.name.k, &proc.name.span,
        || Entity::Proc(Spanned {span: item.span.clone(), k: ProcTc::Unchecked}))?,
      ItemKind::Global(lhs, _) => lhs.on_names(&mut |sp, v| {
        add_item(names, v, sp, || Entity::Global(Spanned {span: sp.clone(), k: GlobalTc::Unchecked}))
      })?,
      ItemKind::Const(lhs, _) => lhs.on_names(&mut |sp, v| {
        add_item(names, v, sp, || Entity::Const(Spanned {span: sp.clone(), k: ConstTc::Unchecked}))
      })?,
      ItemKind::Typedef {name, ..} |
      ItemKind::Struct {name, ..} => add_item(names, name.k, &name.span,
        || Entity::Type(Spanned {span: name.span.clone(), k: TypeTc::Unchecked}))?,
    }
    Ok(())
  }
}