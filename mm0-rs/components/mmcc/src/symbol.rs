//! A simple string interner.

use std::{collections::HashMap, fmt::Display, sync::{Mutex, LazyLock}};
use mm0_util::MutexExt;
use crate::types::IdxVec;

mk_id! {
  /// A `Symbol` is an interned string.
  ///
  /// It is used to avoid copying strings around everywhere in the compiler.
  /// These can refer to keywords or operators, function names, variable names
  /// and any other syntactic entities the compiler needs to refer to.
  ///
  /// Symbols are interned forever: the interner leaks any string it is given.
  /// As a result, symbols can be used across compiler invocations in a single
  /// execution, although they do not have a stable name across executions.
  Symbol(!Debug)
}

/// The global symbol interner.
///
/// You don't normally need to interact directly with this struct, since the
/// [`intern`] function can be used to intern a string without access to the interner,
/// but [`Interner::with`] can be used to lock the interner for a time period
/// to avoid the overhead of repeated locks.
#[derive(Debug)]
pub struct Interner {
  names: HashMap<&'static str, Symbol>,
  strings: IdxVec<Symbol, &'static str>,
}

static INTERNER: LazyLock<Mutex<Interner>> = LazyLock::new(|| {
  let mut i = Interner {
    names: HashMap::new(),
    strings: IdxVec::new(),
  };
  assert_eq!(Symbol::UNDER, i.intern("_"));
  Mutex::new(i)
});

impl Interner {
  /// Acquire the interner to intern a bunch of strings.
  /// **Warning**: Calling [`intern`] from within this function will cause a deadlock! All
  /// interning should go through the [`Interner::intern`] function instead.
  pub fn with<R>(f: impl FnOnce(&mut Interner) -> R) -> R { f(&mut INTERNER.ulock()) }

  /// Intern a single string, returning a `Symbol` that represents that string.
  pub fn intern(&mut self, s: &str) -> Symbol {
    if let Some(&name) = self.names.get(s) { return name }
    // We make no attempt to bound the lifetime of the interner, so it's fine to just
    // leak here. We won't be seeing that many names anyway - this is mostly just
    // names of variables, functions, keywords, and constants.
    let s = Box::leak(s.to_owned().into_boxed_str());
    let n = self.strings.push(s);
    self.names.insert(s, n);
    n
  }

  /// Get the symbol as a string. `Symbol::as_str()` should be used in
  /// preference to this function.
  #[must_use] pub fn get(&self, symbol: Symbol) -> &'static str { self.strings[symbol] }
}

/// Intern a single string, returning a `Symbol` that represents that string.
#[must_use] pub fn intern(s: &str) -> Symbol { Interner::with(|i| i.intern(s)) }

impl Symbol {
  /// The string `"_"`, which is pinned to symbol number 0. (This is used as a special name to
  /// refer to ignored arguments, and so it is convenient to have it be a compile time constant.)
  pub const UNDER: Self = Self(0);

  /// Get the string corresponding to this symbol.
  /// You can also use the `Display` impl to print a `Symbol`.
  #[must_use] pub fn as_str(self) -> &'static str { Interner::with(|i| i.get(self)) }
}

impl Display for Symbol {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { self.as_str().fmt(f) }
}
impl std::fmt::Debug for Symbol {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "{self}") }
}

/// Initialize a map from symbols to values of type `T`.
///
/// Note that this will create an array the same size as all symbols that have
/// ever been interned, so it is best to use this only during initialization
/// for keyword lists and the like.
pub fn init_dense_symbol_map<T: Clone>(kv: &[(Symbol, T)]) -> Box<[Option<T>]> {
  use crate::types::Idx;
  let mut vec = vec![None; kv.iter().map(|p| p.0).max().map_or(0, |n| n.into_usize() + 1)];
  for (k, v) in kv { vec[k.into_usize()] = Some(v.clone()) }
  vec.into()
}
