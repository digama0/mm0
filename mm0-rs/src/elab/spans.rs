//! A data structure for aggregating spans for servicing hovers

use std::mem::MaybeUninit;
use std::collections::BTreeMap;
use std::ops::Range;
use crate::AtomId;
use super::local_context::LocalContext;
use crate::Span;

/// A `Spans<T>` object is created for each declaration, and maintains data on the
/// spans of objects occurring in the statement. For example, we might register
/// spans for variables, theorem references, and function calls, once we have
/// resolved them, with enough data attached to the span so that we can render
/// a useful hover if the user asks for information at a location in that span.
///
/// We leave `T` generic here because it isn't important in this file, but we
/// are only going to instantiate it with
/// `T` = [`ObjectKind`](super::environment::ObjectKind).
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct Spans<T> {
  /// The span that encloses the entire declaration, from the first command keyword
  /// to the final semicolon. All spans in `data` will be sub-spans of this.
  ///
  /// We will always set this value before storing the span in [`Environment.spans`].
  stmt: MaybeUninit<Span>,
  /// The name of the present declaration. This is left uninitialized for
  /// declarations that don't have names, like [`delimiter`](mm1_parser::ast::Delimiter).
  decl: MaybeUninit<AtomId>,
  /// The local context as of the end of the proof. This is used to resolve variables
  /// and subproof names.
  pub lc: Option<LocalContext>,
  /// The actual data associated to spans. They are indexed by span start, and one
  /// start point can contain many spans, even multiple data elements at the same span.
  data: BTreeMap<usize, Vec<(Span, T)>>,
}

impl<'a, T> IntoIterator for &'a Spans<T> {
  type Item = &'a (Span, T);
  type IntoIter = std::iter::Flatten<
    std::collections::btree_map::Values<'a, usize, Vec<(Span, T)>>>;
  fn into_iter(self) -> Self::IntoIter { self.data.values().flatten() }
}

use std::fmt;
impl<T: fmt::Debug> fmt::Debug for Spans<T> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{{ stmt: {:?},\n  data: {:?} }}", self.stmt(), self.data)
  }
}

impl<T> Default for Spans<T> {
  fn default() -> Self { Self::new() }
}

impl<T> Spans<T> {
  /// Create a new [`Spans`] object. The `stmt` and `decl` fields are initially
  /// uninitialized.
  #[must_use] pub fn new() -> Spans<T> {
    Spans {
      stmt: MaybeUninit::uninit(),
      decl: MaybeUninit::uninit(),
      lc: None,
      data: BTreeMap::new()
    }
  }

  /// Initialize the `stmt` field of a [`Spans`].
  pub fn set_stmt(&mut self, sp: Span) { self.stmt = MaybeUninit::new(sp) }

  /// Initialize the `decl` field of a [`Spans`].
  pub fn set_decl(&mut self, a: AtomId) { self.decl = MaybeUninit::new(a) }

  /// Get the `stmt` field of a [`Spans`].
  ///
  /// # Safety
  /// This function must only be called if [`set_stmt`](Self::set_stmt) has previously
  /// been called. We ensure that this is the case for any [`Spans`] object put into
  /// [`Environment.spans`].
  #[must_use] pub fn stmt(&self) -> Span {
    // Safety: by assumption
    unsafe { self.stmt.assume_init() }
  }

  /// Get the `decl` field of a [`Spans`].
  ///
  /// # Safety
  /// This function must only be called if [`set_decl`](Self::set_decl) has previously
  /// been called. We ensure that this is the case for any [`Spans`] object put into
  /// [`Environment.spans`], but only for declarations that actually have names.
  /// (This function is also currently unused.)
  #[must_use] pub fn decl(&self) -> AtomId {
    // Safety: by assumption
    unsafe { self.decl.assume_init() }
  }

  /// Insert a new data element at a given span.
  pub fn insert<'a>(&'a mut self, sp: Span, val: T) -> &'a mut T {
    let v: &'a mut Vec<(Span, T)> = self.data.entry(sp.start).or_default();
    // Safety: As indicated below, we would like to return k directly in the loop,
    // but rust will reject this, claiming a double borrow, and we instead use some
    // unsafe hacks to circumvent the borrow checker. To show this is safe, consider
    // two cases.
    // - If the return is exercised (we found an element and early out):
    //   - let 'b be 'a (the borrow of self),
    //   - and let 'c be empty
    // - Otherwise (we did not find an element, exit the loop and terminate normally):
    //   - let 'b be the duration of the loop,
    //   - and let 'c be from the end of the loop until the end of 'a
    // In either case, 'b and 'c are disjoint, so the "double borrow" is safe.
    // The borrow checker reasons that 'b has to be at least 'a because it is returned,
    // and therefore it overlaps with 'c, but these happen in mutually exclusive
    // situations.
    for (sp1, k) in & /* 'b */ mut *v {
      if sp == *sp1 {
        // return k; // we would like to write this
        #[allow(clippy::useless_transmute)]
        // Safety: see above. We know we are in the first case, so 'b = 'a
        return unsafe { std::mem::transmute::<&/* 'b */ mut T, &/* 'a */ mut T>(k) }
      }
    }
    let v = & /* 'c */ mut *v;
    v.push((sp, val));
    // Safety: We just pushed, so the last_mut() exists
    unsafe { &mut v.last_mut().unwrap_unchecked().1 }
  }

  /// Insert a data element at a given span, if it lies within the current statement's extent.
  /// We will usually use this instead of [`insert`](Self::insert). By making sure that all
  /// spans are stored according to the enclosing statement, we can quickly search for a
  /// span by getting the [`Spans`] object for a statement and then searching only in that
  /// [`Spans`] rather than looking in other statements' [`Spans`] as well.
  pub fn insert_if(&mut self, sp: Option<Span>, val: impl FnOnce() -> T) {
    if let Some(sp) = sp {
      if sp.start >= self.stmt().start {
        self.insert(sp, val());
      }
    }
  }

  /// Get the data at a given [`Span`].
  /// If multiple data elements exist at this span, only the first will be returned.
  #[must_use] pub fn get(&self, sp: Span) -> Option<&T> {
    self.data.get(&sp.start).and_then(|v|
      v.iter().find(|x| x.0 == sp).map(|x| &x.1))
  }

  /// Get the data at a given [`Span`].
  /// If multiple data elements exist at this span, only the first will be returned.
  pub fn get_mut(&mut self, sp: Span) -> Option<&mut T> {
    self.data.get_mut(&sp.start).and_then(|v|
      v.iter_mut().find(|x| x.0 == sp).map(|x| &mut x.1))
  }

  /// Returns an iterator over all data elements in spans that overlap the target
  /// position. ([`Span`]s are considered as closed,
  /// i.e. `start <= pos <= end`, for this purpose.)
  pub fn find_pos(&self, pos: usize) -> impl Iterator<Item=&(Span, T)> {
    self.data.range(..=pos).next_back().into_iter()
      .flat_map(move |(_, v)| v.iter().filter(move |x| pos <= x.0.end))
  }

  /// Get the [`Spans`] object corresponding to the statement that contains the given position,
  /// if one exists.
  #[must_use] pub fn find(spans: &[Self], pos: usize) -> Option<&Self> {
    match spans.binary_search_by_key(&pos, |s| s.stmt().start) {
      Ok(i) => Some(&spans[i]),
      Err(i) => i.checked_sub(1).map(|j| &spans[j]),
    }.filter(|&s| pos < s.stmt().end)
  }

  /// Execute the given closure over all data elements in spans that start in the target
  /// range, that is, `range.start <= sp.start < range.end`.
  /// (This is not as precise a lookup as we would like, but the indexing doesn't
  /// support getting all spans that overlap the target range,
  /// so we work around this in the caller instead.)
  pub fn on_range(spans: &[Self], range: Option<Range<usize>>, mut f: impl FnMut(&Self, &(Span, T))) {
    if let Some(range) = range {
      let i = spans.binary_search_by_key(&range.start, |s| s.stmt().start)
        .unwrap_or_else(|i| i.saturating_sub(1));
      let spans = &spans[i..];
      let j = spans.binary_search_by_key(&range.end.saturating_sub(1), |s| s.stmt().start)
        .unwrap_or_else(|i| i.saturating_sub(1));
      let spans = &spans[..=j];
      spans.iter().for_each(|sp| sp.data.range(range.clone())
        .for_each(|(_, v)| v.iter().for_each(|x| f(sp, x))))
    } else {
      spans.iter().for_each(|sp| sp.data.iter()
        .for_each(|(_, v)| v.iter().for_each(|x| f(sp, x))))
    }
  }
}
