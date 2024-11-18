//! The proof compacter, which takes an elaborated lisp proof s-expr and produces
//! a [`Proof`](super::environment::Proof) object that will be stored in the environment.

use std::rc::Rc;
use std::hash::Hash;
use std::ops::Index;
use std::mem;
use std::collections::{HashMap, hash_map::Entry};
use crate::{AtomId, Type};
use super::{LocalContext, ElabError, Result, Environment,
  SortId, TermId, ThmId, ExprNode, ProofNode, DeclKey, Modifiers};
use super::lisp::{LispVal, LispKind, Uncons, InferTarget, print::FormatEnv};
use super::local_context::{InferSort, try_get_span_from};
use crate::{BoxError, FileSpan};

/// This struct represents the context for the hash-consing step of proof compaction
#[derive(Debug)]
pub struct NodeHasher<'a> {
  /// The local context, which is used to resolve local hypotheses and subproofs.
  pub lc: &'a LocalContext,
  /// The formatting environment, used for error reporting and for access to the [`Environment`].
  pub fe: FormatEnv<'a>,
  /// The initial variable map, which maps variable names to their indices.
  pub var_map: HashMap<AtomId, usize>,
  /// The file span for the theorem, used for error reporting.
  pub fsp: FileSpan,
}

impl<'a> NodeHasher<'a> {
  /// Construct a new [`NodeHasher`], using the [`LocalContext`] to construct the
  /// variable map.
  #[must_use] pub fn new(lc: &'a LocalContext, fe: FormatEnv<'a>, fsp: FileSpan) -> Self {
    let mut var_map = HashMap::new();
    for (i, &(_, a, _)) in lc.var_order.iter().enumerate() {
      if let Some(a) = a {var_map.insert(a, i);}
    }
    NodeHasher {lc, fe, var_map, fsp}
  }

  /// Construct an error at the given expression's location.
  fn err(&self, e: &LispKind, msg: impl Into<BoxError>) -> ElabError {
    self.err_sp(e.fspan().as_ref(), msg)
  }

  /// Construct an error at the given location.
  fn err_sp(&self, fsp: Option<&FileSpan>, msg: impl Into<BoxError>) -> ElabError {
    ElabError::new_e(try_get_span_from(&self.fsp, fsp), msg)
  }
}

/// Basic contextual kind information when interpreting s-expressions as proofs.
///
/// Because the s-expr representation of proof terms is ambiguous between terms,
/// proofs and conversions, we have to know up front what kind of object we are looking
/// at. This enum is used to prevent the Dedup from mixing up identical lisp expressions
/// of different kinds.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ProofKind {
  /// This is an expr, for example [`ProofNode::Term`] or [`ProofNode::Ref`]
  Expr,
  /// This is a proof, for example [`ProofNode::Thm`], [`ProofNode::Conv`] or [`ProofNode::Ref`]
  Proof,
  /// This is a conversion, for example [`ProofNode::Sym`], [`ProofNode::Cong`] or [`ProofNode::Ref`]
  Conv,
}

#[derive(Debug, Default, Clone)]
struct ProofKindMap<T> {
  expr: T,
  proof: T,
  conv: T,
}

impl<T> ProofKindMap<T> {
  fn get_mut(&mut self, kind: ProofKind) -> &mut T {
    match kind {
      ProofKind::Expr => &mut self.expr,
      ProofKind::Proof => &mut self.proof,
      ProofKind::Conv => &mut self.conv,
    }
  }
}

/// A builder for constructing lisp objects from a [`Dedup`].
#[derive(Debug)]
pub struct ToLisp {
  cache: Vec<Option<LispVal>>,
  hyps: Vec<Option<LispVal>>,
}

impl ToLisp {
  /// Get the lisp value of a given index in the [`Dedup`].
  pub fn get<H: NodeHash>(&mut self, env: &mut Environment, de: &Dedup<H>, i: usize) -> LispVal {
    if let Some(x) = &self.cache[i] { return x.clone() }
    let ret = de[i].to_lisp(self, env, de);
    self.cache[i] = Some(ret.clone());
    ret
  }

  /// Insert the argument names, which are not stored in the [`Dedup`].
  pub fn add_arg_names(&mut self, args: impl Iterator<Item=Option<AtomId>>) {
    for (a, val) in args.zip(&mut self.cache) {
      if let Some(a) = a {
        if val.is_some() { *val = Some(LispVal::atom(a)) }
      }
    }
  }

  /// Insert the argument names, which are not stored in the [`Dedup`].
  pub fn add_hyp_names(&mut self, args: impl Iterator<Item=Option<AtomId>>) {
    self.hyps = args.map(|a| a.map(LispVal::atom)).collect()
  }
}

/// A "hashable" type. We use this to abstract the difference between
/// [`ExprHash`] and [`ProofHash`].
///
/// The definition of [`NodeHash`] is mutually recursive
/// with the [`Dedup`] struct. A [`NodeHash`] type represents a nonrecursive shadow
/// of a recursive type (namely [`ExprNode`] and [`ProofNode`], respectively),
/// where recursive occurrences are replaced with indices tracked by the [`Dedup`] type.
/// Effectively, [`Dedup`] is acting as an arena allocator where the pointers are
/// replaced by integers.
pub trait NodeHash: Hash + Eq + Sized {
  /// A variant for invalidated nodes.
  const NONE: Self;
  /// The variant that constructs a variable from an index.
  const REF: fn(ProofKind, usize) -> Self;

  /// Given a lisp expression `r` representing an element of the type,
  /// parse it into a [`NodeHash`] object. If the object has already been constructed,
  /// it may also return an index to the element in the [`Dedup`].
  fn from(nh: &NodeHasher<'_>, fsp: Option<&FileSpan>, kind: ProofKind, r: &LispVal,
    de: &mut Dedup<Self>) -> Result<Result<Self, usize>>;

  /// Calculate the variable dependence of a [`NodeHash`] object, given a function
  /// `deps` that will provide the dependencies of elements. Bump `bv` if this object
  /// is a dummy variable.
  fn vars(&self, bv: &mut u64, deps: impl Fn(usize) -> u64) -> u64;

  /// Convert this value back into a [`LispVal`]. This function is normally not called directly;
  /// instead use [`ToLisp::get`].
  fn to_lisp(&self, builder: &mut ToLisp, env: &mut Environment, de: &Dedup<Self>) -> LispVal;

  /// Calls the given function on all direct children of the node.
  fn on_children(&self, f: impl FnMut(usize));
}

/// The main hash-consing state object.
///
/// This tracks previously hash-consed elements and uses the [`Hash`] implementation
/// required by [`NodeHash`] to hash elements of the hash type `H`.
/// (Since these objects may be somewhat large, we store them
/// behind an [`Rc`] so that they can go in both the map and the vec.)
#[derive(Debug)]
pub struct Dedup<H: NodeHash> {
  /// The map from hash objects to their assigned indexes. These indexes are
  /// incorporated in later hash objects, so hashing is constant time but equality
  /// of the [`NodeHash`] objects still implies deep equality of the trees that
  /// they represent.
  map: HashMap<Rc<H>, usize>,
  /// In order to deduplicate lisp expressions which already have internal sharing
  /// without traversing the same terms many times, we store a pointer hash here
  /// from each expression to its index, if we have already hashed it. We store
  /// a reference to the object in the map to ensure that it is not deallocated.
  /// (There is no safety problem here, but if the object gets deallocated and
  /// another takes its place, we can get a false positive hit in the map.)
  prev: ProofKindMap<HashMap<*const LispKind, Option<(LispVal, usize)>>>,
  /// The list of allocated objects. At each index, we store `(hash, shared, deps)` where
  /// `hash` is the hash object, `shared` is true if this object has more than one
  /// reference, and `deps` is the dependencies of this expression
  /// (calculated as a useful side effect of deduplication).
  pub vec: Vec<(Rc<H>, bool, u64)>,
  /// `2 ^ n` where `n` is the number of bound variables currently allocated.
  /// (Yes, this puts a limit of 64 simultaneous bound variables. In fact the limit is
  /// lower than that, [55](mm0b_parser::MAX_BOUND_VARS),
  /// due to the way BV sets are stored in the compiled `.mmb` format.)
  bv: u64,
}

impl<H: NodeHash> Dedup<H> {
  /// Create a new [`Dedup`], given the list of arguments
  /// ([`Term::args`](super::environment::Term::args)) in the context.
  #[must_use] pub fn new(args: &[(Option<AtomId>, Type)]) -> Dedup<H> {
    let mut bv = 1;
    let vec: Vec<_> = args.iter().enumerate()
      .map(|(i, (_, t))| (Rc::new(H::REF(ProofKind::Expr, i)), true, match t {
        Type::Bound(_) => { let v = bv; bv *= 2; v }
        &Type::Reg(_, deps) => deps,
      })).collect();
    Dedup {
      map: vec.iter().enumerate().map(|(i, r)| (r.0.clone(), i)).collect(),
      prev: Default::default(),
      vec,
      bv,
    }
  }

  /// Returns an iterator over the elements allocated by the [`Dedup`].
  pub fn iter(&self) -> DedupIter<'_, H> { self.into_iter() }

  /// Insert a new hash object `v`, originating from lisp object `p`,
  /// into the [`Dedup`], returning the allocated index.
  pub fn add(&mut self, kind: ProofKind, p: LispVal, v: H) -> usize {
    let n = self.add_direct(v);
    self.prev.get_mut(kind).insert(&*p, Some((p, n)));
    n
  }

  /// Insert a new hash object `v`, originating from lisp object `p`,
  /// into the [`Dedup`], returning the allocated index.
  pub fn dedup(&mut self, nh: &NodeHasher<'_>, kind: ProofKind, e: &LispVal) -> Result<usize> {
    let arc = e.unwrapped_arc();
    let ptr: *const _ = &*arc;
    Ok(match self.prev.get_mut(kind).entry(ptr) {
      Entry::Occupied(o) => match o.get() {
        &Some((_, n)) => self.reuse(n),
        None => return Err(nh.err_sp(e.fspan().as_ref(), "cyclic proof")),
      },
      Entry::Vacant(v) => {
        v.insert(None);
        let n = match H::from(nh, e.fspan().as_ref(), kind, &arc, self)? {
          Ok(v) => self.add_direct(v),
          Err(n) => n,
        };
        self.prev.get_mut(kind).insert(ptr, Some((arc, n))); n
      }
    })
  }

  /// Convert a `Dedup<H>` to `Dedup<T>` given an injective function `f: H -> T`.
  /// Here injectivity is with respect to the [`Eq`] implementations on `H` and `T`:
  /// If `f(x) == f(y)` then `x == y`.
  fn map_inj<T: NodeHash>(&self, mut f: impl FnMut(&H) -> T) -> Dedup<T> {
    let mut map = HashMap::new();
    let vec = self.vec.iter().enumerate().map(|(i, &(ref h, b, v))| {
      let t = Rc::new(f(h));
      map.insert(t.clone(), i);
      (t, b, v)
    }).collect();
    Dedup { map, prev: self.prev.clone(), vec, bv: self.bv }
  }

  /// Construct a new [`ToLisp`] for converting elements in this [`Dedup`] into lisp values.
  #[must_use] pub fn to_lisp_builder(&self) -> ToLisp {
    ToLisp { cache: vec![None; self.vec.len()], hyps: vec![] }
  }

  /// Ensure that any node reachable by more than one path from the given roots is marked as
  /// shared, and every unreachable node is marked as [`NodeHash::NONE`].
  /// This can be used instead of [`IDedup::reuse`] when reuse patterns are not
  /// easily determinable.
  pub fn calc_use(&mut self, num_args: usize, roots: impl IntoIterator<Item=usize>) {
    use bit_set::BitSet;
    fn check<H: NodeHash>(de: &mut Dedup<H>, used: &mut BitSet, n: usize) {
      let val = &mut de.vec[n];
      if used.insert(n) {
        val.0.clone().on_children(|i| check(de, used, i))
      } else {
        val.1 = true
      }
    }
    let mut used = BitSet::with_capacity(self.vec.len());
    for i in 0..num_args { used.insert(i); }
    for val in &mut self.vec[num_args..] { val.1 = false }
    for i in roots { check(self, &mut used, i) }
    for (n, val) in self.vec.iter_mut().enumerate() {
      if !used.contains(n) {
        if let Some(val) = Rc::get_mut(&mut val.0) {
          *val = H::NONE
        } else {
          val.0 = Rc::new(H::NONE)
        }
      }
    }
  }
}

/// A trait that abstracts a few functions on `Dedup<H>`.
pub trait IDedup<H>: Index<usize, Output=H> {
  /// Insert a new hash object `v` into the [`Dedup`], returning the allocated index.
  /// Like [`add`](Dedup::add), but does not add a record for the lisp data.
  fn add_direct(&mut self, v: H) -> usize;

  /// Mark that an already allocated index `n` is being shared.
  fn reuse(&mut self, n: usize) -> usize;
}

impl<H: NodeHash> Index<usize> for Dedup<H> {
  type Output = H;
  fn index(&self, n: usize) -> &H { &self.vec[n].0 }
}

impl<H: NodeHash> IDedup<H> for Dedup<H> {
  fn add_direct(&mut self, v: H) -> usize {
    match self.map.entry(Rc::new(v)) {
      Entry::Vacant(e) => {
        let n = self.vec.len();
        let vars = e.key().vars(&mut self.bv, |i| self.vec[i].2);
        self.vec.push((e.key().clone(), false, vars));
        e.insert(n);
        n
      }
      Entry::Occupied(e) => {
        let &n = e.get();
        self.vec[n].1 = true;
        n
      }
    }
  }

  fn reuse(&mut self, n: usize) -> usize {
    self.vec[n].1 = true;
    n
  }
}

/// An iterator over the elements allocated by a [`Dedup`], created by
/// the [`IntoIterator`] implementation for [`Dedup`].
#[must_use] #[derive(Debug)]
pub struct DedupIter<'a, H: NodeHash>(std::slice::Iter<'a, (Rc<H>, bool, u64)>);

impl<'a, H: NodeHash> Iterator for DedupIter<'a, H> {
  type Item = (&'a H, bool);
  fn next(&mut self) -> Option<(&'a H, bool)> {
    self.0.next().map(|&(ref e, b, _)| (&**e, b))
  }
}

impl<H: NodeHash> ExactSizeIterator for DedupIter<'_, H> {
  fn len(&self) -> usize { self.0.len() }
}

impl<'a, H: NodeHash> IntoIterator for &'a Dedup<H> {
  type Item = (&'a H, bool);
  type IntoIter = DedupIter<'a, H>;
  fn into_iter(self) -> DedupIter<'a, H> { DedupIter(self.vec.iter()) }
}

#[inline] fn push_one<T>(vec: &mut Vec<T>, t: T) -> usize {
  let n = vec.len();
  vec.push(t);
  n
}

#[inline] fn push_iter<T>(vec: &mut Vec<T>, it: impl Iterator<Item=T>) -> usize {
  let n = vec.len();
  vec.extend(it);
  n
}

/// A "hash-consable" type. We use this to abstract the difference between
/// [`ExprNode`] and [`ProofNode`].
///
/// The [`Hash`] type here ([`ExprHash`] and [`ProofHash`]) is a de-recursified
/// version of the type where all recursive occurrences are replaced by `usize`
/// indexes. This trait describes how hash objects can be reconstituted
/// into node objects.
///
/// This trait is mutually recursive with the [`Val`] type.
pub trait Node: Sized {
  /// The type of hash objects.
  type Hash: NodeHash;
  /// The variant constuctor of this type for variables and backreferences.
  const REF: fn(usize) -> Self;
  /// Given a hash object, a list of ids containing values that
  /// have previously been computed, and an allocator for nested values,
  /// reconstruct an element of the recursive type.
  fn from(e: &Self::Hash, ids: &mut [Val<Self>], store: &mut Vec<Self>) -> Self;
}

/// A constructed value corresponding to one index of a [`Dedup`].
///
/// For unshared values, we use the [`Built`](Val::Built) constructor to store
/// a value of type `T` directly, while for shared values we only
/// store a reference to the [`Ref`](Val::Ref) node index that was allocated to it.
/// The [`Done`](Val::Done) constructor represents an unshared value that has
/// already been "used up" by its referent.
#[derive(Debug, Default)]
pub enum Val<T: Node> {
  /// An unshared value.
  Built(T),
  /// A shared value; the corresponding node is `T::REF(n)`.
  Ref(usize),
  /// An unshared value that has been moved away.
  #[default] Done,
}

impl<T: Node> Val<T> {
  /// Take the value of type `T` out of this [`Val`], leaving it
  /// in [`Done`](Val::Done) state for unshared values and "cloning" it
  /// for shared values.
  /// # Panics
  /// Calling [`take`](Val::take) on an unshared value that has already been taken
  /// causes a panic. This is usually caused by a value being marked
  /// as unshared even though it appears twice in the proof.
  /// Calling [`reuse`](IDedup::reuse) should ensure that this doesn't happen.
  pub fn take(&mut self) -> T {
    match mem::take(self) {
      Val::Built(x) => x,
      Val::Ref(n) => {*self = Val::Ref(n); T::REF(n)}
      Val::Done => panic!("taking a value twice")
    }
  }

  /// Returns true if this value is unshared.
  pub fn is_unshared(&self) -> bool { matches!(self, Val::Built(_)) }
}

/// Given a [`Dedup`] (or something that looks like one), consume it
/// and produce a pair `(ids, heap)` where `ids` is a set of
/// `Val<T>` nodes and `heap` is a list of shared values,
/// using the sharing annotations to determine whether to put the
/// values directly in [`Built`](Val::Built) nodes (for unshared nodes) or in
/// the `heap` with [`Ref`](Val::Ref) nodes in the `ids`.
#[allow(clippy::too_long_first_doc_paragraph, clippy::type_complexity)]
pub fn build<'a, T: Node, D>(de: D) -> (Box<[Val<T>]>, Box<[T]>, Vec<T>)
where
  T::Hash: 'a,
  D: IntoIterator<Item=(&'a T::Hash, bool)>,
  D::IntoIter: ExactSizeIterator
{
  let it = de.into_iter();
  let mut ids: Vec<Val<T>> = Vec::with_capacity(it.len());
  let mut heap = Vec::new();
  let mut store = Vec::new();
  for (e, b) in it {
    if *e == T::Hash::NONE {
      ids.push(Val::Done)
    } else {
      let node = T::from(e, &mut ids, &mut store);
      if b {
        ids.push(Val::Ref(heap.len()));
        heap.push(node);
      } else {
        ids.push(Val::Built(node))
      }
    }
  }
  (ids.into(), heap.into(), store)
}

/// The [`NodeHash`] version of [`ExprNode`]. It has the same structure except that
/// all internal references to [`ExprNode`] are replaced by `usize` indexes.
#[derive(PartialEq, Eq, Hash, Debug)]
pub enum ExprHash {
  /// An invalid expression.
  None,
  /// `Ref(n)` is a reference to heap element `n` (the first `args.len()` of them are the variables).
  /// `ProofKind` is here for consistency, but the only valid kind is [`ProofKind::Expr`].
  Ref(ProofKind, usize),
  /// `Dummy(s, sort)` is a fresh dummy variable `s` with sort `sort`
  Dummy(AtomId, SortId),
  /// `App(t, nodes)` is an application of term constructor `t` to subterms
  App(TermId, Box<[usize]>),
}

impl NodeHash for ExprHash {
  const NONE: Self = Self::None;
  const REF: fn(ProofKind, usize) -> Self = Self::Ref;

  fn from(nh: &NodeHasher<'_>, fsp: Option<&FileSpan>, _: ProofKind, r: &LispVal,
      de: &mut Dedup<Self>) -> Result<Result<Self, usize>> {
    Ok(Ok(match &**r {
      LispKind::Atom(AtomId::SORRY) =>
        return Err(ElabError::warn(try_get_span_from(&nh.fsp, fsp), "proof uses sorry")),
      &LispKind::Atom(a) => match nh.var_map.get(&a) {
        Some(&i) => ExprHash::Ref(ProofKind::Expr, i),
        None => match nh.lc.vars.get(&a) {
          Some(&(true, InferSort::Bound { sort, .. })) => {
            if nh.fe.sorts[sort].mods.intersects(Modifiers::STRICT | Modifiers::FREE) {
              return Err(nh.err_sp(fsp,
                format!("dummy variable {{{}: {}}} not permitted for sort",
                  nh.fe.data[a].name, nh.fe.sorts[sort].name)))
            }
            ExprHash::Dummy(a, sort)
          }
          _ => return Err(nh.err_sp(fsp, format!("variable '{}' not found", nh.fe.data[a].name))),
        }
      },
      LispKind::MVar(_, tgt) => return Err(nh.err_sp(fsp,
        format!("{}: {}", nh.fe.to(r), nh.fe.to(tgt)))),
      _ => {
        let mut u = Uncons::from(r.clone());
        let head = u.next().ok_or_else(||
          nh.err_sp(fsp, format!("bad expression {}", nh.fe.to(r))))?;
        let a = head.as_atom().ok_or_else(|| nh.err(&head, "expected an atom"))?;
        let tid = nh.fe.term(a).ok_or_else(||
          nh.err(&head, format!("term '{}' not declared", nh.fe.data[a].name)))?;
        let mut ns = Vec::new();
        for e in &mut u { ns.push(de.dedup(nh, ProofKind::Expr, &e)?) }
        if !u.exactly(0) {
          return Err(nh.err_sp(fsp, format!("bad expression {}", nh.fe.to(r))))
        }
        ExprHash::App(tid, ns.into())
      }
    }))
  }

  fn vars(&self, bv: &mut u64, deps: impl Fn(usize) -> u64) -> u64 {
    match self {
      Self::None => 0,
      &Self::Ref(_, n) => deps(n),
      &Self::Dummy(_, _) => (*bv, *bv *= 2).0,
      Self::App(_, es) => es.iter().fold(0, |a, &i| a | deps(i)),
    }
  }

  fn to_lisp(&self, builder: &mut ToLisp, env: &mut Environment, de: &Dedup<Self>) -> LispVal {
    match *self {
      Self::None => LispVal::undef(),
      Self::Ref(_, i) => LispVal::atom(env.get_atom(format!("v{i}").as_bytes())),
      Self::Dummy(a, _) => LispVal::atom(a),
      Self::App(t, ref es) => {
        let mut args = vec![LispVal::atom(env.terms[t].atom)];
        args.extend(es.iter().map(|&i| builder.get(env, de, i)));
        LispVal::list(args)
      }
    }
  }

  fn on_children(&self, f: impl FnMut(usize)) {
    if let ExprHash::App(_, es) = self {
      es.iter().copied().for_each(f)
    }
  }
}

impl Node for ExprNode {
  type Hash = ExprHash;
  const REF: fn(usize) -> Self = ExprNode::Ref;
  fn from(e: &Self::Hash, ids: &mut [Val<Self>], store: &mut Vec<Self>) -> Self {
    match *e {
      ExprHash::None => panic!("value missing"),
      ExprHash::Ref(_, i) => ExprNode::Ref(i),
      ExprHash::Dummy(a, s) => ExprNode::Dummy(a, s),
      ExprHash::App(t, ref ns) => ExprNode::App(t,
        push_iter(store, ns.iter().map(|&i| Val::take(&mut ids[i])))),
    }
  }
}

impl Environment {
  /// Given a mapping of bound variables to lisp names,
  /// convert a packed representation of dependencies to a lisp list.
  #[must_use] pub fn deps(bvars: &[LispVal], xs: u64) -> LispVal {
    let mut deps = vec![];
    if xs != 0 {
      let mut bv = 1;
      for e in bvars {
        if xs & bv != 0 { deps.push(e.clone()) }
        bv *= 2;
      }
    }
    LispVal::list(deps)
  }

  /// Given a list of binders, convert them to a lisp list, updating
  /// the `heap` mapping of variable indexes to lisp names,
  /// and the `bvs` mapping of bound variable indexes to lisp names.
  pub fn binders(&self, bis: &[(Option<AtomId>, Type)],
      heap: &mut Vec<LispVal>, bvars: &mut Vec<LispVal>) -> LispVal {
    LispVal::list(bis.iter().map(|(a, t)| LispVal::list({
      let a = LispVal::atom(a.unwrap_or(AtomId::UNDER));
      heap.push(a.clone());
      match *t {
        Type::Bound(s) => {bvars.push(a.clone()); vec![a, LispVal::atom(self.sorts[s].atom)]}
        Type::Reg(s, xs) => vec![a, LispVal::atom(self.sorts[s].atom), Self::deps(bvars, xs)]
      }
    })).collect::<Vec<_>>())
  }

  /// Convert an [`ExprNode`] object to a [`LispVal`], under a context `heap`. If
  /// `ds` is set, it will accumulate any [`Dummy`](ExprNode::Dummy)
  /// nodes that are encountered.
  pub fn expr_node(&self, heap: &[LispVal], ds: &mut Option<&mut Vec<LispVal>>,
    store: &[ExprNode], e: &ExprNode
  ) -> LispVal {
    match *e {
      ExprNode::Ref(n) => heap[n].clone(),
      ExprNode::Dummy(a, s) => {
        let a = LispVal::atom(a);
        if let Some(ds) = ds {
          ds.push(LispVal::list(vec![a.clone(), LispVal::atom(self.sorts[s].atom)]));
        }
        a
      }
      ExprNode::App(t, p) => {
        let td = &self.terms[t];
        let es = td.unpack_app(&store[p..]);
        let mut args = vec![LispVal::atom(td.atom)];
        args.extend(es.iter().map(|e| self.expr_node(heap, ds, store, e)));
        LispVal::list(args)
      }
    }
  }

  /// Convert a [`ProofNode`] object to a [`LispVal`], under a context `heap`. If
  /// `ds` is set, it will accumulate any [`Dummy`](ExprNode::Dummy)
  /// nodes that are encountered.
  pub fn proof_node(&self, hyps: &[(Option<AtomId>, ExprNode)],
    heap: &[LispVal], ds: &mut Option<&mut Vec<LispVal>>,
    store: &[ProofNode], p: &ProofNode
  ) -> LispVal {
    match *p {
      ProofNode::Ref(n) => heap[n].clone(),
      ProofNode::Dummy(a, s) => {
        let a = LispVal::atom(a);
        if let Some(ds) = ds {
          ds.push(LispVal::list(vec![a.clone(), LispVal::atom(self.sorts[s].atom)]));
        }
        a
      }
      ProofNode::Term(term, p) |
      ProofNode::Cong(term, p) => {
        let td = &self.terms[term];
        let mut args = vec![LispVal::atom(td.atom)];
        args.extend(td.unpack_term(&store[p..]).iter()
          .map(|e| self.proof_node(hyps, heap, ds, store, e)));
        LispVal::list(args)
      }
      ProofNode::Hyp(h, _) => LispVal::atom(hyps[h].0.unwrap_or(AtomId::UNDER)),
      ProofNode::Thm(thm, p) => {
        let td = &self.thms[thm];
        let es = &store[p+1..][..td.args.len()+td.hyps.len()];
        let mut args = vec![LispVal::atom(td.atom)];
        args.extend(es.iter().map(|e| self.proof_node(hyps, heap, ds, store, e)));
        LispVal::list(args)
      }
      ProofNode::Conv(p) => {
        let (t, c, p) = ProofNode::unpack_conv(&store[p..]);
        LispVal::list(vec![LispVal::atom(AtomId::CONV),
          self.proof_node(hyps, heap, ds, store, t),
          self.proof_node(hyps, heap, ds, store, c),
          self.proof_node(hyps, heap, ds, store, p),
        ])
      }
      ProofNode::Refl(p) => self.proof_node(hyps, heap, ds, store, &store[p]),
      ProofNode::Sym(p) =>
        LispVal::list(vec![LispVal::atom(AtomId::SYM),
          self.proof_node(hyps, heap, ds, store, &store[p])
        ]),
      ProofNode::Unfold(term, p) => {
        let td = &self.terms[term];
        let (_, c, args) = td.unpack_unfold(&store[p..]);
        LispVal::list(vec![LispVal::atom(AtomId::UNFOLD),
          LispVal::atom(td.atom),
          LispVal::list(args.iter().map(|e| self.proof_node(hyps, heap, ds, store, e))
            .collect::<Vec<_>>()),
          self.proof_node(hyps, heap, ds, store, c)
        ])
      }
    }
  }
}

/// The [`NodeHash`] version of [`ProofNode`]. It has the same structure except that
/// all internal references to [`ProofNode`] are replaced by `usize` indexes.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum ProofHash {
  /// An invalid proof node.
  None,
  /// `Ref(n)` is a reference to heap element `n` (the first `args.len()` of them are the variables).
  /// This could be an expr, proof, or conv depending on what is referenced.
  Ref(ProofKind, usize),
  /// `Dummy(s, sort)` is a fresh dummy variable `s` with sort `sort`
  Dummy(AtomId, SortId),
  /// `Term(term, args)` is an application of term constructor `term` to subterms
  Term(TermId, Box<[usize]>),
  /// `Hyp(i, e)` is hypothesis `i` (`hyps[i]` will be a reference to element),
  /// which is a proof of `|- e`.
  Hyp(usize, usize),
  /// `Thm(thm, args, res)` is a proof of `|- res` by applying theorem `thm` to arguments `args`.
  Thm(ThmId, Box<[usize]>, usize),
  /// `Conv(tgt, conv, proof)` is a proof of `|- tgt` if `proof: src` and `conv: tgt = src`.
  Conv(usize, usize, usize),
  /// `Refl(e): e = e`
  Refl(usize),
  /// `Refl(p): e2 = e1` if `p: e1 = e2`
  Sym(usize),
  /// `Cong(term, args): term a1 ... an = term b1 ... bn` if `args[i]: ai = bi`
  Cong(TermId, Rc<[usize]>),
  /// `Unfold(term, args, lhs, sub_lhs, p)` is a proof of `lhs = rhs` if
  /// `lhs` is `term args` and `term` is a definition and `sub_lhs` is the result of
  /// substituting `args` into the definition of `term`, and `p: sub_lhs = rhs`
  Unfold(TermId, Box<[usize]>, usize, usize, usize),
}

impl ProofHash {
  /// Apply a substitution, while preserving sharing. The `n_heap` array contains
  /// indexes for substituted subterms, in case we see the same subterm multiple times.
  pub fn subst(env: &Environment, de: &mut impl IDedup<Self>,
    heap: &[ExprNode], n_heap: &mut [Option<usize>],
    store: &[ExprNode], e: &ExprNode
  ) -> usize {
    match *e {
      ExprNode::Ref(i) =>
        if let Some(n) = n_heap[i] {
          de.reuse(n)
        } else {
          let n = Self::subst(env, de, heap, n_heap, store, &heap[i]);
          n_heap[i] = Some(n);
          n
        },
      ExprNode::Dummy(_, _) => unreachable!(),
      ExprNode::App(t, p) => {
        let es = env.terms[t].unpack_app(&store[p..]);
        let es2 = es.iter().map(|e| Self::subst(env, de, heap, n_heap, store, e)).collect();
        de.add_direct(ProofHash::Term(t, es2))
      }
    }
  }

  /// Returns true if this proof term represents a conversion.
  pub fn is_conv(de: &impl IDedup<Self>, i: usize) -> bool {
    match de[i] {
      Self::None => panic!("value missing"),
      Self::Ref(k, _) => k == ProofKind::Conv,
      Self::Dummy(..) |
      Self::Term(..) |
      Self::Hyp(..) |
      Self::Thm(..) |
      Self::Conv(..) => false,
      Self::Refl(..) |
      Self::Sym(..) |
      Self::Cong(..) |
      Self::Unfold(..) => true,
    }
  }

  /// Get the LHS (if `right = false`) or RHS (if `right = true`) of the conversion
  /// represented by proof term index `i`.
  pub fn conv_side(de: &mut impl IDedup<Self>, i: usize, right: bool) -> usize {
    debug_assert!(Self::is_conv(de, i));
    match de[i] {
      Self::None => panic!("value missing"),
      Self::Ref(_, j) => { assert!(j < i); Self::conv_side(de, j, right) }
      Self::Dummy(..) |
      Self::Term(..) |
      Self::Hyp(..) |
      Self::Thm(..) |
      Self::Conv(..) => unreachable!(),
      Self::Refl(e) => de.reuse(e),
      Self::Sym(c) => Self::conv_side(de, c, !right),
      Self::Cong(t, ref cs) => {
        let ns = cs.clone().iter().map(|&c| Self::conv_side(de, c, right)).collect::<Vec<_>>();
        de.add_direct(Self::Term(t, ns.into()))
      }
      Self::Unfold(_, _, _, _, c) if right => Self::conv_side(de, c, true),
      Self::Unfold(_, _, lhs, _, _) => de.reuse(lhs),
    }
  }

  /// If this is an expression, convert it to a conversion using [`Refl`](ProofHash::Refl).
  /// For conversions, leave it as is.
  /// (This function should not be called on proof terms.)
  #[allow(clippy::wrong_self_convention)]
  pub fn as_conv(de: &mut impl IDedup<Self>, i: usize) -> usize {
    if Self::is_conv(de, i) {
      i
    } else {
      de.add_direct(ProofHash::Refl(i))
    }
  }
}

impl NodeHash for ProofHash {
  const NONE: Self = Self::None;
  const REF: fn(ProofKind, usize) -> Self = Self::Ref;

  fn from(nh: &NodeHasher<'_>, fsp: Option<&FileSpan>, kind: ProofKind, r: &LispVal,
      de: &mut Dedup<Self>) -> Result<Result<Self, usize>> {
    Ok(Ok(match &**r {
      LispKind::Atom(AtomId::SORRY) =>
        return Err(ElabError::warn(try_get_span_from(&nh.fsp, fsp), "proof uses sorry")),
      &LispKind::Atom(a) => match kind {
        ProofKind::Expr | ProofKind::Conv => {
          let e = match nh.var_map.get(&a) {
            Some(&i) => ProofHash::Ref(ProofKind::Expr, i),
            None => match nh.lc.vars.get(&a) {
              Some(&(true, InferSort::Bound { sort, .. })) => {
                if nh.fe.sorts[sort].mods.intersects(Modifiers::STRICT | Modifiers::FREE) {
                  return Err(nh.err_sp(fsp,
                    format!("dummy variable {{{}: {}}} not permitted for sort",
                      nh.fe.data[a].name, nh.fe.sorts[sort].name)))
                }
                ProofHash::Dummy(a, sort)
              }
              _ => return Err(nh.err_sp(fsp, format!("variable '{}' not found", nh.fe.data[a].name))),
            }
          };
          if kind == ProofKind::Conv { ProofHash::Refl(de.add_direct(e)) } else { e }
        }
        ProofKind::Proof => match nh.lc.get_proof(a) {
          Some((_, _, p)) => return Ok(Err(de.dedup(nh, ProofKind::Proof, p)?)),
          None => return Err(nh.err_sp(fsp, format!("hypothesis '{}' not found", nh.fe.data[a].name))),
        }
      },
      LispKind::MVar(_, tgt) => return Err(nh.err_sp(fsp,
        format!("{}: {}", nh.fe.to(r), nh.fe.to(tgt)))),
      LispKind::Goal(tgt) => return Err(nh.err_sp(fsp, format!("|- {}", nh.fe.to(tgt)))),
      _ => {
        let mut u = Uncons::from(r.clone());
        let th_head = u.next().ok_or_else(||
          nh.err_sp(fsp, format!("bad expression {}", nh.fe.to(r))))?;
        let a = th_head.as_atom().ok_or_else(|| nh.err(&th_head, "expected an atom"))?;
        let adata = &nh.fe.data[a];
        match adata.decl {
          Some(DeclKey::Term(tid)) => {
            let mut ns = Vec::new();
            for e in u { ns.push(de.dedup(nh, ProofKind::Expr, &e)?) }
            if ns.iter().any(|&i| Self::is_conv(de, i)) {
              for i in &mut ns {*i = Self::as_conv(de, *i)}
              ProofHash::Cong(tid, ns.into())
            } else {
              ProofHash::Term(tid, ns.into())
            }
          }
          Some(DeclKey::Thm(tid)) => {
            let mut ns = Vec::new();
            let td = &nh.fe.thms[tid];
            for (i, e) in u.enumerate() {
              let kind = if i < td.args.len() {ProofKind::Expr} else {ProofKind::Proof};
              ns.push(de.dedup(nh, kind, &e)?)
            }
            if ns.len() != td.args.len() + td.hyps.len() {
              return Err(nh.err_sp(fsp,
                format!("incorrect number of theorem arguments: {}", nh.fe.to(r))))
            }
            let mut heap = vec![None; td.heap.len()];
            let mut bvars: Vec<u64> = vec![];
            for (i, (_, t)) in td.args.iter().enumerate() {
              heap[i] = Some(ns[i]);
              let deps = de.vec[ns[i]].2;
              let ok = match t {
                Type::Bound(_) => {
                  bvars.push(deps);
                  ns[..i].iter().all(|&j| de.vec[j].2 & deps == 0)
                }
                &Type::Reg(_, mut d) => bvars.iter().all(|&bv| {
                  let old = d;
                  d /= 2;
                  old & 1 != 0 || bv & deps == 0
                }),
              };
              if !ok {
                let mut dvs = vec![];
                let mut bvars = vec![];
                for (i, (_, t)) in td.args.iter().enumerate() {
                  match t {
                    Type::Bound(_) => {
                      bvars.push(i);
                      dvs.extend((0..i).map(|j| (j, i)));
                    }
                    &Type::Reg(_, mut d) =>
                      dvs.extend(bvars.iter()
                        .filter(|_| { let old = d; d /= 2; old & 1 == 0 })
                        .map(|&j| (j, i)))
                  }
                }
                let mut err = format!("disjoint variable violation at {}", adata.name);
                let args: Vec<_> = Uncons::from(r.clone()).skip(1).collect();
                for (i, j) in dvs {
                  if de.vec[ns[i]].2 & de.vec[ns[j]].2 != 0 {
                    use std::fmt::Write;
                    write!(err, "\n  ({}, {}) -> ({}, {})",
                      nh.fe.to(&td.args[i].0.unwrap_or(AtomId::UNDER)),
                      nh.fe.to(&td.args[j].0.unwrap_or(AtomId::UNDER)),
                      nh.fe.pp(&args[i], 80), nh.fe.pp(&args[j], 80)).unwrap();
                  }
                }
                return Err(nh.err(&th_head, err))
              }
            }
            let rhs = Self::subst(nh.fe.env, de, &td.heap, &mut heap, &td.store, &td.ret);
            ProofHash::Thm(tid, ns.into(), rhs)
          },
          None => match a {
            AtomId::CONV => match (u.next(), u.next(), u.next()) {
              (Some(tgt), Some(conv), Some(prf)) if u.exactly(0) => {
                let tgt = de.dedup(nh, ProofKind::Expr, &tgt)?;
                let conv = de.dedup(nh, ProofKind::Conv, &conv)?;
                let conv = Self::as_conv(de, conv);
                let prf = de.dedup(nh, ProofKind::Proof, &prf)?;
                ProofHash::Conv(tgt, Self::as_conv(de, conv), prf)
              }
              _ => return Err(nh.err_sp(fsp, format!("incorrect :conv format {}", nh.fe.to(r))))
            },
            AtomId::SYM => match u.next() {
              Some(p) if u.exactly(0) => {
                let p = de.dedup(nh, ProofKind::Conv, &p)?;
                ProofHash::Sym(Self::as_conv(de, p))
              }
              _ => return Err(nh.err_sp(fsp, format!("incorrect :sym format {}", nh.fe.to(r))))
            },
            AtomId::UNFOLD => {
              let (ty, es, prf) = match (u.next(), u.next(), u.next(), u.next()) {
                (Some(ty), Some(es), Some(prf), None) if u.exactly(0) => (ty, es, prf),
                (Some(ty), Some(es), Some(_), Some(prf)) if u.exactly(0) => (ty, es, prf),
                _ => return Err(nh.err_sp(fsp, format!("incorrect :unfold format {}", nh.fe.to(r))))
              };
              let tid = ty.as_atom().and_then(|a| nh.fe.term(a))
                .ok_or_else(|| nh.err(&ty, "expected a term"))?;
              let mut ns = Vec::new();
              for e in Uncons::from(es) { ns.push(de.dedup(nh, ProofKind::Expr, &e)?) }
              let lhs = de.add_direct(ProofHash::Term(tid, ns.clone().into()));
              let c = de.dedup(nh, ProofKind::Conv, &prf)?;
              let c = Self::as_conv(de, c);
              let l2 = Self::conv_side(de, c, false);
              ProofHash::Unfold(tid, ns.into(), lhs, l2, c)
            },
            _ => return Err(nh.err(&th_head, format!("term/theorem '{}' not declared", adata.name)))
          }
        }
      }
    }))
  }

  fn vars(&self, bv: &mut u64, deps: impl Fn(usize) -> u64) -> u64 {
    match self {
      &Self::Ref(_, n) => deps(n),
      &Self::Dummy(_, _) => (*bv, *bv *= 2).0,
      Self::Term(_, es) => es.iter().fold(0, |a, &i| a | deps(i)),
      _ => 0,
    }
  }

  fn to_lisp(&self, builder: &mut ToLisp, env: &mut Environment, de: &Dedup<Self>) -> LispVal {
    match *self {
      Self::None => LispVal::undef(),
      Self::Ref(_, i) => LispVal::atom(env.get_atom(format!("v{i}").as_bytes())),
      Self::Dummy(a, _) => LispVal::atom(a),
      Self::Term(t, ref es) => {
        let mut args = vec![LispVal::atom(env.terms[t].atom)];
        args.extend(es.iter().map(|&i| builder.get(env, de, i)));
        LispVal::list(args)
      }
      Self::Hyp(i, _) => match builder.hyps.get(i) {
        Some(Some(e)) => e.clone(),
        _ => LispVal::atom(env.get_atom(format!("h{i}").as_bytes()))
      },
      Self::Thm(t, ref es, _) => {
        let mut args = vec![LispVal::atom(env.thms[t].atom)];
        args.extend(es.iter().map(|&i| builder.get(env, de, i)));
        LispVal::list(args)
      }
      Self::Conv(tgt, conv, prf) => LispVal::list([
        LispVal::atom(AtomId::CONV),
        builder.get(env, de, tgt),
        builder.get(env, de, conv),
        builder.get(env, de, prf),
      ]),
      Self::Refl(e) => builder.get(env, de, e),
      Self::Sym(e) => LispVal::list([LispVal::atom(AtomId::SYM), builder.get(env, de, e)]),
      Self::Cong(t, ref es) => {
        let mut args = vec![LispVal::atom(env.terms[t].atom)];
        args.extend(es.iter().map(|&i| builder.get(env, de, i)));
        LispVal::list(args)
      }
      Self::Unfold(t, ref es, _, _, c) => LispVal::list([
        LispVal::atom(AtomId::UNFOLD),
        LispVal::atom(env.terms[t].atom),
        LispVal::list(es.iter().map(|&i| builder.get(env, de, i)).collect::<Box<[_]>>()),
        builder.get(env, de, c),
      ])
    }
  }

  fn on_children(&self, mut f: impl FnMut(usize)) {
    match *self {
      Self::None |
      Self::Ref(_, _) |
      Self::Dummy(_, _) => {}
      Self::Hyp(_, e) |
      Self::Refl(e) |
      Self::Sym(e) => f(e),
      Self::Term(_, ref ns) => ns.iter().copied().for_each(&mut f),
      Self::Thm(_, ref ns, r) => { ns.iter().copied().for_each(&mut f); f(r) }
      Self::Conv(i, j, k) => { f(i); f(j); f(k) }
      Self::Cong(_, ref ns) => ns.iter().copied().for_each(&mut f),
      Self::Unfold(_, ref ns, _, m, c) => {
        ns.iter().copied().for_each(&mut f); f(m); f(c)
      }
    }
  }
}

impl ExprHash {
  /// Convert an [`ExprHash`] directly to a [`ProofHash`]. This is an injective function,
  /// so it can be used with [`map_inj`](Dedup::map_inj).
  #[must_use] pub fn to_proof(&self) -> ProofHash {
    match *self {
      ExprHash::None => ProofHash::None,
      ExprHash::Ref(k, i) => ProofHash::Ref(k, i),
      ExprHash::Dummy(a, s) => ProofHash::Dummy(a, s),
      ExprHash::App(t, ref ns) => ProofHash::Term(t, ns.clone()),
    }
  }
}

impl Dedup<ExprHash> {
  /// Efficiently maps a `Dedup<ExprHash>` to a `Dedup<ProofHash>`. This is
  /// useful for initializing the `Dedup<ProofHash>` based on a previous analysis
  /// of exprs used in the statement of the theorem.
  pub fn map_proof(&self) -> Dedup<ProofHash> {
    self.map_inj(ExprHash::to_proof)
  }
}

impl Node for ProofNode {
  type Hash = ProofHash;
  const REF: fn(usize) -> Self = ProofNode::Ref;
  fn from(e: &Self::Hash, ids: &mut [Val<Self>], store: &mut Vec<Self>) -> Self {
    match *e {
      ProofHash::None => panic!("value missing"),
      ProofHash::Ref(_, i) => ProofNode::Ref(i),
      ProofHash::Dummy(a, s) => ProofNode::Dummy(a, s),
      ProofHash::Term(term, ref ns) => ProofNode::Term(term,
        push_iter(store, ns.iter().map(|&i| Val::take(&mut ids[i])))),
      ProofHash::Hyp(i, e) => ProofNode::Hyp(i, push_one(store, Val::take(&mut ids[e]))),
      ProofHash::Thm(thm, ref ns, r) => {
        let p = push_one(store, Val::take(&mut ids[r]));
        push_iter(store, ns.iter().map(|&i| Val::take(&mut ids[i])));
        ProofNode::Thm(thm, p)
      }
      ProofHash::Conv(tgt, conv, proof) => {
        let p = push_one(store, Val::take(&mut ids[tgt]));
        let _ = push_one(store, Val::take(&mut ids[conv]));
        let _ = push_one(store, Val::take(&mut ids[proof]));
        ProofNode::Conv(p)
      }
      ProofHash::Refl(i) => ProofNode::Refl(push_one(store, Val::take(&mut ids[i]))),
      ProofHash::Sym(i) => ProofNode::Sym(push_one(store, Val::take(&mut ids[i]))),
      ProofHash::Cong(term, ref ns) => ProofNode::Cong(term,
        push_iter(store, ns.iter().map(|&i| Val::take(&mut ids[i])))),
      ProofHash::Unfold(term, ref ns, _, m, c) => {
        let p = push_one(store, Val::take(&mut ids[m]));
        let _ = push_one(store, Val::take(&mut ids[c]));
        let _ = push_iter(store, ns.iter().map(|&i| Val::take(&mut ids[i])));
        ProofNode::Unfold(term, p)
      }
    }
  }
}

/// A structure for performing substitutions on expressions represented as lisp values.
#[derive(Debug)]
pub struct Subst<'a> {
  /// The ambient environment.
  env: &'a Environment,
  /// The heap (from the theorem statement).
  heap: &'a [ExprNode],
  /// The store (from the theorem statement).
  store: &'a [ExprNode],
  /// The already computed substitutions for elements of the heap, with unknown
  /// values set to `#undef`.
  subst: Vec<LispVal>,
}

impl<'a> Subst<'a> {
  /// Contruct a new [`Subst`] object. `args` should be initialized to
  /// the arguments to the theorem application (possibly metavariables).
  #[must_use] pub fn new(env: &'a Environment,
    heap: &'a [ExprNode], store: &'a [ExprNode], mut args: Vec<LispVal>
  ) -> Subst<'a> {
    args.resize(heap.len(), LispVal::undef());
    Subst {env, heap, store, subst: args}
  }

  /// Substitute in an [`ExprNode`]. This version does not support dummy variables,
  /// which means it can be used for theorem applications but not definition unfolding.
  pub fn subst(&mut self, e: &ExprNode) -> LispVal {
    match *e {
      ExprNode::Ref(i) => {
        let e = &self.subst[i];
        if e.is_def() {return e.clone()}
        let e = self.subst(&self.heap[i]);
        self.subst[i] = e.clone();
        e
      }
      ExprNode::Dummy(_, _) => unreachable!(),
      ExprNode::App(t, p) => {
        let td = &self.env.terms[t];
        let mut args = vec![LispVal::atom(td.atom)];
        args.extend(td.unpack_app(&self.store[p..]).iter().map(|e| self.subst(e)));
        LispVal::list(args)
      }
    }
  }

  /// Substitute in an [`ExprNode`]. This version creates new metavariables
  /// when encountering [`Dummy`](ExprNode::Dummy) nodes.
  pub fn subst_mut(&mut self, lc: &mut LocalContext, e: &ExprNode) -> LispVal {
    match *e {
      ExprNode::Ref(i) => {
        let e = &self.subst[i];
        if e.is_def() {return e.clone()}
        let e = self.subst_mut(lc, &self.heap[i]);
        self.subst[i] = e.clone();
        e
      }
      ExprNode::Dummy(_, s) => lc.new_mvar(InferTarget::Bound(self.env.sorts[s].atom), None),
      ExprNode::App(t, p) => {
        let td = &self.env.terms[t];
        let mut args = vec![LispVal::atom(td.atom)];
        args.extend(td.unpack_app(&self.store[p..]).iter().map(|e| self.subst_mut(lc, e)));
        LispVal::list(args)
      }
    }
  }
}
