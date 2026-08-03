//! Exporter for the `Lisp` index table: serializes the global lisp environment
//! into the value stream described in `mm0-rs/mmb-lisp.md`.
//!
//! The exporter runs in two phases. The first ([`Dedup`]) hash-conses every
//! reachable value into a DAG of shadow [`Node`]s — structural values (atoms,
//! strings, spans, cons cells, ...) share by content, while reference-identity
//! values (`atom-map`s, `ref!` cells, closures) are left [opaque](Node::Opaque)
//! and share by pointer — and records, for each node, whether it is reached more
//! than once. The second ([`Emitter`]) walks that DAG and writes the byte stream:
//! a node reached more than once is written once under a save command and reached
//! again by `Ref`, so the file stays a DAG.
//!
//! Both phases drive an explicit work stack rather than native recursion: values
//! nest arbitrarily deep (a million-element list is a million-deep cons chain), so
//! recursion would overflow the machine stack.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::sync::Arc;

use num::{BigInt, ToPrimitive};

use crate::elab::frozen::{
  freeze_merge_strategy, FrozenEnv, FrozenLispKind, FrozenLispVal, FrozenMergeStrategy,
  FrozenMergeStrategyView,
};
use crate::elab::lisp::parser::{Ir, MVarPattern};
use crate::elab::lisp::{Annot, BuiltinProc, InferTarget, Proc, ProcPos, ProcSpec};
use crate::elab::environment::{DeclKey, StmtTrace};
use mm0_util::{ArcString, AtomId, FileRef, FileSpan, Modifiers, Span};

use super::{custom, infer, ir, op, pat_mvar, spec, LAMBDA_NAMED};

fn spec_parts(spec: ProcSpec) -> (bool, u8) {
  match spec {
    ProcSpec::Exact(n) => (false, u8::try_from(n).expect("arity too large")),
    ProcSpec::AtLeast(n) => (true, u8::try_from(n).expect("arity too large")),
  }
}

/// True if it would emit more than two bytes in [`Emitter::sleb`]:
/// a k-byte value fits in `-2^(7k-1) <= n < 2^(7k-1)`.
fn is_big(n: &BigInt) -> bool {
  n.to_i64().is_none_or(|n| !(-1 << 13..1 << 13).contains(&n))
}

/// The `PatternMVar` tag byte.
fn mvar_tag(pat: MVarPattern) -> u32 {
  u32::from(match pat {
    MVarPattern::Unknown => pat_mvar::UNKNOWN,
    MVarPattern::Any => pat_mvar::ANY,
    MVarPattern::Simple => pat_mvar::SIMPLE,
  })
}

/// A metavariable's [`InferTarget`], with any `sort` atom resolved to a DAG index.
#[derive(Clone, PartialEq, Eq, Hash)]
enum MTgt {
  Unknown,
  Provable,
  Bound(u32),
  Reg(u32),
}

/// A de-recursified lisp value: a shadow of [`FrozenLispKind`] whose structural
/// children are replaced by `u32` indices into the [`Dedup`] arena.
#[derive(Clone, PartialEq, Eq, Hash)]
enum Node {
  Undef,
  Bool(bool),
  /// A [`Syntax`](crate::elab::lisp::Syntax) keyword code.
  Syntax(u32),
  /// A [`BuiltinProc`] code.
  Builtin(u32),
  Atom(AtomId),
  Number(BigInt),
  Str(ArcString),
  /// The empty list, and the terminator of a proper cons chain.
  Nil,
  /// A cons cell `(car . cdr)`; `List`/`DottedList` decompose into these.
  Cons(u32, u32),
  /// A source file, deduplicated by its relative path (and by pointer, see
  /// [`Dedup::file_ptr`]). Emitted as its path string.
  FileRef(FileRef),
  /// A span `(file, lo, hi)`, deduplicated by value.
  Span(u32, u32, u32),
  /// A value annotated with a span `(span, value)`.
  Annot(u32, u32),
  /// A metavariable `(index, target)`.
  MVar(u32, MTgt),
  /// A goal wrapping a value.
  Goal(u32),
  /// A `(merge-map s)` partial application, holding its sub-strategy value `s`.
  /// A merge procedure is only ever re-parsed via `into_merge_strategy` on load, so
  /// it carries no identity and hash-conses structurally.
  MergeMap(u32),
  /// A lambda's `(spec, body)` core: `(at_least, count, code)`. The `ProcSpec` is
  /// hashed normally, but the `Arc<[Ir]>` body is opaque — keyed only by its data
  /// pointer, since the same core reached twice is the same allocation. Its embedded
  /// lisp values are translated into the arena during phase one and re-resolved (not
  /// stored) at emit; the instructions themselves are re-read from the original
  /// `Arc` held by the enclosing lambda.
  Code(bool, u8, *const Ir),
  /// A live weak reference, holding a pointer to its target. The target is *not*
  /// traversed through the weak link. At emit, if a strong path put it in the DAG
  /// ([`Dedup::prev`]) the reference is written as a `ref!` cell (`NewRef #undef`,
  /// installed pre-order so the cycle it sits in breaks here) and filled with a weak
  /// link to the target by a deferred `SetWeak`; if not, it degrades to a `DeadWeak`.
  Weak(*const FrozenLispKind),
  /// A `ref!` whose weak target has died; reads back as `(ref! #undef)`. Unlike a
  /// live `ref!` it carries no identity, so it hash-conses like any structural node.
  DeadWeak,
  /// A reference-identity value — an `atom-map`, a live `ref!` cell, or a non-builtin
  /// procedure — kept as a pointer to the original object and re-read at emit time.
  /// It shares only by pointer (via [`Dedup::prev`]), never by content, so `==`
  /// survives; its index is claimed before its children are walked, so a `ref!`
  /// cycle can point back at it.
  Opaque(*const FrozenLispKind),
}

/// Phase one: hash-cons every reachable value into a DAG, marking shared nodes.
struct Dedup<'a> {
  env: &'a FrozenEnv,
  /// Structural nodes by content, for value-equality sharing. Shares ownership of
  /// each node with [`vec`](Self::vec).
  map: HashMap<Rc<Node>, u32>,
  /// Atoms by id: a map key or proc-thunk name is a bare [`AtomId`] with no pointer
  /// of its own, so this is how emission resolves those.
  atoms: HashMap<AtomId, u32>,
  /// Every already-visited lisp object by pointer. This is the fast path that
  /// avoids re-walking shared structure, the sole sharing key for [`Opaque`](Node::Opaque)
  /// nodes, and what closes cycles (a `ref!`'s index is here before its contents).
  prev: HashMap<*const FrozenLispKind, u32>,
  /// A [`FileRef`] by allocation pointer: a fast path past the path-string compare
  /// [`Node::FileRef`] would otherwise do.
  file_ptr: HashMap<*const PathBuf, u32>,
  /// The arena: `(node, shared)`, where `shared` is set once the node is reached
  /// a second time. Shares node ownership with [`map`](Self::map).
  vec: Vec<(Rc<Node>, bool)>,
  /// The targets of the weak references seen so far. Resolved after dedup: a target
  /// that some strong path reached is marked shared (so a `SetWeak` can `Ref` it),
  /// and one that no strong path reached leaves its reference a `DeadWeak`.
  weak_targets: Vec<*const FrozenLispKind>,
  /// The shared index of [`Node::Undef`].
  undef: u32,
  /// The shared index of [`Node::Nil`].
  nil: u32,
}

/// A pending step of the phase-one work stack.
enum Frame<'a> {
  /// Hash-cons this value.
  Go(&'a FrozenLispKind),
  /// Fold `elems` (and a `dotted` tail, else `Nil`) into a cons chain for `ptr`.
  BuildList {
    elems: &'a [FrozenLispVal],
    dotted: Option<&'a FrozenLispVal>,
    ptr: *const FrozenLispKind,
  },
  /// Build `Annot(span, val)` for `ptr`.
  BuildAnnot { span: u32, val: &'a FrozenLispVal, ptr: *const FrozenLispKind },
  /// Build `Goal(val)` for `ptr`.
  BuildGoal { val: &'a FrozenLispVal, ptr: *const FrozenLispKind },
}

#[inline]
fn kptr(v: &FrozenLispVal) -> *const FrozenLispKind { std::ptr::from_ref::<FrozenLispKind>(v) }

impl<'a> Dedup<'a> {
  fn new(env: &'a FrozenEnv) -> Self {
    let mut de = Self {
      env,
      map: HashMap::new(),
      atoms: HashMap::new(),
      prev: HashMap::new(),
      file_ptr: HashMap::new(),
      vec: Vec::new(),
      weak_targets: Vec::new(),
      undef: 0,
      nil: 0,
    };
    de.undef = de.add(Node::Undef);
    de.nil = de.add(Node::Nil);
    de
  }

  /// Add a structural node, sharing (and marking shared) an equal one.
  fn add(&mut self, node: Node) -> u32 {
    let rc = Rc::new(node);
    if let Some(&n) = self.map.get(&rc) {
      self.vec[n as usize].1 = true;
      return n
    }
    let n = u32::try_from(self.vec.len()).expect("too many lisp nodes");
    self.vec.push((Rc::clone(&rc), false));
    self.map.insert(rc, n);
    n
  }

  /// Add an identity node, never merged with any other.
  fn add_direct(&mut self, node: Node) -> u32 {
    let n = u32::try_from(self.vec.len()).expect("too many lisp nodes");
    self.vec.push((Rc::new(node), false));
    n
  }

  fn mark_shared(&mut self, n: u32) { self.vec[n as usize].1 = true }

  fn dedup_atom(&mut self, a: AtomId) -> u32 {
    if let Some(&n) = self.atoms.get(&a) { return n }
    let n = self.add_direct(Node::Atom(a));
    self.atoms.insert(a, n);
    n
  }

  fn dedup_str(&mut self, s: &[u8]) -> u32 { self.add(Node::Str(ArcString::from(s))) }

  fn dedup_fileref(&mut self, file: &FileRef) -> u32 {
    if let Some(&n) = self.file_ptr.get(&file.ptr()) { return n }
    let n = self.add(Node::FileRef(file.clone()));
    self.file_ptr.insert(file.ptr(), n);
    n
  }

  fn dedup_fspan(&mut self, fsp: &FileSpan) -> u32 {
    let file = self.dedup_fileref(&fsp.file);
    self.dedup_span(file, fsp.span)
  }

  /// A span node for `span` within an already-deduped `file` (an `Ir` span carries
  /// only its range; its file is the enclosing lambda's, resolved once).
  #[allow(clippy::cast_possible_truncation)]
  fn dedup_span(&mut self, file: u32, span: Span) -> u32 {
    self.add(Node::Span(file, span.start as u32, span.end as u32))
  }

  fn dedup_number(&mut self, n: &BigInt) -> u32 { self.add(Node::Number(n.clone())) }

  fn dedup_mtgt(&mut self, tgt: InferTarget) -> MTgt {
    match tgt {
      InferTarget::Unknown => MTgt::Unknown,
      InferTarget::Provable => MTgt::Provable,
      InferTarget::Bound(s) => MTgt::Bound(self.dedup_atom(s)),
      InferTarget::Reg(s) => MTgt::Reg(self.dedup_atom(s)),
    }
  }

  /// Hash-cons a merge strategy as the value that `into_merge_strategy` re-parses:
  /// `#undef`, a bare `merge-map` builtin, a `(merge-map s)` partial application, or
  /// the custom procedure itself.
  fn dedup_merge(&mut self, m: &'a FrozenMergeStrategy) -> u32 {
    match m.view() {
      FrozenMergeStrategyView::None => self.undef,
      FrozenMergeStrategyView::Custom(f) => self.dedup_value(f),
      FrozenMergeStrategyView::AtomMap(sub) => match sub.view() {
        FrozenMergeStrategyView::None => self.add(Node::Builtin(BuiltinProc::MergeMap as u32)),
        _ => {
          let s = self.dedup_merge(sub);
          self.add(Node::MergeMap(s))
        }
      },
    }
  }

  /// Hash-cons a lambda's `(spec, body)` core. The body is keyed by pointer, so a
  /// core reached again is the same allocation; the first time, walk its
  /// instructions to translate their embedded lisp values into the arena. `file` is
  /// the enclosing lambda's, shared by every span in the body.
  fn dedup_code(&mut self, code: &'a Arc<[Ir]>, spec: ProcSpec, file: u32) -> u32 {
    let (at_least, n) = spec_parts(spec);
    let node = Node::Code(at_least, n, Arc::as_ptr(code).cast());
    if let Some(&idx) = self.map.get(&node) {
      self.mark_shared(idx);
      return idx
    }
    // Register the core before walking its body, so a core that reaches itself
    // (a recursive closure captured in its own instructions) resolves instead of
    // recursing forever.
    let idx = self.add(node);
    for i in &**code { self.translate_ir(i, file) }
    idx
  }

  /// Translate the lisp values an `Ir` instruction embeds into the arena (its spans,
  /// atoms, constants, strings, numbers, and nested cores). Non-value operands
  /// (counts, flags, jump targets) are re-read from the `Arc` at emit.
  fn translate_ir(&mut self, i: &'a Ir, file: u32) {
    match i {
      Ir::Const(v) => {
        // Safety: `freeze` is a read-only cast; the `Rc` is not cloned.
        self.dedup_value(unsafe { v.freeze() });
      }
      Ir::PatternQuoteAtom(a) | Ir::PatternQExprAtom(a) => { self.dedup_atom(*a); }
      Ir::PatternString(s) => { self.dedup_str(s); }
      Ir::PatternNumber(n) => { self.dedup_number(n); }
      &Ir::AppHead(sp) | &Ir::FocusStart(sp) | &Ir::BranchFail(sp) | &Ir::List(sp, _)
      | &Ir::ArityError(sp, _) => { self.dedup_span(file, sp); }
      &Ir::Global(sp, a) | &Ir::SetMergeStrategy(sp, a) => {
        self.dedup_span(file, sp);
        self.dedup_atom(a);
      }
      &Ir::GlobalDef(s1, s2, a) => {
        self.dedup_span(file, s1);
        self.dedup_span(file, s2);
        self.dedup_atom(a);
      }
      Ir::SetDoc(doc, a) => {
        self.dedup_str(doc.as_bytes());
        self.dedup_atom(*a);
      }
      Ir::App(_, spans, _) | Ir::BuiltinApp(_, _, spans, _) => {
        self.dedup_span(file, spans.0);
        self.dedup_span(file, spans.1);
      }
      Ir::Lambda(_, b) => {
        self.dedup_span(file, b.0);
        self.dedup_code(&b.2, b.1, file);
      }
      // no embedded lisp values
      Ir::Drop(_) | Ir::DropAbove(_) | Ir::Undef | Ir::Dup | Ir::AssertScope(_)
      | Ir::EndScope(_) | Ir::Local(_) | Ir::DottedList(_) | Ir::JumpUnless(_) | Ir::Jump(_)
      | Ir::FocusFinish | Ir::LocalDef(_) | Ir::Branch(..) | Ir::TestPatternResume | Ir::Map
      | Ir::Have | Ir::RefineResume | Ir::RefineGoal(_) | Ir::AddThm | Ir::MergeMap | Ir::OnDecls
      | Ir::PatternResult(_) | Ir::PatternAtom(_) | Ir::PatternEqAtom(_) | Ir::PatternBool(_)
      | Ir::PatternUndef | Ir::PatternMVar(_) | Ir::PatternGoal | Ir::PatternDottedList(_)
      | Ir::PatternList(..) | Ir::PatternTry(..) | Ir::PatternTestPause => {}
    }
  }

  /// Hash-cons a whole value, returning its DAG index.
  fn dedup_value(&mut self, root: &'a FrozenLispKind) -> u32 {
    let mut stack = vec![Frame::Go(root)];
    while let Some(frame) = stack.pop() {
      match frame {
        Frame::Go(k) => {
          let ptr = std::ptr::from_ref(k);
          if let Some(&n) = self.prev.get(&ptr) { self.mark_shared(n); continue }
          match k {
            FrozenLispKind::Undef => { self.prev.insert(ptr, self.undef); }
            &FrozenLispKind::Bool(b) => {
              let n = self.add(Node::Bool(b));
              self.prev.insert(ptr, n);
            }
            &FrozenLispKind::Syntax(s) => {
              let n = self.add(Node::Syntax(s as u32));
              self.prev.insert(ptr, n);
            }
            FrozenLispKind::Number(bi) => {
              let n = self.add(Node::Number(bi.clone()));
              self.prev.insert(ptr, n);
            }
            FrozenLispKind::String(s) => {
              let n = self.add(Node::Str(s.clone()));
              self.prev.insert(ptr, n);
            }
            &FrozenLispKind::Atom(a) => {
              let n = self.dedup_atom(a);
              self.prev.insert(ptr, n);
            }
            &FrozenLispKind::MVar(idx, tgt) => {
              let tgt = self.dedup_mtgt(tgt);
              let n = self.add(Node::MVar(u32::try_from(idx).expect("mvar index too large"), tgt));
              self.prev.insert(ptr, n);
            }
            FrozenLispKind::List(elems) => if elems.is_empty() {
              self.prev.insert(ptr, self.nil);
            } else {
              stack.push(Frame::BuildList { elems, dotted: None, ptr });
              for e in elems { stack.push(Frame::Go(e)) }
            }
            FrozenLispKind::DottedList(elems, r) => {
              stack.push(Frame::BuildList { elems, dotted: Some(r), ptr });
              for e in elems { stack.push(Frame::Go(e)) }
              stack.push(Frame::Go(r));
            }
            FrozenLispKind::Annot(Annot::Span(fsp), val) => {
              let span = self.dedup_fspan(fsp);
              stack.push(Frame::BuildAnnot { span, val, ptr });
              stack.push(Frame::Go(val));
            }
            FrozenLispKind::Goal(val) => {
              stack.push(Frame::BuildGoal { val, ptr });
              stack.push(Frame::Go(val));
            }
            // Reference-identity values (see the module docs) become `Opaque`, re-read at
            // emit time rather than rebuilt from the node. An `Opaque` node is determined
            // by its pointer alone, so the index is available up front and is claimed
            // before the contents; a structural node *is* its children's indices, so
            // `List` and friends must defer to a `Build*` frame that hash-conses once
            // those are known.
            FrozenLispKind::AtomMap(m) => {
              let n = self.add_direct(Node::Opaque(ptr));
              self.prev.insert(ptr, n);
              for (&a, v) in m {
                self.dedup_atom(a);
                stack.push(Frame::Go(v));
              }
            }
            FrozenLispKind::Ref(m) => match m.get_weak() {
              // A strong `ref!`: `Opaque`, traversed like any identity node.
              Some((false, c)) => {
                let n = self.add_direct(Node::Opaque(ptr));
                self.prev.insert(ptr, n);
                stack.push(Frame::Go(c));
              }
              // A live weak reference: record its target but do *not* traverse it, so
              // the weak link alone cannot pull the target into the DAG.
              Some((true, t)) => {
                let target = std::ptr::from_ref(t);
                let n = self.add_direct(Node::Weak(target));
                self.prev.insert(ptr, n);
                self.weak_targets.push(target);
              }
              None => {
                let n = self.add(Node::DeadWeak);
                self.prev.insert(ptr, n);
              }
            }
            FrozenLispKind::Proc(f) => {
              // Safety: `thaw` gives a read-only view.
              match unsafe { f.thaw() } {
                &Proc::Builtin(p) => {
                  let n = self.add(Node::Builtin(p as u32));
                  self.prev.insert(ptr, n);
                }
                Proc::ProofThunk(x, _) => {
                  let n = self.add_direct(Node::Opaque(ptr));
                  self.prev.insert(ptr, n);
                  self.dedup_atom(*x);
                }
                Proc::MergeMap(strat) => {
                  // Safety: the proc is reached through a frozen value.
                  let s = self.dedup_merge(unsafe { freeze_merge_strategy(strat) });
                  let n = self.add(Node::MergeMap(s));
                  self.prev.insert(ptr, n);
                }
                Proc::MatchCont(_) | Proc::RefineCallback => {
                  let n = self.add_direct(Node::Opaque(ptr));
                  self.prev.insert(ptr, n);
                }
                Proc::Lambda { pos, env, spec, code } => {
                  // Opaque, but claim the index first so an env-capture cycle resolves.
                  let n = self.add_direct(Node::Opaque(ptr));
                  self.prev.insert(ptr, n);
                  for v in &**env {
                    // Safety: `freeze` is a read-only cast; the `Rc` is not cloned.
                    self.dedup_value(unsafe { v.freeze() });
                  }
                  if let Some(fsp) = pos.fspan() {
                    let file = self.dedup_fileref(&fsp.file);
                    self.dedup_span(file, fsp.span);
                    if let ProcPos::Named(_, _, a) = pos { self.dedup_atom(*a); }
                    self.dedup_code(code, *spec, file);
                  }
                }
                Proc::Dyn(_) => unreachable!("filtered by `supported`"),
              }
            }
          }
        }
        Frame::BuildList { elems, dotted, ptr } => {
          let mut acc = match dotted {
            Some(r) => self.prev[&kptr(r)],
            None => self.nil,
          };
          for e in elems.iter().rev() {
            let car = self.prev[&kptr(e)];
            acc = self.add(Node::Cons(car, acc));
          }
          self.prev.insert(ptr, acc);
        }
        Frame::BuildAnnot { span, val, ptr } => {
          let v = self.prev[&kptr(val)];
          let n = self.add(Node::Annot(span, v));
          self.prev.insert(ptr, n);
        }
        Frame::BuildGoal { val, ptr } => {
          let v = self.prev[&kptr(val)];
          let n = self.add(Node::Goal(v));
          self.prev.insert(ptr, n);
        }
      }
    }
    self.prev[&std::ptr::from_ref(root)]
  }
}

/// One serialized global definition, as DAG indices into a [`Dedup`].
struct Global {
  name: u32,
  lo: u32,
  hi: u32,
  value: u32,
  span: u32,
  merge: u32,
  doc: u32,
}

/// One declaration's source metadata: what the proof stream does not carry.
struct Decl {
  /// `true` for an `abstract` def.
  abstract_: bool,
  /// The whole declaration's byte range, as a `Span` node.
  full: u32,
  /// The declaration's name, as a `Span` node, in the same file as [`full`](Self::full).
  span: u32,
  /// The doc comment, as a `Str` node, or [`Dedup::undef`].
  doc: u32,
}

/// One entry of the statement trace, in source order.
enum Entry {
  Global(Global),
  Decl(Decl),
}

/// Phase two: walk the [`Dedup`] DAG and write the byte stream.
struct Emitter<'a> {
  de: &'a Dedup<'a>,
  out: Vec<u8>,
  /// The directory of the output file: span file paths are written relative to it (see
  /// [`FileRef::rel`](mm0_util::FileRef::rel)) so the file stays relocatable.
  base: &'a Path,
  /// Heap index of each already-written saved node, for `Ref`.
  emitted: HashMap<u32, u32>,
  /// The next heap index a saving command will claim, mirroring the reader.
  next_heap: u32,
  /// Weak links to complete after every value is written: `(cell heap index, target
  /// node)`. Each becomes a trailing `SetWeak` once its target has a heap slot.
  deferred_weak: Vec<(u32, u32)>,
}

/// A pending step of the phase-two work stack.
enum Emit {
  /// Write this DAG node.
  Node(u32),
  /// Write an `END`.
  End,
  /// Claim the next heap index for this node (a post-order save).
  Save(u32),
}

impl<'a> Emitter<'a> {
  fn new(de: &'a Dedup<'a>, base: &'a Path) -> Self {
    Self {
      de, base,
      out: Vec::new(),
      emitted: HashMap::new(),
      next_heap: 0,
      deferred_weak: Vec::new()
    }
  }

  /// Emit a `(cmd, data)` pair in the shared varint encoding.
  fn cmd(&mut self, cmd: u8, data: u32) {
    if data == 0 {
      self.out.push(cmd);
    } else if let Ok(b) = u8::try_from(data) {
      self.out.push(cmd | 0x40);
      self.out.push(b);
    } else if let Ok(h) = u16::try_from(data) {
      self.out.push(cmd | 0x80);
      self.out.extend_from_slice(&h.to_le_bytes());
    } else {
      self.out.push(cmd | 0xC0);
      self.out.extend_from_slice(&data.to_le_bytes());
    }
  }

  /// A signed LEB128. Numbers outside `i64` range fall back to [`big_sleb`](Self::big_sleb).
  #[allow(clippy::cast_sign_loss)] // `n & 0x7f` is in `0..128`
  fn sleb(&mut self, n: &BigInt) {
    let Some(mut n) = n.to_i64() else { return self.big_sleb(n) };
    loop {
      let b = (n & 0x7f) as u8;
      n >>= 7;
      if (n == 0 && b & 0x40 == 0) || (n == -1 && b & 0x40 != 0) {
        self.out.push(b);
        return
      }
      self.out.push(b | 0x80);
    }
  }

  /// A signed LEB128 of an arbitrary-precision integer, for the rare `Number` outside
  /// `i64` range; the reader's `big_sleb` is the counterpart. Emits the two's-complement
  /// low 7 bits at a time, sign-extending, exactly as [`sleb`](Self::sleb) does.
  fn big_sleb(&mut self, n: &BigInt) {
    let (mut n, mask) = (n.clone(), BigInt::from(0x7f));
    let (zero, neg1) = (BigInt::from(0), BigInt::from(-1));
    loop {
      let b = (&n & &mask).to_u8().expect("low 7 bits fit in a byte");
      n >>= 7u32; // arithmetic shift, so the sign is preserved
      if (n == zero && b & 0x40 == 0) || (n == neg1 && b & 0x40 != 0) {
        self.out.push(b);
        return
      }
      self.out.push(b | 0x80);
    }
  }

  /// An unsigned LEB128.
  fn uleb(&mut self, mut n: u64) {
    loop {
      let b = (n & 0x7f) as u8;
      n >>= 7;
      if n == 0 { self.out.push(b); return }
      self.out.push(b | 0x80);
    }
  }

  /// Emit a string, choosing the `cstr` form unless it is empty or contains a NUL.
  fn emit_str(&mut self, plain: u8, z: u8, s: &[u8]) {
    if s.is_empty() || s.contains(&0) {
      self.cmd(z, u32::try_from(s.len()).expect("string too long"));
      self.out.extend_from_slice(s);
    } else {
      self.cmd(plain, 0);
      self.out.extend_from_slice(s);
      self.out.push(0);
    }
  }

  /// Claim the next heap index for node `i`.
  fn save_heap(&mut self, i: u32) {
    self.emitted.insert(i, self.next_heap);
    self.next_heap += 1;
  }

  fn node(&self, i: u32) -> &Node { &self.de.vec[i as usize].0 }
  fn shared(&self, i: u32) -> bool { self.de.vec[i as usize].1 }

  // Read-only resolvers: recover the arena index of a value translated in phase one,
  // by the same key its `dedup_*` used. These never mutate the arena.
  fn rv(&self, k: &FrozenLispKind) -> u32 { self.de.prev[&std::ptr::from_ref(k)] }
  fn ratom(&self, a: AtomId) -> u32 { self.de.atoms[&a] }
  fn rstr(&self, s: ArcString) -> u32 { self.de.map[&Node::Str(s)] }
  fn rnum(&self, n: &BigInt) -> u32 { self.de.map[&Node::Number(n.clone())] }

  /// Emit an `Ir` span as a `Span` value, built from the enclosing lambda's `file`
  /// (an already-resolved arena index).
  #[allow(clippy::cast_possible_truncation)]
  fn emit_span(&mut self, file: u32, span: Span) {
    let idx = self.de.map[&Node::Span(file, span.start as u32, span.end as u32)];
    self.emit_value(idx);
  }

  /// Emit a `ProcSpec` as a `(at_least, count)` pair.
  fn emit_spec(&mut self, spec: ProcSpec) {
    let (at_least, n) = spec_parts(spec);
    self.out.push(if at_least { spec::AT_LEAST } else { spec::EXACT });
    self.out.push(n);
  }

  /// Emit a lambda's `code` field: a shared `Code` core is written once (with its
  /// spec and body) and `Ref`d thereafter. The body's instructions are re-read from
  /// the live `Arc`, and `file` (the lambda's) supplies every `Ir` span's file.
  fn emit_code(&mut self, file: u32, spec: ProcSpec, code: &Arc<[Ir]>) {
    let (at_least, n) = spec_parts(spec);
    let idx = self.de.map[&Node::Code(at_least, n, Arc::as_ptr(code).cast())];
    if let Some(&h) = self.emitted.get(&idx) { self.cmd(op::REF, h); return }
    self.cmd(op::CODE, 0);
    self.emit_spec(spec);
    for instr in &**code { self.emit_ir(instr, file) }
    self.cmd(op::END, 0); // the `Ir` body terminator
    self.save_heap(idx); // `Code` is saved after its body
  }

  /// Emit one `Ir` instruction: its opcode and non-value operands inline, its value
  /// operands (spans, atoms, constants, ...) re-resolved and written by `read_value`.
  #[allow(clippy::cast_possible_truncation, clippy::too_many_lines)]
  fn emit_ir(&mut self, i: &Ir, file: u32) {
    match i {
      Ir::Undef => self.cmd(ir::UNDEF, 0),
      Ir::Dup => self.cmd(ir::DUP, 0),
      Ir::FocusFinish => self.cmd(ir::FOCUS_FINISH, 0),
      Ir::TestPatternResume => self.cmd(ir::TEST_PATTERN_RESUME, 0),
      Ir::Map => self.cmd(ir::MAP, 0),
      Ir::Have => self.cmd(ir::HAVE, 0),
      Ir::RefineResume => self.cmd(ir::REFINE_RESUME, 0),
      Ir::AddThm => self.cmd(ir::ADD_THM, 0),
      Ir::MergeMap => self.cmd(ir::MERGE_MAP, 0),
      Ir::OnDecls => self.cmd(ir::ON_DECLS, 0),
      Ir::PatternUndef => self.cmd(ir::PATTERN_UNDEF, 0),
      Ir::PatternGoal => self.cmd(ir::PATTERN_GOAL, 0),
      Ir::PatternTestPause => self.cmd(ir::PATTERN_TEST_PAUSE, 0),
      &Ir::Drop(n) => self.cmd(ir::DROP, n as u32),
      &Ir::DropAbove(n) => self.cmd(ir::DROP_ABOVE, n as u32),
      &Ir::AssertScope(n) => self.cmd(ir::ASSERT_SCOPE, n as u32),
      &Ir::EndScope(n) => self.cmd(ir::END_SCOPE, n as u32),
      &Ir::Local(n) => self.cmd(ir::LOCAL, n as u32),
      &Ir::DottedList(n) => self.cmd(ir::DOTTED_LIST, n as u32),
      &Ir::JumpUnless(n) => self.cmd(ir::JUMP_UNLESS, n as u32),
      &Ir::Jump(n) => self.cmd(ir::JUMP, n as u32),
      &Ir::LocalDef(n) => self.cmd(ir::LOCAL_DEF, n as u32),
      &Ir::PatternAtom(n) => self.cmd(ir::PATTERN_ATOM, n as u32),
      &Ir::PatternEqAtom(n) => self.cmd(ir::PATTERN_EQ_ATOM, n as u32),
      &Ir::PatternDottedList(n) => self.cmd(ir::PATTERN_DOTTED_LIST, n as u32),
      &Ir::RefineGoal(b) => self.cmd(ir::REFINE_GOAL, u32::from(b)),
      &Ir::PatternResult(b) => self.cmd(ir::PATTERN_RESULT, u32::from(b)),
      &Ir::PatternBool(b) => self.cmd(ir::PATTERN_BOOL, u32::from(b)),
      &Ir::PatternQuoteAtom(a) => {
        self.cmd(ir::PATTERN_QUOTE_ATOM, 0);
        let x = self.ratom(a);
        self.emit_value(x);
      }
      &Ir::PatternQExprAtom(a) => {
        self.cmd(ir::PATTERN_QEXPR_ATOM, 0);
        let x = self.ratom(a);
        self.emit_value(x);
      }
      Ir::Const(v) => {
        self.cmd(ir::CONST, 0);
        // Safety: `freeze` is a read-only cast.
        let x = self.rv(unsafe { v.freeze() });
        self.emit_value(x);
      }
      Ir::PatternString(s) => {
        self.cmd(ir::PATTERN_STRING, 0);
        let x = self.rstr(s.clone());
        self.emit_value(x);
      }
      Ir::PatternNumber(n) => {
        self.cmd(ir::PATTERN_NUMBER, 0);
        let x = self.rnum(n);
        self.emit_value(x);
      }
      &Ir::AppHead(sp) => {
        self.cmd(ir::APP_HEAD, 0);
        self.emit_span(file, sp);
      }
      &Ir::FocusStart(sp) => {
        self.cmd(ir::FOCUS_START, 0);
        self.emit_span(file, sp);
      }
      &Ir::BranchFail(sp) => {
        self.cmd(ir::BRANCH_FAIL, 0);
        self.emit_span(file, sp);
      }
      &Ir::Global(sp, a) => {
        self.cmd(ir::GLOBAL, 0);
        self.emit_span(file, sp);
        let x = self.ratom(a);
        self.emit_value(x);
      }
      &Ir::SetMergeStrategy(sp, a) => {
        self.cmd(ir::SET_MERGE_STRATEGY, 0);
        self.emit_span(file, sp);
        let x = self.ratom(a);
        self.emit_value(x);
      }
      &Ir::List(sp, n) => {
        self.cmd(ir::LIST, n as u32);
        self.emit_span(file, sp);
      }
      &Ir::GlobalDef(s1, s2, a) => {
        self.cmd(ir::GLOBAL_DEF, 0);
        self.emit_span(file, s1);
        self.emit_span(file, s2);
        let x = self.ratom(a);
        self.emit_value(x);
      }
      Ir::SetDoc(doc, a) => {
        self.cmd(ir::SET_DOC, 0);
        let d = self.rstr(doc.clone().into());
        self.emit_value(d);
        let x = self.ratom(*a);
        self.emit_value(x);
      }
      Ir::App(tail, spans, n) => {
        self.cmd(if *tail { ir::TAIL_APP } else { ir::APP }, *n as u32);
        self.emit_span(file, spans.0);
        self.emit_span(file, spans.1);
      }
      Ir::BuiltinApp(tail, p, spans, n) => {
        self.cmd(if *tail { ir::BUILTIN_TAIL_APP } else { ir::BUILTIN_APP }, *n as u32);
        self.out.push(*p as u8);
        self.emit_span(file, spans.0);
        self.emit_span(file, spans.1);
      }
      &Ir::ArityError(sp, spec) => {
        self.cmd(ir::ARITY_ERROR, 0);
        self.emit_span(file, sp);
        self.emit_spec(spec);
      }
      &Ir::Branch(n, next, cont) => {
        self.cmd(ir::BRANCH, n as u32);
        self.uleb(next as u64);
        self.uleb(cont.map_or(0, |c| c as u64 + 1));
      }
      &Ir::PatternList(n, dot) => {
        self.cmd(ir::PATTERN_LIST, n as u32);
        self.uleb(dot.map_or(0, |d| d as u64 + 1));
      }
      &Ir::PatternTry(ok, err) => {
        self.cmd(ir::PATTERN_TRY, ok as u32);
        self.uleb(err as u64);
      }
      &Ir::PatternMVar(pat) => self.cmd(ir::PATTERN_MVAR, mvar_tag(pat)),
      Ir::Lambda(backref, b) => {
        self.cmd(ir::LAMBDA, u32::from(*backref));
        self.emit_span(file, b.0);
        self.emit_code(file, b.1, &b.2);
      }
    }
  }

  /// Follow a cons chain from `head`, collecting element indices while the tail is
  /// an unshared cons; returns the elements and the dotted tail (`None` if proper).
  fn walk_cons(&self, head: u32) -> (Vec<u32>, Option<u32>) {
    let mut elems = Vec::new();
    let mut cur = head;
    loop {
      let (car, cdr) = match self.node(cur) {
        Node::Cons(a, b) => (*a, *b),
        _ => unreachable!("walk_cons on a non-cons"),
      };
      elems.push(car);
      match self.node(cdr) {
        Node::Nil => return (elems, None),
        Node::Cons(..) if !self.shared(cdr) => cur = cdr,
        _ => return (elems, Some(cdr)),
      }
    }
  }

  /// Emit one value, from an explicit work stack.
  fn emit_value(&mut self, root: u32) {
    let mut stack = vec![Emit::Node(root)];
    while let Some(task) = stack.pop() {
      match task {
        Emit::End => self.cmd(op::END, 0),
        Emit::Save(i) => self.save_heap(i),
        Emit::Node(i) => self.emit_one(i, &mut stack),
      }
    }
  }

  fn emit_one(&mut self, i: u32, stack: &mut Vec<Emit>) {
    // Only a node that took a heap slot (via `save_heap`) is ever `Ref`d. The
    // never-saved leaves — `#undef`, `#t`/`#f`, syntax, builtins, dead weak
    // references, and the standalone empty list — never enter `emitted`, so they
    // always re-emit their one-byte opcode rather than a (never-smaller) `Ref`.
    // `Nil` in a cons tail never reaches here at all; `walk_cons` folds it into the
    // enclosing list.
    if let Some(&h) = self.emitted.get(&i) { self.cmd(op::REF, h); return }
    let shared = self.shared(i);
    match &*self.de.vec[i as usize].0.clone() {
      Node::Undef => self.cmd(op::UNDEF, 0),
      &Node::Bool(b) => self.cmd(if b { op::TRUE } else { op::FALSE }, 0),
      &Node::Syntax(c) => self.cmd(op::SYNTAX, c),
      &Node::Builtin(c) => self.cmd(op::BUILTIN, c),
      Node::Number(n) => {
        // A number has no opcode-level save, so one costs an explicit `Save` byte and a
        // heap slot; that only pays when the number recurs *and* repeating it is dearer
        // than referencing it. A `k`-byte number costs `1 + k` to repeat, a `Ref` at most
        // 5 and usually 2, so the crossover is at three `sleb` bytes.
        let save = shared && is_big(n);
        if save { self.cmd(op::SAVE, 0) }
        self.cmd(op::NUMBER, 0);
        self.sleb(n);
        if save { self.save_heap(i) }
      }
      &Node::Atom(a) => {
        let name = self.de.env.data()[a].name();
        self.emit_str(op::ATOM, op::ATOMZ, name);
        self.save_heap(i); // atoms always save (and so always dedup)
      }
      Node::Str(s) => {
        self.emit_str(op::STRING, op::STRINGZ, s);
        self.save_heap(i);
      }
      Node::FileRef(file) => {
        // Store the path relative to the output file's directory (see the module's
        // callers), falling back to the path as-is when it shares no prefix with `base`.
        let path = &**file.path();
        let rel = pathdiff::diff_paths(path, self.base);
        let rel = rel.as_deref().unwrap_or(path).to_string_lossy();
        self.emit_str(op::STRING, op::STRINGZ, rel.as_bytes());
        self.save_heap(i);
      }
      Node::Nil => { self.cmd(op::LIST, 0); self.cmd(op::END, 0) }
      Node::Cons(..) => {
        let (elems, dotted) = self.walk_cons(i);
        let cmd = match (dotted.is_some(), shared) {
          (false, false) => op::LIST,
          (false, true) => op::LIST_SAVE,
          (true, false) => op::DOTTED_LIST,
          (true, true) => op::DOTTED_LIST_SAVE,
        };
        self.cmd(cmd, 0);
        if shared { stack.push(Emit::Save(i)) }
        stack.push(Emit::End);
        if let Some(t) = dotted { stack.push(Emit::Node(t)) }
        for &e in elems.iter().rev() { stack.push(Emit::Node(e)) }
      }
      &Node::Span(file, lo, hi) => {
        self.cmd(op::SPAN, 0);
        self.out.extend_from_slice(&lo.to_le_bytes());
        self.out.extend_from_slice(&hi.to_le_bytes());
        stack.push(Emit::Save(i)); // the span saves after its file value
        stack.push(Emit::Node(file));
      }
      &Node::Annot(span, val) => {
        if shared { self.cmd(op::SAVE, 0) }
        self.cmd(op::ANNOT, 0);
        if shared { stack.push(Emit::Save(i)) }
        stack.push(Emit::Node(val));
        stack.push(Emit::Node(span));
      }
      Node::MVar(idx, tgt) => {
        self.cmd(op::MVAR, *idx);
        match *tgt {
          MTgt::Unknown => self.out.push(infer::UNKNOWN),
          MTgt::Provable => self.out.push(infer::PROVABLE),
          MTgt::Bound(s) => { self.out.push(infer::BOUND); stack.push(Emit::Node(s)) }
          MTgt::Reg(s) => { self.out.push(infer::REG); stack.push(Emit::Node(s)) }
        }
      }
      &Node::Goal(val) => {
        if shared { self.cmd(op::SAVE, 0) }
        self.cmd(op::GOAL, 0);
        if shared { stack.push(Emit::Save(i)) }
        stack.push(Emit::Node(val));
      }
      &Node::MergeMap(sub) => {
        if shared { self.cmd(op::SAVE, 0) }
        self.cmd(op::CUSTOM_PROC, u32::from(custom::MERGE_MAP));
        if shared { stack.push(Emit::Save(i)) }
        stack.push(Emit::Node(sub));
      }
      // A weak reference is dead unless a strong path serialized its target. If it
      // did, write the cell as a `(ref! #undef)` installed pre-order — this is where
      // the enclosing cycle breaks — and record a `SetWeak` to fill it once the
      // target has been written (see `serialize`).
      &Node::Weak(target) => if let Some(&t) = self.de.prev.get(&target) {
        self.cmd(op::NEW_REF, 0);
        self.save_heap(i);
        self.cmd(op::UNDEF, 0);
        self.deferred_weak.push((self.emitted[&i], t));
      } else {
        self.cmd(op::DEAD_WEAK, 0)
      },
      Node::DeadWeak => self.cmd(op::DEAD_WEAK, 0),
      // A `Code` core is never a stack task: its enclosing lambda emits it (with the
      // file context needed for its `Ir` spans) via `emit_code_field`.
      Node::Code(..) => unreachable!("`Code` is emitted by its enclosing lambda"),
      // Safety: `ptr` was taken from a value borrowed from `env`, which outlives the
      // whole serialization; nothing is mutated in between.
      &Node::Opaque(ptr) => match unsafe { &*ptr } {
        FrozenLispKind::AtomMap(m) => {
          if shared { self.cmd(op::SAVE, 0) }
          self.cmd(op::MAP, 0);
          if shared { stack.push(Emit::Save(i)) }
          stack.push(Emit::End);
          // `HashMap` iteration order is nondeterministic;
          // sort by atom id so the file is reproducible.
          let mut pairs = m.iter().map(|(&a, v)| (a, v)).collect::<Vec<_>>();
          pairs.sort_unstable_by_key(|&(a, _)| a);
          for (a, v) in pairs {
            stack.push(Emit::Node(self.de.prev[&kptr(v)]));
            stack.push(Emit::Node(self.de.atoms[&a]));
          }
        }
        FrozenLispKind::Ref(m) => {
          // Claim the cell before its contents so a back-edge can `Ref` it.
          self.cmd(op::NEW_REF, 0);
          self.save_heap(i);
          let c = m.get().expect("a dead weak reference is a `DeadWeak` node, not `Opaque`");
          stack.push(Emit::Node(self.de.prev[&std::ptr::from_ref(c)]));
        }
        FrozenLispKind::Proc(f) => {
          // A closure or custom proc is saved when shared, post-order like an
          // `atom-map`: a cycle through it always closes at a `ref!` (`NewRef` or the
          // `SetWeak` cell), not at the proc, so it is only ever reached forward.
          if shared {
            self.cmd(op::SAVE, 0);
            stack.push(Emit::Save(i));
          }
          // Safety: `thaw` gives a read-only view.
          match unsafe { f.thaw() } {
            Proc::MatchCont(_) => self.cmd(op::CUSTOM_PROC, u32::from(custom::MATCH_CONT)),
            Proc::RefineCallback => self.cmd(op::CUSTOM_PROC, u32::from(custom::REFINE_CALLBACK)),
            Proc::ProofThunk(x, _) => {
              self.cmd(op::CUSTOM_PROC, u32::from(custom::PROOF_THUNK));
              stack.push(Emit::Node(self.de.atoms[x]));
            }
            Proc::Lambda { pos, env, spec, code } => {
              let named = matches!(pos, ProcPos::Named(..));
              self.cmd(op::LAMBDA, if named { LAMBDA_NAMED } else { 0 });
              for v in &**env {
                // Safety: `freeze` is a read-only cast.
                let idx = self.rv(unsafe { v.freeze() });
                self.emit_value(idx);
              }
              self.cmd(op::END, 0); // ends the captured environment list
              let fsp = pos.fspan().expect("a lambda has a file span");
              let file = self.de.file_ptr[&fsp.file.ptr()];
              self.emit_span(file, fsp.span);
              if let ProcPos::Named(_, nsp, a) = pos {
                #[allow(clippy::cast_possible_truncation)]
                let (lo, hi) = (nsp.start as u32, nsp.end as u32);
                self.out.extend_from_slice(&lo.to_le_bytes());
                self.out.extend_from_slice(&hi.to_le_bytes());
                let x = self.ratom(*a);
                self.emit_value(x);
              }
              self.emit_code(file, *spec, code);
            }
            // `MergeMap` is a `Node::MergeMap`, `Builtin` a `Node::Builtin`.
            Proc::MergeMap(_) | Proc::Builtin(_) | Proc::Dyn(_) =>
              unreachable!("not an opaque procedure"),
          }
        }
        _ => unreachable!("opaque node over a non-identity value"),
      }
    }
  }

  fn emit_spans(&mut self, de: &Dedup<'_>, entries: &[Entry]) {
    let Some((&Entry::Decl(Decl { full, span, .. }), rest)) = entries.split_first()
    else { unreachable!() };
    self.cmd(op::SPANS, u32::try_from(rest.len()).expect("run too long"));
    self.emit_value(full);
    self.emit_value(span);
    let Node::Span(_, _, mut cur) = *de.vec[full as usize].0 else { unreachable!() };
    for entry in rest {
      let Entry::Decl(Decl { full, span, .. }) = *entry else { unreachable!() };
      let Node::Span(_, full_lo, full_hi) = *de.vec[full as usize].0 else { unreachable!() };
      let Node::Span(_, span_lo, span_hi) = *de.vec[span as usize].0 else { unreachable!() };
      for p in [full_lo, span_lo, span_hi, full_hi] { self.uleb(u64::from(p - cur)); cur = p }
    }
  }
}

/// The name of the first global the exporter cannot encode, if any.
///
/// [`serialize`] omits such globals with a warning, which is fine for a debugging index
/// but not for a build cache: a dependent loading the file would silently be missing
/// definitions. `--cache` checks this first and declines to build the file at all.
#[must_use]
pub fn first_unsupported(env: &FrozenEnv) -> Option<ArcString> {
  for (_, adata) in env.data().enum_iter() {
    if let Some(data) = adata.lisp() {
      if !supported(data) { return Some(adata.name().clone()) }
    }
  }
  None
}

/// Serialize an environment's global lisp definitions to a value stream.
///
/// Span file paths are written relative to `base`, the output file's directory. Globals
/// whose value the exporter cannot yet encode (containing a `Dyn` procedure) are skipped
/// and reported via `report` — see [`first_unsupported`].
#[must_use]
pub fn serialize(env: &FrozenEnv, base: &Path, mut report: impl FnMut(&str)) -> Vec<u8> {
  let mut de = Dedup::new(env);
  let mut entries = Vec::new();

  // Walk the statement trace, not the atom table: its order *is* what the table records,
  // and it is the order the proof stream was written in, so a reader stepping the two
  // together knows which declaration each `Decl` entry describes.
  for stmt in env.stmts() {
    let (span, full, doc, abstract_) = match *stmt {
      StmtTrace::Sort(a) => {
        let sd = env.sort(env.data()[a].sort().expect("a Sort trace entry names a sort"));
        (&sd.span, sd.full, &sd.doc, false)
      }
      StmtTrace::Decl(a) => match env.data()[a].decl().expect("a Decl trace entry names a decl") {
        DeclKey::Term(t) => {
          let td = env.term(t);
          (&td.span, td.full, &td.doc, td.vis.contains(Modifiers::ABSTRACT))
        }
        DeclKey::Thm(t) => {
          let td = env.thm(t);
          (&td.span, td.full, &td.doc, false)
        }
      },
      StmtTrace::Global(a) => {
        let adata = &env.data()[a];
        let Some(data) = adata.lisp() else { continue };
        if !supported(data) {
          report(&format!("global '{}' cannot yet be serialized and was omitted", adata.name()));
          continue
        }
        let name = de.dedup_atom(a);
        let value = de.dedup_value(data);
        #[allow(clippy::cast_possible_truncation)]
        let (lo, hi, span) = match data.src() {
          Some((fsp, sp)) => (sp.start as u32, sp.end as u32, de.dedup_fspan(fsp)),
          None => (0, 0, de.undef),
        };
        let merge = de.dedup_merge(data.merge());
        let doc = match data.doc() {
          Some(d) => de.dedup_str(d.as_bytes()),
          None => de.undef,
        };
        entries.push(Entry::Global(Global { name, lo, hi, value, span, merge, doc }));
        continue
      }
      // Verifier-relevant, so it belongs in the proof stream rather than here; the
      // proof stream has no command for it, so it is dropped (see `mmb-lisp.md`).
      StmtTrace::OutputString(_) => continue,
    };
    let file = de.dedup_fileref(&span.file);
    let name = span.span;
    let span = de.dedup_span(file, name);
    let doc = match doc {
      Some(d) => de.dedup_str(d.as_bytes()),
      None => de.undef,
    };
    let full = de.dedup_span(file, full);
    entries.push(Entry::Decl(Decl { abstract_, full, span, doc }));
  }

  // A weak reference's target is only in the DAG if a strong path reached it; mark
  // those shared so they are saved and a `SetWeak` can `Ref` them.
  for t in &de.weak_targets {
    if let Some(&d) = de.prev.get(t) { de.vec[d as usize].1 = true }
  }

  let mut em = Emitter::new(&de, base);
  let mut run = None;
  for (i, entry) in entries.iter().enumerate() {
    if let Entry::Decl(Decl { abstract_: false, doc, full, span }) = *entry {
      if doc == de.undef {
        let Node::Span(f1, full_lo, full_hi) = *de.vec[full as usize].0 else { unreachable!() };
        let Node::Span(f2, span_lo, span_hi) = *de.vec[span as usize].0 else { unreachable!() };
        assert!(f1 == f2 && span_lo <= span_hi);
        let Some((j, file, hi)) = run else { run = Some((i, f1, full_hi)); continue };
        if file == f1 && hi <= full_lo && full_lo <= span_lo && span_hi <= full_hi {
          run = Some((j, file, full_hi))
        } else {
          em.emit_spans(&de, &entries[j..i]);
          run = Some((i, f1, full_hi))
        }
        continue
      }
    }
    if let Some((j, _, _)) = run.take() { em.emit_spans(&de, &entries[j..i]) }
    match entry {
      Entry::Global(g) => {
        em.emit_value(g.name);
        em.out.extend_from_slice(&g.lo.to_le_bytes());
        em.out.extend_from_slice(&g.hi.to_le_bytes());
        em.emit_value(g.value);
        em.emit_value(g.span);
        em.emit_value(g.merge);
        em.emit_value(g.doc);
      }
      Entry::Decl(d) => {
        em.cmd(op::DECL, u32::from(d.abstract_));
        em.emit_value(d.full);
        em.emit_value(d.span);
        em.emit_value(d.doc);
      }
    }
  }
  if let Some((j, _, _)) = run { em.emit_spans(&de, &entries[j..]) }

  // Every target is now written, so close the weak links: fill each cell with a weak
  // reference to its (already-emitted) target.
  for (cell, target) in std::mem::take(&mut em.deferred_weak) {
    em.cmd(op::SET_WEAK, cell);
    em.emit_value(target);
  }
  em.cmd(op::END, 0);
  em.out
}

/// A work item for [`supported`]: a value to check, or a lambda body to scan for
/// embedded values.
enum Chk<'a> {
  Val(&'a FrozenLispKind),
  Code(&'a Arc<[Ir]>),
}

/// Whether the exporter can currently encode `root` (and everything it reaches).
/// Only `Dyn` procedures are unsupported. Iterative, so a deep value cannot
/// overflow the stack.
fn supported(root: &FrozenLispKind) -> bool {
  let mut stack = vec![Chk::Val(root)];
  // Values (and lambda bodies) form cycles through `ref!` cells and captured
  // environments, so memoize by pointer or this traversal would not terminate.
  let mut seen_val: HashSet<*const FrozenLispKind> = HashSet::new();
  let mut seen_code: HashSet<*const [Ir]> = HashSet::new();
  while let Some(item) = stack.pop() {
    match item {
      Chk::Val(k) if !seen_val.insert(std::ptr::from_ref(k)) => {}
      Chk::Code(code) if !seen_code.insert(Arc::as_ptr(code)) => {}
      Chk::Val(k) => match k {
        FrozenLispKind::Undef
        | FrozenLispKind::Bool(_)
        | FrozenLispKind::Number(_)
        | FrozenLispKind::String(_)
        | FrozenLispKind::Atom(_)
        | FrozenLispKind::Syntax(_)
        | FrozenLispKind::MVar(..) => {}
        FrozenLispKind::List(es) => stack.extend(es.iter().map(|e| Chk::Val(e))),
        FrozenLispKind::DottedList(es, r) => {
          stack.extend(es.iter().map(|e| Chk::Val(e)));
          stack.push(Chk::Val(r));
        }
        FrozenLispKind::AtomMap(m) => stack.extend(m.values().map(|v| Chk::Val(v))),
        FrozenLispKind::Annot(_, v) | FrozenLispKind::Goal(v) => stack.push(Chk::Val(v)),
        FrozenLispKind::Ref(m) => if let Some(t) = m.get() { stack.push(Chk::Val(t)) },
        // Safety: `thaw` gives a read-only view; `freeze` is a read-only cast.
        FrozenLispKind::Proc(f) => match unsafe { f.thaw() } {
          Proc::Dyn(_) => return false,
          Proc::Lambda { env, code, .. } => {
            for v in &**env {
              // Safety: `freeze` is a read-only cast.
              stack.push(Chk::Val(unsafe { v.freeze() }));
            }
            stack.push(Chk::Code(code));
          }
          _ => {}
        },
      },
      Chk::Code(code) => for i in code.iter() {
        match i {
          // Safety: `freeze` is a read-only cast.
          Ir::Const(v) => stack.push(Chk::Val(unsafe { v.freeze() })),
          Ir::Lambda(_, b) => stack.push(Chk::Code(&b.2)),
          _ => {}
        }
      }
    }
  }
  true
}
