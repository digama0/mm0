//! MMU importer, which produces an [`Environment`] object from an `.mmu` file.
use std::rc::Rc;
use std::collections::{HashMap, hash_map::Entry};
use crate::{Term, Thm, TermKind, ThmKind,
  AtomId, SortId, Environment, Modifiers, Type, Expr, Proof,
  MAX_BOUND_VARS, Span, BoxError, FileRef, FileSpan};
use crate::elab::{ElabError, Result,
  proof::{IDedup, NodeHash, ExprHash, ProofKind, ProofHash, build}};
use mm1_parser::{whitespace, lisp_ident};

/// The importer, which reads the input `.mmu` file and builds an [`Environment`].
#[derive(Debug)]
pub struct Importer<'a> {
  /// The input file name
  file: &'a FileRef,
  /// The input source text (as a byte slice)
  source: &'a [u8],
  /// The position in the input
  idx: usize,
  /// The environment under construction
  env: Environment,
}

fn span(source: &[u8], s: Span) -> &[u8] { &source[s.start..s.end] }

impl<'a> Importer<'a> {
  fn cur(&self) -> u8 { self.source[self.idx] }
  fn cur_opt(&self) -> Option<u8> { self.source.get(self.idx).copied() }

  fn span(&self, s: Span) -> &'a [u8] { span(self.source, s) }

  fn fspan(&self, s: Span) -> FileSpan {
    FileSpan {file: self.file.clone(), span: s}
  }

  fn ws(&mut self) {
    while self.idx < self.source.len() {
      let c = self.cur();
      if whitespace(c) {self.idx += 1; continue}
      if c == b'-' && self.source.get(self.idx + 1) == Some(&b'-') {
        self.idx += 1;
        while self.idx < self.source.len() {
          let c = self.cur();
          self.idx += 1;
          if c == b'\n' {break}
        }
      } else {break}
    }
  }

  fn ident(&mut self) -> Option<Span> {
    let start = self.idx;
    while self.idx < self.source.len() {
      let c = self.cur();
      if !lisp_ident(c) {break}
      self.idx += 1;
    }
    if self.idx == start {return None}
    (Some((start..self.idx).into()), self.ws()).0
  }

  fn ident_str(&mut self) -> Option<&[u8]> { self.ident().map(|sp| self.span(sp)) }
  fn ident_atom(&mut self) -> Option<AtomId> {
    self.ident().map(|s| self.env.get_atom(span(self.source, s)))
  }
  fn ident_err(&mut self) -> Result<Span> {
    self.ident().ok_or_else(|| self.err("expecting identifier".into()))
  }
  fn ident_atom_err(&mut self) -> Result<AtomId> {
    self.ident_atom().ok_or_else(|| self.err("expecting identifier".into()))
  }

  fn chr(&mut self, c: u8) -> Option<usize> {
    if self.cur_opt()? != c {return None}
    self.idx += 1;
    (Some(self.idx), self.ws()).0
  }

  fn err(&self, msg: BoxError) -> ElabError {
    ElabError::new_e(self.idx..self.idx, msg)
  }

  fn chr_err(&mut self, c: u8) -> Result<usize> {
    self.chr(c).ok_or_else(|| ElabError::new_e(self.idx..=self.idx,
      format!("expecting '{}'", c as char)))
  }

  fn open(&mut self) -> Option<usize> { self.chr(b'(') }
  fn close(&mut self) -> Option<usize> { self.chr(b')').map(|n| n+1) }
  fn open_err(&mut self) -> Result<usize> { self.chr_err(b'(') }
  fn close_err(&mut self) -> Result<usize> { self.chr_err(b')').map(|n| n+1) }

  fn deps(&mut self, bvs: &HashMap<AtomId, u64>) -> Result<u64> {
    self.open_err()?;
    let mut deps = 0;
    while self.close().is_none() {
      let z = self.ident_atom_err()?;
      deps |= bvs.get(&z).ok_or_else(|| self.err("expecting bound variable".into()))?;
    }
    Ok(deps)
  }

  fn dummies(&mut self, vars: &mut HashMap<AtomId, VarKind>) -> Result<()> {
    self.open_err()?;
    while self.close().is_none() {
      self.open_err()?;
      let xsp = self.ident_err()?;
      let x = self.env.get_atom(self.span(xsp));
      let s = self.ident_atom_err()?;
      let s = self.env.data[s].sort.ok_or_else(|| self.err("expecting sort".into()))?;
      if vars.insert(x, VarKind::Dummy(s)).is_some() {
        return Err(ElabError::new_e(xsp, "duplicate variable"))
      }
      self.close_err()?;
    }
    Ok(())
  }
}

#[allow(variant_size_differences)]
enum VarKind {
  Var(usize),
  Dummy(SortId),
}

#[derive(Clone, Copy)]
enum DeclKind {
  Term,
  Def,
  LocalDef,
  Axiom,
  Theorem,
  LocalTheorem,
}

#[derive(Debug)]
struct Dedup<H: NodeHash> {
  map: HashMap<Rc<H>, usize>,
  vec: Vec<(Rc<H>, bool)>,
}

impl<H: NodeHash> Dedup<H> {
  fn new(args: &[(Option<AtomId>, Type)]) -> Dedup<H> {
    let vec: Vec<_> = (0..args.len())
      .map(|i| (Rc::new(H::REF(ProofKind::Expr, i)), true)).collect();
    Dedup {
      map: vec.iter().enumerate().map(|(i, r)| (r.0.clone(), i)).collect(),
      vec,
    }
  }

  fn add(&mut self, v: H) -> usize {
    match self.map.entry(Rc::new(v)) {
      Entry::Vacant(e) => {
        let n = self.vec.len();
        self.vec.push((e.key().clone(), false));
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

  fn map_inj<T: NodeHash>(&self, mut f: impl FnMut(&H) -> T) -> Dedup<T> {
    let mut d = Dedup {
      map: HashMap::new(),
      vec: Vec::with_capacity(self.vec.len()),
    };
    for (i, &(ref h, b)) in self.vec.iter().enumerate() {
      let t = Rc::new(f(h));
      d.map.insert(t.clone(), i);
      d.vec.push((t, b));
    }
    d
  }
}

impl<H: NodeHash> std::ops::Index<usize> for Dedup<H> {
  type Output = H;
  fn index(&self, n: usize) -> &H { &self.vec[n].0 }
}

impl<H: NodeHash> IDedup<H> for Dedup<H> {
  fn add_direct(&mut self, v: H) -> usize { self.add(v) }

  fn reuse(&mut self, n: usize) -> usize {
    self.vec[n].1 = true;
    n
  }
}

#[must_use] #[derive(Debug)]
struct DedupIter<'a, H: NodeHash>(std::slice::Iter<'a, (Rc<H>, bool)>);

impl<'a, H: NodeHash> Iterator for DedupIter<'a, H> {
  type Item = (&'a H, bool);
  fn next(&mut self) -> Option<(&'a H, bool)> {
    self.0.next().map(|&(ref e, b)| (&**e, b))
  }
}

impl<'a, H: NodeHash> ExactSizeIterator for DedupIter<'a, H> {
  fn len(&self) -> usize { self.0.len() }
}

impl<'a, H: NodeHash> IntoIterator for &'a Dedup<H> {
  type Item = (&'a H, bool);
  type IntoIter = DedupIter<'a, H>;
  fn into_iter(self) -> DedupIter<'a, H> { DedupIter(self.vec.iter()) }
}

impl Dedup<ExprHash> {
  fn map_proof(&self) -> Dedup<ProofHash> {
    self.map_inj(ExprHash::to_proof)
  }
}

impl<'a> Importer<'a> {
  fn run(&mut self) -> Result<()> {
    self.ws();
    while let Some(start) = self.open() {
      match self.ident_str() {
        Some(b"sort") => {
          let x = self.ident_err()?;
          let mut next = self.ident_str();
          let mut mods = Modifiers::empty();
          if next == Some(b"pure") {next = self.ident_str(); mods |= Modifiers::PURE;}
          if next == Some(b"strict") {next = self.ident_str(); mods |= Modifiers::STRICT;}
          if next == Some(b"provable") {next = self.ident_str(); mods |= Modifiers::PROVABLE;}
          if next == Some(b"free") {mods |= Modifiers::FREE;}
          let end = self.close_err()?;
          let a = self.env.get_atom(self.span(x));
          self.env.add_sort(a, self.fspan(x), (start..end).into(), mods, None)
            .map_err(|e| e.into_elab_error(x))?;
        }
        Some(b"term") => self.decl(start, DeclKind::Term)?,
        Some(b"axiom") => self.decl(start, DeclKind::Axiom)?,
        Some(b"def") => self.decl(start, DeclKind::Def)?,
        Some(b"theorem") => self.decl(start, DeclKind::Theorem)?,
        Some(b"local") => match self.ident_str() {
          Some(b"def") => self.decl(start, DeclKind::LocalDef)?,
          Some(b"theorem") => self.decl(start, DeclKind::LocalTheorem)?,
          _ => return Err(self.err("expecting 'def' or 'theorem'".into()))
        }
        _ => return Err(self.err("expecting command keyword".into()))
      }
    }
    if self.idx != self.source.len() {
      return Err(self.err("expected '(' or EOF".into()))
    }
    Ok(())
  }

  fn decl(&mut self, start: usize, dk: DeclKind) -> Result<()> {
    let span = self.ident_err()?;
    let atom = self.env.get_atom(self.span(span));
    self.open_err()?;
    let mut args = vec![];
    let mut vars = HashMap::new();
    let mut bvs = HashMap::new();
    let mut next_bv = 1;
    while self.close().is_none() {
      self.open_err()?;
      let ysp = self.ident_err()?;
      let y = self.env.get_atom(self.span(ysp));
      let oy = if y == AtomId::UNDER {None} else {
        vars.insert(y, VarKind::Var(args.len()));
        Some(y)
      };
      let s = self.ident_atom().and_then(|s| self.env.data[s].sort)
        .ok_or_else(|| self.err("expecting sort".into()))?;
      if self.close().is_some() {
        if next_bv >= 1 << MAX_BOUND_VARS {
          return Err(ElabError::new_e(ysp,
            format!("too many bound variables (max {})", MAX_BOUND_VARS)))
        }
        if y != AtomId::UNDER {bvs.insert(y, next_bv);}
        next_bv *= 2;
        args.push((oy, Type::Bound(s)))
      } else {
        let deps = self.deps(&bvs)?;
        args.push((oy, Type::Reg(s, deps)));
        self.close_err()?;
      }
    }
    match dk {
      DeclKind::Term | DeclKind::Def | DeclKind::LocalDef => {
        self.open_err()?;
        let ret = self.ident_atom_err()?;
        let ret = self.env.data[ret].sort
          .ok_or_else(|| self.err("expecting sort".into()))?;
        let deps = self.deps(&bvs)?;
        self.close_err()?;
        let kind = if let DeclKind::Term = dk {
          TermKind::Term
        } else {
          self.dummies(&mut vars)?;
          let mut de = Dedup::new(&args);
          let i = self.expr(&mut de, &vars)?;
          let (mut ids, heap, mut store) = build(&de);
          store.push(ids[i].take());
          TermKind::Def(Some(Expr {heap, store: store.into()}))
        };
        let end = self.close_err()?;
        self.env.add_term(Term {
          atom,
          span: self.fspan(span),
          vis: if let DeclKind::LocalDef = dk {Modifiers::LOCAL} else {Modifiers::empty()},
          full: (start..end).into(),
          doc: None,
          args: args.into(),
          ret: (ret, deps),
          kind,
        }).map_err(|e| e.into_elab_error(span))?;
      }
      DeclKind::Axiom | DeclKind::Theorem | DeclKind::LocalTheorem => {
        let mut de = Dedup::new(&args);
        self.open_err()?;
        let mut is = vec![];
        while self.close().is_none() {
          if let DeclKind::Axiom = dk {
            is.push((None, self.expr(&mut de, &vars)?))
          } else {
            self.open_err()?;
            let h = self.ident_atom_err()?;
            let oh = if h == AtomId::UNDER {None} else {Some(h)};
            let i = self.expr(&mut de, &vars)?;
            self.close_err()?;
            is.push((oh, i))
          }
        }
        let ir = self.expr(&mut de, &vars)?;
        let (mut ids, heap, store) = build(&de);
        let hyps = is.iter().map(|&(a, i)| (a, ids[i].take())).collect();
        let ret = ids[ir].take();
        let kind = if let DeclKind::Axiom = dk {
          ThmKind::Axiom
        } else {
          self.dummies(&mut vars)?;
          let mut de = de.map_proof();
          let mut is2 = Vec::new();
          let mut proofs = HashMap::new();
          for (i, &(a, e)) in is.iter().enumerate() {
            if let Some(a) = a {
              let n = de.add(ProofHash::Hyp(i, e));
              is2.push(n);
              proofs.insert(a, n);
            }
          }
          let ip = self.proof(&mut de, &vars, &mut proofs, ProofKind::Proof)?;
          let (mut ids, heap, mut store) = build(&de);
          let hyps = is2.into_iter().map(|i| ids[i].take()).collect();
          store.push(ids[ip].take());
          ThmKind::Thm(Some(Proof {heap, hyps, store: store.into()}))
        };
        let end = self.close_err()?;
        self.env.add_thm(Thm {
          atom,
          span: self.fspan(span),
          vis: if let DeclKind::Theorem = dk {Modifiers::PUB} else {Modifiers::empty()},
          full: (start..end).into(),
          doc: None,
          args: args.into(), heap, store: store.into(), hyps, ret, kind
        }).map_err(|e| e.into_elab_error(span))?;
      }
    }
    Ok(())
  }

  fn expr(&mut self, de: &mut Dedup<ExprHash>, vars: &HashMap<AtomId, VarKind>) -> Result<usize> {
    #[allow(clippy::branches_sharing_code)]
    let e = if self.open().is_some() {
      let t = self.ident_atom_err()?;
      let t = self.env.term(t).ok_or_else(|| self.err("expecting term".into()))?;
      let mut args = vec![];
      while self.close().is_none() {args.push(self.expr(de, vars)?)}
      ExprHash::App(t, args.into_boxed_slice())
    } else {
      let a = self.ident_atom_err()?;
      match *vars.get(&a).ok_or_else(|| self.err("unknown variable".into()))? {
        VarKind::Var(i) => ExprHash::Ref(ProofKind::Expr, i),
        VarKind::Dummy(s) => ExprHash::Dummy(a, s),
      }
    };
    Ok(de.add(e))
  }

  fn conv(&mut self, de: &mut Dedup<ProofHash>,
    vars: &HashMap<AtomId, VarKind>,
    proofs: &mut HashMap<AtomId, usize>,
  ) -> Result<usize> {
    self.proof(de, vars, proofs, ProofKind::Conv).map(|i| ProofHash::as_conv(de, i))
  }

  fn proof(&mut self, de: &mut Dedup<ProofHash>,
    vars: &HashMap<AtomId, VarKind>,
    proofs: &mut HashMap<AtomId, usize>,
    ty: ProofKind
  ) -> Result<usize> {
    let e = if self.open().is_some() {
      match self.ident_atom_err()? {
        AtomId::CONV => {
          if ty != ProofKind::Proof {
            return Err(self.err(":conv in invalid position".into()))
          }
          (ProofHash::Conv(
            self.proof(de, vars, proofs, ProofKind::Expr)?,
            self.conv(de, vars, proofs)?,
            self.proof(de, vars, proofs, ProofKind::Proof)?),
          self.close_err()?).0
        }
        AtomId::SYM => {
          if ty != ProofKind::Conv {
            return Err(self.err(":sym in invalid position".into()))
          }
          (ProofHash::Sym(self.conv(de, vars, proofs)?), self.close_err()?).0
        }
        AtomId::UNFOLD => {
          if ty != ProofKind::Conv {
            return Err(self.err(":unfold in invalid position".into()))
          }
          let t = self.ident_atom_err()?;
          let tid = self.env.term(t).ok_or_else(|| self.err("expecting term".into()))?;
          self.open_err()?;
          let mut ns = vec![];
          while self.close().is_none() {ns.push(self.proof(de, vars, proofs, ProofKind::Expr)?)}
          self.open_err()?;
          while self.close().is_none() {self.ident_err()?;} // ignore dummies
          let c = self.conv(de, vars, proofs)?;
          self.close_err()?;
          let lhs = de.add(ProofHash::Term(tid, ns.clone().into()));
          let l2 = ProofHash::conv_side(de, c, false);
          ProofHash::Unfold(tid, ns.into(), lhs, l2, c)
        }
        AtomId::LET => {
          if ty != ProofKind::Proof {
            return Err(self.err(":let in invalid position".into()))
          }
          let h = self.ident_atom_err()?;
          let p1 = self.proof(de, vars, proofs, ProofKind::Proof)?;
          let old = proofs.insert(h, p1);
          let p2 = self.proof(de, vars, proofs, ProofKind::Proof)?;
          self.close_err()?;
          if let Some(i) = old {proofs.insert(h, i);} else {proofs.remove(&h);}
          return Ok(p2)
        }
        t => if ty == ProofKind::Proof {
          let t = self.env.thm(t).ok_or_else(|| self.err("expecting theorem".into()))?;
          self.open_err()?;
          let td = &self.env.thms[t];
          let nargs = td.args.len();
          let mut heap = vec![None; td.heap.len()];
          let mut ns = Vec::with_capacity(nargs);
          while self.close().is_none() {ns.push(self.proof(de, vars, proofs, ProofKind::Expr)?)}
          if ns.len() != nargs {
            return Err(self.err("incorrect number of term arguments".into()))
          }
          for (i, &n) in ns.iter().enumerate() { heap[i] = Some(n) }
          while self.close().is_none() {ns.push(self.proof(de, vars, proofs, ProofKind::Proof)?)}
          let td = &self.env.thms[t];
          let rhs = ProofHash::subst(&self.env, de, &td.heap, &mut heap, &td.store, &td.ret);
          ProofHash::Thm(t, ns.into(), rhs)
        } else {
          let tid = self.env.term(t).ok_or_else(|| self.err("expecting term".into()))?;
          let mut ns = vec![];
          while self.close().is_none() {ns.push(self.proof(de, vars, proofs, ty)?)}
          if ns.iter().any(|&i| ProofHash::is_conv(de, i)) {
            for i in &mut ns {*i = ProofHash::as_conv(de, *i)}
            ProofHash::Cong(tid, ns.into())
          } else {
            ProofHash::Term(tid, ns.into())
          }
        }
      }
    } else {
      let a = self.ident_atom_err()?;
      if ty == ProofKind::Proof {
        return Ok(de.reuse(*proofs.get(&a).ok_or_else(|| self.err("unknown subproof".into()))?))
      }
      match *vars.get(&a).ok_or_else(|| self.err("unknown variable".into()))? {
        VarKind::Var(i) => ProofHash::Ref(ProofKind::Expr, i),
        VarKind::Dummy(s) => ProofHash::Dummy(a, s),
      }
    };
    Ok(de.add(e))
  }
}

/// Construct an [`Environment`] from an `mmu` file.
pub fn elab(file: &FileRef, source: &[u8]) -> (Result<()>, Environment) {
  let mut p = Importer { file, source, idx: 0, env: Environment::new() };
  (p.run(), p.env)
}
