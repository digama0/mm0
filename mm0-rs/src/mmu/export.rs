//! MMU exporter, which produces `.mmu` ASCII proof files from an
//! [`Environment`](crate::Environment) object.
use std::collections::HashMap;
use std::io::{self, Write};
use std::mem;
use crate::{Type, AtomId, SortId, TermKind, ThmKind,
  ExprNode, ProofNode, StmtTrace, DeclKey, Modifiers, FrozenEnv};

fn list<A, W: Write>(w: &mut W, mut es: impl Iterator<Item=A>,
    mut f: impl FnMut(&mut W, A) -> io::Result<()>) -> io::Result<()> {
  match es.next() {
    None => write!(w, "()"),
    Some(x) => {
      write!(w, "(")?;
      f(w, x)?;
      for e in es {write!(w, " ")?; f(w, e)?}
      write!(w, ")")
    }
  }
}

fn is_nonatomic_proof(e: &ProofNode) -> bool {
  matches!(e, ProofNode::Thm {..} | ProofNode::Conv(_))
}

#[allow(clippy::too_many_arguments)]
fn build_unfold_map<'a>(env: &FrozenEnv,
  m: &mut HashMap<AtomId, &'a ProofNode>, checked: &mut [bool],
  heap: &[ExprNode], store: &[ExprNode], node: &ExprNode,
  t_heap: &'a [ProofNode], t_store: &'a [ProofNode], mut tgt: &'a ProofNode
) {
  match *node {
    ExprNode::Ref(i) => if !mem::replace(&mut checked[i], true) {
      build_unfold_map(env, m, checked, heap, store, &heap[i], t_heap, t_store, tgt)
    },
    ExprNode::Dummy(a, _) => {m.insert(a, tgt);}
    ExprNode::App(t, p) => {
      let td = env.term(t);
      loop {
        match *tgt {
          ProofNode::Ref(j) => tgt = &t_heap[j],
          ProofNode::Term(t2, p2) if t == t2 => {
            for (e1, e2) in td.unpack_app(&store[p..]).iter().zip(td.unpack_term(&t_store[p2..])) {
              build_unfold_map(env, m, checked, heap, store, e1, t_heap, t_store, e2)
            }
            break
          }
          _ => unreachable!()
        }
      }
    }
  }
}

type Line = (usize, Vec<u8>);

impl FrozenEnv {
  fn write_deps(&self, w: &mut impl Write, bvars: &[Option<AtomId>], mut vs: u64) -> io::Result<()> {
    list(w, bvars.iter().filter(|_| {let old = vs; vs /= 2; old & 1 != 0}),
      |w, &a| write!(w, "{}", self.data()[a.expect("you can only depend on variables with names")].name()))
  }

  fn write_binders(&self, w: &mut impl Write, bis: &[(Option<AtomId>, Type)]) -> io::Result<Vec<Option<AtomId>>> {
    let mut bvars = vec![];
    list(w, bis.iter(), |w, &(a, ty)| {
      write!(w, "({} ", a.map_or("_", |a| self.data()[a].name().as_str()))?;
      match ty {
        Type::Bound(s) => {
          bvars.push(a);
          write!(w, "{})", &self.sort(s).name)
        }
        Type::Reg(s, vs) => {
          write!(w, "{} ", &self.sort(s).name)?;
          self.write_deps(w, &bvars, vs)?;
          write!(w, ")")
        }
      }
    })?;
    Ok(bvars)
  }

  fn write_expr_node(&self,
    dummies: &mut HashMap<AtomId, SortId>,
    heap: &[Vec<u8>], store: &[ExprNode], node: &ExprNode,
  ) -> io::Result<Vec<u8>> {
    fn f(
      env: &FrozenEnv, w: &mut Vec<u8>,
      dummies: &mut HashMap<AtomId, SortId>,
      heap: &[Vec<u8>], store: &[ExprNode], node: &ExprNode
    ) -> io::Result<()> {
      match *node {
        ExprNode::Ref(i) => w.extend_from_slice(&heap[i]),
        ExprNode::Dummy(a, s) => {
          assert!(dummies.insert(a, s).map_or(true, |s2| s == s2));
          w.extend_from_slice(env.data()[a].name());
        }
        ExprNode::App(t, p) => {
          let td = env.term(t);
          write!(w, "({}", env.data()[td.atom].name())?;
          for e in td.unpack_app(&store[p..]) {
            w.push(b' ');
            f(env, w, dummies, heap, store, e)?;
          }
          w.push(b')');
        }
      }
      Ok(())
    }
    let mut ret = Vec::new();
    f(self, &mut ret, dummies, heap, store, node)?;
    Ok(ret)
  }

  #[allow(clippy::too_many_arguments)]
  fn write_proof_node(&self,
    dummies: &mut HashMap<AtomId, SortId>,
    hyps: &[(Option<AtomId>, ExprNode)],
    heap: &[ProofNode],
    store: &[ProofNode],
    lines: &[(Vec<Line>, Line)],
    node: &ProofNode,
    indent: usize,
  ) -> io::Result<(Vec<Line>, Line)> {
    struct State<'a> {
      env: &'a FrozenEnv,
      w: Vec<Line>, i: usize, l: Vec<u8>,
      dummies: &'a mut HashMap<AtomId, SortId>,
      hyps: &'a [(Option<AtomId>, ExprNode)],
      heap: &'a [ProofNode],
      store: &'a [ProofNode],
      lines: &'a [(Vec<Line>, Line)],
    }
    impl<'a> Write for State<'a> {
      fn write(&mut self, buf: &[u8]) -> io::Result<usize> {self.l.write(buf)}
      fn flush(&mut self) -> io::Result<()> {self.l.flush()}
    }
    impl<'a> State<'a> {
      fn line(&mut self, indent: usize) {
        let l = mem::take(&mut self.l);
        self.w.push((mem::replace(&mut self.i, indent), l));
      }

      fn go(&mut self, e: &ProofNode, indent: usize) -> io::Result<()> {
        match *e {
          ProofNode::Ref(i) => {
            let (ref w2, (n, ref l2)) = self.lines[i];
            if w2.is_empty() {
              self.l.extend_from_slice(l2);
            } else {
              self.l.extend_from_slice(&w2[0].1);
              self.w.push((
                mem::replace(&mut self.i, indent + n),
                mem::replace(&mut self.l, l2.clone())));
              for &(n, ref l2) in &w2[1..] {
                self.w.push((indent + n, l2.clone()));
              }
            }
          }
          ProofNode::Dummy(a, s) => {
            assert!(self.dummies.insert(a, s).map_or(true, |s2| s == s2));
            self.l.extend_from_slice(self.env.data()[a].name());
          }
          ProofNode::Hyp(i, _) =>
            self.l.extend_from_slice(self.env.data()[
              self.hyps[i].0.expect("a nameless hyp can't be referred to")
            ].name()),
          ProofNode::Term(term, p) => {
            let td = self.env.term(term);
            write!(self, "({}", self.env.data()[td.atom].name()).unwrap();
            for e in td.unpack_term(&self.store[p..]) {
              self.l.push(b' ');
              self.go(e, indent)?;
            }
            self.l.push(b')');
          }
          ProofNode::Thm(thm, p) => {
            let td = self.env.thm(thm);
            let (_, subst, subproofs) = td.unpack_thm(&self.store[p..]);
            write!(self, "({} ", self.env.data()[td.atom].name())?;
            list(self, subst.iter(), |this, e| this.go(e, indent))?;
            for e in subproofs {
              self.line(indent + 1);
              self.go(e, indent + 1)?;
            }
            self.l.push(b')');
          }
          ProofNode::Conv(p) => {
            let (e, c, p) = ProofNode::unpack_conv(&self.store[p..]);
            self.l.extend_from_slice(b"(:conv ");
            self.go(e, indent)?;
            self.line(indent + 1);
            self.go(c, indent + 1)?;
            self.line(indent + 1);
            self.go(p, indent + 1)?;
            self.l.push(b')');
          }
          ProofNode::Refl(e) => self.go(&self.store[e], indent)?,
          ProofNode::Sym(c) => {
            self.l.extend_from_slice(b"(:sym ");
            self.go(&self.store[c], indent)?;
            self.l.push(b')');
          }
          ProofNode::Cong(term, p) => {
            let td = self.env.term(term);
            write!(self, "({}", self.env.data()[td.atom].name())?;
            for e in td.unpack_term(&self.store[p..]) {
              self.line(indent + 1);
              self.go(e, indent + 1)?;
            }
            self.l.push(b')');
          }
          ProofNode::Unfold(term, p) => {
            let td = self.env.term(term);
            let (sub_lhs, c, args) = td.unpack_unfold(&self.store[p..]);
            write!(self, "(:unfold {} ", self.env.data()[td.atom].name())?;
            list(self, args.iter(), |this, e| this.go(e, indent))?;
            let mut m = HashMap::new();
            if let TermKind::Def(Some(expr)) = &td.kind {
              build_unfold_map(self.env, &mut m, &mut vec![false; expr.heap.len()],
                &expr.heap, &expr.store, expr.head(), self.heap, self.store, sub_lhs)
            }
            self.l.push(b' ');
            let mut ds = m.into_iter().collect::<Vec<_>>();
            ds.sort_by_key(|&(a, _)| &**self.env.data()[a].name());
            list(self, ds.into_iter(), |this, (_, e)| this.go(e, indent))?;
            self.line(indent + 1);
            self.go(c, indent + 1)?;
            self.l.push(b')');
          }
        }
        Ok(())
      }
    }

    let mut s = State {
      env: self, w: vec![], i: indent, l: vec![],
      dummies, hyps, heap, store, lines
    };
    s.go(node, indent)?;
    Ok((s.w, (s.i, s.l)))
  }

  /// Write this environment into an `mmu` file.
  pub fn export_mmu(&self, mut w: impl Write) -> io::Result<()> {
    let w = &mut w;
    for s in self.stmts() {
      match *s {
        StmtTrace::Sort(a) => {
          let ad = &self.data()[a];
          let mods = self.sort(ad.sort().expect("expected a sort")).mods;
          write!(w, "(sort {}", ad.name())?;
          if mods.contains(Modifiers::PURE) {write!(w, " pure")?}
          if mods.contains(Modifiers::STRICT) {write!(w, " strict")?}
          if mods.contains(Modifiers::PROVABLE) {write!(w, " provable")?}
          if mods.contains(Modifiers::FREE) {write!(w, " free")?}
          writeln!(w, ")\n")?;
        }
        StmtTrace::Decl(a) => {
          let ad = &self.data()[a];
          match ad.decl().expect("expected a term/thm") {
            DeclKey::Term(tid) => {
              let td = self.term(tid);
              write!(w, "({}{} {} ",
                if td.vis == Modifiers::LOCAL {"local "} else {""},
                if matches!(td.kind, TermKind::Term) {"term"} else {"def"}, ad.name())?;
              let bvs = self.write_binders(w, &td.args)?;
              write!(w, " ({} ", &self.sort(td.ret.0).name)?;
              self.write_deps(w, &bvs, td.ret.1)?;
              write!(w, ")")?;
              if let TermKind::Def(Some(expr)) = &td.kind {
                let mut dummies = HashMap::new();
                let mut strs: Vec<Vec<u8>> = td.args.iter().map(|&(a, _)|
                  a.map_or(vec![], |a| Vec::from(self.data()[a].name().as_str()))).collect();
                for e in &expr.heap[td.args.len()..] {
                  let c = self.write_expr_node(&mut dummies, &strs, &expr.store, e)?;
                  strs.push(c);
                }
                let ret = self.write_expr_node(&mut dummies, &strs, &expr.store, expr.head())?;
                writeln!(w)?;
                let mut dummies = dummies.into_iter().collect::<Vec<_>>();
                dummies.sort_by_key(|&(a, _)| &**self.data()[a].name());
                list(w, dummies.into_iter(), |w, (a, s)|
                  write!(w, "({} {})", self.data()[a].name(), self.sort(s).name))?;
                writeln!(w)?;
                w.write_all(&ret)?;
              }
              writeln!(w, ")\n")?;
            }
            DeclKey::Thm(tid) => {
              let td = self.thm(tid);
              write!(w, "({} {} ",
                match td.kind {
                  ThmKind::Axiom => "axiom",
                  ThmKind::Thm(_) if td.vis == Modifiers::PUB => "theorem",
                  ThmKind::Thm(_) => "local theorem",
                },
                ad.name())?;
              self.write_binders(w, &td.args)?;
              let mut dummies = HashMap::new();
              let mut strs: Vec<Vec<u8>> = td.args.iter().map(|&(a, _)|
                a.map_or(vec![], |a| Vec::from(self.data()[a].name().as_str()))).collect();
              for e in &td.heap[td.args.len()..] {
                let c = self.write_expr_node(&mut dummies, &strs, &td.store, e)?;
                strs.push(c);
              }
              {
                let mut it = td.hyps.iter();
                match (it.next(), &td.kind) {
                  (None, _) => write!(w, " ()")?,
                  (Some((_, ty)), ThmKind::Axiom) => {
                    write!(w, "\n  (")?;
                    w.write_all(&self.write_expr_node(&mut dummies, &strs, &td.store, ty)?)?;
                    for (_, ty) in it {
                      write!(w, "\n   ")?;
                      w.write_all(&self.write_expr_node(&mut dummies, &strs, &td.store, ty)?)?;
                    }
                    write!(w, ")")?;
                  }
                  (Some((hyp, ty)), ThmKind::Thm(_)) => {
                    write!(w, "\n  (({} ", hyp.map_or("_", |a| self.data()[a].name().as_str()))?;
                    w.write_all(&self.write_expr_node(&mut dummies, &strs, &td.store, ty)?)?;
                    write!(w, ")")?;
                    for (hyp, ty) in it {
                      write!(w, "\n   ({} ", hyp.map_or("_", |a| self.data()[a].name().as_str()))?;
                      w.write_all(&self.write_expr_node(&mut dummies, &strs, &td.store, ty)?)?;
                      write!(w, ")")?;
                    }
                    write!(w, ")")?;
                  }
                }
              }
              write!(w, "\n  ")?;
              w.write_all(&self.write_expr_node(&mut dummies, &strs, &td.store, &td.ret)?)?;
              match &td.kind {
                ThmKind::Axiom => {},
                ThmKind::Thm(None) => panic!("proof {} missing", self.data()[td.atom].name()),
                ThmKind::Thm(Some(pf)) => {
                  fn write_lines(w: &mut impl Write, (mut ls, nv): (Vec<Line>, Line)) -> io::Result<()> {
                    ls.push(nv);
                    let mut first = true;
                    for (n, v) in ls {
                      if !mem::replace(&mut first, false) {
                        w.write_all(b"\n")?;
                        w.write_all(&vec![b' '; 2 * n])?
                      }
                      w.write_all(&v)?;
                    }
                    Ok(())
                  }

                  writeln!(w)?;
                  let mut idx = 1;
                  for a in td.args.iter().filter_map(|&(a, _)| a)
                    .chain(td.hyps.iter().filter_map(|&(a, _)| a))
                    .chain(dummies.iter().map(|(&a, _)| a)) {
                    let mut s = self.data()[a].name().as_str().chars();
                    if s.next() == Some('H') {
                      if let Ok(n) = s.as_str().parse::<u32>() {idx = n+1}
                    }
                  }
                  let mut lets_start = vec![];
                  let mut lets_end = vec![];
                  let mut strs: Vec<_> = strs.into_iter().take(td.args.len())
                    .map(|v| (vec![], (0, v))).collect();
                  for e in &pf.heap[strs.len()..] {
                    let mut c = self.write_proof_node(
                      &mut dummies, &td.hyps, &pf.heap, &pf.store, &strs, e, 0)?;
                    if is_nonatomic_proof(e) {
                      write!(lets_start, "(:let H{} ", idx)?;
                      write_lines(&mut lets_start, c)?;
                      lets_start.push(b'\n');
                      lets_end.push(b')');
                      c = (vec![], (0, format!("H{}", idx).into_bytes()));
                      idx += 1
                    }
                    strs.push(c);
                  }
                  let pf = self.write_proof_node(
                    &mut dummies, &td.hyps, &pf.heap, &pf.store, &strs, pf.head(), 0)?;
                  let mut dummies = dummies.into_iter().collect::<Vec<_>>();
                  dummies.sort_by_key(|&(a, _)| &**self.data()[a].name());
                  list(w, dummies.into_iter(), |w, (a, s)|
                    write!(w, "({} {})", self.data()[a].name(), self.sort(s).name))?;
                  writeln!(w)?;
                  w.write_all(&lets_start)?;
                  write_lines(w, pf)?;
                  w.write_all(&lets_end)?;
                }
              }
              writeln!(w, ")\n")?;
            }
          }
        }
        StmtTrace::Global(_) => {}
        StmtTrace::OutputString(_) => writeln!(w, "(output string)\n")?
      }
    }
    Ok(())
  }
}
