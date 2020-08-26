//! MMU exporter, which produces `.mmu` ASCII proof files from an `Environment` object.
use std::collections::HashMap;
use std::io::{self, Write};
use std::mem;
use crate::elab::environment::{
  Type, Expr, Proof, AtomID, SortID,
  ExprNode, ProofNode, StmtTrace, DeclKey, Modifiers};
use crate::elab::FrozenEnv;

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

fn build_unfold_map<'a>(env: &FrozenEnv, m: &mut HashMap<AtomID, &'a ProofNode>, checked: &mut [bool],
  heap: &[ExprNode], head: &ExprNode, theap: &'a [ProofNode], mut tgt: &'a ProofNode) {
  match *head {
    ExprNode::Ref(i) => if !mem::replace(&mut checked[i], true) {
      build_unfold_map(env, m, checked, heap, &heap[i], theap, tgt)
    },
    ExprNode::Dummy(a, _) => {m.insert(a, tgt);}
    ExprNode::App(t, ref es) => loop {
      match *tgt {
        ProofNode::Ref(j) => tgt = &theap[j],
        ProofNode::Term {term: t2, args: ref es2} if t == t2 && es.len() == es2.len() => {
          for (e1, e2) in es.iter().zip(&**es2) {
            build_unfold_map(env, m, checked, heap, e1, theap, e2)
          }
          break
        }
        _ => unreachable!()
      }
    }
  }
}

type Line = (usize, Vec<u8>);

impl FrozenEnv {
  fn write_deps(&self, w: &mut impl Write, bvs: &[Option<AtomID>], mut vs: u64) -> io::Result<()> {
    list(w, bvs.iter().filter(|_| {let old = vs; vs /= 2; old & 1 != 0}),
      |w, a| write!(w, "{}", self.data()[a.unwrap()].name()))
  }

  fn write_binders(&self, w: &mut impl Write, bis: &[(Option<AtomID>, Type)]) -> io::Result<Vec<Option<AtomID>>> {
    let mut bvs = vec![];
    list(w, bis.iter(), |w, &(a, ty)| {
      write!(w, "({} ", a.map_or("_", |a| &self.data()[a].name()))?;
      match ty {
        Type::Bound(s) => {
          bvs.push(a);
          write!(w, "{})", &self.sort(s).name)
        }
        Type::Reg(s, vs) => {
          write!(w, "{} ", &self.sort(s).name)?;
          self.write_deps(w, &bvs, vs)?;
          write!(w, ")")
        }
      }
    })?;
    Ok(bvs)
  }

  fn write_expr_node(&self,
    dummies: &mut HashMap<AtomID, SortID>,
    heap: &[Vec<u8>],
    head: &ExprNode,
  ) -> Vec<u8> {
    fn f(
      env: &FrozenEnv, w: &mut Vec<u8>,
      dummies: &mut HashMap<AtomID, SortID>,
      heap: &[Vec<u8>],
      head: &ExprNode) {
      match *head {
        ExprNode::Ref(i) => w.extend_from_slice(&heap[i]),
        ExprNode::Dummy(a, s) => {
          assert!(dummies.insert(a, s).map_or(true, |s2| s == s2));
          w.extend_from_slice(env.data()[a].name().as_bytes());
        }
        ExprNode::App(t, ref es) => {
          write!(w, "({}", env.data()[env.term(t).atom].name()).unwrap();
          for e in es {
            w.push(b' ');
            f(env, w, dummies, heap, e);
          }
          w.push(b')');
        }
      }
    }
    let mut ret = Vec::new();
    f(self, &mut ret, dummies, heap, head);
    ret
  }

  fn write_proof_node(&self,
    dummies: &mut HashMap<AtomID, SortID>,
    hyps: &[(Option<AtomID>, ExprNode)],
    heap: &[ProofNode],
    lines: &[(Vec<Line>, Line)],
    head: &ProofNode,
    indent: usize,
  ) -> (Vec<Line>, Line) {
    struct State<'a> {
      env: &'a FrozenEnv,
      w: Vec<Line>, i: usize, l: Vec<u8>,
      dummies: &'a mut HashMap<AtomID, SortID>,
      hyps: &'a [(Option<AtomID>, ExprNode)],
      heap: &'a [ProofNode],
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

      fn go(&mut self, e: &ProofNode, indent: usize) {
        match e {
          &ProofNode::Ref(i) => {
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
          &ProofNode::Dummy(a, s) => {
            assert!(self.dummies.insert(a, s).map_or(true, |s2| s == s2));
            self.l.extend_from_slice(self.env.data()[a].name().as_bytes());
          }
          &ProofNode::Hyp(i, _) =>
            self.l.extend_from_slice(self.env.data()[self.hyps[i].0.unwrap()].name().as_bytes()),
          &ProofNode::Term {term, ref args} => {
            let td = self.env.term(term);
            write!(self, "({}", self.env.data()[td.atom].name()).unwrap();
            assert!(td.args.len() == args.len());
            for e in &**args {
              self.l.push(b' ');
              self.go(e, indent);
            }
            self.l.push(b')');
          }
          &ProofNode::Thm {thm, ref args, ..} => {
            let td = self.env.thm(thm);
            let nargs = td.args.len();
            write!(self, "({} ", self.env.data()[td.atom].name()).unwrap();
            list(self, args[..nargs].iter(), |this, e| {this.go(e, indent); Ok(())}).unwrap();
            for e in &args[nargs..] {
              self.line(indent + 1);
              self.go(e, indent + 1);
            }
            self.l.push(b')');
          }
          ProofNode::Conv(args) => {
            let (e, c, p) = &**args;
            self.l.extend_from_slice(b"(:conv ");
            self.go(e, indent);
            self.line(indent + 1);
            self.go(c, indent + 1);
            self.line(indent + 1);
            self.go(p, indent + 1);
            self.l.push(b')');
          }
          ProofNode::Refl(e) => self.go(e, indent),
          ProofNode::Sym(c) => {
            self.l.extend_from_slice(b"(:sym ");
            self.go(c, indent);
            self.l.push(b')');
          }
          &ProofNode::Cong {term, ref args} => {
            write!(self, "({}", self.env.data()[self.env.term(term).atom].name()).unwrap();
            for e in &**args {
              self.line(indent + 1);
              self.go(e, indent + 1);
            }
            self.l.push(b')');
          }
          &ProofNode::Unfold {term, ref args, ref res} => {
            let (_, sub_lhs, c) = &**res;
            let td = self.env.term(term);
            write!(self, "(:unfold {} ", self.env.data()[td.atom].name()).unwrap();
            list(self, args.iter(), |this, e| {this.go(e, indent); Ok(())}).unwrap();
            let mut m = HashMap::new();
            if let Some(Some(Expr {heap: eheap, head})) = &td.val {
              build_unfold_map(&self.env, &mut m, &mut vec![false; eheap.len()],
                eheap, head, self.heap, sub_lhs)
            }
            self.l.push(b' ');
            let mut ds = m.into_iter().collect::<Vec<_>>();
            ds.sort_by_key(|&(a, _)| &**self.env.data()[a].name());
            list(self, ds.into_iter(), |this, (_, e)| {this.go(e, indent); Ok(())}).unwrap();
            self.line(indent + 1);
            self.go(c, indent + 1);
            self.l.push(b')');
          }
        }
      }
    }

    let mut s = State {env: self, w: vec![], i: indent, l: vec![], dummies, hyps, heap, lines};
    s.go(head, indent);
    (s.w, (s.i, s.l))
  }

  /// Write this environment into an `mmu` file.
  pub fn export_mmu(&self, mut w: impl Write) -> io::Result<()> {
    let w = &mut w;
    for &s in self.stmts() {
      match s {
        StmtTrace::Sort(a) => {
          let ad = &self.data()[a];
          let mods = self.sort(ad.sort().unwrap()).mods;
          write!(w, "(sort {}", ad.name())?;
          if mods.contains(Modifiers::PURE) {write!(w, " pure")?}
          if mods.contains(Modifiers::STRICT) {write!(w, " strict")?}
          if mods.contains(Modifiers::PROVABLE) {write!(w, " provable")?}
          if mods.contains(Modifiers::FREE) {write!(w, " free")?}
          writeln!(w, ")\n")?;
        }
        StmtTrace::Decl(a) => {
          let ad = &self.data()[a];
          match ad.decl().unwrap() {
            DeclKey::Term(tid) => {
              let td = self.term(tid);
              write!(w, "({}{} {} ",
                if td.vis == Modifiers::LOCAL {"local "} else {""},
                if td.val.is_some() {"def"} else {"term"}, ad.name())?;
              let bvs = self.write_binders(w, &td.args)?;
              write!(w, " ({} ", &self.sort(td.ret.0).name)?;
              self.write_deps(w, &bvs, td.ret.1)?;
              write!(w, ")")?;
              if let Some(Some(Expr {heap, head})) = &td.val {
                let mut dummies = HashMap::new();
                let mut strs: Vec<Vec<u8>> = td.args.iter().map(|&(a, _)|
                  a.map_or(vec![], |a| Vec::from(self.data()[a].name().as_bytes()))).collect();
                for e in &heap[td.args.len()..] {
                  let c = self.write_expr_node(&mut dummies, &strs, e);
                  strs.push(c);
                }
                let ret = self.write_expr_node(&mut dummies, &strs, head);
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
              write!(w, "({}{} {} ",
                if td.vis == Modifiers::PUB || td.proof.is_none() {""} else {"local "},
                if td.proof.is_some() {"theorem"} else {"axiom"}, ad.name())?;
              self.write_binders(w, &td.args)?;
              let mut dummies = HashMap::new();
              let mut strs: Vec<Vec<u8>> = td.args.iter().map(|&(a, _)|
                a.map_or(vec![], |a| Vec::from(self.data()[a].name().as_bytes()))).collect();
              for e in &td.heap[td.args.len()..] {
                let c = self.write_expr_node(&mut dummies, &strs, e);
                strs.push(c);
              }
              {
                let mut it = td.hyps.iter();
                match it.next() {
                  None => write!(w, " ()")?,
                  Some((hyp, typ)) => if td.proof.is_some() {
                    write!(w, "\n  (({} ", hyp.map_or("_", |a| &self.data()[a].name()))?;
                    w.write_all(&self.write_expr_node(&mut dummies, &strs, typ))?;
                    write!(w, ")")?;
                    for (hyp, typ) in it {
                      write!(w, "\n   ({} ", hyp.map_or("_", |a| &self.data()[a].name()))?;
                      w.write_all(&self.write_expr_node(&mut dummies, &strs, typ))?;
                      write!(w, ")")?;
                    }
                    write!(w, ")")?;
                  } else {
                    write!(w, "\n  (")?;
                    w.write_all(&self.write_expr_node(&mut dummies, &strs, typ))?;
                    for (_, typ) in it {
                      write!(w, "\n   ")?;
                      w.write_all(&self.write_expr_node(&mut dummies, &strs, typ))?;
                    }
                    write!(w, ")")?;
                  }
                }
              }
              write!(w, "\n  ")?;
              w.write_all(&self.write_expr_node(&mut dummies, &strs, &td.ret))?;
              match &td.proof {
                None => {},
                Some(None) => panic!("proof {} missing", self.data()[td.atom].name()),
                Some(Some(Proof {heap, head, ..})) => {
                  writeln!(w)?;
                  let mut idx = 1;
                  for a in td.args.iter().filter_map(|&(a, _)| a)
                    .chain(td.hyps.iter().filter_map(|&(a, _)| a))
                    .chain(dummies.iter().map(|(&a, _)| a)) {
                    let mut s = self.data()[a].name().chars();
                    if let Some('H') = s.next() {
                      if let Ok(n) = s.as_str().parse::<u32>() {idx = n+1}
                    }
                  }
                  let mut lets_start = vec![];
                  let mut lets_end = vec![];
                  let mut strs: Vec<_> = strs.into_iter().take(td.args.len())
                    .map(|v| (vec![], (0, v))).collect();
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
                  for e in &heap[strs.len()..] {
                    let mut c = self.write_proof_node(&mut dummies, &td.hyps, heap, &strs, e, 0);
                    if is_nonatomic_proof(e) {
                      write!(lets_start, "(:let H{} ", idx).unwrap();
                      write_lines(&mut lets_start, c).unwrap();
                      lets_start.push(b'\n');
                      lets_end.push(b')');
                      c = (vec![], (0, format!("H{}", idx).into_bytes()));
                      idx += 1
                    }
                    strs.push(c);
                  }
                  let pf = self.write_proof_node(&mut dummies, &td.hyps, heap, &strs, head, 0);
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
      }
    }
    Ok(())
  }
}
