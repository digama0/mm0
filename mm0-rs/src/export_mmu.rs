use std::collections::BTreeMap;
use std::io::{self, Write};
use crate::elab::environment::{
  Environment, Type, Expr, Proof, AtomID, SortID,
  ExprNode, ProofNode, StmtTrace, DeclKey, Modifiers};

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
  match e {
    ProofNode::Thm {..} | ProofNode::Conv(_) => true,
    _ => false,
  }
}

impl Environment {
  fn write_deps(&self, w: &mut impl Write, bvs: &[Option<AtomID>], mut vs: u64) -> io::Result<()> {
    list(w, bvs.iter().filter(|_| (vs & 1 != 0, vs /= 2).0),
      |w, a| write!(w, "{}", self.data[a.unwrap()].name))
  }

  fn write_binders(&self, w: &mut impl Write, bis: &[(Option<AtomID>, Type)]) -> io::Result<Vec<Option<AtomID>>> {
    let mut bvs = vec![];
    list(w, bis.iter(), |w, &(a, ty)| {
      write!(w, "({} ", a.map_or("_", |a| &self.data[a].name))?;
      match ty {
        Type::Bound(s) => {
          bvs.push(a);
          write!(w, "{})", &self.sorts[s].name)
        }
        Type::Reg(s, vs) => {
          write!(w, "{} ", &self.sorts[s].name)?;
          self.write_deps(w, &bvs, vs)?;
          write!(w, ")")
        }
      }
    })?;
    Ok(bvs)
  }

  fn write_expr_node(&self,
    dummies: &mut BTreeMap<AtomID, SortID>,
    heap: &[Vec<u8>],
    head: &ExprNode,
  ) -> Vec<u8> {
    fn f(
      env: &Environment, w: &mut Vec<u8>,
      dummies: &mut BTreeMap<AtomID, SortID>,
      heap: &[Vec<u8>],
      head: &ExprNode) {
      match head {
        &ExprNode::Ref(i) => w.extend_from_slice(&heap[i]),
        &ExprNode::Dummy(a, s) => {
          assert!(dummies.insert(a, s).map_or(true, |s2| s == s2));
          w.extend_from_slice(env.data[a].name.as_bytes());
        }
        &ExprNode::App(t, ref es) => {
          write!(w, "({}", env.data[env.terms[t].atom].name).unwrap();
          for e in es {
            w.push(b' ');
            f(env, w, dummies, heap, e);
          }
          w.push(b')');
        }
      }
    }
    let mut ret = Vec::new();
    f(&self, &mut ret, dummies, heap, head);
    ret
  }

  fn write_proof_node(&self,
    dummies: &mut BTreeMap<AtomID, SortID>,
    hyps: &[(Option<AtomID>, ExprNode)],
    heap: &[Vec<u8>],
    head: &ProofNode,
    indent: &mut Vec<u8>,
  ) -> Vec<u8> {
    fn f(
      env: &Environment, w: &mut Vec<u8>,
      dummies: &mut BTreeMap<AtomID, SortID>,
      hyps: &[(Option<AtomID>, ExprNode)],
      heap: &[Vec<u8>],
      head: &ProofNode,
      indent: &mut Vec<u8>) {
      match head {
        &ProofNode::Ref(i) => w.extend_from_slice(&heap[i]),
        &ProofNode::Dummy(a, s) => {
          assert!(dummies.insert(a, s).map_or(true, |s2| s == s2));
          w.extend_from_slice(env.data[a].name.as_bytes());
        }
        &ProofNode::Hyp(i, _) => {
          w.extend_from_slice(env.data[hyps[i].0.unwrap()].name.as_bytes());
        }
        &ProofNode::Term {term, ref args} => {
          write!(w, "({}", env.data[env.terms[term].atom].name).unwrap();
          for e in &**args {
            w.push(b' ');
            f(env, w, dummies, hyps, heap, e, indent);
          }
          w.push(b')');
        }
        &ProofNode::Thm {thm, ref args, ..} => {
          let td = &env.thms[thm];
          let nargs = td.args.len();
          write!(w, "({} ", env.data[td.atom].name).unwrap();
          list(w, args[..nargs].iter(), |w, e|
            Ok(f(env, w, dummies, hyps, heap, e, indent))).unwrap();
          let len = indent.len();
          indent.extend_from_slice(b"  ");
          for e in &args[nargs..] {
            w.push(b'\n'); w.extend_from_slice(&indent);
            f(env, w, dummies, hyps, heap, e, indent);
          }
          w.push(b')');
          indent.truncate(len);
        }
        ProofNode::Conv(args) => {
          let (e, c, p) = &**args;
          w.extend_from_slice(b"(:conv ");
          f(env, w, dummies, hyps, heap, e, indent);
          let len = indent.len();
          indent.extend_from_slice(b"  ");
          w.push(b'\n'); w.extend_from_slice(&indent);
          f(env, w, dummies, hyps, heap, c, indent);
          w.push(b'\n'); w.extend_from_slice(&indent);
          f(env, w, dummies, hyps, heap, p, indent);
          w.push(b')');
          indent.truncate(len);
        }
        ProofNode::Refl(e) => f(env, w, dummies, hyps, heap, e, indent),
        ProofNode::Sym(c) => {
          w.extend_from_slice(b"(:sym ");
          f(env, w, dummies, hyps, heap, c, indent);
          w.push(b')');
        }
        &ProofNode::Cong {term, ref args} => {
          write!(w, "({}", env.data[env.terms[term].atom].name).unwrap();
          let len = indent.len();
          indent.extend_from_slice(b"  ");
          for e in &**args {
            w.push(b'\n'); w.extend_from_slice(&indent);
            f(env, w, dummies, hyps, heap, e, indent);
          }
          w.push(b')');
          indent.truncate(len);
        }
        &ProofNode::Unfold {term, ref args, ref res} => {
          write!(w, "(:unfold {} ", env.data[env.terms[term].atom].name).unwrap();
          list(w, args.iter(), |w, e|
            Ok(f(env, w, dummies, hyps, heap, e, indent))).unwrap();
          let len = indent.len();
          indent.extend_from_slice(b"  ");
          w.push(b'\n'); w.extend_from_slice(&indent);
          f(env, w, dummies, hyps, heap, &res.2, indent);
          w.push(b')');
          indent.truncate(len);
        }
      }
    }
    let mut ret = Vec::new();
    f(&self, &mut ret, dummies, hyps, heap, head, indent);
    ret
  }

  pub fn export_mmu(&self, w: &mut impl Write) -> io::Result<()> {
    for &s in &self.stmts {
      match s {
        StmtTrace::Sort(a) => {
          let ad = &self.data[a];
          let mods = self.sorts[ad.sort.unwrap()].mods;
          write!(w, "(sort {}", ad.name)?;
          if mods.contains(Modifiers::PURE) {write!(w, " pure")?}
          if mods.contains(Modifiers::STRICT) {write!(w, " strict")?}
          if mods.contains(Modifiers::PROVABLE) {write!(w, " provable")?}
          if mods.contains(Modifiers::FREE) {write!(w, " free")?}
          write!(w, ")\n\n")?;
        }
        StmtTrace::Decl(a) => {
          let ad = &self.data[a];
          match ad.decl.unwrap() {
            DeclKey::Term(t) => {
              let td = &self.terms[t];
              write!(w, "({}{} {} ",
                if td.vis == Modifiers::LOCAL {"local "} else {""},
                if let Some(_) = td.val {"def"} else {"term"}, ad.name)?;
              let bvs = self.write_binders(w, &td.args)?;
              write!(w, " ({} ", &self.sorts[td.ret.0].name)?;
              self.write_deps(w, &bvs, td.ret.1)?;
              write!(w, ")")?;
              if let Some(Some(Expr {heap, head})) = &td.val {
                let mut dummies = BTreeMap::new();
                let mut strs: Vec<Vec<u8>> = td.args.iter().map(|&(a, _)|
                  a.map_or(vec![], |a| Vec::from(self.data[a].name.as_bytes()))).collect();
                for e in &heap[td.args.len()..] {
                  let c = self.write_expr_node(&mut dummies, &strs, e);
                  strs.push(c);
                }
                let ret = self.write_expr_node(&mut dummies, &strs, head);
                write!(w, " ")?;
                list(w, dummies.into_iter(), |w, (a, s)|
                  write!(w, "({} {})", self.data[a].name, self.sorts[s].name))?;
                write!(w, " ")?;
                w.write_all(&ret)?;
              }
              write!(w, ")\n\n")?;
            }
            DeclKey::Thm(t) => {
              let td = &self.thms[t];
              write!(w, "({}{} {} ",
                if td.vis == Modifiers::PUB || td.proof.is_none() {""} else {"local "},
                if let Some(_) = td.proof {"theorem"} else {"axiom"}, ad.name)?;
              self.write_binders(w, &td.args)?;
              let mut dummies = BTreeMap::new();
              let mut strs: Vec<Vec<u8>> = td.args.iter().map(|&(a, _)|
                a.map_or(vec![], |a| Vec::from(self.data[a].name.as_bytes()))).collect();
              for e in &td.heap[td.args.len()..] {
                let c = self.write_expr_node(&mut dummies, &strs, e);
                strs.push(c);
              }
              {
                let mut it = td.hyps.iter();
                match it.next() {
                  None => write!(w, " ()")?,
                  Some((h, e)) => {
                    write!(w, "\n  (({} ", h.map_or("_", |a| &self.data[a].name))?;
                    w.write_all(&self.write_expr_node(&mut dummies, &strs, e))?;
                    write!(w, ")")?;
                    for (h, e) in it {
                      write!(w, "\n   ({} ", h.map_or("_", |a| &self.data[a].name))?;
                      w.write_all(&self.write_expr_node(&mut dummies, &strs, e))?;
                      write!(w, ")")?;
                    }
                    write!(w, ")")?;
                  }
                }
              }
              write!(w, "\n  ")?;
              w.write_all(&self.write_expr_node(&mut dummies, &strs, &td.ret))?;
              match &td.proof {
                None => {},
                Some(None) => panic!("proof {} missing", self.data[td.atom].name),
                Some(Some(Proof {heap, head, ..})) => {
                  write!(w, "\n")?;
                  let mut idx = 1;
                  for a in td.args.iter().filter_map(|&(a, _)| a)
                    .chain(td.hyps.iter().filter_map(|&(a, _)| a))
                    .chain(dummies.iter().map(|(&a, _)| a)) {
                    let mut s = self.data[a].name.chars();
                    if let Some('H') = s.next() {
                      if let Ok(n) = s.as_str().parse::<u32>() {idx = n+1}
                    }
                  }
                  let mut lets_start = vec![];
                  let mut lets_end = vec![];
                  let mut indent = vec![];
                  for e in &heap[strs.len()..] {
                    let mut c = self.write_proof_node(&mut dummies, &td.hyps, &strs, e, &mut indent);
                    if is_nonatomic_proof(e) {
                      write!(lets_start, "(:let H{} ", idx).unwrap();
                      lets_start.append(&mut c);
                      lets_start.push(b'\n');
                      lets_end.push(b')');
                      c = format!("H{}", idx).into_bytes();
                      idx += 1
                    }
                    strs.push(c);
                  }
                  let pf = self.write_proof_node(&mut dummies, &td.hyps, &strs, head, &mut indent);

                  list(w, dummies.into_iter(), |w, (a, s)|
                    write!(w, "({} {})", self.data[a].name, self.sorts[s].name))?;
                  write!(w, "\n")?;
                  w.write_all(&lets_start)?;
                  w.write_all(&pf)?;
                  w.write_all(&lets_end)?;
                }
              }
              write!(w, ")\n\n")?;
            }
          }
        }
        StmtTrace::Global(_) => {}
      }
    }
    Ok(())
  }
}