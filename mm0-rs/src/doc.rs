//! Build documentation pages for MM1/MM0 files
use std::{collections::HashMap, path::PathBuf};
use std::mem;
use std::fs::{self, File};
use std::io::{self, BufWriter, Write};
use bit_set::BitSet;
use clap::ArgMatches;
use crate::{util::FileRef, lined_string::LinedString};
use crate::elab::{Environment, lisp::{LispVal, print::FormatEnv, pretty::Pretty},
  environment::{DeclKey, Proof, ProofNode, StmtTrace, AtomID, ThmID, ThmKind, Thm,
    ExprNode, Type}};

const PP_WIDTH: usize = 200;

struct AxiomUse(HashMap<ThmID, BitSet>);

impl AxiomUse {
  fn new(env: &Environment) -> (Vec<ThmID>, Self) {
    let mut axuse = HashMap::new();
    let mut to_tid = vec![ThmID(u32::MAX)];
    for (tid, td) in env.thms.enum_iter() {
      if let ThmKind::Axiom = td.kind {
        let axid = to_tid.len();
        to_tid.push(tid);
        let mut bs = BitSet::new();
        bs.insert(axid);
        axuse.insert(tid, bs);
      }
    }
    (to_tid, AxiomUse(axuse))
  }

  fn accumulate(&mut self, env: &Environment, bs: &mut BitSet, node: &ProofNode) {
    match node {
      ProofNode::Ref(_) |
      ProofNode::Dummy(_, _) |
      ProofNode::Term {..} |
      ProofNode::Hyp(_, _) |
      ProofNode::Refl(_) |
      ProofNode::Sym(_) |
      ProofNode::Cong {..} |
      ProofNode::Unfold {..} => {}
      ProofNode::Conv(p) => self.accumulate(env, bs, &p.2),
      &ProofNode::Thm {thm: tid, ref args, ..} => {
        bs.union_with(self.get(env, tid));
        for p in &**args { self.accumulate(env, bs, p) }
      }
    }
  }

  fn get<'a, 'b>(&'a mut self, env: &'b Environment, tid: ThmID) -> &'a BitSet {
    if let Some(bs) = self.0.get(&tid) {
      // Safety: This is the same issue that comes up in Spans::insert.
      // We are performing a lifetime cast here because rust can't see that
      // in the None case it is safe to drop the borrow of `self.axuse`.
      return unsafe { std::mem::transmute(bs) }
    }
    let mut bs = BitSet::new();
    let td = &env.thms[tid];
    match &td.kind {
      ThmKind::Axiom => unreachable!(),
      ThmKind::Thm(None) => {bs.insert(0);}
      ThmKind::Thm(Some(Proof {heap, head, ..})) => {
        for p in &heap[td.args.len()..] { self.accumulate(env, &mut bs, p) }
        self.accumulate(env, &mut bs, head)
      }
    }
    self.0.entry(tid).or_insert(bs)
  }
}

struct RenderProof<'a, W> {
  source: &'a LinedString,
  env: &'a mut Environment,
  w: &'a mut W,
  line: u32,
  args: &'a [(Option<AtomID>, Type)],
  heap: &'a [ProofNode],
  hyps: &'a [(Option<AtomID>, ExprNode)],
  heap_lines: Box<[Option<Result<u32, LispVal>>]>,
}

enum LineKind {
  Hyp(Option<AtomID>),
  Thm(ThmID),
  Conv,
}
impl<'a, W: Write> RenderProof<'a, W> {
  fn new(source: &'a LinedString, env: &'a mut Environment,
    w: &'a mut W,
    args: &'a [(Option<AtomID>, Type)],
    hyps: &'a [(Option<AtomID>, ExprNode)],
    heap: &'a [ProofNode],
  ) -> Self {
    RenderProof { source, env, w, line: 1, args, heap, hyps,
      heap_lines: vec![None; heap.len()].into_boxed_slice() }
  }

  fn render_line(&mut self, hyps: &[u32], kind: LineKind, e: &LispVal) -> io::Result<u32> {
    let kind_class = match kind {
      LineKind::Hyp(_) => "sh",
      LineKind::Thm(_) => "st",
      LineKind::Conv => "sc"
    };
    write!(self.w, r#"        <tr class="{kind_class}">
          <td><a name="{step}"/>{step}</td>
          <td>"#, kind_class = kind_class, step = self.line)?;
    let mut first = true;
    for hyp in hyps {
      if !mem::take(&mut first) { write!(self.w, ", ")? }
      write!(self.w, r##"<a href="#{id}">{id}</a>"##, id = hyp)?
    }
    write!(self.w, "</td>\n          <td>")?;
    match kind {
      LineKind::Hyp(None) => write!(self.w, "<i>hyp</i>")?,
      LineKind::Hyp(Some(a)) => write!(self.w, "<i>hyp {}</i>", self.env.data[a].name)?,
      LineKind::Thm(tid) => write!(self.w, r#"<a href="{thm}.html">{thm}</a>"#,
        thm = self.env.data[self.env.thms[tid].atom].name)?,
      LineKind::Conv => write!(self.w, "<i>conv</i>")?,
    }
    write!(self.w, "</td>\n          <td><pre>")?;
    let w = &mut self.w;
    FormatEnv {source: self.source, env: self.env}
      .pretty(|pr| pr.pp_expr(e).1.doc.render(PP_WIDTH, w))?;
    write!(self.w, "</pre></td>\n        </tr>")?;
    Ok((self.line, self.line += 1).0)
  }


  fn render(&mut self, p: &'a ProofNode) -> io::Result<Result<u32, LispVal>> {
    Ok(match *p {
      ProofNode::Ref(i) =>
        if let Some(n) = &self.heap_lines[i] {n.clone()}
        else {
          let res = if let Some((a, _)) = self.args.get(i) {
            let a = a.unwrap_or_else(|| self.env.get_atom(format!("v{}", i+1).as_bytes()));
            Err(LispVal::atom(a))
          } else { self.render(&self.heap[i])? };
          self.heap_lines[i] = Some(res.clone());
          res
        },
      ProofNode::Dummy(a, _) => Err(LispVal::atom(a)),
      ProofNode::Term {term, ref args} => {
        let mut out = Vec::with_capacity(args.len()+1);
        out.push(LispVal::atom(self.env.terms[term].atom));
        for e in &**args {
          out.push(self.render(e)?.unwrap_err());
        }
        Err(LispVal::list(out))
      }
      ProofNode::Hyp(i, ref e) => {
        let e = self.render(e)?.unwrap_err();
        Ok(self.render_line(&[], LineKind::Hyp(self.hyps[i].0), &e)?)
      }
      ProofNode::Thm {thm, ref args, ref res} => {
        let td = &self.env.thms[thm];
        let mut hyps = Vec::with_capacity(td.hyps.len());
        for e in &args[td.args.len()..] {
          hyps.push(self.render(e)?.unwrap())
        }
        let res = self.render(res)?.unwrap_err();
        Ok(self.render_line(&hyps, LineKind::Thm(thm), &res)?)
      }
      ProofNode::Conv(ref p) => {
        let n = self.render(&p.2)?.unwrap();
        let tgt = self.render(&p.0)?.unwrap_err();
        Ok(self.render_line(&[n], LineKind::Conv, &tgt)?)
      }
      ProofNode::Refl(_) |
      ProofNode::Sym(_) |
      ProofNode::Cong {..} |
      ProofNode::Unfold {..} => unreachable!()
    })
  }
}

struct BuildDoc<'a, W> {
  thm_folder: PathBuf,
  source: &'a LinedString,
  env: Environment,
  axuse: (Vec<ThmID>, AxiomUse),
  index: Option<W>,
}

impl<'a, W: Write> BuildDoc<'a, W> {
  fn thm_doc(&mut self, tid: ThmID) -> io::Result<()> {
    let mut file = self.thm_folder.to_owned();
    let td: &Thm = unsafe { mem::transmute(&self.env.thms[tid]) };
    let thmname = &self.env.data[td.atom].name;
    let filename = td.span.file.rel();
    file.push(&format!("{}.html", thmname));
    let mut file = BufWriter::new(File::create(file)?);
    let kind = if let ThmKind::Axiom = td.kind {"Axiom"} else {"Theorem"};
    writeln!(file, r#"<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <meta name="generator" content="mm0-doc">
  <meta name="description" content="Documentation for theorem `{thmname}` in `{filename}`.">
  <meta name="keywords" content="mm0, metamath-zero">
  <title>{thmname} - {filename} - Metamath Zero</title>
  <link rel="stylesheet" type="text/css" href="../stylesheet.css" />
  <!-- <link rel="shortcut icon" href="../favicon.ico"> -->
</head>
<body>
  <section class="main">
    <h1 class="title">{kind} <a class="thm" href="">{thmname}</a></h1>"#,
      thmname = thmname, filename = filename, kind = kind)?;
    if let Some(doc) = &td.doc {
      use pulldown_cmark::{Parser, html};
      write!(file, r#"<div class="doc">"#)?;
      html::write_html(&mut file, Parser::new(doc))?;
      write!(file, "</div>\n")?;
    }
    writeln!(file, "    <pre>{}</pre>", FormatEnv {source: self.source, env: &self.env}.to(td))?;
    if let ThmKind::Thm(Some(pf)) = &td.kind {
      writeln!(file, r#"    <table class="proof">
      <tbody>
        <tr class="proof-head"><th>Step</th><th>Hyp</th><th>Ref</th><th>Expression</th></tr>"#)?;
      let rp = RenderProof::new(self.source, &mut self.env, &mut file, &td.args, &td.hyps, &pf.heap);
      let _ = {rp}.render(&pf.head)?;
      writeln!(file, "      </tbody>\n    </table>")?;

    }
    if let ThmKind::Thm(_) = td.kind {
      writeln!(file, "    <h2 class=\"axioms\">Axiom use</h2>")?;
      let mut first = true;
      for i in self.axuse.1.get(&self.env, tid) {
        if !mem::take(&mut first) { writeln!(file, ",")? }
        if i == 0 {
          write!(file, "<i>sorry</i>")?
        } else {
          write!(file, r#"    <a href="{thm}.html">{thm}</a>"#,
            thm = self.env.data[self.env.thms[self.axuse.0[i]].atom].name)?
        }
      }
    }
    writeln!(file, "  </section>\n</body>\n</html>")
  }

  fn write_all(&mut self, path: &FileRef, stmts: &[StmtTrace]) -> io::Result<()> {
    let file = self.index.as_mut().unwrap();
    writeln!(file, r#"<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <meta name="generator" content="mm0-doc">
  <meta name="description" content="Documentation index for `{filename}`.">
  <meta name="keywords" content="mm0, metamath-zero">
  <title>{filename} - Index - Metamath Zero</title>
  <link rel="stylesheet" type="text/css" href="stylesheet.css" />
  <!-- <link rel="shortcut icon" href="favicon.ico"> -->
</head>
<body>
  <section class="index-main">
    <h1 class="index-title">Index</h1>"#,
      filename = path.rel())?;
    for s in stmts {
      let file = self.index.as_mut().unwrap();
      match *s {
        StmtTrace::Global(_) |
        StmtTrace::OutputString(_) => {}
        StmtTrace::Sort(a) =>
          writeln!(file, "    <p><pre>{}</pre></p>",
            self.env.sorts[self.env.data[a].sort.unwrap()])?,
        StmtTrace::Decl(a) => {
          match self.env.data[a].decl.unwrap() {
            DeclKey::Term(tid) =>
              writeln!(file, "    <p><pre>{}</pre></p>",
                FormatEnv {source: self.source, env: &self.env}
                  .to(&self.env.terms[tid]))?,
            DeclKey::Thm(tid) => {
              let mut file = file;
              let td = &self.env.thms[tid];
              let fe = FormatEnv {source: self.source, env: &self.env};
              write!(file, r#"    <p><pre>{}{} <a href="thms/{name}.html">{name}</a>"#, td.vis,
                if matches!(td.kind, ThmKind::Axiom) {"axiom"} else {"theorem"},
                name = fe.to(&td.atom))?;
              fe.pretty(|pr| -> io::Result<()> {
                let mut buf = String::new();
                pr.thm_headless(td, Pretty::nil()).render_fmt(PP_WIDTH, &mut buf).unwrap();
                use pulldown_cmark::escape::{escape_html, WriteWrapper};
                escape_html(WriteWrapper(&mut file), &buf)
              })?;
              writeln!(file, "</pre></p>")?;
              self.thm_doc(tid)?
            }
          }
        }
      }
    }
    let file = self.index.as_mut().unwrap();
    writeln!(file, "  </section>\n</body>\n</html>")
  }
}
/// Main entry point for `mm0-rs doc` subcommand.
///
/// # Arguments
///
/// `mm0-rs doc <in.mm1> [doc]`, where:
///
/// - `in.mm1` is the initial file to elaborate.
/// - `doc` is the output folder, which will be created if not present.
pub fn main(args: &ArgMatches<'_>) -> io::Result<()> {
  let path = args.value_of("INPUT").expect("required arg");
  let path: FileRef = fs::canonicalize(path)?.into();
  let (fc, old) = crate::compiler::elab_for_result(path.clone())?;
  let old = old.unwrap_or_else(|| std::process::exit(1));
  let mut env = Environment::new();
  env.merge(&old, (0..0).into(), &mut vec![]).unwrap();
  let mut dir = PathBuf::from(args.value_of("OUTPUT").unwrap_or("doc"));
  fs::create_dir_all(&dir)?;
  let only = args.value_of("only");
  let index = if only.is_some() {None} else {
    let mut file = dir.to_owned();
    file.push("index.html");
    Some(BufWriter::new(File::create(file)?))
  };
  dir.push("thms");
  fs::create_dir_all(&dir)?;
  let mut bd = BuildDoc {
    source: fc.ascii(),
    axuse: AxiomUse::new(&env),
    thm_folder: dir, env, index,
  };
  if let Some(only) = only {
    for thm in only.split(',') {
      let a = bd.env.get_atom(thm.as_bytes());
      match bd.env.data[a].decl {
        None => eprintln!("warning: unknown theorem '{}'", thm),
        Some(DeclKey::Term(_)) => eprintln!("warning: expected a theorem, got term '{}'", thm),
        Some(DeclKey::Thm(tid)) => bd.thm_doc(tid)?,
      }
    }
  } else {
    bd.write_all(&path, old.stmts())?;
  }
  Ok(())
}