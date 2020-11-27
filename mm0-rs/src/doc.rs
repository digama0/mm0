//! Build documentation pages for MM1/MM0 files
use std::{collections::{hash_map::Entry, HashMap}, hash::Hash, path::PathBuf};
use std::mem;
use std::fs::{self, File};
use std::io::{self, BufWriter, Write};
use bit_set::BitSet;
use clap::ArgMatches;
use lsp_types::Url;
use crate::{elab::environment::{AtomData, DocComment}, lined_string::LinedString, util::{ArcString, FileRef}};
use crate::elab::{Environment, lisp::{LispVal, print::FormatEnv, pretty::Pretty},
  environment::{DeclKey, Proof, ProofNode, StmtTrace, AtomID, ThmID, ThmKind, Thm,
    ExprNode, Type}};

const PP_WIDTH: usize = 160;

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
      #[allow(clippy::useless_transmute, clippy::transmute_ptr_to_ptr)]
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

#[derive(Debug, Clone, Copy)]
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
    write!(self.w, "        <tr class=\"{}\">\n          <td>{}</td>\n          <td>",
      kind_class, self.line)?;
    let mut first = true;
    for hyp in hyps {
      if !mem::take(&mut first) { write!(self.w, ", ")? }
      write!(self.w, r##"<a href="#{id}">{id}</a>"##, id = hyp)?
    }
    write!(self.w, "</td>\n          <td>")?;
    match kind {
      LineKind::Hyp(None) => write!(self.w, "<i>hyp</i>")?,
      LineKind::Hyp(Some(a)) => write!(self.w, "<i>hyp {}</i>", self.env.data[a].name)?,
      LineKind::Thm(tid) => write!(self.w, r#"<a class="thm" href="{thm}.html">{thm}</a>"#,
        thm = self.env.data[self.env.thms[tid].atom].name)?,
      LineKind::Conv => write!(self.w, "<i>conv</i>")?,
    }
    write!(self.w, "</td>\n          <td><a name=\"{}\"></a><pre>", self.line)?;
    let w = &mut *self.w;
    FormatEnv {source: self.source, env: self.env}
      .pretty(|pr| pr.pp_expr(e).1.doc.render(PP_WIDTH, w))?;
    writeln!(self.w, "</pre></td>\n        </tr>")?;
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
          out.push(self.render(e)?.expect_err("bad_proof"));
        }
        Err(LispVal::list(out))
      }
      ProofNode::Hyp(i, ref e) => {
        let e = self.render(e)?.expect_err("bad_proof");
        Ok(self.render_line(&[], LineKind::Hyp(self.hyps[i].0), &e)?)
      }
      ProofNode::Thm {thm, ref args, ref res} => {
        let td = &self.env.thms[thm];
        let mut hyps = Vec::with_capacity(td.hyps.len());
        for e in &args[td.args.len()..] {
          hyps.push(self.render(e)?.expect("bad proof"))
        }
        let res = self.render(res)?.expect_err("bad_proof");
        Ok(self.render_line(&hyps, LineKind::Thm(thm), &res)?)
      }
      ProofNode::Conv(ref p) => {
        let n = self.render(&p.2)?.expect("bad proof");
        let tgt = self.render(&p.0)?.expect_err("bad_proof");
        Ok(self.render_line(&[n], LineKind::Conv, &tgt)?)
      }
      ProofNode::Refl(_) |
      ProofNode::Sym(_) |
      ProofNode::Cong {..} |
      ProofNode::Unfold {..} => unreachable!()
    })
  }
}

#[repr(transparent)]
struct CaseInsensitiveName(ArcString);

impl<'a> From<&'a ArcString> for &'a CaseInsensitiveName {
  #[allow(clippy::transmute_ptr_to_ptr)]
  fn from(s: &'a ArcString) -> Self { unsafe { mem::transmute(s) } }
}
impl Hash for CaseInsensitiveName {
  fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
    self.0.len().hash(state);
    for &c in &*self.0 {
      c.to_ascii_lowercase().hash(state)
    }
  }
}
impl PartialEq for CaseInsensitiveName {
  fn eq(&self, other: &Self) -> bool {
    self.0.len() == other.0.len() &&
    self.0.iter().zip(other.0.iter()).all(|(&x, &y)|
      x.to_ascii_lowercase() == y.to_ascii_lowercase())
  }
}
impl Eq for CaseInsensitiveName {}

struct BuildDoc<'a, W> {
  thm_folder: PathBuf,
  source: &'a LinedString,
  base_url: Option<Url>,
  env: Environment,
  axuse: (Vec<ThmID>, AxiomUse),
  index: Option<W>,
  mangler: Mangler,
}

#[derive(Default)]
struct Mangler {
  used: HashMap<CaseInsensitiveName, usize>,
  thms: HashMap<ThmID, usize>,
}
impl Mangler {
  fn get(&mut self, env: &Environment, tid: ThmID) -> usize {
    match self.thms.entry(tid) {
      Entry::Occupied(e) => *e.get(),
      Entry::Vacant(e) => {
        let n = match self.used.entry(CaseInsensitiveName(
          env.data[env.thms[tid].atom].name.clone()
        )) {
          Entry::Occupied(mut e) => {
            let p = e.get_mut();
            let n = *p + 1;
            *p = n;
            n
          }
          Entry::Vacant(e) => *e.insert(0),
        };
        *e.insert(n)
      }
    }
  }
  fn mangle<T>(&mut self, env: &Environment, tid: ThmID, f: impl FnOnce(&str, &str) -> T) -> T {
    let s = env.data[env.thms[tid].atom].name.as_str();
    match self.get(env, tid) {
      0 => f(s, s),
      n => f(s, &format!("{}.{}", s, n))
    }
  }
}

fn header(w: &mut impl Write, rel: &str, desc: &str, title: &str, h1: &str, nav: &str) -> io::Result<()> {
  writeln!(w, r#"<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <meta name="generator" content="mm0-doc">
  <meta name="description" content="{desc}">
  <meta name="keywords" content="mm0, metamath-zero">
  <title>{title} - Metamath Zero</title>
  <link rel="stylesheet" type="text/css" href="{rel}stylesheet.css" />
  <link rel="stylesheet" href="https://fonts.googleapis.com/css?family=Neuton&amp;subset=latin" type="text/css" media="screen" charset="utf-8">
  <link rel="stylesheet" href="https://fonts.googleapis.com/css?family=Nobile:regular,italic,bold,bolditalic&amp;subset=latin" type="text/css" media="screen" charset="utf-8">
  <!-- <link rel="shortcut icon" href="{rel}favicon.ico"> -->
</head>
<body>
  <div class="body">
    <h1 class="title">
      {h1}
      <span class="nav">{nav}</span>
    </h1>"#,
      rel = rel, desc = desc, title = title, h1 = h1, nav = nav)
}
const FOOTER: &'static str = "  </div>\n</body>\n</html>";

fn render_doc(w: &mut impl Write, doc: &Option<DocComment>) -> io::Result<()> {
  if let Some(doc) = doc {
    use pulldown_cmark::{Parser, html};
    write!(w, r#"    <div class="doc">"#)?;
    html::write_html(&mut *w, Parser::new(doc))?;
    writeln!(w, "</div>")?;
  }
  Ok(())
}

fn disambiguated_anchor(w: &mut impl Write, ad: &AtomData, sort: bool) -> io::Result<()> {
  match ad {
    AtomData {sort: Some(_), decl: Some(_), ..} if sort => write!(w, "{}.sort", ad.name),
    AtomData {sort: Some(_), decl: Some(DeclKey::Term(_)), ..} => write!(w, "{}.term", ad.name),
    AtomData {sort: Some(_), decl: Some(DeclKey::Thm(_)), ..} => write!(w, "{}.thm", ad.name),
    _ => write!(w, "{}", ad.name),
  }
}

impl<'a, W: Write> BuildDoc<'a, W> {
  fn thm_doc(&mut self, tid: ThmID) -> io::Result<()> {
    let mut file = self.thm_folder.to_owned();
    #[allow(clippy::useless_transmute)]
    let td: &Thm = unsafe { mem::transmute(&self.env.thms[tid]) };
    self.mangler.mangle(&self.env, tid, |_, s| file.push(&format!("{}.html", s)));
    let mut file = BufWriter::new(File::create(file)?);
    let kind = if let ThmKind::Axiom = td.kind {"Axiom"} else {"Theorem"};
    let ad = &self.env.data[td.atom];
    let thmname = &ad.name;
    let filename = td.span.file.rel();
    let mut nav = String::from("<a href=\"../index.html#");
    disambiguated_anchor(unsafe {nav.as_mut_vec()}, ad, true)?;
    nav.push_str("\">index</a>");
    if let Some(base) = &self.base_url {
      use std::fmt::Write;
      let url = base.join(filename).map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
      write!(&mut nav, " | <a href=\"{}", url).expect("writing to a string");
      let range = self.source.to_range(td.full);
      if range.start.line == range.end.line {
        write!(&mut nav, "#L{}\">src</a>", range.start.line + 1)
      } else {
        write!(&mut nav, "#L{}-L{}\">src</a>", range.start.line + 1, range.end.line + 1)
      }.expect("writing to a string");
    }
    header(&mut file, "../",
      &format!("Documentation for theorem `{}` in `{}`.", thmname, filename),
      &format!("{} - {}", thmname, filename),
      &format!(r#"{} <a class="thm" href="">{}</a>"#, kind, thmname),
      &nav)?;
    render_doc(&mut file, &td.doc)?;
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
          self.mangler.mangle(&self.env, self.axuse.0[i], |thm, mangled|
            write!(file, r#"    <a class="thm" href="{}.html">{}</a>"#, mangled, thm))?
        }
      }
      writeln!(file)?
    }
    writeln!(file, "{}", FOOTER)
  }

  fn write_all(&mut self, path: &FileRef, stmts: &[StmtTrace]) -> io::Result<()> {
    let file = self.index.as_mut().expect("index file missing");
    let nav: String;
    let nav = if let Some(base) = &self.base_url {
      let url = base.join(path.rel()).map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
      nav = format!("<a href=\"{}\">src</a>", url);
      &nav
    } else {""};
    header(file, "",
      &format!("Documentation index for `{}`.", path.rel()),
      &format!("{} - Index", path.rel()),
      "Index",
      nav)?;
    for s in stmts {
      use pulldown_cmark::escape::{escape_html, WriteWrapper};
      let mut file = self.index.as_mut().expect("index file missing");
      let fe = FormatEnv {source: self.source, env: &self.env};
      match *s {
        StmtTrace::Global(_) |
        StmtTrace::OutputString(_) => {}
        StmtTrace::Sort(a) => {
          let ad = &self.env.data[a];
          write!(file, "    <a name=\"")?;
          disambiguated_anchor(&mut file, ad, true)?;
          writeln!(file, "\"></a>")?;
          let sd = &self.env.sorts[ad.sort.expect("wf env")];
          render_doc(&mut file, &sd.doc)?;
          writeln!(file, "    <pre>{}</pre>", sd)?
        }
        StmtTrace::Decl(a) => {
          let ad = &self.env.data[a];
          write!(file, "    <a name=\"")?;
          disambiguated_anchor(&mut file, ad, false)?;
          writeln!(file, "\"></a>")?;
          match ad.decl.expect("wf env") {
            DeclKey::Term(tid) => {
              let td = &self.env.terms[tid];
              render_doc(&mut file, &td.doc)?;
              write!(file, "    <pre>")?;
              escape_html(WriteWrapper(&mut file), &format!("{}", fe.to(td)))?;
              writeln!(file, "</pre>")?;
            }
            DeclKey::Thm(tid) => {
              let td = &self.env.thms[tid];
              render_doc(&mut file, &td.doc)?;
              self.mangler.mangle(&self.env, tid, |name, mangled|
                write!(file, r#"    <pre>{}{} <a class="thm" href="thms/{mangled}.html">{name}</a>"#, td.vis,
                  if matches!(td.kind, ThmKind::Axiom) {"axiom"} else {"theorem"},
                  mangled = mangled, name = name))?;
              fe.pretty(|pr| -> io::Result<()> {
                let mut buf = String::new();
                pr.thm_headless(td, Pretty::nil()).render_fmt(PP_WIDTH, &mut buf)
                  .expect("writing to a string");
                escape_html(WriteWrapper(&mut file), &buf)
              })?;
              writeln!(file, "</pre>")?;
              self.thm_doc(tid)?
            }
          }
        }
      }
    }
    let file = self.index.as_mut().expect("index file missing");
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
  println!("writing docs");
  let mut env = Environment::new();
  env.merge(&old, (0..0).into(), &mut vec![]).expect("can't fail");
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
  let base_url = match args.value_of("src") {
    Some("-") => None,
    src => Some(Url::parse(src.unwrap_or("https://github.com/digama0/mm0/blob/master/examples/"))
      .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?),
  };
  let mut bd = BuildDoc {
    source: fc.ascii(),
    base_url,
    axuse: AxiomUse::new(&env),
    thm_folder: dir, env, index,
    mangler: Mangler::default(),
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