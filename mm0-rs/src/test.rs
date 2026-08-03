use std::path::Path;
use crate::compiler;
use test_each_file::test_each_path;

fn compile_mm1([input]: [&Path; 1]) {
  compiler::Args { input: input.to_owned(), ..<_>::default() }.main().expect("IO failure")
}

test_each_path! { for ["mm1"] in "../tests/mm1/pass" => compile_mm1 }

/// Round-trip the `Nota` index table: elaborate an `.mm1`, export it to an mmb in
/// memory, read the notation table back, and check it reproduces the notations the
/// elaborator's own [`ParserEnv`](crate::ParserEnv) holds — which is what MM1
/// prints with. See the "Nota" section of `mm0-c/mmb.md`.
mod nota_roundtrip {
  use crate::{
    FrozenEnv, Literal, Prec, TermId, ErrorLevel,
    compiler::elab_for_result,
    mmb::export::{Exporter, BigBuffer},
  };
  use mm0b_parser::{BasicMmbFile, NotaLit};

  /// A precedence in a form that compares equal regardless of which side produced
  /// it. The three cases are genuinely distinct: the outer `None` is a precedence
  /// that would not fit the table's `u16` (it can never occur in practice, and the
  /// exporter drops the whole notation if it does — so the reference must drop it
  /// too), the inner `None` is `max`, and `Some(Some(n))` is a finite precedence.
  #[allow(clippy::option_option)]
  fn prec(p: Prec) -> Option<Option<u32>> {
    match p {
      Prec::Max => Some(None),
      Prec::Prec(n) => u16::try_from(n).ok().filter(|&n| n != u16::MAX).map(|n| Some(n.into())),
    }
  }

  /// A notation flattened to a comparable form: `(term, prec, literals)`, with each
  /// literal either a constant token or `(arg index, precedence)`. A coercion is the
  /// empty literal list.
  type Canon = (u32, Option<u32>, Vec<Lit>);
  #[derive(PartialEq, Eq, Debug)]
  enum Lit { Const(String), Var(u8, Option<u32>) }

  /// The notations the elaborator holds, in the order and form the exporter should
  /// have written them: one per notation, coercion first for a term that has one,
  /// with a prefix's leading constant spelled back into the literal list.
  fn expected(env: &FrozenEnv) -> Vec<Canon> {
    let pe = env.pe();
    let mut out = vec![];
    for i in 0..env.terms().len() {
      #[allow(clippy::cast_possible_truncation)]
      let tid = TermId(i as u32);
      let Some((coe, fix)) = pe.decl_nota.get(&tid) else { continue };
      if *coe { out.push((tid.0, None, vec![])) }
      'nota: for (tk, infix) in fix {
        let info = if *infix { &pe.infixes[tk] } else { &pe.prefixes[tk] };
        // `None` here is `max`, a perfectly good prefix precedence (numerals, `T.`,
        // set-builder `{|}`); only a genuinely unrepresentable one skips.
        let Some(p) = prec(pe.consts[tk].1) else { continue };
        let mut lits = vec![];
        if !*infix { lits.push(Lit::Const(String::from_utf8_lossy(tk).into_owned())) }
        for lit in &info.lits {
          match *lit {
            Literal::Const(ref s) =>
              lits.push(Lit::Const(String::from_utf8_lossy(s).into_owned())),
            Literal::Var(idx, vp) => match (u8::try_from(idx), prec(vp)) {
              (Ok(idx), Some(vp)) => lits.push(Lit::Var(idx, vp)),
              // Unrepresentable: the exporter drops the whole notation, so skip it.
              _ => continue 'nota,
            },
          }
        }
        if u8::try_from(lits.len()).is_ok() { out.push((tid.0, p, lits)) }
      }
    }
    out
  }

  /// The notations as read back out of a freshly exported mmb.
  fn actual(env: &FrozenEnv) -> Vec<Canon> {
    let path = crate::FileRef::from(std::path::PathBuf::from("test.mmb"));
    let mut buf = vec![];
    {
      let mut report = |_: ErrorLevel, _: &str| {};
      let mut ex = Exporter::new(path, None, env, &mut report, BigBuffer::new(&mut buf));
      ex.run(true).expect("export failed");
      ex.finish().expect("export finish failed");
    }
    let file = BasicMmbFile::parse(&buf).expect("the exported mmb should parse");
    file.notations().expect("the mmb should have a Nota table").map(|n| {
      let lits = n.lits().map(|l| match l {
        NotaLit::Const(s) => Lit::Const(s.to_owned()),
        NotaLit::Var { idx, prec: p } => Lit::Var(idx, prec(p).expect("stored precedence")),
      }).collect();
      (n.term.0, prec(n.prec).expect("stored precedence"), lits)
    }).collect()
  }

  // The `mm1_parser` test fixture, a self-contained peano with prefixes, infixes
  // and general `notation`s of every shape — including tokens long enough to reach
  // the overflow area. It is not one of the live example files, which are tested
  // elsewhere.
  #[test]
  fn peano() {
    let path = std::fs::canonicalize("components/mm1_parser/test_resources/peano.mm1")
      .expect("fixture missing");
    let (_, env) = elab_for_result(path.into(), false).expect("io failure");
    let env = env.expect("elaboration failed");
    assert_eq!(expected(&env), actual(&env), "notation round-trip mismatch");
  }
}

/// The `Delm` index table survives a round trip through the exporter and reader:
/// the delimiter bytes read back out of a freshly exported mmb equal the ones the
/// elaborator holds.
mod delim_roundtrip {
  use crate::{
    ErrorLevel, FrozenEnv,
    compiler::elab_for_result,
    mmb::export::{BigBuffer, Exporter},
  };
  use mm0b_parser::BasicMmbFile;

  /// The `(left, right)` delimiter bytes the elaborator holds. Walking `0..=255`
  /// yields them ascending, so the two sides compare without sorting.
  fn expected(env: &FrozenEnv) -> (Vec<u8>, Vec<u8>) {
    let pe = env.pe();
    let left = (0..=u8::MAX).filter(|&c| pe.delims_l.get(c)).collect();
    let right = (0..=u8::MAX).filter(|&c| pe.delims_r.get(c)).collect();
    (left, right)
  }

  /// The delimiter bytes read back out of a freshly exported mmb.
  fn actual(env: &FrozenEnv) -> (Vec<u8>, Vec<u8>) {
    let path = crate::FileRef::from(std::path::PathBuf::from("test.mmb"));
    let mut buf = vec![];
    {
      let mut report = |_: ErrorLevel, _: &str| {};
      let mut ex = Exporter::new(path, None, env, &mut report, BigBuffer::new(&mut buf));
      ex.run(true).expect("export failed");
      ex.finish().expect("export finish failed");
    }
    let file = BasicMmbFile::parse(&buf).expect("the exported mmb should parse");
    let d = file.delimiters().expect("the mmb should have a Delm table");
    (d.left().to_vec(), d.right().to_vec())
  }

  #[test]
  fn peano() {
    let path = std::fs::canonicalize("components/mm1_parser/test_resources/peano.mm1")
      .expect("fixture missing");
    let (_, env) = elab_for_result(path.into(), false).expect("io failure");
    let env = env.expect("elaboration failed");
    let (el, er) = expected(&env);
    let (al, ar) = actual(&env);
    assert_eq!((&el, &er), (&al, &ar), "delimiter round-trip mismatch");
    // Ground truth, so the round trip is not passing vacuously on two empty sets:
    // peano's openers (and `~`) split after them, its closers split before them.
    assert_eq!(al, b"([{~".to_vec(), "peano's left delimiters");
    assert_eq!(ar, b"),]}".to_vec(), "peano's right delimiters");
  }
}

/// A multi-file build where the dependency's whole environment — sorts, terms, and the
/// global lisp definitions — travels through an `.mmb` on disk instead of the in-memory
/// `FrozenEnv` merge path. `a.mm1` defines lisp procedures (including a recursive one
/// that references itself by name, plus builtin arithmetic); it is compiled to `a.mmb`
/// with its debug index. `b.mm1` then `import`s that `.mmb` and *runs* those procedures,
/// erroring if a reconstructed closure computes the wrong result. Because an
/// elaboration error `panic!`s under `cfg(test)`, a faithful mmb round-trip of the lisp
/// environment is exactly what lets this test pass.
mod mmb_dependency {
  use crate::compiler::Args;
  use std::{fs, path::PathBuf};

  /// A dependency defining lisp procedures: a plain one and a recursive one that
  /// references itself by name and uses builtin arithmetic.
  const A_SRC: &str = "\
strict provable sort wff;
term wi: wff > wff > wff; infixr wi: $->$ prec 25;
axiom ax_id: $ a -> a $;
do {
  (def (my-id x) x)
  (def (my-sum n) (if {n = 0} 0 {n + (my-sum {n - 1})}))
};
";

  /// A dependent that `import`s `a` and *runs* its procedures, `error`ing (hence, under
  /// `cfg(test)`, panicking) if a reconstructed closure computes the wrong result. `{dep}`
  /// is the import target (`a.mmb` for a direct mmb import, `a.mm1` for the cache path).
  fn b_src(dep: &str) -> String {
    format!("import \"{dep}\";
do {{
  (if {{(my-id 7) = 7}} #undef (error \"my-id was not reconstructed\"))
  (if {{(my-sum 4) = 10}} #undef (error \"my-sum was not reconstructed\"))
}};
")
  }

  /// A fresh, empty temp directory unique to this test.
  fn tmp(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("mm0rs-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create temp dir");
    dir
  }

  /// The dependency's whole environment — sorts, terms, and the global lisp definitions
  /// — travels through an explicit `.mmb` import instead of the in-memory `FrozenEnv`
  /// merge path. `b.mm1` `import`s `a.mmb` directly and runs its procedures.
  #[test]
  fn lisp_env_through_mmb() {
    let dir = tmp("mmb-dep");
    let (a, a_mmb, b) = (dir.join("a.mm1"), dir.join("a.mmb"), dir.join("b.mm1"));
    fs::write(&a, A_SRC).expect("write a.mm1");
    fs::write(&b, b_src("a.mmb")).expect("write b.mm1");

    // Compile the dependency to `a.mmb`, index (and thus the `Lisp` table) included.
    Args { input: a, output: Some(a_mmb.clone()), quiet: true, ..<_>::default() }
      .main().expect("compile a.mm1");
    assert!(a_mmb.exists(), "a.mmb was not written");
    Args { input: b, quiet: true, ..<_>::default() }.main().expect("compile b.mm1");
    let _ = fs::remove_dir_all(&dir);
  }

  /// `--cache` records each build's *transitive* source closure in the `.mmb`'s `Deps`
  /// table. `c` imports `b` imports `a`; `c` never names `a`, yet `a.mm1` must appear in
  /// `c.mmb`'s dependency list (and `c` still runs `a`'s procedures, via the transitive
  /// merge). This is what makes the freshness check sound across transitive edits.
  #[test]
  fn cache_records_transitive_deps() {
    use crate::mmb::import::read_deps;
    let dir = tmp("cache-deps");
    let (a, b, c) = (dir.join("a.mm1"), dir.join("b.mm1"), dir.join("c.mm1"));
    fs::write(&a, A_SRC).expect("write a.mm1");
    fs::write(&b, "import \"a.mm1\";\n").expect("write b.mm1");
    fs::write(&c, b_src("b.mm1")).expect("write c.mm1");

    Args { input: c, quiet: true, cache: true, ..<_>::default() }.main().expect("compile c.mm1");
    // Paths are stored relative to `c.mmb`'s directory; here every fixture is a sibling.
    let deps = read_deps(&dir.join("c.mmb")).expect("c.mmb should carry a Deps table");
    assert!(deps.contains(&PathBuf::from("a.mm1")), "transitive dependency a.mm1 not recorded: {deps:?}");
    assert!(deps.contains(&PathBuf::from("b.mm1")), "direct dependency b.mm1 not recorded: {deps:?}");
    let _ = fs::remove_dir_all(&dir);
  }

  /// Notations must survive the cache: a dependency's `Nota` and `Delm` tables are read
  /// back into the dynamic parser, so a dependent can still parse math strings using
  /// them. The *chained* infix `a -> a -> a` additionally requires the notation's
  /// associativity, which is recovered from the literals' precedences.
  #[test]
  fn cache_preserves_notation() {
    let dir = tmp("cache-nota");
    let (a, a_mmb, b) = (dir.join("a.mm1"), dir.join("a.mmb"), dir.join("b.mm1"));
    fs::write(&a, A_SRC).expect("write a.mm1");
    Args { input: a, quiet: true, cache: true, ..<_>::default() }.main().expect("prime a.mmb");
    let primed = fs::metadata(&a_mmb).expect("a.mmb").modified().expect("mtime");

    // `->`, its precedence and its associativity come only from `a`, loaded from `a.mmb`.
    fs::write(&b, "import \"a.mm1\";\naxiom ax2: $ a -> a -> a $;\n").expect("write b.mm1");
    Args { input: b, quiet: true, cache: true, ..<_>::default() }.main().expect("compile b.mm1");
    assert_eq!(fs::metadata(&a_mmb).expect("a.mmb").modified().expect("mtime"), primed,
      "a.mmb was rewritten, so the notation did not come from the cache");
    let _ = fs::remove_dir_all(&dir);
  }

  /// `--cache`: an import whose sibling `.mmb` is fresh is loaded from the cache, and the
  /// dependency is not rebuilt. We prime `a.mmb`, then build `b` (which imports `a.mm1`)
  /// and check `a.mmb` was left untouched — a rebuild would have rewritten it.
  #[test]
  fn cache_hit_skips_rebuild() {
    let dir = tmp("cache-hit");
    let (a, a_mmb, b) = (dir.join("a.mm1"), dir.join("a.mmb"), dir.join("b.mm1"));
    fs::write(&a, A_SRC).expect("write a.mm1");
    Args { input: a, quiet: true, cache: true, ..<_>::default() }.main().expect("prime a.mmb");
    let primed = fs::metadata(&a_mmb).expect("a.mmb").modified().expect("mtime");

    fs::write(&b, b_src("a.mm1")).expect("write b.mm1");
    Args { input: b, quiet: true, cache: true, ..<_>::default() }.main().expect("compile b.mm1");
    assert_eq!(fs::metadata(&a_mmb).expect("a.mmb").modified().expect("mtime"), primed,
      "a.mmb was rewritten, so the fresh cache was not used");
    let _ = fs::remove_dir_all(&dir);
  }

  /// `read_deps` seeks through a file it did not write, sizing an allocation from a count
  /// stored in it, so every malformed shape must decline rather than panic or allocate
  /// wildly. A `None` here is the safe answer: the caller treats it as "not a cache".
  #[test]
  fn read_deps_rejects_malformed() {
    use crate::mmb::import::read_deps;
    let dir = tmp("deps-malformed");
    fs::create_dir_all(&dir).expect("mkdir");
    let mut hdr = vec![0u8; 40];
    let idx = |h: &mut Vec<u8>, p: u64| h[32..40].copy_from_slice(&p.to_le_bytes());
    let cases: Vec<(&str, Vec<u8>)> = vec![
      ("empty", vec![]),
      ("shorter than the header", vec![0; 20]),
      ("p_index = 0 (no index)", hdr.clone()),
      ("p_index past EOF", { idx(&mut hdr, 1 << 40); hdr.clone() }),
      // A 16-entry index claimed at 40, but the file stops there: the `avail` bound must
      // reject it before `vec![0; count * 16]`.
      ("index count past EOF", { idx(&mut hdr, 40); let mut h = hdr.clone();
        h.extend_from_slice(&16u64.to_le_bytes()); h }),
      // The count is `u64::MAX`, so `count * 16` overflows; `checked_mul` must catch it.
      ("index count overflows", { idx(&mut hdr, 40); let mut h = hdr.clone();
        h.extend_from_slice(&u64::MAX.to_le_bytes()); h }),
      // `2^40` entries does not overflow, so only the `avail` bound stops this from
      // sizing a 16 TiB `Vec` off a number read out of a 48 byte file.
      ("index count absurd but not overflowing", { idx(&mut hdr, 40); let mut h = hdr.clone();
        h.extend_from_slice(&(1u64 << 40).to_le_bytes()); h }),
      // A well-formed `Deps` entry whose path list is truncated: no NUL terminator.
      ("truncated path list", { idx(&mut hdr, 40); let mut h = hdr;
        h.extend_from_slice(&1u64.to_le_bytes());                 // one index entry
        h.extend_from_slice(mm0b_parser::cmd::INDEX_DEP.as_slice());
        h.extend_from_slice(&0u32.to_le_bytes());
        h.extend_from_slice(&64u64.to_le_bytes());                // ptr to the list
        h.resize(64, 0);
        h.extend_from_slice(&2u64.to_le_bytes());                 // claims two paths
        h.extend_from_slice(b"a.mm1\0b.mm1");                     // second unterminated
        h }),
    ];
    for (name, bytes) in cases {
      let p = dir.join("t.mmb");
      fs::write(&p, &bytes).expect("write fixture");
      assert_eq!(read_deps(&p), None, "malformed .mmb accepted: {name}");
    }
    assert_eq!(read_deps(&dir.join("nonexistent.mmb")), None, "missing file accepted");
    let _ = fs::remove_dir_all(&dir);
  }
}
