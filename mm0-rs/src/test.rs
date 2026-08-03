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
    let (_, env) = elab_for_result(path.into()).expect("io failure");
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
    let (_, env) = elab_for_result(path.into()).expect("io failure");
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
  use std::fs;

  const A_SRC: &str = "\
strict provable sort wff;
term wi: wff > wff > wff; infixr wi: $->$ prec 25;
axiom ax_id: $ a -> a $;
do {
  (def (my-id x) x)
  (def (my-sum n) (if {n = 0} 0 {n + (my-sum {n - 1})}))
};
";

  const B_SRC: &str = "\
import \"a.mmb\";
do {
  (if {(my-id 7) = 7} #undef (error \"my-id did not survive the mmb round-trip\"))
  (if {(my-sum 4) = 10} #undef (error \"my-sum did not survive the mmb round-trip\"))
};
";

  #[test]
  fn lisp_env_through_mmb() {
    let dir = std::env::temp_dir().join(format!("mm0rs-mmb-dep-{}", std::process::id()));
    fs::create_dir_all(&dir).expect("create temp dir");
    let (dep_src, dep_mmb, main_src) =
      (dir.join("a.mm1"), dir.join("a.mmb"), dir.join("b.mm1"));
    fs::write(&dep_src, A_SRC).expect("write a.mm1");
    fs::write(&main_src, B_SRC).expect("write b.mm1");

    // Compile the dependency to `a.mmb`, index (and thus the `Lisp` table) included.
    Args { input: dep_src, output: Some(dep_mmb.clone()), quiet: true, ..<_>::default() }
      .main().expect("compile a.mm1");
    assert!(dep_mmb.exists(), "a.mmb was not written");

    // Compile the dependent: `import "a.mmb"` reads the dependency straight from the
    // `.mmb`, and the `do` block runs its lisp procedures. Any mismatch `error`s, which
    // `panic!`s the elaboration under `cfg(test)`.
    Args { input: main_src, quiet: true, ..<_>::default() }.main().expect("compile b.mm1");

    let _ = fs::remove_dir_all(&dir);
  }
}
