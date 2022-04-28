
use clap::clap_app;

fn main() -> std::io::Result<()> {
  let app = clap_app!(mm0_rs =>
    (name: "mm0-rs")
    (version: "0.1")
    (author: "Mario Carneiro <mcarneir@andrew.cmu.edu>")
    (about: "MM0 toolchain")
    (@setting InferSubcommands)
    (@setting SubcommandRequiredElseHelp)
    (@setting VersionlessSubcommands)
    (@subcommand compile =>
      (about: "Compile MM1 files into MMB")
      (@arg no_proofs: -n --("no-proofs") "Disable proof checking until (check-proofs #t)")
      (@arg check_parens: --("warn-unnecessary-parens") "Warn on unnecessary parentheses")
      (@arg quiet: -q --quiet "Hide diagnostic messages")
      (@arg strip: -s --("strip") "Don't add debugging data to .mmb files")
      (@arg output: -o --output [FILE]
        "Print 'output' commands to a file (use '-' to print to stdout)")
      (@arg INPUT: +required "Sets the input file (.mm1 or .mm0)")
      (@arg OUTPUT: "Sets the output file (.mmb or .mmu)"))
    (@subcommand join =>
      (about: "Join MM1/MM0 files with imports by concatenation")
      (@arg no_header: -h --("no-header") "Skip top header")
      (@arg bare: -b --("bare") "Don't add any comments")
      (@arg INPUT: +required "Sets the input file (.mm1 or .mm0)")
      (@arg OUTPUT: "Sets the output file (.mm1 or .mm0), or stdin if omitted"))
    (@subcommand doc =>
      (about: "Build documentation pages")
      (@arg INPUT: +required "Sets the input file (.mm1 or .mm0)")
      (@arg OUTPUT: "Sets the output folder, or 'doc' if omitted")
      (@arg only: --only [THMS] +use_delimiter
        "Show only declarations THMS (a comma separated list)")
      (@arg open: --open "Open the generated documentation in a browser")
      (@arg open_to: --("open-to") [THM] "Open a particular generated page (implies --open)")
      (@arg order: --("order") [ORDER]
         possible_values(&["pre", "post"]) default_value("post")
         "Proof tree traversal order")
      (@arg src: --src [URL] "Use URL as the base for source doc links (use - to disable)")));

  #[cfg(feature = "server")]
  let app = clap_app!(@app (app)
    (@subcommand server =>
      (about: "MM1 LSP server")
      (@arg no_proofs: -n --("no-proofs") "Disable proof checking until (check-proofs #t)")
      (@arg check_parens: --("warn-unnecessary-parens") "Warn on unnecessary parentheses")
      (@arg debug: -d --debug "Enable debug logging")
      (@arg no_log_errors: -q --quiet "Don't print errors in server output log")));

  let m = app.get_matches();

  match m.subcommand() {
    ("compile", Some(m)) => {
      if m.is_present("no_proofs") { mm0_rs::set_check_proofs(false) }
      if m.is_present("check_parens") { mm0_rs::set_check_parens(true) }
      mm0_rs::compiler::main(m)?
    }
    ("join", Some(m)) => mm0_rs::joiner::main(m)?,
    #[cfg(feature = "doc")]
    ("doc", Some(m)) => mm0_rs::doc::main(m)?,
    #[cfg(feature = "server")]
    ("server", Some(m)) => {
      if m.is_present("no_proofs") { mm0_rs::set_check_proofs(false) }
      if m.is_present("check_parens") { mm0_rs::set_check_parens(true) }
      mm0_rs::server::main(m)
    }
    _ => unreachable!()
  }
  Ok(())
}
