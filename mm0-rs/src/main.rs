extern crate log;
#[macro_use] extern crate bitflags;
#[macro_use] extern crate lazy_static;
#[macro_use] extern crate futures;

mod util;
mod lined_string;
mod parser;
#[macro_use] mod server;
mod compiler;
mod joiner;
mod elab;
/// Import and export functionality for MMB binary proof format
///
/// See [`mm0-c/verifier.c`] for information on the MMB format.
///
/// [`mm0-c/verifier.c`]: https://github.com/digama0/mm0/blob/master/mm0-c/verifier.c
mod mmb { pub mod export; }
/// Import and export functionality for MMU ascii proof format
///
/// See [The `.mmu` file format] for information on the MMU format.
///
/// [The `.mmu` file format]: https://github.com/digama0/mm0/blob/master/mm0-hs/README.md#the-mmu-file-format
mod mmu { pub mod import; pub mod export; }
mod mmc;

use clap::clap_app;

fn main() -> std::io::Result<()> {
  let m = clap_app!(mm0_rs =>
    (name: "mm0-rs")
    (version: "0.1")
    (author: "Mario Carneiro <mcarneir@andrew.cmu.edu>")
    (about: "MM0 toolchain")
    (@setting InferSubcommands)
    (@setting SubcommandRequiredElseHelp)
    (@setting VersionlessSubcommands)
    (@subcommand server =>
      (about: "MM1 LSP server")
      (@arg debug: -d --debug "Enable debug logging"))
    (@subcommand compile =>
      (about: "Compile MM1 files into MMB")
      (@arg INPUT: +required "Sets the input file (.mm1 or .mm0)")
      (@arg OUTPUT: "Sets the output file (.mmb or .mmu)"))
    (@subcommand join =>
      (about: "Join MM1/MM0 files with imports by concatenation")
      (@arg INPUT: +required "Sets the input file (.mm1 or .mm0)")
      (@arg OUTPUT: "Sets the output file (.mm1 or .mm0), or stdin if omitted")))
    .get_matches();

  match m.subcommand() {
    ("server", Some(m)) => Ok(server::main(m)),
    ("compile", Some(m)) => Ok(compiler::main(m)?),
    ("join", Some(m)) => Ok(joiner::main(m)?),
    _ => unreachable!()
  }
}
