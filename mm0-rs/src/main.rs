//! MM0 toolchain. See [`mm0-rs/README.md`] for overall documentation.
//!
//! ```
//! USAGE:
//! mm0-rs <SUBCOMMAND>
//!
//! FLAGS:
//!     -h, --help       Prints help information
//!     -V, --version    Prints version information
//!
//! SUBCOMMANDS:
//!     compile    Compile MM1 files into MMB
//!     help       Prints this message or the help of the given subcommand(s)
//!     join       Join MM1/MM0 files with imports by concatenation
//!     server     MM1 LSP server
//! ```
//!
//! [`mm0-rs/README.md`]: https://github.com/digama0/mm0/blob/master/mm0-rs/README.md

// rust lints we want
#![warn(bare_trait_objects, elided_lifetimes_in_paths,
  missing_copy_implementations, missing_debug_implementations, future_incompatible,
  rust_2018_idioms, trivial_numeric_casts, variant_size_differences, unreachable_pub,
  unused, missing_docs)]
// all the clippy
#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
// all the clippy::restriction lints we want
#![warn(clippy::else_if_without_else, clippy::float_arithmetic,
  clippy::get_unwrap, clippy::inline_asm_x86_att_syntax, clippy::integer_division,
  clippy::rc_buffer, clippy::rest_pat_in_fully_bound_structs,
  clippy::string_add, clippy::unwrap_used, clippy::wrong_pub_self_convention)]
// all the clippy lints we don't want
#![allow(clippy::cognitive_complexity, clippy::default_trait_access, clippy::filter_map,
  clippy::find_map, clippy::map_err_ignore, clippy::missing_const_for_fn,
  clippy::missing_errors_doc, clippy::module_name_repetitions,
  clippy::multiple_crate_versions, clippy::option_if_let_else, clippy::shadow_unrelated,
  clippy::too_many_lines, clippy::use_self)]

#[macro_use] extern crate bitflags;
#[macro_use] extern crate lazy_static;
#[macro_use] extern crate futures;
#[macro_use] extern crate deepsize_derive;
#[macro_use] extern crate debug_derive;

mod deepsize;
pub mod util;
pub mod lined_string;
pub mod parser;
#[cfg(feature = "server")]
#[macro_use] pub mod server;
pub mod compiler;
pub mod joiner;
pub mod elab;
/// Import and export functionality for MMB binary proof format
///
/// See [`mm0-c/verifier.c`] for information on the MMB format.
///
/// [`mm0-c/verifier.c`]: https://github.com/digama0/mm0/blob/master/mm0-c/verifier.c
pub mod mmb { pub mod export; }
/// Import and export functionality for MMU ascii proof format
///
/// See [The `.mmu` file format] for information on the MMU format.
///
/// [The `.mmu` file format]: https://github.com/digama0/mm0/blob/master/mm0-hs/README.md#the-mmu-file-format
pub mod mmu { pub mod import; pub mod export; }
pub mod mmc;

use std::sync::atomic::{AtomicBool, Ordering};
use clap::clap_app;

static CHECK_PROOFS: AtomicBool = AtomicBool::new(true);
pub(crate) fn get_check_proofs() -> bool { CHECK_PROOFS.load(Ordering::Relaxed) }

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
      (@arg output: -o --output [FILE] "Print 'output' commands to a file (use '-' to print to stdout)")
      (@arg INPUT: +required "Sets the input file (.mm1 or .mm0)")
      (@arg OUTPUT: "Sets the output file (.mmb or .mmu)"))
    (@subcommand join =>
      (about: "Join MM1/MM0 files with imports by concatenation")
      (@arg no_header: -h --("no-header") "Skip top header")
      (@arg bare: -b --("bare") "Don't add any comments")
      (@arg INPUT: +required "Sets the input file (.mm1 or .mm0)")
      (@arg OUTPUT: "Sets the output file (.mm1 or .mm0), or stdin if omitted")));

  #[cfg(feature = "server")]
  let app = clap_app!(@app (app)
    (@subcommand server =>
      (about: "MM1 LSP server")
      (@arg no_proofs: -n --("no-proofs") "Disable proof checking until (check-proofs #t)")
      (@arg debug: -d --debug "Enable debug logging")
      (@arg no_log_errors: -q --quiet "Don't print errors in server output log")
      (@arg elab_on: -e --("elab-on") [STRING] "apply changes & elab on [c]hange (default) or [s]ave")));

  let m = app.get_matches();

  match m.subcommand() {
    ("compile", Some(m)) => {
      if m.is_present("no_proofs") { CHECK_PROOFS.store(false, Ordering::Relaxed) }
      compiler::main(m)?
    }
    ("join", Some(m)) => joiner::main(m)?,
    #[cfg(feature = "server")]
    ("server", Some(m)) => {
      if m.is_present("no_proofs") { CHECK_PROOFS.store(false, Ordering::Relaxed) }
      server::main(m)
    }
    _ => unreachable!()
  }
  Ok(())
}
