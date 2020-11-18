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

#![warn(bare_trait_objects)]
#![warn(elided_lifetimes_in_paths)]
#![warn(missing_copy_implementations, missing_debug_implementations)]
#![warn(future_incompatible, rust_2018_idioms)]
#![warn(trivial_numeric_casts)]
#![warn(variant_size_differences)]
#![warn(unreachable_pub)]
#![warn(unused)]
#![warn(missing_docs)]
// #![warn(clippy::all, clippy::restriction, clippy::pedantic, clippy::nursery, clippy::cargo)]
#![allow(clippy::as_conversions, clippy::module_name_repetitions, clippy::multiple_crate_versions,
  clippy::implicit_return, clippy::missing_docs_in_private_items, clippy::pattern_type_mismatch,
  clippy::missing_const_for_fn, clippy::expect_used, clippy::use_self, clippy::integer_arithmetic,
  clippy::indexing_slicing, clippy::panic, clippy::wildcard_enum_match_arm, clippy::missing_errors_doc,
  clippy::shadow_unrelated, clippy::too_many_lines, clippy::clone_on_ref_ptr, clippy::unimplemented,
  clippy::let_underscore_must_use, clippy::default_trait_access, clippy::shadow_reuse)]

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
      (@arg no_proofs: -n --("no-proofs") "Disable proof checking until (check-proofs #t)")
      (@arg INPUT: +required "Sets the input file (.mm1 or .mm0)")
      (@arg OUTPUT: "Sets the output file (.mm1 or .mm0), or stdin if omitted")));

  #[cfg(feature = "server")]
  let app = clap_app!(@app (app)
    (@subcommand server =>
      (about: "MM1 LSP server")
      (@arg debug: -d --debug "Enable debug logging")
      (@arg no_log_errors: -q --quiet "Don't print errors in server output log")));

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
