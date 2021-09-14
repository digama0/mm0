//! MM0 toolchain. See [`mm0-rs/README.md`] for overall documentation.
//!
//! ```text
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
#![warn(clippy::float_arithmetic,
  clippy::get_unwrap, clippy::inline_asm_x86_att_syntax, clippy::integer_division,
  clippy::rc_buffer, clippy::rest_pat_in_fully_bound_structs,
  clippy::string_add, clippy::unwrap_used)]
// all the clippy lints we don't want
#![allow(clippy::cognitive_complexity, clippy::comparison_chain,
  clippy::default_trait_access, clippy::enum_glob_use, clippy::inline_always,
  clippy::manual_map, clippy::map_err_ignore, clippy::missing_const_for_fn,
  clippy::missing_errors_doc, clippy::missing_panics_doc, clippy::module_name_repetitions,
  clippy::multiple_crate_versions, clippy::option_if_let_else, clippy::redundant_pub_crate,
  clippy::semicolon_if_nothing_returned, clippy::shadow_unrelated, clippy::too_many_lines,
  clippy::use_self)]

#[macro_use] extern crate lazy_static;
#[macro_use] extern crate futures;
#[macro_use] extern crate debug_derive;
#[macro_use] extern crate mm0_util;

#[cfg(feature = "mmc")]
#[macro_use] extern crate if_chain;

#[cfg(feature = "memory")]
#[macro_use] extern crate mm0_deepsize;

#[cfg(feature = "memory")]
pub use mm0_deepsize::deep_size_0;

#[cfg(not(feature = "memory"))]
/// A macro to generate an impl for types with no inner allocation.
#[macro_export] macro_rules! deep_size_0 {($($e:tt)*) => {}}

#[cfg(feature = "server")]
#[macro_use] pub mod server;
pub mod compiler;
pub mod joiner;
pub mod elab;
#[cfg(feature = "doc")]
pub mod doc;
/// Import and export functionality for MMB binary proof format
///
/// See [`mm0-c/verifier.c`] for information on the MMB format.
///
/// [`mm0-c/verifier.c`]: https://github.com/digama0/mm0/blob/master/mm0-c/verifier.c
pub mod mmb { pub mod export; pub mod import; }
/// Import and export functionality for MMU ascii proof format
///
/// See [The `.mmu` file format] for information on the MMU format.
///
/// [The `.mmu` file format]: https://github.com/digama0/mm0/blob/master/mm0-hs/README.md#the-mmu-file-format
pub mod mmu { pub mod import; pub mod export; }
#[cfg(feature = "mmc")]
pub mod mmc;

use std::sync::atomic::{AtomicBool, Ordering};

pub use elab::{environment::*,
  frozen::{FrozenAtomData, FrozenEnv, FrozenLispKind, FrozenLispVal},
  lisp::{self, debug::EnvDebug, print::{EnvDisplay, FormatEnv}, LispKind, LispVal, Uncons},
  local_context::{try_get_span, LocalContext},
  ElabError, Elaborator};
pub use mm0_util::*;
pub use mm1_parser::{ast, DocComment, ErrorLevel};
pub use mm0b_parser::MAX_BOUND_VARS;

static CHECK_PROOFS: AtomicBool = AtomicBool::new(true);
pub(crate) fn get_check_proofs() -> bool { CHECK_PROOFS.load(Ordering::Relaxed) }

/// Set the initial proof checking behavior at the start of an MM1 file
/// before a `(check-proofs)` command is found.
pub fn set_check_proofs(b: bool) { CHECK_PROOFS.store(b, Ordering::Relaxed) }
