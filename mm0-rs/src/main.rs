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
mod vfs;
mod elab;
mod mmb { pub mod export; }
mod mmu { pub mod import; pub mod export; }

use std::{env, io};

fn main() -> io::Result<()> {
  let mut args = env::args().skip(1);
  match args.next().expect("expected a subcommand").as_str() {
    "server" => Ok(server::main(args)),
    "compile" => Ok(compiler::main(args)?),
    "join" => Ok(joiner::main(args)?),
    _ => panic!("incorrect subcommand, expected {server, compile, join}")
  }
}
