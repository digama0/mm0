extern crate log;
#[macro_use] extern crate bitflags;
#[macro_use] extern crate lazy_static;
#[macro_use] extern crate futures;

mod util;
mod lined_string;
mod parser;
#[macro_use] mod server;
mod compiler;
mod vfs;
mod elab;

use std::{env, io};

fn main() -> io::Result<()> {
  let mut args = env::args().skip(1);
  match args.next().expect("expected a subcommand").as_str() {
    "server" => Ok(server::main(args)),
    "compile" => Ok(compiler::main(args)?),
    _ => panic!("incorrect subcommand, expected {server}")
  }
}
