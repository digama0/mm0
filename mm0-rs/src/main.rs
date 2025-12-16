use clap::Parser;

#[derive(Parser)]
#[clap(version, author, about)]
#[clap(infer_subcommands = true)]
#[clap(subcommand_required = true)]
#[clap(arg_required_else_help = true)]
enum Cli {
  Compile(mm0_rs::compiler::Args),
  Join(mm0_rs::joiner::Args),
  Doc(mm0_rs::doc::Args),
  #[cfg(feature = "server")]
  Server(mm0_rs::server::Args),
}

fn main() -> std::io::Result<()> {
  match Cli::parse() {
    Cli::Compile(args) => {
      if args.no_proofs { mm0_rs::set_check_proofs(false) }
      if args.check_parens { mm0_rs::set_check_parens(true) }
      args.main()
    }
    Cli::Join(args) => args.main(),
    Cli::Doc(args) => args.main(),
    #[cfg(feature = "server")]
    Cli::Server(args) => {
      if args.no_proofs { mm0_rs::set_check_proofs(false) }
      if args.check_parens { mm0_rs::set_check_parens(true) }
      args.main();
      Ok(())
    }
  }
}
