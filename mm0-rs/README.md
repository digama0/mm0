# mm0-rs

This is an alternative implementation of the MM1 server of [`mm0-hs`](../mm0-hs/README.md), written in Rust. `mm0-rs server` acts as an LSP server in the same way as `mm0-hs server`, which means that if you have the `vscode-mm0` extension installed, you can choose either program as your LSP server and it will provide live diagnostics, go to definition support, hovers and so on. It does not support all the other commands (yet!) like `mm0-hs verify` or `mm0-hs from-mm`, but it is much faster than the Haskell implementation as a language server while supporting similar features.

Watch this space for more updates, as `mm0-rs` is under active development. See [`mm1.md`](../mm0-hs/mm1.md) for a description of the MM1 specification, which is implemented by both `mm0-hs` and `mm0-rs`.

## Compilation

To compile `mm0-rs`, first install Rust.
You then need to download this repository (e.g.,
`git clone https://github.com/digama0/mm0.git`).
Then cd into this `mm0-rs` directory (using `cd mm0/mm0-rs`) and run:

    cargo build --release

You then should make it easy to execute.
One way is to copy or symlink the resulting executable file `target/release/mm0-rs` to your system path.
An alternative, if you're integrating with Visual Studio Code as suggested
below, is to point `vscode-mm0` to the executable using (as
explained below) the setting "metamath-zero.executablePath": "mm0-rs"
in your `settings.json` file.

## Integration with Visual Studio Code

We typically use Visual Studio Code, an open source software
editor / IDE which supports LSP servers.
If you choose to do the same,
[download and install Visual Studio Code](https://code.visualstudio.com/).

Select View/Extensions, search for "Metamath"
Look for "Metamath Zero" & press its "install" button.

If `mm0-rs` is not on your path, then you need to
change the Visual Studio Code settings so it can execute `mm0-rs`.
To do this, after you've installed "Metamath Zero" look at the name,
click on its small "gear symbol" to change its settings.
Note: if you click on its "gear symbol" and see nothing, that's a bug
in the Visual Studio Code program; restart it and again select View/Extensions
to you can see the settings to change them.
Now modify the "Metamath-zero Executable Path" setting (which corresponds
to `metamath-zero.executablePath` in `settings.json`)
to be the correct path for the executable
(it defaults to `mm0-rs`).
You should probably use an absolute path (e.g., one starting with "/"
on Linux/Unix/MacOS).

## Usage

The `mm0-rs` program provides a number of modes and options if you
want to invoke it directly. For example:

* `mm0-rs server` causes it to send and receive LSP server commands via stdin and stdout. This is not used directly from the CLI but rather is invoked by `vscode-mm0` when it is set up to use `mm0-rs` as a language server.
* `mm0-rs server --debug` is run by `vscode-mm0` when the extension itself is run in debugging mode, and this will enable backtraces and logging.
* `mm0-rs compile foo.mm1` will compile an MM1 file, reporting errors to the console. This is essentially the console version of the `server` mode.

You can easily use `mm0-rs` from within Visual Studio Code.
Start Visual Studio Code, then use File/Open,
and navigate to the mm0/examples directory.
Select a file to look at; `do-block.mm1` and `demo.mm1`
are good starting points.
Select "View/Problems" to see a summary.

File `demo.mm1` show what proofs look like in MM1.
A theorem proof looks like `theorem NAME: $ ... expression... $ =`
followed by an s-expression-like proof.
"(stat)" prints the current proof state.

There aren't too many fancy tactics right now unless you write them
yourself (in the manner of `norm_num`). If you want to keep moving
up the hierarchy of complexity, you can try to follow the first few
proofs in peano.mm1 (after the big do block, starting at theorem
a1i). It takes quite a while before the
proofs start getting complicated enough to need tactic mode (search
for "focus"), although the "named" tactic is used in lots of simpler
theorems to wrap a proof script to name dummy variables.

To create a disconnected step, you can use `have` in the form
`(have 'NAME $ EXPRESSION $ _)` and the _ will give you EXPRESSION
as the goal, which need not have anything to do with
what the current theorem is. You can use NAME to refer to the step later.

If you want to say "unify the goal with this expression" you
can use `{_ : $ EXPRESSION $}` and the _ will unify the goal against
EXPRESSION, which you can obtain by copy-pasting from the goal and
making modifications.
