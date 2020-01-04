# mm0-rs

This is an alternative implementation of the MM1 server of [`mm0-hs`](../mm0-hs/README.md), written in Rust. `mm0-rs server` acts as an LSP server in the same way as `mm0-hs server`, which means that if you have the `vscode-mm0` extension installed, you can choose either program as your LSP server and it will provide live diagnostics, go to definition support, hovers and so on. It does not support all the other commands (yet!) like `mm0-hs verify` or `mm0-hs from-mm`, but it is much faster than the Haskell implementation as a language server while supporting similar features.

Watch this space for more updates, as `mm0-rs` is under active development. See [`mm1.md`](`mm0-hs/mm1.md`) for a description of the MM1 specification, which is implemented by both `mm0-hs` and `mm0-rs`.

## Compilation

To compile `mm0-rs`, run

    cargo build --release

from the `mm0-rs` directory, then copy or symlink the resulting executable file `target/release/mm0-rs` to your system path and/or point `vscode-mm0` to it using the setting

  "metamath-zero.executablePath": "mm0-rs",

in your `settings.json` file.