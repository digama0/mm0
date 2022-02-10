# MM0/MM1 tutorial

These are the files for the Youtube [MM0/MM1 tutorial](https://www.youtube.com/watch?v=A7WfrW7-ifw).
The timestamps are approximately where each file first appears in the video.

1. [Installing MM0](01-installation.mm0) 00:00
2. [Introduction to MM0](02-mm0-intro.mm0) 01:55
3. [Introduction to MM1](03-mm1-intro.mm1) 08:31
4. [Advanced MM1 features](04-mm1-features.mm1) 20:15

Installation:
* Get VS Code (https://code.visualstudio.com/)
* Get the vscode extension (search for metamath-zero in the marketplace)
* Get mm0-rs
  * Get Rust (https://rustup.rs/)
  * Go to mm0-rs/ directory
  * Run `cargo build --release`
  * Copy `mm0-rs/target/release/mm0-rs` to your system PATH
    * or set "Metamath-zero: Executable Path" in vscode settings
