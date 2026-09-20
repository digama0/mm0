## Metamath Zero Explorer

These are the sources for the web site version of `mm0-rs`: a Monaco editor in
the browser, backed by `mm0-rs` compiled to WebAssembly, which elaborates as you
type and reports diagnostics live.

It follows the system light/dark preference until the toggle in the bar pins
one. The pin is stored under the key the homepage uses, and both are served
from the same origin, so a theme chosen on either applies to both.

### Building

Requires the wasm target and [`wasm-pack`](https://drager.github.io/wasm-pack/):

```sh
rustup target add wasm32-unknown-unknown
cargo install wasm-pack
npm install
```

Then:

```sh
npm start   # dev server, opens a browser
npm run build   # production build into dist/
```

`webpack` drives `wasm-pack` for you, so there is no separate wasm build step.
Note that `m0e` is a browser crate and cannot be built for the host: it is a
`cdylib` against `wasm-bindgen` and the `wasm32`-only parts of `mm0-rs`.
`.cargo/config.toml` defaults the target accordingly, so a bare `cargo build`
works and rust-analyzer sees the right configuration.

### How the files are loaded

There is no filesystem in the browser, so `mm0-rs` cannot read an `import`ed
file on demand. Instead `src/index.js` captures a snapshot of `../examples`
at build time and seeds every file into the VFS up front (`seed_file`), which
is what makes `import` resolve; only the file selected in the dropdown is
actually elaborated. Adding an example to `examples/` is enough to have it
appear -- the list is not written down anywhere.
