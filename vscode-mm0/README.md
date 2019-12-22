# Metamath Zero

This extension provides support for the verification and specification language [Metamath Zero](http://github.com/digama0/mm0). Syntax highlighting is available out of the box, and if [`mm0-hs`](http://github.com/digama0/mm0/tree/master/mm0-hs) is installed, it will use the `mm0-hs server` LSP server to provide additional features.

## Installation

The extension is available on the VSCode marketplace, under the code `digama0.metamath-zero`.

To install from source, run `npm run compile` from the `vscode-mm0` directory, then copy or symlink the directory to `~/.vscode/extensions/vscode-mm0/`.

## Requirements

Requires [`mm0-hs`](http://github.com/digama0/mm0/tree/master/mm0-hs), which can be built and installed using:

    stack build mm0-hs
    stack install

## Release Notes

### 1.0.0

Initial release
