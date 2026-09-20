const path = require("path");
const webpack = require("webpack");
const CopyPlugin = require("copy-webpack-plugin");
const WasmPackPlugin = require("@wasm-tool/wasm-pack-plugin");
const MonacoWebpackPlugin = require('monaco-editor-webpack-plugin');

const dist = path.resolve(__dirname, "dist");
const examples = path.resolve(dist, "examples");

// Where the "open in explorer" handoff navigates to. The editor and the MMB
// proof explorer are separate apps under one origin (the handoff goes through a
// per-origin IndexedDB store, so any same-origin path works); a full site
// deploys them as siblings and sets this to e.g. `../mmb/`. It is optional and
// has no default: with M0E_EXPLORER_URL unset there is no explorer to hand off
// to, so the button is dropped entirely (see src/index.js). A trailing slash is
// added when the value is set. The explorer is never copied into this bundle.
const explorerUrl = process.env.M0E_EXPLORER_URL
  ? process.env.M0E_EXPLORER_URL.replace(/\/?$/, "/")
  : null;

module.exports = {
  mode: "production",
  // mode: "development",
  entry: {
    index: "./src/index.js"
  },
  output: {
    path: dist,
    filename: "[name].js",
    // Drops stale hashed assets from previous builds. Doing this here rather
    // than with `rimraf dist` means it happens only for a build that writes to
    // dist -- `webpack serve` keeps its output in memory and never does.
    clean: true
  },
  module: {
    rules: [{
      test: /\.css$/,
      use: ['style-loader', 'css-loader']
    }, {
      test: /\.ttf$/,
      use: ['file-loader']
    }, {
      test: /\.(mm0|mm1|mmu)$/,
      use: ['raw-loader']
    }, {
      test: /\.wasm$/,
      type: 'webassembly/sync',
    }]
  },
  performance: {
    hints: false,
    maxEntrypointSize: 5000000,
    maxAssetSize: 5000000
  },
  experiments: {
    syncWebAssembly: true
  },
  plugins: [
    new CopyPlugin({
      patterns: [
        "static",
        { from: "../examples/*.mm0", to: examples },
        { from: "../examples/*.mm1", to: examples },
        { from: "../examples/*.mmu", to: examples },
      ]
    }),

    // The explorer handoff target, frozen into the bundle so index.js can build
    // its navigation URL (or `null` to drop the feature). Not read from
    // process.env at runtime -- there is no process in the browser; DefinePlugin
    // substitutes the literal at build.
    new webpack.DefinePlugin({
      "process.env.EXPLORER_URL": JSON.stringify(explorerUrl),
    }),

    // `M0E_FAST=1` passes `--no-opt`, which skips wasm-opt. wasm-pack runs it on
    // every build with no cache of its own and it is three to five minutes of
    // the wall clock; the cost of skipping is a wasm about a quarter larger,
    // which matters for a deploy and not at all for a local preview.
    // It goes in `extraArgs`, not `args`: the plugin puts `args` before the
    // `build` subcommand, where a build option is not a valid argument.
    new WasmPackPlugin({
      crateDirectory: __dirname,
      extraArgs: process.env.M0E_FAST ? '--no-opt' : '',
    }),
    new MonacoWebpackPlugin({languages: []})
  ]
};
