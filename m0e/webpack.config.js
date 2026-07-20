const path = require("path");
const CopyPlugin = require("copy-webpack-plugin");
const WasmPackPlugin = require("@wasm-tool/wasm-pack-plugin");
const MonacoWebpackPlugin = require('monaco-editor-webpack-plugin');

const dist = path.resolve(__dirname, "dist");
const examples = path.resolve(dist, "examples");

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
        // The proof explorer, served under this same origin so the handoff can
        // go through its IndexedDB store (which is per-origin) and a same-tab
        // navigation. Its index.html loads ./ui and ./dist by relative path, so
        // it works unchanged under the explorer/ subpath. Only the browser
        // runtime is copied -- dist/test and dist/tools are Node-only and would
        // choke the minifier.
        { from: "../mm0-js/index.html", to: path.resolve(dist, "explorer") },
        { from: "../mm0-js/ui", to: path.resolve(dist, "explorer/ui") },
        { from: "../mm0-js/dist/src", to: path.resolve(dist, "explorer/dist/src") },
        { from: "../mm0-js/dist/ui", to: path.resolve(dist, "explorer/dist/ui") },
      ]
    }),

    new WasmPackPlugin({
      crateDirectory: __dirname,
    }),
    new MonacoWebpackPlugin({languages: []})
  ]
};
