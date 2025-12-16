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
    filename: "[name].js"
  },
  devServer: {
    static: dist,
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

    new WasmPackPlugin({
      crateDirectory: __dirname,
    }),
    new MonacoWebpackPlugin({languages: []})
  ]
};
