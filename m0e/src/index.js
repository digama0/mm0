// Imported rather than inlined into static/index.html: webpack *copies* that
// file, so edits to it do not reliably re-emit under `webpack serve`, whereas a
// real module is watched and hot-reloaded like the rest of the source.
import './ui.css';

import * as monaco from 'monaco-editor/esm/vs/editor/editor.api';
// monaco's metadata.js lists two features under the label "semanticTokens" --
// documentSemanticTokens and viewportSemanticTokens -- and the webpack plugin
// keys features by label (`featuresById[feature.label] = feature`), so the
// second silently overwrites the first. Only the viewport one gets bundled, and
// DocumentSemanticTokensFeature, which is what actually asks a provider for a
// document's tokens, is never registered. Import it directly; it registers
// itself as an import side effect.
import 'monaco-editor/esm/vs/editor/contrib/semanticTokens/browser/documentSemanticTokens.js';
import * as mm0 from "./language-configuration.js";

const lang = 'metamath-zero';
const defaultFile = "demo.mm1";

// A snapshot of examples/, captured at build time. The browser has no
// filesystem for mm0-rs to fall back on, so every file that an `import` might
// reach has to be seeded into the VFS up front; that means we need the
// contents of all of them here, not just the one on screen.
const req = require.context("../../examples", false, /\.mm[01]$/);
const examples = new Map(req.keys()
  .map(key => [key.replace(/^\.\//, ""), req(key).default])
  .sort(([a], [b]) => a.localeCompare(b)));

// A standalone theme resolves a semantic token type by matching its *name*
// against these TextMate rules, and the match is by prefix -- so Night Owl's
// `variable.other` does not answer for `variable`. A type that matches nothing
// resolves to no styling and monaco then drops the token entirely, which reads
// as semantic highlighting silently not working. One rule per type in the
// server's legend, in Night Owl's palette:
const semanticRules = [
  { token: 'variable', foreground: '7FDBCA' },   // local / lisp variable
  { token: 'parameter', foreground: 'F78C6C' },  // dummy variable
  { token: 'property', foreground: 'FFCB8B' },   // hypothesis / subproof
  { token: 'method', foreground: '82AAFF' },     // theorem
  { token: 'function', foreground: 'ADDB67' },   // lisp function
  // A builtin. Monaco resolves a semantic token by matching
  // `[type, ...modifiers].join('.')` against these rules, with the same
  // dot-prefix fallback as everywhere else -- so this has to be listed after
  // (more specific than) `function`, which would otherwise answer for it.
  // vscode maps `function.defaultLibrary` onto `support.function` by its
  // standard fallback rules, and 82AAFF is what Night Owl gives that scope.
  { token: 'function.defaultLibrary', foreground: '82AAFF' },
  { token: 'macro', foreground: 'C792EA' },      // lisp macro
  { token: 'keyword', foreground: 'FF5874' },
  { token: 'comment', foreground: '637777' },
];

// Theme rules for the scopes the Monarch grammar emits, where Night Owl's own
// answer is wrong for this language.
//
// `entity.name.type` is every sort -- declared by `sort`, and used in binders
// and return types. Night Owl has no rule for it at all, so it would draw in
// the default foreground; green is what it uses for `support.type` elsewhere,
// and it has to read differently from `entity.name.class`, the name a
// declaration binds.
//
// A math string is *not* a string to look at. The TextMate grammar gives the
// region no scope at all -- only the `$`s are named -- so in vscode a formula
// draws in the plain foreground and only the semantic tokens inside it have
// colour. Monarch has to name the region something to track it, and anything
// containing `string` inherits Night Owl's green, so the colour is put back to
// the theme's own foreground rather than the token being renamed: that keeps
// the region a string as far as monaco is concerned, which is what stops
// bracket matching from reaching inside a formula.
const grammarRules = data => [
  { token: 'entity.name.type', foreground: 'ADDB67' },
  { token: 'string.template', foreground: data.colors['editor.foreground'].replace('#', '') },
];

import('monaco-themes/themes/Night Owl.json').then(data => {
  monaco.editor.defineTheme('night-owl',
    {...data, rules: [...data.rules, ...grammarRules(data), ...semanticRules]})
  monaco.editor.setTheme('night-owl')
})

monaco.languages.register({
  id: lang,
  extensions: [".mm0", ".mm1"],
  aliases: ["Metamath Zero", "metamath-zero"],
  mimetypes: ["text/x-metamath-zero", "text/plaintext"],
});

monaco.languages.setMonarchTokensProvider(lang, mm0.language)

// One model per example, so that switching files preserves edits, undo history
// and diagnostics. `mm0-rs` names files as `wasm:/<name>`, which is also how we
// recover the model a `publishDiagnostics` refers to.
const models = new Map();
const modelFor = name => {
  let model = models.get(name);
  if (!model) {
    model = monaco.editor.createModel(
      examples.get(name), lang, monaco.Uri.parse(`wasm:/${name}`));
    models.set(name, model);
  }
  return model;
};

const select = document.getElementById("file");
for (const name of examples.keys()) {
  select.add(new Option(name, name, name === defaultFile, name === defaultFile));
}

// Created before any model of ours exists: the editor options are what put
// `editor.semanticHighlighting.enabled` into the configuration service, and
// monaco decides whether to watch a model for semantic tokens when the model is
// added. Creating models first means that decision is taken while the setting
// still says no.
const editor = monaco.editor.create(document.getElementById("container"), {
  theme: 'vs-dark',
  // The default is 'configuredByTheme', and a standalone theme's
  // `semanticHighlighting` is hardcoded to false and never read back from the
  // theme data -- so deferring to the theme means it is never on at all.
  'semanticHighlighting.enabled': true,
  // The Contents panel is a better index of a proof file than a thumbnail of
  // its shape, and on a narrow window the minimap costs the code real columns.
  minimap: { enabled: false },
  scrollBeyondLastLine: false,
});

// Eagerly, so that a definition landing in another file has a model to peek
// into: `mm0-rs` will happily point at a file the user has never opened.
for (const name of examples.keys()) modelFor(name);
editor.setModel(modelFor(defaultFile));

const nameOf = uri => uri.replace(/^.*\//, "");
const lspPosition = position =>
  ({ line: position.lineNumber - 1, character: position.column - 1 });
const monacoRange = range => ({
  startLineNumber: range.start.line + 1,
  startColumn: range.start.character + 1,
  endLineNumber: range.end.line + 1,
  endColumn: range.end.character + 1,
});
const textDocument = model => ({ uri: model.uri.toString() });

// `Hover.contents` is any of a string, a `{language, value}` pair, a
// `{kind, value}` markup, or an array of those.
const hoverContents = contents => (Array.isArray(contents) ? contents : [contents])
  .map(part => {
    if (typeof part === "string") return { value: part };
    if (part.language !== undefined) {
      return { value: "```" + part.language + "\n" + part.value + "\n```" };
    }
    return { value: part.value };
  });

// `documentSymbol` reports a sort as CLASS, both `term` and `def` as
// CONSTRUCTOR, and both `axiom` and `theorem` as METHOD -- so the LSP kind
// throws away the distinction a reader of a proof file most wants, between what
// is assumed and what is proved. The `detail` string opens with the real
// keyword, so take it from there and let the kind cover the lisp globals.
const keywordOf = symbol => {
  const word = (symbol.detail || "").trim().split(/[\s(]/)[0];
  if (word === "provable") return "sort";
  if (["sort", "term", "def", "axiom", "theorem"].includes(word)) return word;
  return "lisp";
};

const outlineList = document.getElementById("outline-list");
const outlineCount = document.getElementById("outline-count");
const problems = document.getElementById("problems");
const problemList = document.getElementById("problem-list");
const problemCount = document.getElementById("problem-count");
const state = document.getElementById("state");
const importsEl = document.getElementById("imports");
const outlineFilter = document.getElementById("outline-filter");
const exploreButton = document.getElementById("explore");

// Hand a compiled .mmb to the proof explorer, a sibling app under this same
// origin (EXPLORER_BASE, set from M0E_EXPLORER_URL; see webpack.config.js). It
// reopens a stored file whose name matches the one in its address (see
// mm0-js's `resolveFile`), so the handoff is: write the bytes into its
// IndexedDB store under that name, then navigate there. The store is
// per-origin, not per-path, so the write is visible across the two apps.
//
// `resolveFile` prefers a bundled example when the name matches one, so the
// exported name keeps the source extension -- `peano.mm1.mmb`, never the bare
// `peano.mmb` that would reopen the example instead of what was just compiled.
// Substituted by webpack's DefinePlugin: the explorer's base URL (ending in a
// slash), or `null` when M0E_EXPLORER_URL was unset at build time. Null means
// there is nowhere to hand a proof off to, so the button is removed and the
// rest of the handoff never runs.
const EXPLORER_BASE = process.env.EXPLORER_URL;
if (!EXPLORER_BASE) exploreButton.remove();
const EXPLORER_DB = "mm0-js";
const EXPLORER_STORE = "files";
const EXPLORER_KEY = "last";
const putInExplorerStore = (name, bytes) => new Promise((resolve, reject) => {
  const open = indexedDB.open(EXPLORER_DB, 1);
  // Match the store mm0-js creates, in case the explorer has not run yet.
  open.onupgradeneeded = () => {
    if (!open.result.objectStoreNames.contains(EXPLORER_STORE)) {
      open.result.createObjectStore(EXPLORER_STORE);
    }
  };
  open.onerror = () => reject(open.error);
  open.onsuccess = () => {
    const db = open.result;
    const tx = db.transaction(EXPLORER_STORE, "readwrite");
    tx.objectStore(EXPLORER_STORE).put({ name, bytes: bytes.slice().buffer }, EXPLORER_KEY);
    tx.oncomplete = () => { db.close(); resolve(); };
    tx.onerror = () => { db.close(); reject(tx.error); };
  };
});

const empty = (list, text) => {
  list.replaceChildren(Object.assign(document.createElement("li"),
    { className: "empty", textContent: text }));
};

const rowButton = (onClick, ...children) => {
  const li = document.createElement("li");
  const button = document.createElement("button");
  button.className = "row";
  button.append(...children);
  button.addEventListener("click", onClick);
  li.append(button);
  return { li, button };
};

const span = (className, text) =>
  Object.assign(document.createElement("span"), { className, textContent: text });

import("../pkg/index.js").then(wasm => {
  wasm.init();
  for (const [name, text] of examples) wasm.seed_file(name, text);

  const reveal = range => {
    editor.setSelection(range);
    editor.revealRangeInCenterIfOutsideViewport(range);
    editor.focus();
  };

  // Diagnostics annotated at the end of the line they belong to. In MM0 these
  // are not only complaints: an info-severity diagnostic is how the elaborator
  // reports output, so a `do` block's results end up beside the code that
  // produced them rather than in a panel somewhere else.
  const severities = new Map([
    [monaco.MarkerSeverity.Error, "error"],
    [monaco.MarkerSeverity.Warning, "warning"],
    [monaco.MarkerSeverity.Info, "info"],
    [monaco.MarkerSeverity.Hint, "hint"],
  ]);
  const lens = editor.createDecorationsCollection();
  const refreshLens = () => {
    const model = editor.getModel();
    const byLine = new Map();
    for (const marker of monaco.editor.getModelMarkers({ resource: model.uri })) {
      const line = marker.startLineNumber;
      const previous = byLine.get(line);
      // one annotation per line: the worst thing on it wins, and the rest are
      // counted rather than stacked
      if (!previous) byLine.set(line, { marker, extra: 0 });
      else byLine.set(line, {
        marker: marker.severity > previous.marker.severity ? marker : previous.marker,
        extra: previous.extra + 1,
      });
    }

    lens.set([...byLine].flatMap(([line, { marker, extra }]) => {
      const kind = severities.get(marker.severity) || "info";
      // injected text must be a single line, and these messages often are not,
      // so mark where the breaks were rather than quietly running it together
      const text = marker.message
        .replace(/\r?\n/g, " ↵ ").replace(/[ \t]+/g, " ").trim();
      const suffix = extra ? `  (+${extra} more)` : "";
      const column = model.getLineMaxColumn(line);
      return [{
        range: new monaco.Range(line, column, line, column),
        options: {
          after: {
            content: `    ${text}${suffix}`,
            inlineClassName: `lens lens-${kind}`,
          },
          showIfCollapsed: true,
        },
      }, {
        range: new monaco.Range(line, 1, line, 1),
        options: { isWholeLine: true, className: `lens-line lens-line-${kind}` },
      }];
    }));
  };

  // Report on the file being shown, from the markers it already has. Deriving
  // this from "diagnostics arrived just now" would leave the state stuck on
  // "checking" for any file that is already done -- switching to one is not
  // a reason for the server to say anything about it again.
  const diagnosed = new Set();

  const refreshProblems = () => {
    const model = editor.getModel();
    const errors = monaco.editor.getModelMarkers({ resource: model.uri })
      .filter(m => m.severity === monaco.MarkerSeverity.Error)
      .sort((a, b) => a.startLineNumber - b.startLineNumber);

    if (!diagnosed.has(nameOf(model.uri.path))) {
      state.dataset.state = "checking";
      state.textContent = "checking";
    } else if (errors.length) {
      state.dataset.state = "errors";
      state.textContent = errors.length === 1 ? "1 error" : `${errors.length} errors`;
    } else {
      state.dataset.state = "verified";
      state.textContent = "verified";
    }

    // Only a file that elaborated without errors can be compiled and handed
    // to the explorer. No-op when there is no explorer (button removed).
    if (EXPLORER_BASE) {
      exploreButton.disabled = !diagnosed.has(nameOf(model.uri.path)) || errors.length > 0;
    }

    refreshLens();
    problems.dataset.shown = errors.length ? "yes" : "no";
    problemCount.textContent = errors.length || "";
    problemList.replaceChildren(...errors.map(marker =>
      rowButton(() => reveal(marker),
        span("line", marker.startLineNumber),
        span("msg", marker.message.split("\n")[0])).li));
  };

  // `peano_hex.mm1` declares 1217 things, which is past the point where a list
  // is something you read: keep the symbols and let the filter decide what is
  // on screen.
  let symbols = [];
  const renderOutline = () => {
    const needle = outlineFilter.value.trim().toLowerCase();
    const shown = needle
      ? symbols.filter(s => s.name.toLowerCase().includes(needle))
      : symbols;

    outlineCount.textContent = needle && symbols.length
      ? `${shown.length}/${symbols.length}` : (symbols.length || "");

    if (!symbols.length) return empty(outlineList, "nothing declared yet");
    if (!shown.length) return empty(outlineList, `no match for "${needle}"`);

    outlineList.replaceChildren(...shown.map(symbol => {
      const keyword = keywordOf(symbol);
      const { li, button } = rowButton(
        () => reveal(monacoRange(symbol.selectionRange)),
        span("kw", keyword), span("name", symbol.name));
      button.dataset.kw = keyword;
      button.title = symbol.detail || symbol.name;
      return li;
    }));
  };
  outlineFilter.addEventListener("input", renderOutline);

  // The outline is the file's mathematical contents, so it is worth asking for
  // again whenever the file has been re-elaborated -- but no faster than the
  // user can read it.
  let outlineTimer = 0;
  const refreshOutline = () => {
    clearTimeout(outlineTimer);
    outlineTimer = setTimeout(async () => {
      const model = editor.getModel();
      const result = await request("textDocument/documentSymbol",
        { textDocument: textDocument(model) }).catch(() => null);
      if (model !== editor.getModel()) return;   // switched away mid-request
      symbols = result || [];
      renderOutline();
    }, 150);
  };

  // What this file pulls in. The server resolves these against the seeded
  // files; we read them off the source so the header is right immediately,
  // rather than only once elaboration has reported back.
  const refreshImports = name => {
    const source = modelFor(name).getValue();
    const imported = [...source.matchAll(/^\s*import\s+"([^"]+)"/gm)].map(m => m[1]);
    importsEl.replaceChildren();
    if (!imported.length) return;
    importsEl.append(document.createTextNode("imports "));
    imported.forEach((dep, i) => {
      if (i) importsEl.append(document.createTextNode(", "));
      const button = Object.assign(document.createElement("button"),
        { textContent: dep, type: "button" });
      if (models.has(dep)) {
        button.addEventListener("click", () => show(dep));
      } else {
        // seeded files are all there is, so this import cannot resolve
        button.className = "missing";
        button.disabled = true;
        button.title = `${dep} is not one of the bundled files`;
      }
      importsEl.append(button);
    });
  };

  // Elaborating a file is what produces its diagnostics, and it only has to be
  // asked for once per file -- edits are pushed through `update_file` after.
  const opened = new Set();
  const show = name => {
    const model = modelFor(name);
    editor.setModel(model);
    if (!opened.has(name)) {
      opened.add(name);
      model.onDidChangeContent(e => wasm.update_file(name, e.versionId, e.changes));
      wasm.open_file(name, model.getVersionId(), model.getValue());
    }
    refreshImports(name);
    refreshProblems();
    refreshOutline();
  };

  // Without an opener, a definition in another file can only be peeked: a
  // standalone editor does nothing for resources other than its own model.
  monaco.editor.registerEditorOpener({
    openCodeEditor(source, resource, selectionOrPosition) {
      const name = nameOf(resource.path);
      if (!models.has(name)) return false;
      show(name);
      if (selectionOrPosition) {
        // either an IRange or an IPosition
        const position = selectionOrPosition.startLineNumber === undefined
          ? selectionOrPosition
          : {
            lineNumber: selectionOrPosition.startLineNumber,
            column: selectionOrPosition.startColumn,
          };
        editor.setPosition(position);
        editor.revealPositionInCenter(position);
      }
      editor.focus();
      return true;
    },
  });

  // `mm0-rs` already implements the LSP requests; there is just no socket to
  // carry them here. So talk to it as an LSP client would: send a request with
  // an id, and settle the promise when the reply turns up in the same queue the
  // notifications arrive on.
  let nextId = 1;
  const pending = new Map();
  const request = (method, params) => new Promise((resolve, reject) => {
    const id = nextId++;
    pending.set(id, { resolve, reject });
    try {
      wasm.send_request(id, method, params);
    } catch (e) {
      pending.delete(id);
      reject(e);
    }
  });

  setInterval(() => {
    for (;;) {
      const msg = wasm.poll_message();
      if (!msg) break;
      // a reply, rather than a notification
      if (msg.method === undefined && msg.id !== undefined) {
        const handler = pending.get(msg.id);
        if (handler) {
          pending.delete(msg.id);
          if (msg.error) handler.reject(new Error(msg.error.message));
          else handler.resolve(msg.result ?? null);
        }
        continue;
      }
      switch (msg.method) {
        case "textDocument/publishDiagnostics": {
          const model = models.get(nameOf(msg.params.uri));
          if (!model) break;
          const markers = msg.params.diagnostics.map(diag => ({
            severity: 1 << (4 - diag.severity),
            ...monacoRange(diag.range),
            message: diag.message,
          }));
          monaco.editor.setModelMarkers(model, lang, markers);
          diagnosed.add(nameOf(msg.params.uri));
          if (model === editor.getModel()) {
            refreshProblems();
            // the file has just been re-elaborated, so its contents may differ
            refreshOutline();
          }
          break;
        }
        default: console.log(msg); break;
      }
    }
  }, 50);

  if (EXPLORER_BASE) exploreButton.addEventListener("click", async () => {
    const source = nameOf(editor.getModel().uri.path);
    const mmbName = `${source}.mmb`;
    exploreButton.disabled = true;
    const previous = exploreButton.textContent;
    exploreButton.textContent = "compiling…";
    try {
      const bytes = await wasm.export_mmb(source);
      await putInExplorerStore(mmbName, bytes);
      // Same-tab navigation, so the store write is visible: it is the same
      // origin and the write has already committed.
      window.location.href = `${EXPLORER_BASE}#/${encodeURIComponent(mmbName)}`;
    } catch (e) {
      exploreButton.textContent = "export failed";
      console.error("export_mmb", e);
      setTimeout(() => { exploreButton.textContent = previous; refreshProblems(); }, 2000);
    }
  });

  // After `request` exists: opening a file asks for its outline.
  select.addEventListener("change", () => show(select.value));
  editor.onDidChangeModel(() => {
    const name = nameOf(editor.getModel().uri.path);
    if (select.value !== name) select.value = name;
  });
  show(defaultFile);

  monaco.languages.registerHoverProvider(lang, {
    provideHover: async (model, position) => {
      const res = await request("textDocument/hover", {
        textDocument: textDocument(model),
        position: lspPosition(position),
      });
      if (!res) return null;
      return {
        contents: hoverContents(res.contents),
        ...(res.range ? { range: monacoRange(res.range) } : {}),
      };
    },
  });

  monaco.languages.registerDefinitionProvider(lang, {
    provideDefinition: async (model, position) => {
      const res = await request("textDocument/definition", {
        textDocument: textDocument(model),
        position: lspPosition(position),
      });
      if (!res) return null;
      // either `Location`s or `LocationLink`s, depending on the server's view
      // of what the client supports
      return (Array.isArray(res) ? res : [res]).map(loc => loc.targetUri === undefined
        ? { uri: monaco.Uri.parse(loc.uri), range: monacoRange(loc.range) }
        : {
          uri: monaco.Uri.parse(loc.targetUri),
          range: monacoRange(loc.targetSelectionRange),
        });
    },
  });

  // The order here is the server's token table (see `token_types!`); the
  // indices in the encoded stream are positions in this list.
  const legend = {
    tokenTypes: ["variable", "parameter", "property", "method",
      "function", "macro", "keyword", "comment"],
    // The server declares one modifier, `defaultLibrary`, and sets it on every
    // builtin lisp function -- `apply` has it, a user `def` does not. Leaving
    // this empty is not merely cosmetic: monaco decodes the bitset by walking
    // `legend.tokenModifiers`, so an empty list drops the bit before any theme
    // sees it, and builtins become indistinguishable from anything else.
    tokenModifiers: ["defaultLibrary"],
  };
  monaco.languages.registerDocumentSemanticTokensProvider(lang, {
    getLegend: () => legend,
    provideDocumentSemanticTokens: async model => {
      const res = await request("textDocument/semanticTokens/full",
        { textDocument: textDocument(model) });
      // LSP and monaco agree on the delta encoding, so `data` passes straight
      // through
      return res && { data: new Uint32Array(res.data) };
    },
    releaseDocumentSemanticTokens: () => {},
  });

  // A handle for poking at all this from the devtools console.
  window.m0e = { wasm, request, models, editor, legend };
})

window.onresize = () => editor.layout()
