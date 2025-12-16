import * as monaco from 'monaco-editor/esm/vs/editor/editor.api';
import * as mm0 from "./language-configuration.js";

import demo from "../../examples/demo.mm1";
const filename = "demo.mm1";
const lang = 'metamath-zero';

import('monaco-themes/themes/Night Owl.json').then(data => {
  monaco.editor.defineTheme('night-owl', data)
  monaco.editor.setTheme('night-owl')
})

monaco.languages.register({
  id: lang,
  extensions: [".mm0", ".mm1"],
  aliases: ["Metamath Zero", "metamath-zero"],
  mimetypes: ["text/x-metamath-zero", "text/plaintext"],
});

monaco.languages.setMonarchTokensProvider(lang, mm0.language)

const editor = monaco.editor.create(document.getElementById("container"), {
  theme: 'vs-dark',
  value: demo,
  language: lang
});

import("../pkg/index.js").then(wasm => {
  wasm.init();
  const model = editor.getModel();
  wasm.open_file(filename, model.getVersionId(), model.getValue());

  setInterval(() => {
    while (true) {
      const msg = wasm.poll_message();
      if (msg) {
        switch (msg.method) {
          case "textDocument/publishDiagnostics":
            const markers = msg.params.diagnostics.map(diag => ({
              severity: 1 << (4 - diag.severity),
              startLineNumber: diag.range.start.line + 1,
              startColumn: diag.range.start.character + 1,
              endLineNumber: diag.range.end.line + 1,
              endColumn: diag.range.end.character + 1,
              message: diag.message,
            }));
            monaco.editor.setModelMarkers(model, lang, markers);
            break;
          default: console.log(msg); break;
        }
      } else {
        break;
      }
    }
  }, 200);

  model.onDidChangeContent(e => wasm.update_file(filename, e.versionId, e.changes));

  // monaco.languages.registerCompletionItemProvider(lang, {
  //   provideCompletionItems: () => ({
  //     suggestions: [{
  //       label: 'simpleText',
  //       kind: monaco.languages.CompletionItemKind.Text,
  //       insertText: 'simpleText'
  //     }, {
  //       label: 'testing',
  //       kind: monaco.languages.CompletionItemKind.Keyword,
  //       insertText: 'testing(${1:condition})',
  //       insertTextRules: monaco.languages.CompletionItemInsertTextRule.InsertAsSnippet
  //     }, {
  //       label: 'ifelse',
  //       kind: monaco.languages.CompletionItemKind.Snippet,
  //       insertText: [
  //         'if (${1:condition}) {',
  //         '\t$0',
  //         '} else {',
  //         '\t',
  //         '}'
  //       ].join('\n'),
  //       insertTextRules: monaco.languages.CompletionItemInsertTextRule.InsertAsSnippet,
  //       documentation: 'If-Else Statement'
  //     }]
  //   }),
  // });
})

window.onresize = () => editor.layout()
