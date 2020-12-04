import * as monaco from 'monaco-editor/esm/vs/editor/editor.api';
import * as mm0 from "./language-configuration.js";

import demo from "../../examples/demo.mm1";
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

import("../pkg/index.js").then(wasm => {
  wasm.init();
  monaco.languages.registerCompletionItemProvider(lang, {
    provideCompletionItems: () => {
      var suggestions = [{
        label: 'simpleText',
        kind: monaco.languages.CompletionItemKind.Text,
        insertText: 'simpleText'
      }, {
        label: 'testing',
        kind: monaco.languages.CompletionItemKind.Keyword,
        insertText: 'testing(${1:condition})',
        insertTextRules: monaco.languages.CompletionItemInsertTextRule.InsertAsSnippet
      }, {
        label: 'ifelse',
        kind: monaco.languages.CompletionItemKind.Snippet,
        insertText: [
          'if (${1:condition}) {',
          '\t$0',
          '} else {',
          '\t',
          '}'
        ].join('\n'),
        insertTextRules: monaco.languages.CompletionItemInsertTextRule.InsertAsSnippet,
        documentation: 'If-Else Statement'
      }];
      return { suggestions: suggestions };
    }
  });
})

const editor = monaco.editor.create(document.getElementById("container"), {
  theme: 'vs-dark',
  value: demo,
  language: lang
});

window.onresize = () => editor.layout()