import * as monaco from 'monaco-editor/esm/vs/editor/editor.api';
import * as mm0 from "./language-configuration.js";

import demo from "../../examples/demo.mm1";
const lang = 'metamath-zero';

import('monaco-themes/themes/Night Owl.json').then(data => {
  monaco.editor.defineTheme('night-owl', data)
  monaco.editor.setTheme('night-owl')
})

import("../pkg/index.js").then(wasm => {
  const State = wasm.State;
  const tokenize = wasm.tokenize;
  // import txt from 'examples/demo.mm1';

  // Register a new language
  monaco.languages.register({
    id: lang,
    extensions: [".mm0", ".mm1"],
    aliases: ["Metamath Zero", "metamath-zero"],
    mimetypes: ["text/x-metamath-zero", "text/plaintext"],
  });
  // wasm.setLanguageSettings(
  //   monaco.languages.getEncodedLanguageId(lang))

  // Register a tokens provider for the language
  monaco.languages.setMonarchTokensProvider(lang, mm0.language)
  // {
  //   getInitialState: () => new State(),
  //   tokenizeEncoded: (line, state) => {
  //     console.log(line);
  //     console.log(tokenize(line, state));
  //     return {
  //       tokens: [{startIndex: 5, scopes: "custom-info"}, {startIndex: 20, scopes: "source"}],
  //       endState: new State(state.value + 1)
  //     }
  //   }
  // });

  // Register a completion item provider for the new language
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

monaco.editor.create(document.getElementById("container"), {
  theme: 'vs-dark',
  value: demo,
  language: lang
});
