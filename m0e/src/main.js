// import * as monaco from 'monaco-editor';
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api';
// if shipping only a subset of the features & languages is desired

window.wasm = import("../pkg/index.js");
import {State, tokenize} from "../pkg/index.js";
import demo from "../../examples/demo.mm1";

// import txt from 'examples/demo.mm1';

// Register a new language
monaco.languages.register({ id: 'metamath-zero' });

// Register a tokens provider for the language
monaco.languages.setTokensProvider('metamath-zero', {
  getInitialState: () => new State(),
  tokenizeEncoded: (line, state) => {
    console.log(line);
    console.log(tokenize(line, state));
    return {
      tokens: [{startIndex: 5, scopes: "custom-info"}, {startIndex: 20, scopes: "source"}],
      endState: new State(state.value + 1)
    }
  }
});

// Define a new theme that contains only rules that match this language
monaco.editor.defineTheme('myCoolTheme', {
  base: 'vs',
  inherit: false,
  rules: [
    { token: 'custom-info', foreground: '808080' },
    { token: 'custom-error', foreground: 'ff0000', fontStyle: 'bold' },
    { token: 'custom-notice', foreground: 'FFA500' },
    { token: 'custom-date', foreground: '008800' },
  ]
});

// Register a completion item provider for the new language
monaco.languages.registerCompletionItemProvider('metamath-zero', {
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

monaco.editor.create(document.getElementById("container"), {
  theme: 'monokai',
  value: demo,
  language: 'metamath-zero'
});
