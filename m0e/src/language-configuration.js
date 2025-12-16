// import * as monaco from 'monaco-editor/esm/vs/editor/editor.api';

export const language = {
  // Set defaultToken to invalid to see what you do not tokenize yet
  // defaultToken: 'invalid',

  keywords: [
    'axiom', 'coercion', 'def', 'delimiter', 'free', 'infixl', 'infixr',
    'input', 'max', 'notation', 'output', 'prec', 'prefix', 'provable',
    'pure', 'sort', 'strict', 'term', 'theorem'
  ],

  entityKeywords: [
    'sort', 'def', 'term', 'axiom', 'theorem', 'notation', 'prefix',
    'output', 'input', 'coercion', 'infixl', 'infixr'
  ],

  lispKeywords: [
    'def', 'fn', 'quote', 'unquote', 'if', 'begin', 'focus', 'let',
    'letrec', 'match', 'match-fn', 'match-fn*'
  ],

  lispBuiltins: [
    'display', 'error', 'print', 'report-at', 'begin', 'apply', '+', '*', '^',
    'max', 'min', '-', '//', '%', '<', '<=', '>', '>=', '=', 'shl', 'shr',
    'band', 'bor', 'bxor', 'bnot', '==', '->string', 'string->atom',
    'string-append', 'string-len', 'string-nth', 'substr', 'string->list',
    'list->string', 'not', 'and', 'or', 'list', 'cons', 'hd', 'tl', 'nth',
    'map', 'bool?', 'atom?', 'pair?', 'null?', 'number?', 'string?', 'fn?',
    'def?', 'ref?', 'ref!', 'get!', 'set!', 'set-weak!', 'copy-span', 'stack-span',
    'async', 'atom-map?', 'atom-map!', 'lookup', 'insert!', 'insert', 'set-timeout',
    'set-stack-limit', 'mvar?', 'goal?', 'mvar!', 'pp', 'goal', 'goal-type',
    'infer-type', 'infer-sort', 'get-mvars', 'get-goals', 'set-goals',
    'set-close-fn', 'local-ctx', 'to-expr', 'refine', 'have', 'stat', 'get-decl',
    'add-decl!', 'add-term!', 'add-thm!', 'dummy!', 'check-proofs', 'set-reporting',
    'refine-extra-args', 'eval-string', 'mmc-init'
  ],

  // symbols used as brackets
  brackets: [
    ['{', '}', 'delimiter.curly'],
    ['[', ']', 'delimiter.square'],
    ['(', ')', 'delimiter.parenthesis']
  ],

  word: /[a-zA-Z_][0-9a-zA-Z_]*/,

  lispWord: /[a-zA-Z_!%&*/:<=>?\\^~+.@-][0-9a-zA-Z_!%&*/:<=>?\\^~+.@-]*/,

  escapes: /\\(?:[nr\\"]|x[0-9A-Fa-f]{2})/,

  tokenizer: {
    root: [
      [/\d+|max/, 'constant.numeric'],
      [/do|import/, { token: 'keyword', next: '@lisp' }],
      [/@word/, { cases: {
        '@keywords': { cases: {
          '@entityKeywords': { token: 'keyword', next: '@entity' },
          '@default': 'keyword'
        } },
        '@default': 'identifier'
      } }],
      [/[;,.>:]/, 'delimiter'],
      [/@/, { token: 'keyword', next: '@lisp' }],
      [/=/, { token: 'delimiter', next: '@lisp' }],
      { include: '@lisp_common' },
    ],

    entity: [
      { include: '@whitespace' },
      [/@word/, { token: 'entity.name.class', next: '@pop' }],
      [/./, { token: 'invalid', next: '@pop' }]
    ],

    string: [
      [/[^\\"]+/,  'string'],
      [/@escapes/, 'string.escape'],
      [/\\./,      'string.escape.invalid'],
      [/"/,        { token: 'string.quote', bracket: '@close', next: '@pop' } ]
    ],

    formula: [
      [/\$/, { token: 'string.template.delimiter', bracket: '@close', next: '@pop' } ],
      [/[^$]+/, 'string.template']
    ],

    lisp_common: [
      { include: '@whitespace' },
      [/[{}()\[\]]/, '@brackets'],
      [/"/,  { token: 'string.quote', bracket: '@open', next: '@string' } ],
      [/\$/,  { token: 'string.template.delimiter', bracket: '@open', next: '@formula' } ],
    ],

    lisp: [
      [/;/, { token: 'delimiter', next: '@pop' } ],
      [/@/, 'punctuation.accessor'],
      [/\\./, 'operator'],
      [/[',](?! )/, 'string.quote'],
			[/#(t|f|undef)/, 'constant'],
      { include: '@lisp_common' },
      [/@lispWord/, { cases: {
        '@lispKeywords': 'keyword',
        '@lispBuiltins': 'entity.name.function',
        '@default': 'identifier'
      } }],
			[/0[xX][0-9a-fA-F]+/, 'constant.numeric.hex'],
			[/[1-9][0-9]*/, 'constant.numeric'],
    ],

    whitespace: [
      [/[ \n]+/, 'white'],
      [/--\|.*$/,    'comment.doc'],
      [/--.*$/,    'comment'],
    ],
  },
};
