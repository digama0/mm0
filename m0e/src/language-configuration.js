// import * as monaco from 'monaco-editor/esm/vs/editor/editor.api';

// A Monarch port of vscode-mm0's TextMate grammar, `syntaxes/mm0.json`. That
// file is the reference: where the two can be made to say the same thing they
// should, and `test/highlight.test.mjs` runs both over every file in examples/
// and fails on any character they would paint differently. Scope names are
// taken from there rather than invented, so that a theme written for the vscode
// extension lands on the same tokens here.
//
// The two are not equally expressive, and the difference shows up twice.
// Monarch has no lookbehind and no notion of "am I in head position", so a list
// head is matched together with the paren that opens it -- which is what the
// TextMate grammar does too, with `begin: "\\(\\s*([\\w...]+)?"`. And a Monarch
// state is a stack, not a region with a name, so the one TextMate construct
// that colours a whole region, `@'(...)` in an annotation, is not reproduced;
// no example uses it, so the test has nothing to say about it either.

// A word in head position: the thing being applied. Shared by the three ways a
// head can be introduced -- `(f x)`, `'(f x)` and `@ f x`.
const head = { cases: {
  '@lispKeywords': 'keyword.other.command',
  '@lispBuiltins': 'support.function',
  '@default': 'entity.name.function'
} };

export const language = {
  // Set defaultToken to invalid to see what you do not tokenize yet
  // defaultToken: 'invalid',

  keywords: [
    'abstract', 'axiom', 'coercion', 'def', 'delimiter', 'exit', 'free',
    'infixl', 'infixr', 'input', 'local', 'max', 'notation', 'output', 'prec',
    'prefix', 'provable', 'pub', 'pure', 'sort', 'strict', 'term', 'theorem'
  ],

  // `pub`/`abstract`/`local` before a declaration, `pure`/`strict`/`provable`/
  // `free` before a sort. `keyword.control.modifier`, not `keyword`: the
  // TextMate grammar separates them and themes colour them differently.
  modifiers: ['pub', 'abstract', 'local', 'pure', 'strict', 'provable', 'free'],

  // Keywords that introduce a name. `sort` names a *sort*, which the TextMate
  // grammar scopes `entity.name.type` where a declaration gets
  // `entity.name.function` -- so the two must not share a state here either.
  sortKeywords: ['sort'],

  entityKeywords: ['def', 'term', 'axiom', 'theorem', 'output', 'input', 'coercion'],

  // `notation` takes binders and a return type before its `=`; the three
  // fixity keywords take a token and a precedence. Their tails are different
  // enough to need separate states.
  notationKeywords: ['notation'],
  infixKeywords: ['prefix', 'infixl', 'infixr'],

  // Exactly the list the TextMate grammar treats as lisp keywords. It is not
  // the interpreter's list -- `quote` and `unquote` are missing from it, and
  // `set-merge-strategy` is in it -- but matching it is the point.
  lispKeywords: [
    'if', 'def', 'fn', 'let', 'letrec', 'match', 'match-fn', 'match-fn*',
    'begin', 'focus', 'set-merge-strategy'
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
      { include: '@whitespace' },
      [/\d+|max(?![0-9a-zA-Z_])/, 'constant.numeric'],
      [/(do|import)(?![0-9a-zA-Z_])/, { token: 'keyword.other.command', next: '@lisp' }],
      [/@word/, { cases: {
        '@modifiers': 'keyword.control.modifier',
        '@sortKeywords': { token: 'keyword.other.command', next: '@sortName' },
        '@notationKeywords': { token: 'keyword.other.notation', next: '@notationName' },
        '@infixKeywords': { token: 'keyword.other.notation', next: '@infixName' },
        '@entityKeywords': { token: 'keyword.other.command', next: '@entity' },
        '@keywords': 'keyword',
        '@default': 'identifier'
      } }],
      // A binder list. Like `@sortRef` this has to be its own state rather than
      // bare brackets: a *variable* may be named for a keyword too, as in
      // mm0.mm1's `def DDef (id args ret def: nat)`, and at statement level
      // `def` would otherwise be read as one. `#binder` spans the same parens.
      // The two bracket shapes are separate states because the TextMate
      // grammar names their contents differently.
      [/\(/, { token: '@brackets', next: '@binderRound' }],
      [/\{/, { token: '@brackets', next: '@binderCurly' }],
      [/;/, 'punctuation.terminator.statement'],
      [/[,.>]/, 'delimiter'],
      // Everything after a colon in a statement names a sort: the type of a
      // binder, `{x: nat}`, or the return type, `: wff`. `#binder` and
      // `#return-type` key off the same colon in the TextMate grammar.
      [/:/, { token: 'keyword.operator.colon', next: '@sortRef' }],
      // The `@` of an annotation carries no scope of its own in the TextMate
      // grammar -- it is part of a `begin` pattern with no capture name.
      [/@/, { token: '', next: '@annotation' }],
      [/=/, { token: 'delimiter', next: '@lisp' }],
      { include: '@lisp_common' },
    ],

    entity: [
      { include: '@whitespace' },
      // `entity.name.function`, not `entity.name.class`: that is the scope the
      // TextMate grammar gives a declaration's name -- for `def`/`term`/
      // `axiom`/`theorem` and for `notation`/`coercion`/`infixl` alike -- and
      // themes colour the two differently (One Dark Pro draws a class where a
      // sort belongs).
      [/@word/, { token: 'entity.name.function', next: '@pop' }],
      [/./, { token: 'invalid', next: '@pop' }]
    ],

    // The name in a `sort` declaration: a sort, not a declaration.
    sortName: [
      { include: '@whitespace' },
      [/@word/, { token: 'entity.name.type', next: '@pop' }],
      [/./, { token: 'invalid', next: '@pop' }]
    ],

    // A sort used rather than declared. This spans to the end of the binder or
    // the statement rather than stopping after one word, because a sort may be
    // named for a keyword -- hol.mm1 declares a sort called `term` -- and
    // handing `term > term` back to the statement state would read the second
    // one as the keyword. `#return-type` covers the same region in the
    // TextMate grammar, ending at a lookahead rather than a token.
    //
    // A formula can stand here too, in `theorem foo: $ ... $` and in a
    // hypothesis binder, and then there is no sort to name.
    sortRef: [
      { include: '@whitespace' },
      [/[;=)}]/, { token: '@rematch', next: '@pop' }],
      [/\$/, { token: 'punctuation.definition.math-string.begin', bracket: '@open', switchTo: '@formula' }],
      [/@word/, { token: 'entity.name.type', switchTo: '@sortArgs' }],
      [/./, 'delimiter']
    ],

    // The names a binder binds, up to its `:`. A hypothesis binder holds a
    // formula instead, `(h: $ a $)`.
    binderRound: [
      { include: '@whitespace' },
      [/\)/, { token: '@brackets', next: '@pop' }],
      [/:/, { token: 'keyword.operator.colon', next: '@sortRef' }],
      // `(.x: nat)`: a dummy. The dot itself carries no scope.
      [/(\.)(@word)/, ['delimiter', 'variable.parameter.dummy']],
      [/@word/, 'variable.other.regular'],
      [/./, 'delimiter']
    ],

    // `{x: nat}` binds a bound variable, and the TextMate grammar says so --
    // its contents are `variable.parameter.bound` where a round binder's are
    // `variable.other.regular`.
    binderCurly: [
      { include: '@whitespace' },
      [/\}/, { token: '@brackets', next: '@pop' }],
      [/:/, { token: 'keyword.operator.colon', next: '@sortRef' }],
      [/@word/, 'variable.parameter.bound'],
      [/./, 'delimiter']
    ],

    // After the sort: the bound variables it may depend on, `(p: wff x y)`.
    // A `>` ends them and starts another sort, `term app: term > term > term;`.
    sortArgs: [
      { include: '@whitespace' },
      [/[;=)}]/, { token: '@rematch', next: '@pop' }],
      [/>/, { token: 'delimiter', switchTo: '@sortRef' }],
      [/@word/, 'variable.parameter.bound'],
      [/./, 'delimiter']
    ],

    // `notation foo (x y): sort = ... ;`
    notationName: [
      { include: '@whitespace' },
      [/@word/, { token: 'entity.name.function', switchTo: '@notationHead' }],
      [/./, { token: 'invalid', next: '@pop' }]
    ],

    notationHead: [
      { include: '@whitespace' },
      [/;/, { token: 'punctuation.terminator.statement', next: '@pop' }],
      [/=/, { token: 'delimiter', switchTo: '@notationTail' }],
      [/\(/, { token: '@brackets', next: '@binderRound' }],
      [/\{/, { token: '@brackets', next: '@binderCurly' }],
      [/:/, { token: 'keyword.operator.colon', next: '@sortRef' }],
      [/./, 'delimiter']
    ],

    // Right of the `=`: literal tokens, precedences, associativity, and the
    // names of the binders being placed. Nothing here is lisp, and nothing in
    // `$...$` here is a formula -- it is the concrete syntax being declared.
    notationTail: [
      { include: '@whitespace' },
      [/;/, { token: 'punctuation.terminator.statement', next: '@pop' }],
      [/\$[^$]*\$/, 'string.quoted.single.constant'],
      [/[lr]assoc(?![0-9a-zA-Z_])/, 'keyword.other.notation'],
      [/\d+|max(?![0-9a-zA-Z_])/, 'constant.numeric'],
      [/@word/, 'variable.other.unknown'],
      [/./, 'delimiter']
    ],

    // `infixl foo: $tok$ prec 42;`
    infixName: [
      { include: '@whitespace' },
      [/@word/, { token: 'entity.name.function', switchTo: '@infixTail' }],
      [/./, { token: 'invalid', next: '@pop' }]
    ],

    infixTail: [
      { include: '@whitespace' },
      [/;/, { token: 'punctuation.terminator.statement', next: '@pop' }],
      [/:/, 'keyword.operator.colon'],
      [/\$[^$]*\$/, 'string.quoted.single.constant'],
      [/prec(?![0-9a-zA-Z_])/, 'keyword.other'],
      [/\d+|max(?![0-9a-zA-Z_])/, 'constant.numeric'],
      [/@word/, 'variable.other.unknown'],
      [/./, 'delimiter']
    ],

    // The TextMate grammar names the whole `"..."` region, delimiters included.
    string: [
      [/[^\\"]+/,  'string.quoted.double'],
      [/@escapes/, 'constant.character.escape'],
      [/\\./,      'constant.character.escape.invalid'],
      [/"/,        { token: 'string.quoted.double', bracket: '@close', next: '@pop' } ]
    ],

    // A math string is *not* a string to look at. The TextMate grammar gives
    // the region no scope at all and only names the `$`s, so in vscode a
    // formula draws in the plain foreground and only the semantic tokens inside
    // it have colour. Monarch has to name the region something in order to
    // track it; `string.template` is the name, and index.js paints it back to
    // the theme's foreground. Keeping `string` in the name is what stops monaco
    // from matching brackets across a formula.
    formula: [
      [/\$/, { token: 'punctuation.definition.math-string.end', bracket: '@close', next: '@pop' } ],
      [/[^$]+/, 'string.template']
    ],

    lisp_common: [
      { include: '@whitespace' },
      [/[{}()\[\]]/, '@brackets'],
      [/"/,  { token: 'string.quoted.double', bracket: '@open', next: '@string' } ],
      [/\$/,  { token: 'punctuation.definition.math-string.begin', bracket: '@open', next: '@formula' } ],
    ],

    // A `do` block is lisp all the way to its `;`, which is what this state is
    // for. An annotation is not -- see `@annotation`.
    lisp: [
      [/;/, { token: 'punctuation.terminator.statement', next: '@pop' } ],
      { include: '@lisp_body' },
    ],

    lisp_body: [
      // `(f a @ g b c)` is `(f a (g b c))`, so the word after an `@` is in head
      // position exactly as if a paren had opened there. The space is required:
      // `@` is itself a word character in lisp, and `@foo` is an atom.
      [/(@)(\s+)(@lispWord)/, ['keyword.operator', 'white', head]],
      // `(?=\s|$)` rather than `(?=\s)`: a proof that runs over several lines
      // ends most of them on a bare `@`, and monarch tokenizes a line at a
      // time, so there is no whitespace left for the lookahead to see.
      [/@(?=\s|$)/, 'keyword.operator'],
      [/\\./, 'operator'],
      // The head of a list is the function being applied; every other word is
      // an atom. Monarch has no way to ask "am I in head position?", so the
      // paren and the head are matched together -- which is exactly what the
      // TextMate grammar does with `begin: "\\(\\s*([\\w...]+)?"`.
      // A builtin in head position is scoped apart from any other head, as the
      // TextMate grammar does -- Night Owl draws the two the same, but a theme
      // is entitled to tell `support.function` from `entity.name.function`.
      [/('+)(\()(\s*)(@lispWord)/, ['string.quoted.other', '@brackets', 'white', head]],
      [/('+)(\()/, ['string.quoted.other', '@brackets']],
      [/(\()(\s*)(@lispWord)/, ['@brackets', 'white', head]],
      // A quote that does not open a list, and an unquote comma, carry no scope
      // of their own -- neither is in the character class the TextMate grammar
      // matches atoms with, so both fall through it to the enclosing region.
      [/['`,]/, ''],
      [/#(t|f|undef)/, 'constant.language'],
      { include: '@lisp_common' },
      [/0[xX][0-9a-fA-F]+/, 'constant.numeric.hex'],
      // Not in head position, so it is an atom, whatever it is named. The
      // TextMate grammar has no non-head case for a keyword or a builtin
      // either: `'(def x)` is a list holding the atom `def`.
      [/@lispWord/, 'variable.other.unknown'],
      // `[1-9][0-9]*` left a bare `0` matching nothing at all, which monaco
      // draws in the default foreground -- `(ref! 0)`, `{n = 0}`. The hex rule
      // above already claimed a leading `0x`.
      [/[0-9]+/, 'constant.numeric'],
    ],

    // `@_ local def foo`, `@(mmc-th ...) theorem bar`: an annotation is a
    // *single* lisp value in front of an ordinary statement, so it has to hand
    // control back rather than running to the `;` the way `do` does. Without
    // that, the whole statement is lexed as lisp and the declaration's name
    // never reaches `@entity` -- which is what the TextMate grammar avoids by
    // giving `#lisp-annot` one pattern per value shape.
    annotation: [
      { include: '@whitespace' },
      // Matched on its own rather than as part of the `(`: `@brackets` only
      // accepts text that is literally a bracket, so `'(` would be rejected.
      [/'+/, 'string.quoted.other'],
      [/\(/, { token: '@brackets', switchTo: '@annotation_head' }],
      [/#(t|f|undef)/, { token: 'constant.language', next: '@pop' }],
      [/0[xX][0-9a-fA-F]+/, { token: 'constant.numeric.hex', next: '@pop' }],
      [/\d+/, { token: 'constant.numeric', next: '@pop' }],
      [/@lispWord/, { token: 'variable.other.unknown', next: '@pop' }],
      [/./, { token: 'invalid', next: '@pop' }],
    ],

    // The word right after the `(` is the head, the same as anywhere else in
    // lisp; it needs its own state only because a group action cannot also
    // switch states.
    annotation_head: [
      { include: '@whitespace' },
      [/@lispWord/, { cases: {
        '@lispKeywords': { token: 'keyword.other.command', switchTo: '@annotation_list' },
        '@lispBuiltins': { token: 'support.function', switchTo: '@annotation_list' },
        '@default': { token: 'entity.name.function', switchTo: '@annotation_list' }
      } }],
      [/./, { token: '@rematch', switchTo: '@annotation_list' }],
    ],

    // The parenthesised form, which ends at its own matching `)` -- nested
    // lists push a copy of this state, so the count is the stack depth.
    annotation_list: [
      // `@annotation_head` rather than `@push`: the head of a nested list has
      // to be read before the `(` is handed to the generic bracket rule, and
      // `annotation_head` switches to a fresh `annotation_list` once it has,
      // which leaves the stack exactly where `@push` would have.
      [/\(/, { token: '@brackets', next: '@annotation_head' }],
      [/\)/, { token: '@brackets', next: '@pop' }],
      { include: '@lisp_body' },
    ],

    whitespace: [
      [/[ \n]+/, 'white'],
      [/--\|.*$/,    'comment.special'],
      [/--.*$/,    'comment.line.double-dash'],
    ],
  },
};
