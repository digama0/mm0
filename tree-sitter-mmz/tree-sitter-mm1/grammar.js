module.exports = grammar({
  name: 'mm1',

  inline: $ => [
    $.binder_contents,
  ],

  rules: {
    source_file: $ => repeat($.statement),
    whitespace: $ => repeat1($.whitestuff),
    whitestuff: $ => choice(
      $.whitechar, 
      $.line_comment
    ),
    whitechar: $ => choice(
      ' ', 
      '\n'
    ),
    line_comment: $ => seq(
      '--', 
      /[^\n]*/, 
      '\n'
    ),
    doc_comment: $ => seq(
      '--|', 
      /[^\n]*/, 
      '\n'
    ),

    number: $ => choice(
      '0', 
      seq(
        /[1-9]/,
        /[0-9]*/
      )
    ),
    math_string: $ => seq(
      '$', 
      /[^\$]*/, 
      '$'
    ),
    identifier: $ => /[a-zA-Z_][a-zA-Z0-9_]*/,
    statement: $ => choice(
      $.sort_stmt,
      $.line_comment,
      $.doc_comment,
      $.notation_stmt,
      $.inout_stmt,
      $.decl_stmt,
      $.do_stmt,
      $.annot_stmt,
    ),
    sort_mod: $ => choice(
      'pure',
      'strict',
      'provable',
      'free'
    ),
    visibility: $ => choice(
        'pub',
        'abstract',
        'local',
    ),
    decl_kind: $ => choice(
        'term',
        'axiom',
        'def',
        'theorem'
    ),
    decl_stmt: $ => seq(
        field('vis', optional($.visibility)),
        field('k', $.decl_kind),
        field('id', $.identifier),
        field('bis', alias(repeat($.binder), $.binder_list)),
        optional(
          seq(
            ':',
            field('type', $.arrow_type),
          ),
        ),
        optional(
          seq(
            '=', 
            field('val', $.sexpr)
          )
        ),
        ';'
    ),
    type_or_fmla: $ => choice(
        $.type,
        alias($.math_string, $.formula)
    ),
    // This is different from the mm1 grammar in that the locals
    // are `var_decl+` instead of `var_decl*`. I'm not sure what the utility
    // of an empty binder list is, but it seems like + makes more sense?
    binder_contents: $ => 
    seq(
      alias(
        repeat1(
          field('local', $.var_decl)
        ),
      $.local_list
      ),
      optional(
        seq(
          ':',
          field('ty', $.type_or_fmla)
        )
      )
    ),
    binder: $ => choice(
        seq(
          '{',
          $.binder_contents,
          '}'
        ),
        seq(
          '(',
          $.binder_contents,
          ')'
        )
    ),
    var_decl: $ => seq(
        optional('.'),
        $.identifier_
    ),
    arrow_type: $ => choice(
        $.type_or_fmla,
        seq(
            $.type_or_fmla,
            '>',
            $.arrow_type
        )
    ),
    sort_stmt: $ => seq(
      field('mods', repeat($.sort_mod)),
      'sort',
      field('id', $.identifier),
      ';'
    ),
    type: $ => seq($.identifier, repeat($.identifier)),
    identifier_: $ => choice(
      $.identifier, 
      '_'
    ),
    notation_stmt: $ => choice(
      $.delimiter_stmt,
      $.simple_notation_stmt,
      $.coercion_stmt,
      $.gen_notation_stmt
    ),
    delimiter_stmt: $ => seq(
      'delimiter',
      $.math_string,
      optional($.math_string),
      ';'
    ),
    simple_notation_stmt: $ => seq(
      choice('infixl', 'infixr', 'prefix'),
      $.identifier,
      ':',
      alias($.math_string, $.constant),
      'prec',
      $.precedence_lvl,
      ';'
    ),
    precedence_lvl: $ => choice($.number, 'max'),
    coercion_stmt: $ => seq(
      'coercion',
      field('id', $.identifier),
      ':',
      field('from', $.identifier),
      '>',
      field('to', $.identifier),
      ';'
    ),
    gen_notation_stmt: $ => seq(
      'notation',
      field('id', $.identifier),
      field('bis', alias(repeat($.binder), $.binder_list)),
      optional(seq(':',
      field('ty', $.type))),
      '=',
      field('prec', $.prec_constant),
      field('lits', repeat($.notation_literal)),
      ';'
    ),
    notation_literal: $ => choice(
      $.prec_constant,
      $.identifier
    ),
    prec_constant: $ => seq(
      '(',
      alias($.math_string, $.constant),
      ':',
      $.precedence_lvl,
      ')'
    ),
    inout_stmt: $ => choice(
      $.input_stmt,
      $.output_stmt
    ),
    input_stmt: $ => seq(
      'input',
      alias($.identifier, $.input_kind),
      ':',
      repeat(
        choice(
        $.identifier,
        $.math_string
        )
      ),
      ';'
    ),
    output_stmt: $ => seq(
      'output',
      alias($.identifier, $.output_kind),
      ':',
      repeat(
        choice(
        $.identifier,
        $.math_string
        )
      ),
      ';'
    ),
    init: $ => choice(
        /[a-z]/,
        /[A-Z]/,
        /[!%&*/:<=>?^_~]/,
    ),
    // This indirection with `token` is apparently the only good way to
    // get it to properly parse as `token` (subsequent)* instead of a bunch
    // of nodes with their own children, since tree-sitter really wants it to be a tree.
    // Also the `token` thing doesn't accept named rules. According to this:
    // https://github.com/tree-sitter/tree-sitter/issues/449 it was going to be relaxed
    // at some point.
    atom: $ => prec.left(1, choice(
        seq(
          $.init,
          alias(
            token(
              repeat(
                choice(
                  /[a-z]/,
                  /[A-Z]/,
                  /[0-9]/,
                  /[!%&*/:<=>?^_~+-.@]/ 
                )
              )
            ),
            $.subsequent
          )
        ),        
        seq(
          '->',
          alias(
            token(
              repeat(
                choice(
                  /[a-z]/,
                  /[A-Z]/,
                  /[0-9]/,
                  /[!%&*/:<=>?^_~+-.@]/ 
                )
              )
            ),
            $.subsequent
          )          
        ),
        '+',
        '-',
        '...',
    )),
    sexpr: $ => choice(
        $.atom,
        $.list,
        $.number,
        $.sexpr_string,
        $.sexpr_bool,
        '#undef',
        alias($.math_string, $.formula),
        seq(
            '\'',
            $.sexpr
        ),
        seq(
            ',',
            $.sexpr
        )
    ),
    do_stmt: $ => choice(
      $.do_block,
      $.do_inline
    ),
    do_block: $ => prec(2, 
      seq(
        'do',
        '{',
        repeat(
          prec(2, choice(
            $.sexpr,
            $.line_comment,
            $.doc_comment,
          )),
        ),
        '}',
        ';'
      )
    ),
    do_inline: $ => seq(
      'do',
      repeat1(prec(1, $.sexpr)),
      ';'
    ),
    // we can't abstract list_inner since it matches the empty string.
    list: $ => choice(
        prec.right(2, 
          seq(
            '@',
            alias(choice(repeat($.sexpr), seq(repeat1($.sexpr), '.', $.sexpr )), $.list_inner)
          )
        ),
        seq(
            '(',
            alias(choice(repeat($.sexpr), seq(repeat1($.sexpr), '.', $.sexpr )), $.list_inner),
            ')'
        ),
        seq(
            '[',
            alias(choice(repeat($.sexpr), seq(repeat1($.sexpr), '.', $.sexpr )), $.list_inner),
            ']'
        ),
        alias(
          seq(
            '{',
            alias(choice(repeat($.sexpr), seq(repeat1($.sexpr), '.', $.sexpr )), $.list_inner),
            '}'
        ), $.curly_list)
    ),
    sexpr_number: $ => choice(
        repeat1(/[0-9]/),
        seq(
            '0',
            choice(
                'x',
                'X'
            ),
            repeat1(/[0-9a-fA-F]/)
        )
    ),
    sexpr_string: $ => prec(30, seq(
        '"',
        repeat($.sexpr_char),
        '"'
    )),
    sexpr_char: $ => prec(40, choice(
        /[^\"\\]/,
        '\"',
        '\\',
        '\n',
        '\r'
    )),
    sexpr_bool: $ => choice(
        '#t',
        '#f'
    ),
    annot_stmt: $ => seq(
      '@',
      $.sexpr,
      $.statement
    ),
  }
});

