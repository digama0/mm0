module.exports = grammar({
  name: 'mm0',

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
      $.term_stmt,
      $.line_comment,
      $.doc_comment,
      $.notation_stmt,
      $.assert_stmt,
      $.def_stmt,
      $.inout_stmt
    ),
    sort_mod: $ => choice(
      'pure',
      'strict',
      'provable',
      'free'
    ),
    sort_stmt: $ => seq(
      field('mods', repeat($.sort_mod)),
      'sort',
      field('id', $.identifier),
      ';'
    ),
    type: $ => repeat1($.identifier),
    identifier_: $ => choice(
      $.identifier, 
      '_'
    ),
    term_stmt: $ => seq(
      'term',
      field('id', $.identifier),
      field('bis', alias(repeat($.type_binder), $.binder_list)),
      ':',
      $.arrow_type,
      ';'
    ),
    curly_type_binder: $ => seq(
      '{',
      repeat($.identifier),
      ':',
      $.type,
      '}'
    ),
    paren_type_binder: $ => seq(
      '(',
      repeat($.identifier_),
      ':',
      $.type,
      ')'
    ),
    type_binder: $ => choice($.curly_type_binder, $.paren_type_binder),
    arrow_type: $ => choice($.type, seq($.type, '>', $.arrow_type)),
    assert_stmt: $ => seq(
      choice('axiom', 'theorem'), 
      field('id', $.identifier),
      field('bis', alias(repeat($.formula_type_binder), $.binder_list)),
      ':',
      field('ty', $.formula_arrow_type),
      ';'
    ),
    formula_type_binder: $ => choice(
      seq('{', repeat($.identifier), ':', $.type, '}'),
      seq('(', repeat($.identifier), ':', choice($.type, alias($.math_string, $.formula)), ')'),
    ),
    formula_arrow_type: $ => choice(
        alias($.math_string, $.formula),
        seq(
          choice(
            $.type,
            alias($.math_string, $.formula)
          ),
          '>',
          $.formula_arrow_type,
        ),
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
      field('bis', alias(repeat($.type_binder), $.type_binder_list)),
      ':',
      field('ty', $.type),
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
    def_stmt: $ => seq(
      'def',
      field('id', $.identifier),
      field('bis', alias(repeat($.dummy_binder), $.dummy_binder_list)),
      ':',
      $.type,
      optional(seq('=', alias($.math_string, $.formula))),
      ';'
    ),
    dummy_binder: $ => choice(
      seq(
        '{', 
        repeat($.dummy_identifier),
        ':',
        $.type,
        '}'
      ),
      seq(
        '(',
        repeat($.dummy_identifier),
        ':',
        $.type,
        ')'
      ),
    ),
    dummy_identifier: $ => choice(
      seq('.', $.identifier), 
      $.identifier_
    ),
    inout_stmt: $ => choice(
      $.input_stmt,
      $.output_stmt
    ),
    input_stmt: $ => seq(
      'input',
      alias($.identifier, $.input_kind),
      ':',
      repeat(choice(
        $.identifier,
        $.math_string
      )),
      ';'
    ),
    output_stmt: $ => seq(
      'output',
      alias($.identifier, $.output_kind),
      ':',
      repeat(choice(
        $.identifier,
        $.math_string
      )),
      ';'
    )
  }
});

