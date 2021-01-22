if exists("b:current_syntax")
  finish
endif

let b:current_syntax = "metamath-zero"

syn region mm0_fmla start='\$' end='\$' containedin=ALL keepend
syn region mm0_string start='"' skip='\\"' end='"' contained keepend
syn match mm0_lisp_ident contained
  \ "[a-zA-Z_!%&*/:<=>?\^~+\-.][a-zA-Z0-9_!%&*/:<=>?\^~+\-.]*"
syn cluster mm0_lisp add=mm0_lisp_ident,mm0_string

syn match mm0_modifier
  \ "\%(pure\s\+\)\?\%(strict\s\+\)\?\%(provable\s\+\)\?\%(free\s\+\)\?\%(sort\)\@="
  \ nextgroup=mm0_decl
syn match mm0_modifier "\%(\%(local\|abstract\)\s\+\)\?\%(def\)\@=" nextgroup=mm0_decl
syn match mm0_modifier "\%(\%(pub\)\s\+\)\?\%(theorem\)\@=" nextgroup=mm0_decl

syn keyword mm0_decl sort def term axiom theorem
  \ nextgroup=mm0_decl_ident skipwhite skipempty

syn match mm0_decl_ident "\<[a-zA-Z_][a-zA-Z0-9_]*\>"
  \ contained nextgroup=mm0_binder,mm0_decl_type skipwhite skipempty

syn region mm0_binder start="(" skip="\$[^$]*\$" end=")" contained
  \ contains=mm0_binder_open,mm0_deps_sort,mm0_fmla transparent keepend
  \ nextgroup=mm0_binder,mm0_decl_type skipwhite skipempty
syn region mm0_binder start="{" skip="\$[^$]*\$" end="}" contained
  \ contains=mm0_binder_open,mm0_deps_sort,mm0_fmla transparent keepend
  \ nextgroup=mm0_binder,mm0_decl_type,mm0_decl_value skipwhite skipempty
syn match mm0_binder_open "[({]" contained containedin=mm0_binder
  \ nextgroup=mm0_binder_var skipwhite skipempty
syn match mm0_binder_close "[)}]" display contained containedin=mm0_binder
syn match mm0_binder_var "\%(\.\s*\)\?\<[a-zA-Z_][a-zA-Z0-9_]*\>" contained
  \ nextgroup=mm0_binder_var,mm0_colon,mm0_binder_close skipwhite skipempty
syn match mm0_colon ":" display contained
syn match mm0_deps_sort "\<[a-zA-Z_][a-zA-Z0-9_]*\>" contained
  \ nextgroup=mm0_deps_ident skipwhite skipempty
syn match mm0_deps_ident "\<[a-zA-Z_][a-zA-Z0-9_]*\>" contained
  \ nextgroup=mm0_deps_ident skipwhite skipempty

syn region mm0_decl_type start=":" end=";" contained transparent keepend
  \ contains=mm0_colon,mm0_deps_sort,mm0_fmla,mm0_arrow,mm0_decl_value skipwhite skipempty

syn region mm0_decl_value start="=" end=";\@=" contained transparent keepend
  \ contains=mm0_equal,@mm0_lisp skipwhite skipempty

syn region mm0_delimiter_region start="delimiter" end=";"
  \ contains=mm0_delimiter,mm0_fmla transparent keepend
syn keyword mm0_delimiter delimiter contained

syn region mm0_import_region start="import" end=";"
  \ contains=mm0_import,mm0_string transparent keepend
syn keyword mm0_import import contained

syn region mm0_io_region start="input\|output" end=";"
  \ contains=mm0_io,mm0_colon,@mm0_lisp transparent keepend
syn keyword mm0_io input output contained
  \ nextgroup=mm0_io_ident skipwhite skipempty
syn match mm0_io_ident "\<[a-zA-Z_][a-zA-Z0-9_]*\>" contained

syn region mm0_infix_region start="infixl\|infixr\|prefix" end=";"
  \ transparent keepend contains=mm0_infix
syn keyword mm0_infix infixl infixr prefix contained
  \ nextgroup=mm0_infix_ident skipwhite skipempty
syn match mm0_infix_ident "\<[a-zA-Z_][a-zA-Z0-9_]*\>" contained
  \ nextgroup=mm0_infix_colon skipwhite skipempty
syn match mm0_infix_colon ":" contained
  \ nextgroup=mm0_infix_fmla skipwhite skipempty
syn region mm0_infix_fmla start='\$' end='\$' contained keepend
  \ nextgroup=mm0_prec skipwhite skipempty
syn keyword mm0_prec prec contained
  \ nextgroup=mm0_prec_num skipwhite skipempty
syn match mm0_prec_num "\<\%(max\|0\|[1-9][0-9]*\)" display contained

syn keyword mm0_nota notation
  \ nextgroup=mm0_nota_ident skipwhite skipempty
syn match mm0_nota_ident "\<[a-zA-Z_][a-zA-Z0-9_]*\>"
  \ contained nextgroup=mm0_nota_binder,mm0_nota_type,mm0_nota_equal skipwhite skipempty
syn region mm0_nota_binder start="(" skip="\$[^$]*\$" end=")" contained
  \ contains=mm0_binder_open,mm0_deps_sort transparent keepend
  \ nextgroup=mm0_nota_binder,mm0_nota_type,mm0_nota_equal skipwhite skipempty
syn region mm0_nota_binder start="{" skip="\$[^$]*\$" end="}" contained
  \ contains=mm0_binder_open,mm0_deps_sort transparent keepend
  \ nextgroup=mm0_nota_binder,mm0_nota_type,mm0_nota_equal skipwhite skipempty
syn region mm0_nota_type start=":" end=";" contained transparent keepend
  \ contains=mm0_colon,mm0_deps_sort,mm0_nota_equal skipwhite skipempty
syn match mm0_nota_equal "=" contained nextgroup=mm0_nota_var skipwhite skipempty
syn match mm0_nota_var "\<[a-zA-Z_][a-zA-Z0-9_]*\>" contained
  \ nextgroup=mm0_nota_var,mm0_nota_assoc skipwhite skipempty
syn region mm0_nota_var start="(" skip="\$[^$]*\$" end=")" contained
  \ contains=mm0_nota_operator,mm0_fmla,mm0_prec_num transparent keepend
  \ nextgroup=mm0_nota_var,mm0_nota_assoc skipwhite skipempty
syn match mm0_nota_operator "[(:)]" contained
syn match mm0_nota_assoc "[lr]assoc" contained
  \ nextgroup=mm0_prec_num skipwhite skipempty

syn region mm0_do_region start="do" end=";"
  \ contains=mm0_do,mm0_do_semi,@mm0_lisp transparent keepend
syn match mm0_do "do\%(\s*{\)\?" contained
  \ nextgroup=@mm0_lisp skipwhite skipempty
syn match mm0_do_semi "\%(}\)\?;" contained

syn region mm0_lisp_paren start="(" end=")" contains=@mm0_lisp fold transparent
syn region mm0_lisp_paren start="{" end="}" contains=@mm0_lisp fold transparent
syn region mm0_lisp_paren start="\[" end="\]" contains=@mm0_lisp fold transparent
syn match mm0_lisp_func contained
  \ "\%((\|@\s\+\)\@<=[a-zA-Z_!%&*/:<=>?\^~+\-.][a-zA-Z0-9_!%&*/:<=>?\^~+\-.]*"
syn cluster mm0_lisp add=mm0_lisp_paren,mm0_lisp_func
syn match mm0_at_sign "@" contained
syn match mm0_lisp_undef "#undef" contained
syn match mm0_lisp_bool "#[tf]" contained
syn match mm0_lisp_number "[0-9]\+" contained
syn cluster mm0_lisp add=mm0_at_sign,mm0_lisp_undef,mm0_lisp_bool,mm0_lisp_number
syn match mm0_lisp_if contained
  \ "\%(if\|match\|match-fn\*\?\)[a-zA-Z0-9_!%&*/:<=>?\^~+\-.]\@!"
syn match mm0_lisp_keyword contained
  \ "\%(def\|fn\|let\|letrec\|begin\|focus\|set-merge-strategy\)[a-zA-Z0-9_!%&*/:<=>?\^~+\-.]\@!"
syn match mm0_lisp_predef contained
  \ "\%(+\|\*\|-\|<=\?\|>=\?\|==\?\|->string\|string-\%(>atom\|append\)\|display\|error\|print\|apply\|min\|max\|not\|or\|list\|cons\|hd\|tl\|lookup\|insert\|async\|set-timeout\|goal\|goal-type\|infer-type\|pp\|[gs]et-goals\|to-expr\|refine\|stat\|have\|get-decl\|\%(pair\|null\|int\|bool\|atom\|string\|fn\|number\|ref\|atom-map\|def\|goal\|mvar\)?\|\%(ref\|get\|set\|atom-map\|insert\|mvar\|add-\%(decl\|term\|thm\)\)!\|refine-extra-args\)[a-zA-Z0-9_!%&*/:<=>?\^~+\-.]\@!"
syn cluster mm0_lisp add=mm0_lisp_if,mm0_lisp_keyword,mm0_lisp_predef
syn match mm0_lisp_quote "'\s\@!" contained
syn match mm0_lisp_antiquote ",\s\@!" contained
syn cluster mm0_lisp add=mm0_lisp_quote,mm0_lisp_antiquote,mm0_string

syn match mm0_arrow ">" contained
syn match mm0_equal "=" contained
syn match mm0_semi ";" containedin=ALL
syn match mm0_doc_comment "--|.*$" containedin=ALL oneline
syn match mm0_comment "--.*$" containedin=ALL oneline

hi def link mm0_binder_var   mm0_ident
hi def link mm0_binder_open  mm0_operator
hi def link mm0_binder_close mm0_operator
hi def link mm0_infix_colon  mm0_colon
hi def link mm0_colon        mm0_operator
hi def link mm0_deps_sort    mm0_decl_ident
hi def link mm0_infix_ident  mm0_decl_ident
hi def link mm0_nota_ident   mm0_decl_ident
hi def link mm0_nota_binder  mm0_decl_ident
hi def link mm0_io_ident     Constant
hi def link mm0_deps_ident   mm0_ident
hi def link mm0_nota_var     mm0_ident
hi def link mm0_lisp_ident   mm0_ident
hi def link mm0_decl         mm0_keyword
hi def link mm0_delimiter    mm0_keyword
hi def link mm0_infix        mm0_keyword
hi def link mm0_nota         mm0_keyword
hi def link mm0_prec         mm0_keyword
hi def link mm0_import       mm0_keyword
hi def link mm0_do           mm0_keyword
hi def link mm0_nota_assoc   mm0_keyword
hi def link mm0_io           mm0_keyword
hi def link mm0_keyword      Keyword
hi def link mm0_arrow        mm0_operator
hi def link mm0_semi         mm0_operator
hi def link mm0_do_semi      mm0_operator
hi def link mm0_nota_equal   mm0_equal
hi def link mm0_equal        mm0_operator
hi def link mm0_nota_operator mm0_operator
hi def link mm0_at_sign      mm0_lisp_operator
hi def link mm0_lisp_func    Function
hi def link mm0_lisp_undef   Constant
hi def link mm0_lisp_bool    Boolean
hi def link mm0_lisp_if      Conditional
hi def link mm0_lisp_predef  Constant
hi def link mm0_lisp_keyword Keyword
hi def link mm0_lisp_number  mm0_number
hi def link mm0_lisp_quote   mm0_lisp_operator
hi def link mm0_lisp_antiquote mm0_lisp_operator
hi def link mm0_lisp_operator mm0_operator
hi def link mm0_decl_ident   Type
hi def link mm0_ident        Identifier
hi def link mm0_doc_comment  SpecialComment
hi def link mm0_comment      Comment
hi def link mm0_prec_num     mm0_number
hi def link mm0_number       Number
hi def link mm0_operator     Operator
hi def link mm0_modifier     Type
hi def link mm0_infix_fmla   mm0_fmla
hi def link mm0_fmla         String
hi def link mm0_string       String
