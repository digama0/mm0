if exists("b:current_syntax")
  finish
endif

let b:current_syntax = "metamath-zero"

syntax match     mm0Comment "-- .*$"
syntax keyword   mm0Keyword   sort term axiom theorem delimiter def import
syntax keyword   mm0Keyword   infixr infixl prefix do
syntax keyword   mm0Modifier  pub provable prec local

syntax match     mm0Operator ":" ">" ";" "\{" "\}"
syntax region    mm0Form start='\$' end='\$' containedin=ALL keepend
syntax region    mm0String start='"' end='"' containedin=ALL keepend

hi def link mm0Keyword    Statement
hi def link mm0Comment    Comment
hi def link mm0Operator   Operator
hi def link mm0Modifier   Type
hi def link mm0Form       String
hi def link mm0String     String
