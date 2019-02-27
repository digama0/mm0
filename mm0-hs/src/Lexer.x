{
module Lexer (Token(..),lexer) where
import Control.Monad.State
import Control.Monad.Except
import Data.Word
import Types
import qualified Data.ByteString.Lazy.Char8 as C
}

%wrapper "basic-bytestring"

$identstart = [a-z A-Z _]
$identrest = [$identstart 0-9 \-]

@ident = $identstart $identrest*
@number = 0 | [1-9] [0-9]*
@formula = \$ [^\$]+ \$

tokens :-
  $white+   ;
  "--".*    ;
  axiom     {\_ -> TokAxiom}
  coercion  {\_ -> TokCoercion}
  def       {\_ -> TokDef}
  infixl    {\_ -> TokInfix False}
  infixr    {\_ -> TokInfix True}
  max       {\_ -> TokMax}
  nonempty  {\_ -> TokNonempty}
  notation  {\_ -> TokNotation}
  output    {\_ -> TokOutput}
  prec      {\_ -> TokPrec}
  prefix    {\_ -> TokPrefix}
  provable  {\_ -> TokProvable}
  pure      {\_ -> TokPure}
  sort      {\_ -> TokSort}
  strict    {\_ -> TokStrict}
  term      {\_ -> TokTerm}
  theorem   {\_ -> TokTheorem}
  var       {\_ -> TokVar}
  "_"       {\_ -> TokAnon}
  @ident    {TokIdent . C.unpack}
  @number   {TokNumber . C.unpack}
  @formula  {TokFormula}
  "*"       {\_ -> TokStar}
  "."       {\_ -> TokDot}
  ":"       {\_ -> TokColon}
  ";"       {\_ -> TokSemi}
  "("       {\_ -> TokLParen}
  ")"       {\_ -> TokRParen}
  ">"       {\_ -> TokArrow}
  "{"       {\_ -> TokLBrace}
  "}"       {\_ -> TokRBrace}
  "="       {\_ -> TokEqual}

{
data Token =
    TokAxiom
  | TokCoercion
  | TokDef
  | TokInfix Bool
  | TokMax
  | TokNonempty
  | TokNotation
  | TokOutput
  | TokPrec
  | TokPrefix
  | TokProvable
  | TokPure
  | TokSort
  | TokStrict
  | TokTerm
  | TokTheorem
  | TokVar
  | TokIdent String
  | TokNumber String
  | TokFormula ByteString.ByteString
  | TokStar
  | TokDot
  | TokColon
  | TokSemi
  | TokLParen
  | TokRParen
  | TokArrow
  | TokLBrace
  | TokRBrace
  | TokEqual
  | TokAnon
  deriving (Eq, Show)

lexer :: ByteString.ByteString -> [Token]
lexer = alexScanTokens
}
