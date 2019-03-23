{
module Lexer (Token(..), Alex, lexer, failLC, runAlex) where
import Control.Monad.State
import Control.Monad.Except
import Data.Word
import AST
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as L
import qualified Data.ByteString.Lazy.Char8 as C
}

$identstart = [a-z A-Z _]
$identrest = [$identstart 0-9]

@ident = $identstart $identrest*
@number = 0 | [1-9] [0-9]*
@formula = \$ [[^\$] \n]+ \$

tokens :-
  $white+   ;
  "--".*    ;
  axiom     {\_ -> TokAxiom}
  coercion  {\_ -> TokCoercion}
  def       {\_ -> TokDef}
  delimiter {\_ -> TokDelimiter}
  free      {\_ -> TokFree}
  infixl    {\_ -> TokInfix False}
  infixr    {\_ -> TokInfix True}
  max       {\_ -> TokMax}
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
  @formula  {\s -> TokFormula $ L.toStrict $ L.drop 1 $ L.take (L.length s - 1) s}
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
  | TokDelimiter
  | TokFree
  | TokInfix Bool
  | TokMax
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
  | TokFormula B.ByteString
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
  | TokEOF
  deriving (Eq, Show)

data AlexPosn = AlexPosn !Int !Int !Int

alexMove :: AlexPosn -> Bool -> AlexPosn
alexMove (AlexPosn a l _) True  = AlexPosn (a+1) (l+1)   1
alexMove (AlexPosn a l c) False = AlexPosn (a+1)  l     (c+1)

type AlexInput = (AlexPosn, L.ByteString)

alexGetByte :: AlexInput -> Maybe (Word8, AlexInput)
alexGetByte (p, cs) =
  case L.uncons cs of
    Nothing -> Nothing
    Just (b, cs') -> Just (b, (alexMove p (b == 10), cs')) -- 10 = '\n'

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar = undefined

type Alex = StateT AlexInput (Either String)

failLC :: String -> Alex a
failLC err = do
  (AlexPosn _ l c, _) <- get
  throwError ("Error at line " ++ show l ++ " column " ++ show c ++ ": " ++ err)

readToken :: Alex Token
readToken = do
  s <- get
  case alexScan s 0 of
    AlexEOF -> return TokEOF
    AlexError _ -> failLC "Lexical error"
    AlexSkip s' _ -> do
      put s'
      readToken
    AlexToken s' len tk -> do
      put s'
      return (tk (L.take (fromIntegral len) (snd s)))

lexer :: (Token -> Alex a) -> Alex a
lexer = (readToken >>=)

runAlex :: Alex a -> L.ByteString -> Either String a
runAlex m s = evalStateT m (AlexPosn 0 1 1, s)

}
