{
module Lexer (Token(..),P,evalP,lexer) where
import Control.Monad.State
import Control.Monad.Except
import Data.Word
}

tokens :-
       $white+ ;
       true    {TTrue}
       false   {TFalse}
       0       {TZero}
       succ    {TSucc}
       pred    {TPred}
       if      {TIf}
       then    {TThen}
       else    {TElse}
       iszero  {TIsZero}

{
data Token = 
     TTrue
     | TFalse
     | TZero
     | TSucc
     | TPred
     | TIf
     | TThen
     | TElse
     | TIsZero
     | TEOF
     deriving (Eq,Show)

-- The functions that must be provided to Alex's basic interface
type AlexInput = [Word8]
alexGetByte :: AlexInput -> Maybe (Word8,AlexInput)
alexGetByte (b:bs) = Just (b,bs)
alexGetByte []    = Nothing

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar = undefined


-- Our Parser monad
type P a = StateT AlexInput (Either String) a

evalP::P a -> AlexInput -> Either String a
evalP = evalStateT

-- Action to read a token
readToken::P Token
readToken = do
      s <- get  
      case alexScan s 0 of
           AlexEOF -> return TEOF
           AlexError _ -> throwError "!Lexical error"
           AlexSkip inp' _ -> do
              put inp'
              readToken
           AlexToken inp' _ tk -> do 
              put inp'
              return tk

-- The lexer function to be passed to Happy
lexer::(Token -> P a)->P a
lexer cont = readToken >>= cont

}    
