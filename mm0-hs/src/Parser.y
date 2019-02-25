{
module Parser(parse) where
import AST
import qualified Lexer as L
import Control.Monad.Except
}

%monad{L.P}
%lexer{L.lexer}{L.TEOF}
%name parse
%tokentype{L.Token}
%error {parseError}

%token
  true  	{L.TTrue}
  false 	{L.TFalse}
  zero   	{L.TZero}
  iszero        {L.TIsZero}
  succ		{L.TSucc}
  pred		{L.TPred}
  if		{L.TIf}
  then		{L.TThen}
  else		{L.TElse}

%%

Term	:  true				{STrue}
	|  false			{SFalse}
	|  zero				{SZero}
	|  iszero Term			{SIsZero $2}
	|  succ Term			{SSucc $2}
	|  pred Term			{SPred $2}
	|  if Term then Term else Term	{SIfThen $2 $4 $6}

{
parseError _ = throwError "!Parse Error"

}
