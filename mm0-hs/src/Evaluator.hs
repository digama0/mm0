module Evaluator where
import qualified AST as P

data Value =
  VBool Bool
  |VInt Integer
   deriving Show
            
eval::P.Term -> Maybe Value

eval P.STrue = Just (VBool True)
eval P.SFalse = Just (VBool False)
eval P.SZero = Just (VInt 0)

eval (P.SIsZero t) = 
  case eval t of
    Just (VInt i) -> Just (VBool (i == 0))
    _ -> Nothing

eval (P.SSucc t) =
  case eval t of
    Just (VInt i) -> Just (VInt (i+1))
    _ -> Nothing

eval (P.SPred t) = 
  case eval t of
    Just (VInt i) | i>0 -> Just(VInt (i-1))
    _ -> Nothing

eval (P.SIfThen t1 t2 t3) =
  case eval t1 of
    Just (VBool True) -> eval t2
    Just (VBool False) -> eval t3
    _ -> Nothing


