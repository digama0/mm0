module AST where

data Term =
     STrue
     | SFalse
     | SZero
     | SIsZero Term
     | SSucc Term
     | SPred Term
     | SIfThen Term Term Term
     deriving Show
