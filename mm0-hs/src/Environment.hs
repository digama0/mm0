module Environment where

import Control.Monad.Except
import qualified Data.Map.Strict as M
import AST
import Util

data DepType = DepType {
  dSort :: Ident,
  dDeps :: [Ident] }

instance Show DepType where
  showsPrec _ (DepType t ts) r =
    t ++ foldr (\t' r -> ' ' : t' ++ r) r ts

data SExpr = SVar Ident | App Ident [SExpr]

instance Show SExpr where
  showsPrec n (SVar v) r = v ++ r
  showsPrec n (App v []) r = v ++ r
  showsPrec n (App v vs) r =
    let f r = v ++ foldr (\e r -> ' ' : showsPrec 1 e r) r vs in
    if n == 0 then f r else '(' : f (')' : r)

data Decl =
    DTerm
      [(Ident, Ident)]   -- bound variables
      [DepType]          -- args
      DepType            -- return type
  | DAxiom
      [(Ident, Ident)]   -- bound variables
      [(Ident, DepType)] -- args
      [SExpr]            -- hypotheses
      SExpr              -- conclusion
  | DDef
      [(Ident, Ident)]   -- bound variables
      [(Ident, DepType)] -- args
      DepType            -- return type
      (Maybe (
        [(Ident, Ident)], -- dummy vars
        SExpr))           -- definition
  deriving (Show)

type Vars = M.Map Ident VarType

data Stack = Stack {
  sVars :: Vars,
  sRest :: Maybe Stack }
  deriving (Show)

data Environment = Environment {
  eSorts :: M.Map Ident SortData,
  eDecls :: M.Map Ident Decl }
  deriving (Show)

getTerm :: Environment -> Ident -> Maybe ([(Ident, Ident)], [DepType], DepType)
getTerm e v = eDecls e M.!? v >>= go where
  go (DTerm vs args r) = Just (vs, args, r)
  go (DDef vs args r _) = Just (vs, snd <$> args, r)
  go (DAxiom _ _ _ _) = Nothing

getArity :: Environment -> Ident -> Maybe Int
getArity e v = (\(bs, args, _) -> length bs + length args) <$> getTerm e v

getVarM :: MonadError String m => Ident -> Stack -> m VarType
getVarM v s = fromJustError "type depends on unknown variable" (sVars s M.!? v)

varTypeToDep :: [Ident] -> VarType -> DepType
varTypeToDep ds (VType t) = DepType t []
varTypeToDep ds (Open t) = DepType t ds
