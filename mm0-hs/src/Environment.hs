module Environment where

import Control.Monad.Except
import qualified Data.Map.Strict as M
import AST
import Util

data PBinder = PBound Ident Ident | PReg Ident DepType

instance Show PBinder where
  showsPrec n (PBound v t) r = v ++ ": " ++ showsPrec n t r
  showsPrec n (PReg v t) r = v ++ ": " ++ showsPrec n t r

binderName :: PBinder -> Ident
binderName (PBound v _) = v
binderName (PReg v _) = v

binderType :: PBinder -> DepType
binderType (PBound _ t) = (DepType t [])
binderType (PReg _ ty) = ty

data SExpr = SVar Ident | App Ident [SExpr]

instance Show SExpr where
  showsPrec n (SVar v) r = v ++ r
  showsPrec n (App v []) r = v ++ r
  showsPrec n (App v vs) r =
    let f r = v ++ foldr (\e r -> ' ' : showsPrec 1 e r) r vs in
    if n == 0 then f r else '(' : f (')' : r)

data Decl =
    DTerm
      [PBinder]  -- bound variables, args
      DepType    -- return type
  | DAxiom
      [PBinder]  -- bound variables, args
      [SExpr]    -- hypotheses
      SExpr      -- conclusion
  | DDef
      [PBinder]  -- bound variables, args
      DepType    -- return type
      (Maybe (
        M.Map Ident Ident, -- dummy vars
        SExpr))            -- definition
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

getTerm :: Environment -> Ident -> Maybe ([PBinder], DepType)
getTerm e v = eDecls e M.!? v >>= go where
  go (DTerm args r) = Just (args, r)
  go (DDef args r _) = Just (args, r)
  go (DAxiom _ _ _) = Nothing

getArity :: Environment -> Ident -> Maybe Int
getArity e v = length . fst <$> getTerm e v

getVarM :: MonadError String m => Ident -> Stack -> m VarType
getVarM v s = fromJustError "type depends on unknown variable" (sVars s M.!? v)

varTypeToDep :: [Ident] -> VarType -> DepType
varTypeToDep ds (VType t) = DepType t []
varTypeToDep ds (Open t) = DepType t ds
