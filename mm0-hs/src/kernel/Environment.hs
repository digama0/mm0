module Environment where

import qualified Data.Map.Strict as M
import qualified Data.Sequence as Q

type Ident = String

data DepType = DepType {
  dSort :: Ident,
  dDeps :: [Ident] } deriving (Eq)

instance Show DepType where
  showsPrec _ (DepType t ts) r =
    t ++ foldr (\t' r -> ' ' : t' ++ r) r ts

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

data SortData = SortData {
  sPure :: Bool,
  sStrict :: Bool,
  sProvable :: Bool,
  sFree :: Bool }
  deriving (Show)

data Spec =
    SSort Ident SortData
  | SDecl Ident Decl
  | SThm {
      tName :: Ident,
      tArgs :: [PBinder],
      tHyps :: [SExpr],
      tReturn :: SExpr }
  deriving (Show)

data Environment = Environment {
  eSorts :: M.Map Ident SortData,
  eDecls :: M.Map Ident Decl,
  eSpec :: Q.Seq Spec }
  deriving (Show)

newEnv :: Environment
newEnv = Environment M.empty M.empty Q.empty

getTerm :: Environment -> Ident -> Maybe ([PBinder], DepType)
getTerm e v = eDecls e M.!? v >>= go where
  go (DTerm args r) = Just (args, r)
  go (DDef args r _) = Just (args, r)
  go (DAxiom _ _ _) = Nothing

getArity :: Environment -> Ident -> Maybe Int
getArity e v = length . fst <$> getTerm e v
