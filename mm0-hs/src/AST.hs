module AST where

import Control.Monad.Except
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import qualified Data.Map.Strict as M
import Environment (Ident, DepType(..), SortData(..))
import Util

type AST = [Stmt]

data Stmt = Sort Ident SortData
  | Var [Ident] VarType
  | Term Ident [Binder] DepType
  | Axiom Ident [Binder] Formula
  | Theorem Ident [Binder] Formula
  | Def Ident [Binder] DepType (Maybe Formula)
  | Notation Notation
  | Inout Inout
  | Block [Stmt]

data Notation =
    Delimiter Const
  | Prefix Ident Const Prec
  | Infix Bool Ident Const Prec
  | Coercion Ident Ident Ident
  | NNotation Ident [Binder] DepType [Literal]
  deriving (Show)

data Literal = NConst Const Prec | NVar Ident deriving (Show)

type Const = B.ByteString
type Prec = Int

type InputKind = String
type OutputKind = String

data Inout =
    Input InputKind [Either Ident Formula]
  | Output OutputKind [Either Ident Formula]
  deriving (Show)

data Local = LBound Ident | LReg Ident | LDummy Ident | LAnon

instance Show Local where
  showsPrec _ (LBound v) r = v ++ r
  showsPrec _ (LReg v) r = v ++ r
  showsPrec _ (LDummy v) r = '.' : v ++ r
  showsPrec _ LAnon r = '_' : r

data Type = TType DepType | TFormula Formula deriving (Eq)

instance Show Type where
  showsPrec _ (TType ty) r = shows ty r
  showsPrec _ (TFormula f) r = '$' : C.unpack f ++ '$' : r

data VarType = VTReg Ident | Open Ident

instance Show VarType where
  showsPrec _ (VTReg v) r = v ++ r
  showsPrec _ (Open v) r = v ++ '*' : r

type Formula = B.ByteString

data Binder = Binder Local Type

showsBinderGroup :: [Local] -> Type -> ShowS
showsBinderGroup (l : ls) ty =
  let f = shows l . flip (foldr (\i -> (' ' :) . shows i)) ls . (": " ++) . shows ty in
  if isLBound l then ('{' :) . f . ('}' :) else ('(' :) . f . (')' :)

instance Show Binder where
  showsPrec _ (Binder l ty) = showsBinderGroup [l] ty

isLBound :: Local -> Bool
isLBound (LBound _) = True
isLBound _ = False

localName :: Local -> Maybe Ident
localName (LBound v) = Just v
localName (LReg v) = Just v
localName (LDummy v) = Just v
localName LAnon = Nothing

type Vars = M.Map Ident VarType

data Stack = Stack {
  sVars :: Vars,
  sRest :: Maybe Stack }
  deriving (Show)

getVarM :: MonadError String m => Ident -> Stack -> m VarType
getVarM v s = fromJustError "type depends on unknown variable" (sVars s M.!? v)

varTypeToDep :: [Ident] -> VarType -> DepType
varTypeToDep ds (VTReg t) = DepType t []
varTypeToDep ds (Open t) = DepType t ds

varTypeSort :: VarType -> Ident
varTypeSort (VTReg s) = s
varTypeSort (Open s) = s

showsGroupedBinders :: [Binder] -> ShowS
showsGroupedBinders bis r =
  foldr (\(gr, ty) -> (' ' :) . showsBinderGroup gr ty) r (join bis Nothing)
  where
  join :: [Binder] -> Maybe ([Local], Bool, Type) -> [([Local], Type)]
  join [] o = flush o []
  join (Binder x ty : bis) (Just (xs, b, ty')) | isLBound x == b && ty == ty' =
    join bis (Just (x : xs, b, ty'))
  join (Binder x ty : bis) o = flush o (join bis (Just ([x], isLBound x, ty)))

  flush :: Maybe ([Local], Bool, Type) -> [([Local], Type)] -> [([Local], Type)]
  flush Nothing l = l
  flush (Just (xs, _, ty)) l = (reverse xs, ty) : l

showsAssert :: [Binder] -> Formula -> ShowS
showsAssert l f = let (l1, l2) = split l in
    showsGroupedBinders l1 . (':' :) .
    flip (foldr (\f -> ("\n  $" ++) . (C.unpack f ++) . ("$ >" ++))) l2 .
    ("\n  $" ++) . (C.unpack f ++) . ("$;" ++)
  where
  split :: [Binder] -> ([Binder], [Formula])
  split [] = ([], [])
  split (bi : bis) = case split bis of
    ([], r) -> case bi of
      Binder _ (TFormula f) -> ([], f : r)
      _ -> ([bi], r)
    (l, r) -> (bi : l, r)

instance Show Stmt where
  showsPrec _ (Sort x (SortData p s pr f)) r =
    (if p then "pure " else "") ++ (if s then "strict " else "") ++
    (if pr then "provable " else "") ++ (if f then "free " else "") ++
    "sort " ++ x ++ ';' : r
  showsPrec _ (Var ids ty) r = "var" ++
    foldr (\i r -> ' ' : i ++ r) (": " ++ shows ty (';' : r)) ids
  showsPrec _ (Term x bis ty) r = "term " ++ x ++
    showsGroupedBinders bis (": " ++ shows ty (';' : r))
  showsPrec _ (Axiom x bis ty) r = "axiom " ++ x ++ showsAssert bis ty r
  showsPrec _ (Theorem x bis ty) r = "theorem " ++ x ++ showsAssert bis ty r
  showsPrec _ (Def x bis ty o) r = "def " ++ x ++
    showsGroupedBinders bis (": " ++ shows ty s) where
    s = case o of
      Nothing -> ';' : r
      Just f -> " = " ++ shows f (';' : r)
  showsPrec _ (Notation n) r = shows n r
  showsPrec _ (Inout io) r = shows io r
  showsPrec _ (Block ss) r = "{" ++
    foldr (\s r -> '\n' : shows s ('\n' : r)) ("}" ++ r) ss
