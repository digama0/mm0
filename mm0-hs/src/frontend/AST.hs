module AST (module AST, Ident, DepType(..), SortData(..)) where

import Control.Monad.Except
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import Environment (Ident, DepType(..), SortData(..))
import Util

type AST = [Stmt]

data Stmt =
    Sort Ident SortData
  | Term Ident [Binder] DepType
  | Axiom Ident [Binder] Formula
  | Theorem Ident [Binder] Formula
  | Def Ident [Binder] DepType (Maybe Formula)
  | Notation Notation
  | Inout Inout

data Notation =
    Delimiter Const
  | Prefix Ident Const Prec
  | Infix Bool Ident Const Prec
  | Coercion Ident Ident Ident
  | NNotation Ident [Binder] DepType [Literal]

data Literal = NConst Const Prec | NVar Ident

data Const = Const T.Text
type Prec = Int

instance Show Const where
  showsPrec _ (Const f) r =  '$' : T.unpack f ++ '$' : r

type InputKind = T.Text
type OutputKind = T.Text

data Inout =
    Input InputKind [Either Ident Formula]
  | Output OutputKind [Either Ident Formula]

data Local = LBound Ident | LReg Ident | LDummy Ident | LAnon

instance Show Local where
  showsPrec _ (LBound v) r = T.unpack v ++ r
  showsPrec _ (LReg v) r = T.unpack v ++ r
  showsPrec _ (LDummy v) r = '.' : T.unpack v ++ r
  showsPrec _ LAnon r = '_' : r

data Type = TType DepType | TFormula Formula

instance Show Type where
  showsPrec _ (TType ty) = shows ty
  showsPrec _ (TFormula f) = shows f

data Formula = Formula T.Text

instance Show Formula where
  showsPrec _ (Formula f) r =  '$' : T.unpack f ++ '$' : r

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

eqType :: Type -> Type -> Bool
eqType (TType t1) (TType t2) = t1 == t2
eqType _ _ = False

showsGroupedBinders :: [Binder] -> ShowS
showsGroupedBinders bis r =
  foldr (\(gr, ty) -> (' ' :) . showsBinderGroup gr ty) r (join bis Nothing)
  where
  join :: [Binder] -> Maybe ([Local], Bool, Type) -> [([Local], Type)]
  join [] o = flush o []
  join (Binder x ty : bis) (Just (xs, b, ty')) | isLBound x == b && eqType ty ty' =
    join bis (Just (x : xs, b, ty'))
  join (Binder x ty : bis) o = flush o (join bis (Just ([x], isLBound x, ty)))

  flush :: Maybe ([Local], Bool, Type) -> [([Local], Type)] -> [([Local], Type)]
  flush Nothing l = l
  flush (Just (xs, _, ty)) l = (reverse xs, ty) : l

showsAssert :: [Binder] -> Formula -> ShowS
showsAssert l f = let (l1, l2) = split l in
    showsGroupedBinders l1 . (':' :) .
    flip (foldr (\f -> ("\n  " ++) . shows f . (" >" ++))) l2 .
    ("\n  " ++) . shows f . (';' :)
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
    "sort " ++ T.unpack x ++ ';' : r
  showsPrec _ (Term x bis ty) r = "term " ++ T.unpack x ++
    showsGroupedBinders bis (": " ++ shows ty (';' : r))
  showsPrec _ (Axiom x bis ty) r = "axiom " ++ T.unpack x ++ showsAssert bis ty r
  showsPrec _ (Theorem x bis ty) r = "theorem " ++ T.unpack x ++ showsAssert bis ty r
  showsPrec _ (Def x bis ty o) r = "def " ++ T.unpack x ++
    showsGroupedBinders bis (": " ++ shows ty s) where
    s = case o of
      Nothing -> ';' : r
      Just f -> " = " ++ shows f (';' : r)
  showsPrec _ (Notation n) r = shows n r
  showsPrec _ (Inout io) r = shows io r

instance Show Notation where
  showsPrec _ (Delimiter ds) = ("delimiter " ++) . shows ds . (';' :)
  showsPrec _ (Prefix x s prec) = ("prefix " ++) . (T.unpack x ++) .
    (": " ++) . shows s . (" prec " ++) . shows prec . (';' :)
  showsPrec _ (Infix right x s prec) = ("infix" ++) .
    (((if right then 'r' else 'l') : ' ' : T.unpack x) ++) .
    (": " ++) . shows s . (" prec " ++) . shows prec . (';' :)
  showsPrec _ (NNotation x bis ty lits) = ("notation " ++) . (T.unpack x ++) .
    showsGroupedBinders bis . (": " ++) . shows ty . (" =" ++) .
    flip (foldr (\lit -> (' ' :) . shows lit)) lits

instance Show Literal where
  showsPrec _ (NConst c p) = ('(' :) . shows c . (':' :) . shows p . (')' :)
  showsPrec _ (NVar v) = shows v

showsIdentFmla :: Either Ident Formula -> ShowS
showsIdentFmla (Left v) = (T.unpack v ++)
showsIdentFmla (Right f) = shows f

instance Show Inout where
  showsPrec _ (Input ik fs) = ("input " ++) . (T.unpack ik ++) .
    flip (foldr (\s -> (' ' :) . showsIdentFmla s)) fs
  showsPrec _ (Output ik fs) = ("output " ++) . (T.unpack ik ++) .
    flip (foldr (\s -> (' ' :) . showsIdentFmla s)) fs
