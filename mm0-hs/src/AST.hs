module AST where

import Control.Monad.Except
import qualified Data.ByteString as B
import qualified Data.Map.Strict as M
import Environment (Ident, DepType(..), SortData)
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
  deriving (Show)

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

data Type = TType DepType | TFormula Formula deriving (Show)

data VarType = VTReg Ident | Open Ident

instance Show VarType where
  showsPrec _ (VTReg v) r = v ++ r
  showsPrec _ (Open v) r = v ++ '*' : r

type Formula = B.ByteString

data Binder = Binder Local Type

instance Show Binder where
  showsPrec n (Binder (LBound v) ty) =
    (('{' : v ++ ": ") ++) . showsPrec n ty . ('}' :)
  showsPrec n (Binder l ty) =
    ('(' :) . showsPrec n l . (": " ++) . showsPrec n ty . (')' :)

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
