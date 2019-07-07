module CAST (module CAST, Ident, DepType(..), SortData(..)) where

import Control.Monad.Except
import qualified Data.ByteString as B
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import Environment (Ident, SortData(..))
import Util

type Offset = Int
data AtPos a = AtPos Offset a
data Span a = Span Offset a Offset

instance Functor AtPos where
  fmap f (AtPos l a) = AtPos l (f a)

type AST = [AtPos Stmt]

data Visibility = Public | Abstract | Local | VisDefault
data DeclKind = DKTerm | DKAxiom | DKTheorem | DKDef
data Stmt =
    Sort Ident SortData
  | Decl Visibility DeclKind Ident [Binder] (Maybe [Type]) (Maybe LispVal)
  | Theorems [Binder] [LispVal]
  | Notation Notation
  | Inout Inout
  | Annot LispVal Stmt
  | Do [LispVal]

data Notation =
    Delimiter [Char]
  | Prefix Ident Const Prec
  | Infix Bool Ident Const Prec
  | Coercion Ident Ident Ident
  | NNotation Ident [Binder] (Maybe Type) [Literal]

data Literal = NConst Const Prec | NVar Ident

data Const = Const T.Text
type Prec = Int

type InputKind = String
type OutputKind = String

data Inout =
    Input InputKind [LispVal]
  | Output OutputKind [LispVal]

data Local = LBound Ident | LReg Ident | LDummy Ident | LAnon

data DepType = DepType (AtPos Ident) [AtPos Ident]

data Type = TType DepType | TFormula Formula

data Formula = Formula Offset T.Text

data Binder = Binder Offset Local (Maybe Type)

isLBound :: Local -> Bool
isLBound (LBound _) = True
isLBound _ = False

localName :: Local -> Maybe Ident
localName (LBound v) = Just v
localName (LReg v) = Just v
localName (LDummy v) = Just v
localName LAnon = Nothing

data LispVal =
    Atom T.Text
  | List [LispVal]
  | Cons LispVal LispVal
  | Number Integer
  | String T.Text
  | Bool Bool
  | LFormula Formula

cons :: LispVal -> LispVal -> LispVal
cons l (List r) = List (l : r)
cons l r = Cons l r
