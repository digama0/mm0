module CAST (module CAST, DepType(..), SortData(..)) where

import Control.Monad.Except
import qualified Data.ByteString as B
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import Environment (SortData(..))
import Util

type Offset = Int
data AtPos a = AtPos Offset a
data Span a = Span Offset a Offset

instance Functor AtPos where
  fmap f (AtPos l a) = AtPos l (f a)

type AST = [AtPos Stmt]

data Visibility = Public | Abstract | Local | VisDefault deriving (Eq)
data DeclKind = DKTerm | DKAxiom | DKTheorem | DKDef deriving (Eq)
data Stmt =
    Sort Offset T.Text SortData
  | Decl Visibility DeclKind Offset T.Text
      [Binder] (Maybe [Type]) (Maybe LispVal)
  | Theorems [Binder] [LispVal]
  | Notation Notation
  | Inout Inout
  | Annot LispVal (AtPos Stmt)
  | Do [LispVal]

data Notation =
    Delimiter [Char]
  | Prefix Offset T.Text Const Prec
  | Infix Bool Offset T.Text Const Prec
  | Coercion T.Text T.Text T.Text
  | NNotation T.Text [Binder] (Maybe Type) [Literal]

data Literal = NConst Const Prec | NVar T.Text

data Const = Const {cOffs :: Offset, cToken :: T.Text}
type Prec = Int

type InputKind = T.Text
type OutputKind = T.Text

data Inout =
    Input InputKind [LispVal]
  | Output OutputKind [LispVal]

data Local = LBound T.Text | LReg T.Text | LDummy T.Text | LAnon

data DepType = DepType (AtPos T.Text) [AtPos T.Text]

data Formula = Formula Offset T.Text

data Type = TType DepType | TFormula Formula

tyOffset :: Type -> Offset
tyOffset (TType (DepType (AtPos o _) _)) = o
tyOffset (TFormula (Formula o _)) = o

data Binder = Binder Offset Local (Maybe Type)

isLBound :: Local -> Bool
isLBound (LBound _) = True
isLBound _ = False

isLCurly :: Local -> Bool
isLCurly (LBound _) = True
isLCurly (LDummy _) = True
isLCurly _ = False

localName :: Local -> Maybe T.Text
localName (LBound v) = Just v
localName (LReg v) = Just v
localName (LDummy v) = Just v
localName LAnon = Nothing

data LispVal =
    Atom T.Text
  | List [LispVal]
  | DottedList [LispVal] LispVal
  | Number Integer
  | String T.Text
  | Bool Bool
  | LFormula Formula

cons :: LispVal -> LispVal -> LispVal
cons l (List r) = List (l : r)
cons l (DottedList rs r) = DottedList (l : rs) r

lvLength :: LispVal -> Int
lvLength (DottedList e _) = length e
lvLength (List e) = length e
lvLength _ = 0

data LocalCtx = LocalCtx {

}
