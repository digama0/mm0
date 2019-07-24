module MM0.Compiler.AST (module MM0.Compiler.AST,
  AtDepType(..), SortData(..)) where

import qualified Data.Vector as V
import qualified Data.Text as T
import MM0.Kernel.Environment (SortData(..), DepType(..))

type Offset = Int
data AtPos a = AtPos Offset a
type Range = (Offset, Offset)
data Span a = Span Range a

instance Functor AtPos where
  fmap f (AtPos o a) = AtPos o (f a)

instance Show a => Show (AtPos a) where
  showsPrec n = showsPrec n . unPos

instance Functor Span where
  fmap f (Span o a) = Span o (f a)

instance Show a => Show (Span a) where
  showsPrec n = showsPrec n . unSpan

unPos :: AtPos a -> a
unPos (AtPos _ a) = a

unSpan :: Span a -> a
unSpan (Span _ a) = a

type AST = V.Vector (Span Stmt)

data Visibility = Public | Abstract | Local | VisDefault deriving (Eq)
data DeclKind = DKTerm | DKAxiom | DKTheorem | DKDef deriving (Eq)
instance Show DeclKind where
  show DKTerm = "term"
  show DKAxiom = "axiom"
  show DKTheorem = "theorem"
  show DKDef = "def"

data Stmt =
    Sort Offset T.Text SortData
  | Decl Visibility DeclKind Offset T.Text
      [Binder] (Maybe [Type]) (Maybe AtLisp)
  | Theorems [Binder] [AtLisp]
  | Notation Notation
  | Inout Inout
  | Annot AtLisp (Span Stmt)
  | Do [AtLisp]

data Notation =
    Delimiter [Char] (Maybe [Char])
  | Prefix Offset T.Text Const Prec
  | Infix Bool Offset T.Text Const Prec
  | Coercion Offset T.Text T.Text T.Text
  | NNotation Offset T.Text [Binder] (Maybe Type) [AtPos Literal]

data Literal = NConst Const Prec | NVar T.Text

data Const = Const {cOffs :: Offset, cToken :: T.Text}
data Prec = Prec Int | PrecMax deriving (Eq)

instance Show Prec where
  show (Prec n) = show n
  show PrecMax = "max"

instance Ord Prec where
  _ <= PrecMax = True
  PrecMax <= _ = False
  Prec m <= Prec n = m <= n

type InputKind = T.Text
type OutputKind = T.Text

data Inout =
    Input InputKind [AtLisp]
  | Output OutputKind [AtLisp]

data Local = LBound T.Text | LReg T.Text | LDummy T.Text | LAnon deriving (Show)

data AtDepType = AtDepType (AtPos T.Text) [AtPos T.Text] deriving (Show)

unDepType :: AtDepType -> DepType
unDepType (AtDepType t ts) = DepType (unPos t) (unPos <$> ts)

data Formula = Formula Offset T.Text deriving (Show)

data Type = TType AtDepType | TFormula Formula deriving (Show)

tyOffset :: Type -> Offset
tyOffset (TType (AtDepType (AtPos o _) _)) = o
tyOffset (TFormula (Formula o _)) = o

data Binder = Binder Offset Local (Maybe Type) deriving (Show)

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

type AtLisp = Span LispAST
data LispAST =
    AAtom T.Text
  | AList [AtLisp]
  | ADottedList AtLisp [AtLisp] AtLisp
  | ANumber Integer
  | AString T.Text
  | ABool Bool
  | AFormula Formula

instance Show LispAST where
  showsPrec _ (AAtom e) = (T.unpack e ++)
  showsPrec _ (AList [Span _ (AAtom "quote"), e]) = ('\'' :) . shows e
  showsPrec _ (AList [Span _ (AAtom "unquote"), e]) = (',' :) . shows e
  showsPrec _ (AList ls) = ('(' :) . f ls . (')' :) where
    f [] = id
    f [e] = shows e
    f (e : es) = shows e . (' ' :) . f es
  showsPrec _ (ADottedList l ls e') =
    ('(' :) . flip (foldr (\e -> shows e . (' ' :))) (l : ls) .
    (". " ++) . shows e' . (')' :)
  showsPrec _ (ANumber n) = shows n
  showsPrec _ (AString s) = shows s
  showsPrec _ (ABool True) = ("#t" ++)
  showsPrec _ (ABool False) = ("#f" ++)
  showsPrec _ (AFormula (Formula _ f)) = ('$' :) . (T.unpack f ++) . ('$' :)

data QExpr = QApp (Span T.Text) [QExpr] | QUnquote AtLisp deriving (Show)
