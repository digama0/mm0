{-# LANGUAGE ScopedTypeVariables, BangPatterns #-}
module MM0.Compiler.PositionInfo (Lines, Spans, PosInfo(..), PIType(..),
  getLines, offToPos, posToOff, toSpans, getPosInfo) where

import Control.Monad
import Control.Monad.ST
import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader
import Data.Vector.Algorithms.Search
import qualified Data.HashMap.Strict as H
import qualified Data.Vector as V
import qualified Data.Vector.Mutable.Dynamic as VD
import qualified Data.Text as T
import MM0.Compiler.AST
import MM0.Kernel.Environment (VarName)

type Lines = V.Vector Offset

getLines :: T.Text -> Lines
getLines t = runST $ do
  v <- VD.new 0
  let go '\n' !o = o + 1 <$ VD.pushBack v (o + 1)
      go _ !o = return (o + 1)
  _ <- T.foldl' (\m c -> m >>= go c) (return 0) t
  VD.unsafeFreeze v

binarySearch' :: (a -> Offset) -> V.Vector a -> Offset -> Int
binarySearch' f larr o = runST $
  V.unsafeThaw larr >>= binarySearchP (\a -> o < f a)

offToPos :: Lines -> Offset -> (Int, Int)
offToPos larr o = (line, col) where
  !line = binarySearch' id larr o
  !col = case line of
    0 -> o
    _ -> o - larr V.! (line - 1)

posToOff :: Lines -> Int -> Int -> Offset
posToOff _ 0 c = c
posToOff larr l c = larr V.! (l - 1) + c

data PIType = PISort | PIVar (Maybe Binder) | PITerm | PIMath | PIAtom Bool (Maybe Binder)
data PosInfo = PosInfo T.Text PIType

type Spans = V.Vector (Span PosInfo)
type MakeSpan s = ReaderT (H.HashMap VarName Binder) (ST s)

toSpans :: AtPos Stmt -> Spans
toSpans = \st -> runST $ VD.new 0 >>= \v -> toSpans' v st >> VD.unsafeFreeze v where
  toSpans' :: forall s. VD.STVector s (Span PosInfo) -> AtPos Stmt -> ST s ()
  toSpans' vec = \st -> runReaderT (atStmt st) H.empty where

    push :: Offset -> T.Text -> PIType -> MakeSpan s ()
    push o t i = lift $ VD.pushBack vec (Span o (PosInfo t i) (o + T.length t))

    pushVar :: Offset -> T.Text -> MakeSpan s ()
    pushVar o t = asks (H.lookup t) >>= push o t . PIVar

    atStmt :: AtPos Stmt -> MakeSpan s ()
    atStmt (AtPos _ st) = stmt st

    stmt :: Stmt -> MakeSpan s ()
    stmt (Decl _ _ _ _ bis ty val) =
      withBinders bis (mapM_ (mapM_ typ) ty >> mapM_ (atLisp False) val)
    stmt (Theorems bis val) = withBinders bis (mapM_ (atLisp False) val)
    stmt (Notation (Delimiter _ _)) = return ()
    stmt (Notation (Prefix o t _ _)) = push o t PITerm
    stmt (Notation (Infix _ o t _ _)) = push o t PITerm
    stmt (Notation (Coercion o t _ _)) = push o t PITerm
    stmt (Notation (NNotation o t bis ty lits)) = push o t PITerm >>
      withBinders bis (mapM_ typ ty >> mapM_ atLit lits)
    stmt (Inout (Input _ vals)) = mapM_ (atLisp False) vals
    stmt (Inout (Output _ vals)) = mapM_ (atLisp False) vals
    stmt (Annot anno st) = atLisp False anno >> atStmt st
    stmt (Do val) = mapM_ (atLisp False) val
    stmt (Sort _ _ _) = return ()

    withBinders :: [Binder] -> MakeSpan s () -> MakeSpan s ()
    withBinders [] m = m
    withBinders (bi@(Binder o l ty) : bis) m = do
      forM_ (localName l) $ \n -> push o n (PIVar (Just bi))
      mapM_ typ ty
      local (maybe id (flip H.insert bi) (localName l)) (withBinders bis m)

    typ :: Type -> MakeSpan s ()
    typ (TType (AtDepType (AtPos o t) vs)) = do
      push o t PISort
      forM_ vs $ \(AtPos o' v) -> pushVar o' v
    typ (TFormula f) = formula f

    formula :: Formula -> MakeSpan s ()
    formula (Formula o t) = push o t PIMath

    atLit :: AtPos Literal -> MakeSpan s ()
    atLit (AtPos _ (NConst _ _)) = return ()
    atLit (AtPos o (NVar v)) = pushVar o v

    atLisp :: Bool -> AtLisp -> MakeSpan s ()
    atLisp q (AtLisp o (AAtom t)) = asks (H.lookup t) >>= push o t . PIAtom q
    atLisp _ (AtLisp _ (AList (AtLisp _ (AAtom "quote") : es))) = mapM_ (atLisp True) es
    atLisp _ (AtLisp _ (AList (AtLisp _ (AAtom "unquote") : es))) = mapM_ (atLisp False) es
    atLisp q (AtLisp _ (AList es)) = mapM_ (atLisp q) es
    atLisp q (AtLisp _ (ADottedList l es r)) = atLisp q l >> mapM_ (atLisp q) es >> atLisp q r
    atLisp _ (AtLisp _ (AFormula f)) = formula f
    atLisp _ (AtLisp _ _) = return ()

getPosInfo :: AST -> V.Vector Spans -> Offset -> Maybe (AtPos Stmt, Span PosInfo)
getPosInfo ast spans o =
  case binarySearch' (\(AtPos i _) -> i) ast o of
    0 -> Nothing
    n -> let ss = spans V.! (n - 1) in
      case binarySearch' (\(Span i _ _) -> i) ss o of
        0 -> Nothing
        m -> let s@(Span _ _ j) = ss V.! (m - 1) in
          if o <= j then Just (ast V.! (n - 1), s) else Nothing
