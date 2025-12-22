module MM0.HOL.ToLisp where

import qualified Data.Text as T
import MM0.HOL.Types

class ToLisp a where
  toLisp :: a -> ShowS

newtype Binders a = Binders [(Ident, a)]

instance ToLisp T.Text where
  toLisp s r = "\"" ++ T.unpack s ++ "\"" ++ r

instance ToLisp a => ToLisp (Binders a) where
  toLisp (Binders vs) r = foldr (\(x, t) r' ->
    " (" ++ toLisp x (" " ++ toLisp t (')' : r'))) r vs

instance ToLisp SType where
  toLisp (SType ss s) r = '(' : foldr (\x -> (' ' :) . toLisp x) (' ' : toLisp s (')' : r)) ss

instance ToLisp HType where
  toLisp (HType ss s) r = '(' : foldr (\x -> (' ' :) . toLisp x) (' ' : toLisp s (')' : r)) ss

instance ToLisp SLam where
  toLisp (SLam [] e) r = toLisp e r
  toLisp (SLam vs e) r = ("(fn" ++) $ toLisp (Binders vs) $ ' ' : toLisp e (')' : r)

instance ToLisp Term where
  toLisp (LVar v) = toLisp v
  toLisp (RVar v []) = toLisp v
  toLisp (RVar v xs) = ('(' :) . toLisp v . flip (foldr (\x -> (' ' :) . toLisp x)) xs . (')' :)
  toLisp (HApp t [] []) = toLisp t
  toLisp (HApp t es xs) = ('(' :) . toLisp t .
    flip (foldr (\e -> (' ' :) . toLisp e)) es .
    flip (foldr (\x -> (' ' :) . toLisp x)) xs . (')' :)
  toLisp HTSorry = ('?' :)

instance ToLisp GType where
  toLisp (GType [] e) r = toLisp e r
  toLisp (GType vs e) r = ("(!" ++) $ toLisp (Binders vs) $ ' ' : toLisp e (')' : r)

instance ToLisp TType where
  toLisp (TType vs hs ret) r =
    ("(!! (" ++) $ toLisp (Binders vs) $ (") " ++) $
    flip (foldr (\x -> (' ' :) . toLisp x)) hs $ ' ' : toLisp ret (')' : r)

instance ToLisp HProofLam where
  toLisp (HProofLam [] e) r = toLisp e r
  toLisp (HProofLam vs e) r = ("(fn" ++) $ toLisp (Binders vs) $ ' ' : toLisp e (')' : r)

instance ToLisp HProof where
  toLisp (HHyp v []) = toLisp v
  toLisp (HHyp v xs) = ('(' :) . toLisp v . flip (foldr (\x -> (' ' :) . toLisp x)) xs . (')' :)
  toLisp (HThm t [] [] []) = toLisp t
  toLisp (HThm t es hs xs) = ('(' :) . toLisp t .
    flip (foldr (\e -> (' ' :) . toLisp e)) es .
    flip (foldr (\e -> (' ' :) . toLisp e)) hs .
    flip (foldr (\x -> (' ' :) . toLisp x)) xs . (')' :)
  toLisp (HSave v p xs) = ("(let (" ++) . toLisp v . (' ' :) . toLisp p .
    (")\n" ++) . toLisp (RVar v xs) . (')' :)
  toLisp (HForget _ p) = ("(forget " ++) . toLisp p . (')' :)
  toLisp (HConv c p) = ("(mp " ++) . toLisp c . (' ' :) . toLisp p . (')' :)
  toLisp HSorry = ('?' :)

instance ToLisp HConvLam where
  toLisp (HConvLam [] e) r = toLisp e r
  toLisp (HConvLam vs e) r = ("(fn" ++) $ toLisp (Binders vs) $ ' ' : toLisp e (')' : r)

instance ToLisp HConv where
  toLisp (CRefl _) = ("rfl" ++)
  toLisp (CSymm c) = ("(-" ++) . toLisp c . (')' :)
  toLisp (CTrans c1 c2) = ("(+" ++) . toLisp c1 . (' ' :) . toLisp c2 . (')' :)
  toLisp (CCong t cs xs) =  ('(' :) . toLisp t .
    flip (foldr (\e -> (' ' :) . toLisp e)) cs .
    flip (foldr (\e -> (' ' :) . toLisp e)) xs . (')' :)
  toLisp (CDef t es xs) = ("(delta " ++) . toLisp t .
    flip (foldr (\e -> (' ' :) . toLisp e)) es .
    flip (foldr (\e -> (' ' :) . toLisp e)) xs . (')' :)

instance ToLisp HDecl where
  toLisp (HDSort s) r = "(sort " ++ toLisp s (')' : r)
  toLisp (HDTerm t ty) r = "(term " ++ toLisp t (" " ++ toLisp ty (')' : r))
  toLisp (HDDef t rv lv s val) r =
    ("(def " ++) $ toLisp t $ (" (for" ++) $ toLisp (Binders rv) $
    toLisp (Binders lv) $ (") " ++) $ toLisp s $ toLisp val $ ')' : r
  toLisp (HDThm t ty Nothing) r = ("(axiom " ++) $ toLisp t $ (' ' :) $ toLisp ty $ ')' : r
  toLisp (HDThm t (TType vs hs (GType ss ret)) (Just (gs, p))) r =
    ("(theorem " ++) $ toLisp t $ (" (for" ++) $ toLisp (Binders vs) $ (") (for" ++) $
    toLisp (Binders $ zip gs hs) $ (") (for" ++) $ toLisp (Binders ss) $ (") " ++) $
    toLisp ret $ ("\n  " ++) $ toLisp p $ ')' : r

instance ToLisp a => ToLisp (WithComment a) where
  toLisp (WC Nothing a) = toLisp a
  toLisp (WC (Just s) a) = (";; " ++) . flip (T.foldr replace) s . ('\n' :) . toLisp a where
    replace '\n' = ("\n;; " ++)
    replace c = (c :)
