module ToLean(leanToString, writeLean) where

import Data.Semigroup
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State.Strict
import Environment (Ident)
import HolTypes
import Util

data LeanState = LeanState

mkLeanState :: LeanState
mkLeanState = LeanState

type LeanM m = ReaderT (String -> m ()) (StateT LeanState m)

writeLean :: Monad m => (String -> m ()) -> [HDecl] -> m ()
writeLean f ds = evalStateT (runReaderT (preamble $ mapM_ leanDecl ds) f) mkLeanState

leanToString :: [HDecl] -> [String]
leanToString ds = appEndo (execWriter $ writeLean (tell . Endo . (:)) ds) []

emit :: Monad m => String -> LeanM m ()
emit s = do f <- ask; lift $ lift $ f s

preamble :: Monad m => LeanM m () -> LeanM m ()
preamble m = emit "namespace mm0\n" >> m >> emit "end mm0"

mangle :: String -> ShowS
mangle ('_' : s) r = '\x00AB' : s ++ '\x00BB' : r
mangle s r = s ++ r

printSType :: Bool -> SType -> ShowS
printSType p (SType [] s) = mangle s
printSType p (SType ss s) = showParen p $
  \r -> foldr (\x -> mangle x . (" \x2192 " ++)) (mangle s r) ss

printHType :: HType -> ShowS
printHType (HType [] s) r = printSType False s r
printHType (HType ss s) r =
  foldr (\x -> printSType True x . (" \x2192 " ++)) (printSType False s r) ss

printBinderGroup :: [Ident] -> ShowS -> ShowS
printBinderGroup ls pr r =
  " (" ++ foldr (\i -> mangle i . (' ' :)) (": " ++ pr (')' : r)) ls

printGroupedBinders :: [(Ident, SType)] -> ShowS
printGroupedBinders bis r =
  foldr (\(gr, ty) -> printBinderGroup gr (printSType False ty)) r (join bis Nothing)
  where
  join :: [(Ident, SType)] -> Maybe ([Ident], SType) -> [([Ident], SType)]
  join [] o = flush o []
  join ((x, ty) : bis) (Just (xs, ty')) | ty == ty' =
    join bis (Just (x : xs, ty'))
  join ((x, ty) : bis) o = flush o (join bis (Just ([x], ty)))

  flush :: Maybe ([Ident], SType) -> [([Ident], SType)] -> [([Ident], SType)]
  flush Nothing l = l
  flush (Just (xs, ty)) l = (reverse xs, ty) : l

shortBinds :: Char -> [(Ident, Sort)] -> ShowS
shortBinds c vs r = c : foldr (\(v, _) -> (' ' :) . mangle v) (", " ++ r) vs

printSLam :: Bool -> SLam -> ShowS
printSLam p (SLam [] e) = printTerm p e
printSLam p (SLam vs e) = showParen p $ shortBinds '\x03BB' vs . shows e

printTerm :: Bool -> Term -> ShowS
printTerm p (LVar v) = mangle v
printTerm p (RVar v []) = mangle v
printTerm p (RVar v xs) = showParen p $
  mangle v . flip (foldr (\x -> (' ' :) . mangle x)) xs
printTerm p (HApp t [] []) = mangle t
printTerm p (HApp t es xs) = showParen p $ mangle t .
  flip (foldr (\e -> (' ' :) . printSLam True e)) es .
  flip (foldr (\x -> (' ' :) . mangle x)) xs
printTerm p HTSorry = ("sorry" ++)

printGType :: Bool -> GType -> ShowS
printGType _ (GType [] e) = ("\x22A6 " ++) . shows e
printGType p (GType vs e) = showParen p $
  shortBinds '\x2200' vs . ("\x22A6 " ++) . shows e

printProofLam :: Bool -> HProofLam -> ShowS
printProofLam p (HProofLam [] e) = printProof p e
printProofLam p (HProofLam vs e) = showParen p $
  shortBinds '\x03BB' vs . printProof False e

printProof :: Bool -> HProof -> ShowS
printProof p (HHyp v []) = mangle v
printProof p (HHyp v xs) = showParen p $
  (v ++) . flip (foldr (\x -> (' ' :) . mangle x)) xs
printProof p (HThm t [] [] []) = mangle t
printProof p (HThm t es hs xs) = showParen p $ mangle t .
  flip (foldr (\e -> (' ' :) . printSLam True e)) es .
  flip (foldr (\e -> (' ' :) . printProofLam True e)) hs .
  flip (foldr (\x -> (' ' :) . mangle x)) xs
printProof p (HSave v pr xs) = showParen p $ \r ->
  "let " ++ mangle v (" := " ++ shows pr (" in " ++ shows (HHyp v xs) r))
printProof p (HForget pr) = showParen p $ ("forget " ++) . shows pr
printProof p (HConv _ pr) = printProof p pr
printProof p HSorry = ("sorry" ++)

leanDecl :: Monad m => HDecl -> LeanM m ()
leanDecl (HDSort s) = do
  let s' = mangle s
  emit $ "constant " ++ s' " : Type\n"
  emit $ "constant " ++ s' ".proof : " ++ s' " \x2192 Prop"
  emit $ "prefix `\x22A6`:26 := " ++ s' ".proof"
  emit $ "constant " ++ s' ".forget {p : Prop} : (" ++ s' " \x2192 p) \x2192 p"
  emit $ "open " ++ s' "(forget)\n"
leanDecl (HDTerm x ty) = emit $ "constant " ++ mangle x " : " ++ printHType ty "\n"
leanDecl (HDDef x ss xs r t) =
  let bis = printGroupedBinders (ss ++ (mapSnd (SType []) <$> xs)) in
  emit $ ("def " ++) $ mangle x $ bis (" : " ++ r ++ " :=\n" ++ printTerm False t "\n")
leanDecl (HDThm x (TType vs gs ret) Nothing) =
  emit $ ("axiom " ++) $ mangle x $ printGroupedBinders vs $ " : " ++
    foldr (\g r -> printGType True g (" \x2192 " ++ r)) (printGType False ret "\n") gs
leanDecl (HDThm x (TType vs gs (GType xs ret)) (Just (hs, pr))) = do
  let bis1 = printGroupedBinders vs
  let bis2 r = foldr (\(h, g) ->
        printBinderGroup [h] (printGType False g)) r (zip hs gs)
  let bis3 = printGroupedBinders (mapSnd (SType []) <$> xs)
  emit $ ("theorem " ++) $ mangle x $ bis1 $ bis2 $ bis3 $ " : \x22A6 " ++ printTerm False ret " :="
  emit $ printProof False pr "\n"
