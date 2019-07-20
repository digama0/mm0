module MM0.Compiler.PrettyPrinter (PP, doc, dlift, ppExpr, render, ppExpr', (<+>),
  unifyErr) where

import Control.Applicative
import Control.Monad.State
import Data.Void
import Data.Text.Prettyprint.Doc hiding (lparen, rparen)
import Data.Text.Prettyprint.Doc.Render.Text
import qualified Data.HashMap.Strict as H
import qualified Data.Vector as V
import qualified Data.Text as T
import MM0.Compiler.Env
import MM0.FrontEnd.MathParser (appPrec)

data PP = PP {
  _lTerminate :: Bool,
  _rTerminate :: Bool,
  small :: Bool,
  doc :: Doc Void }

dlift :: Doc Void -> PP
dlift = PP False False False

word :: T.Text -> PP
word = PP False False True . pretty

dmap :: (Doc Void -> Doc Void) -> PP -> PP
dmap f (PP l r s e) = PP l r s (f e)

surround' :: Doc Void -> PP -> PP -> PP
surround' x (PP l _ _ dl) (PP _ r _ dr) = PP l r False (dl <> x <> dr)

(<<>>) :: PP -> PP -> PP
(<<>>) (PP l lr _ dl) (PP rl r _ dr) = PP l r False $
  dl <> (if lr || rl then softline' else softline) <> dr

(<<|>>) :: PP -> PP -> PP
(<<|>>) (PP l lr _ dl) (PP rl r _ dr) = PP l r False $
  dl <> (if lr || rl then line' else line) <> dr

render :: PP -> T.Text
render = renderStrict . layoutPretty defaultLayoutOptions . doc

ppExpr' :: LispVal -> ElabM T.Text
ppExpr' = fmap render . ppExpr

unifyErr :: LispVal -> LispVal -> ElabM PP
unifyErr e1 e2 = liftA2
  (\p1 p2 -> dlift $ sep ["failed to unify:", doc p1, flatAlt "  =?=" "=?=", doc p2])
  (ppExpr e1) (ppExpr e2)

ppExpr :: LispVal -> ElabM PP
ppExpr v = gets (pDelims . ePE) >>= flip ppExpr1 v

ppExpr1 :: Delims -> LispVal -> ElabM PP
ppExpr1 delims = \v -> ppExpr2 (Prec 0) v where

  token :: Token -> PP
  token tk =
    let l = delimVal delims (T.head tk)
        r = delimVal delims (T.last tk) in
    PP (isRightDelim l) (isLeftDelim r) True $ pretty tk

  lparen = token "("
  rparen = token ")"

  ppExpr2 :: Prec -> LispVal -> ElabM PP
  ppExpr2 tgt (Ref g) = getRef g >>= ppExpr2 tgt
  ppExpr2 _ (MVar n _ _ _) = return $ word $ "?" <> alphanumber n
  ppExpr2 _ (Atom _ x) = return $ word x
  ppExpr2 tgt (List (Atom _ t : es)) = try (now >>= getTerm t) >>= \case
    Nothing -> ppApp tgt ("?" <> t <> "?") <$> mapM (ppExpr2 PrecMax) es
    Just (_, _, _, Nothing) -> ppApp tgt t <$> mapM (ppExpr2 PrecMax) es
    Just (_, _, _, Just (NCoe _ _)) -> case es of
      [e] -> ppExpr2 tgt e
      _ -> ppApp tgt ("?" <> t <> "?") <$> mapM (ppExpr2 PrecMax) es
    Just (_, _, _, Just (NPrefix tk)) -> do
      PrefixInfo _ _ lits <- gets ((H.! tk) . pPrefixes . ePE)
      (_, p) <- gets ((H.! tk) . pPrec . ePE)
      parenBelow p tgt <$> ppPfx tk lits es
    Just (_, _, _, Just (NInfix tk)) -> case es of
      [e1, e2] -> do
        InfixInfo _ _ r <- gets ((H.! tk) . pInfixes . ePE)
        (_, p) <- gets ((H.! tk) . pPrec . ePE)
        parenBelow p tgt <$> ppInfix r p t (token tk) e1 e2
      _ -> ppApp tgt ("?" <> t <> "?") <$> mapM (ppExpr2 PrecMax) es
  ppExpr2 _ _ = return $ word "???"

  parenBelow :: Prec -> Prec -> PP -> PP
  parenBelow p tgt e | tgt <= p = e
  parenBelow _ _ e = lparen <<>> e <<>> rparen

  ppApp :: Prec -> T.Text -> [PP] -> PP
  ppApp _ t [] = word t
  ppApp p t es = dmap group $ parenBelow (Prec appPrec) p $
    dmap (nest 2) $ soft (word t) es where

    soft :: PP -> [PP] -> PP
    soft e [] = e
    soft e1 (e2 : es') =
      if small e1 then
        surround' softline e1 (soft e2 es')
      else hard e1 (e2 : es')

    hard :: PP -> [PP] -> PP
    hard e [] = e
    hard e1 (e2 : es') = surround' line e1 (hard e2 es')

  ppPfx :: Token -> [PLiteral] -> [LispVal] -> ElabM PP
  ppPfx tk lits es = go (token tk) lits where
    vec = V.fromList es
    go :: PP -> [PLiteral] -> ElabM PP
    go e [] = return e
    go e (PConst c : lits') = go (e <<>> token c) lits'
    go e (PVar n p : lits') = do
      e' <- ppExpr2 p (vec V.! n)
      go (e <<>> e') lits'

  ppInfix :: Bool -> Prec -> TermName -> PP -> LispVal -> LispVal -> ElabM PP
  ppInfix _ PrecMax _ _ = error "impossible"
  ppInfix r (Prec p) t tk = \e1 e2 ->
    dmap (group . nest 2) <$> (if r then ppInfixr else ppInfixl) e1 e2
    where

    ppInfixl :: LispVal -> LispVal -> ElabM PP
    ppInfixl e1 e2 = do
      pp1 <- case e1 of
        List [Atom _ t', e11, e12] | t == t' -> ppInfixl e11 e12
        _ -> dmap group <$> ppExpr2 (Prec p) e1
      pp2 <- dmap group <$> ppExpr2 (Prec (p+1)) e2
      return (pp1 <<>> tk <<|>> pp2)

    ppInfixr :: LispVal -> LispVal -> ElabM PP
    ppInfixr e1 e2 = do
      pp1 <- dmap group <$> ppExpr2 (Prec (p+1)) e1
      pp2 <- case e2 of
        List [Atom _ t', e21, e22] | t == t' -> ppInfixr e21 e22
        _ -> dmap group <$> ppExpr2 (Prec p) e2
      return (pp1 <<>> tk <<|>> pp2)
