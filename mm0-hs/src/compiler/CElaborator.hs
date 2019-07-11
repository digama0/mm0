{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module CElaborator (elaborate, ErrorLevel(..), ElabError(..)) where

import Control.Monad.State
import Data.List
import Data.Bits
import Data.Word8
import qualified Data.HashMap.Strict as H
import qualified Data.Vector.Unboxed as U
import qualified Data.Text as T
import CParser (ParseError)
import CAST
import CEnv
import CMathParser
import Util

elaborate :: [ParseError] -> AST -> IO (Env, [ElabError])
elaborate errs ast = do
  (_, env, errs') <- runElab (mapM_ elabStmt ast) (toElabError <$> errs)
  return (env, errs')

elabStmt :: AtPos Stmt -> Elab ()
elabStmt (AtPos pos s) = resuming $ case s of
  Sort px x sd -> addSort px x sd
  Decl vis dk px x bis ret v -> addDecl vis dk px x bis ret v
  Notation (Delimiter cs Nothing) -> lift $ addDelimiters cs cs
  Notation (Delimiter ls (Just rs)) -> lift $ addDelimiters ls rs
  Notation (Prefix px x tk prec) -> addPrefix px x tk prec
  Notation (Infix r px x tk prec) -> addInfix r px x tk prec
  _ -> unimplementedAt pos

checkNew :: ErrorLevel -> Offset -> T.Text -> (v -> Offset) -> T.Text ->
  H.HashMap T.Text v -> ElabM (v -> H.HashMap T.Text v)
checkNew l o msg f k m = case H.lookup k m of
  Nothing -> return (\v -> H.insert k v m)
  Just a -> do
    reportErr $ ElabError l o o msg [(f a, f a, "previously declared here")]
    mzero

addSort :: Offset -> T.Text -> SortData -> ElabM ()
addSort px x sd = do
  ins <- gets eSorts >>= checkNew ELError px
    ("duplicate sort declaration '" <> x <> "'") (\(_, i, _) -> i) x
  n <- next
  modify $ \env -> env {
    eSorts = ins (n, px, sd),
    eProvableSorts = (guard (sProvable sd) >> [x]) ++ eProvableSorts env }

inferDepType :: AtDepType -> ElabM ()
inferDepType (AtDepType (AtPos o t) ts) = do
  lift $ resuming $ do
    (_, _sd) <- try (now >>= getSort t) >>=
      fromJustAt o ("sort '" <> t <> "' not declared")
    -- TODO: check sd
    return ()
  lift $ modifyInfer $ \ic -> ic {
    icDependents = foldl' (\m (AtPos i x) ->
      H.alter (Just . maybe [i] (i:)) x m) (icDependents ic) ts }

inferBinder :: Binder -> ElabM ()
inferBinder bi@(Binder o l oty) = case oty of
  Nothing -> addVar True
  Just (TType ty) -> inferDepType ty >> addVar False
  Just (TFormula f) -> () <$ (parseMath f >>= inferQExprProv)
  where

  addVar :: Bool -> ElabM ()
  addVar noType = do
    locals <- gets (icLocals . eInfer)
    locals' <- case localName l of
      Nothing -> do
        when noType $ escapeAt o "cannot infer variable type"
        return $ locals
      Just n -> do
        ins <- checkNew ELWarning o
          ("variable '" <> n <> "' shadows previous declaration")
          liOffset n locals
        return (ins (LIOld bi Nothing))
    lift $ modifyInfer $ \ic -> ic {icLocals = locals'}

addDecl :: Visibility -> DeclKind -> Offset -> T.Text ->
  [Binder] -> Maybe [Type] -> Maybe LispVal -> ElabM ()
addDecl _vis _dk _px _x bis ret _v = do
  let (bis', ret') = unArrow bis ret
  withInfer $ do
    mapM_ inferBinder bis'
    case ret' of
      Nothing -> return ()
      Just (TType ty) -> inferDepType ty
      Just (TFormula f) -> () <$ (parseMath f >>= inferQExprProv)
    return ()

unArrow :: [Binder] -> Maybe [Type] -> ([Binder], Maybe Type)
unArrow bis Nothing = (bis, Nothing)
unArrow bis (Just tys') = mapFst (bis ++) (go tys') where
  go [] = undefined
  go [ty] = ([], Just ty)
  go (ty:tys) = mapFst (Binder (tyOffset ty) LAnon (Just ty) :) (go tys)

addDelimiters :: [Char] -> [Char] -> Elab ()
addDelimiters ls rs = modifyPE $ go 2 rs . go 1 ls where
  go w cs pe = pe { pDelims = Delims $ arr U.// (f <$> cs) } where
    Delims arr = pDelims pe
    f :: Char -> (Int, Word8)
    f c = let i = fromEnum (toEnum (fromEnum c) :: Word8)
          in (i, (U.unsafeIndex arr i) .|. w)

mkLiterals :: Int -> Prec -> Int -> [PLiteral]
mkLiterals 0 _ _ = []
mkLiterals 1 p n = [PVar n p]
mkLiterals i p n = PVar n PrecMax : mkLiterals (i-1) p (n+1)

addPrefix :: Offset -> T.Text -> Const -> Prec -> ElabM ()
addPrefix px x tk prec = do
  (_, bis, _) <- try (now >>= getTerm x) >>=
    fromJustAt px ("term '" <> x <> "' not declared")
  insertPrec tk prec
  insertPrefixInfo tk (PrefixInfo (cOffs tk) x (mkLiterals (length bis) prec 0))

addInfix :: Bool -> Offset -> T.Text -> Const -> Prec -> ElabM ()
addInfix r px x tk prec = do
  (_, bis, _) <- try (now >>= getTerm x) >>=
    fromJustAt px ("term '" <> x <> "' not declared")
  guardAt px ("'" <> x <> "' must be a binary operator") (length bis == 2)
  insertPrec tk prec
  insertInfixInfo tk (InfixInfo (cOffs tk) x r)

insertPrec :: Const -> Prec -> ElabM ()
insertPrec (Const o tk) p = do
  env <- get
  case H.lookup tk (pPrec (ePE env)) of
    Just (i, p') | p /= p' ->
      reportErr $ ElabError ELError o o
        ("incompatible precedence for '" <> tk <> "'")
        [(i, i, "previously declared here")]
    _ -> lift $ modifyPE $ \e -> e {pPrec = H.insert tk (o, p) (pPrec e)}

checkToken :: Const -> ElabM ()
checkToken (Const _ tk) | T.length tk == 1 = return ()
checkToken (Const o tk) = do
  delims <- gets (pDelims . ePE)
  guardAt o ("invalid token '" <> tk <> "'")
    (T.all ((== 0) . delimVal delims) tk)

insertPrefixInfo :: Const -> PrefixInfo -> ElabM ()
insertPrefixInfo c@(Const o tk) ti = do
  checkToken c
  env <- get
  ins <- checkNew ELError o ("token '" <> tk <> "' already declared")
    (\(PrefixInfo i _ _) -> i) tk (pPrefixes (ePE env))
  lift $ modifyPE $ \e -> e {pPrefixes = ins ti}

insertInfixInfo :: Const -> InfixInfo -> ElabM ()
insertInfixInfo c@(Const o tk) ti = do
  checkToken c
  env <- get
  ins <- checkNew ELError o ("token '" <> tk <> "' already declared")
    (\(InfixInfo i _ _) -> i) tk (pInfixes (ePE env))
  lift $ modifyPE $ \e -> e {pInfixes = ins ti}

app1 :: TermName -> SExpr -> SExpr
app1 t e = App t [e]

coerce :: Maybe Sort -> (Offset, SExpr, Sort) -> ElabM (Offset, SExpr, Sort)
coerce Nothing r = return r
coerce (Just s2) (o, e, s1) =
  try (getCoe app1 s1 s2) >>= \case
    Just c -> return (o, c e, s2)
    Nothing -> do
      reportErr $ ElabError ELError o o
        ("type error, expected " <> s2 <> ", got " <> s1) []
      mzero

inferQExpr :: Maybe Sort -> QExpr -> ElabM (Offset, SExpr, Sort)
inferQExpr tgt q = inferQExpr' tgt q >>= coerce tgt

inferQExpr' :: Maybe Sort -> QExpr -> ElabM (Offset, SExpr, Sort)
inferQExpr' tgt (QApp (AtPos o t) ts) = do
  var <- gets (H.lookup t . icLocals . eInfer)
  tm <- try (now >>= getTerm t)
  case (var, tm) of
    (Just (LIOld _ (Just s)), _) -> do
      unless (null ts) $ escapeAt o (t <> " is not a function")
      return (o, SVar t, s)
    (Just (LIOld bi Nothing), _) -> do
      unless (null ts) $ escapeAt o (t <> " is not a function")
      s <- fromJustAt o "cannot infer type" tgt
      lift $ modifyInfer $ \ic -> ic {
        icLocals = H.insert t (LIOld bi (Just s)) (icLocals ic) }
      return (o, SVar t, s)
    (_, Just (_, bis, DepType s _)) -> do
      let {m = length ts; n = length bis}
      unless (m == n) $ escapeAt o ("term '" <> t <> "' applied to " <>
        T.pack (show m) <> " arguments, expected " <> T.pack (show n))
      ts' <- zipWithM (\bi t' -> do
          (_, e, _) <- inferQExpr (Just $ dSort $ binderType bi) t'
          return e) bis ts
      return (o, App t ts', s)
    (Just (LINew o1 _ s1), Nothing) -> do
      unless (null ts) $ escapeAt o (t <> " is not a function")
      forM_ tgt $ \s2 ->
        unless (s1 == s2) $ escapeErr $ ElabError ELError o o
          ("inferred two types " <> s1 <> ", " <> s2 <> " for " <> t)
          [(o1, o1, "inferred " <> s1 <> " here"), (o, o, "inferred " <> s2 <> " here")]
      return (o, SVar t, s1)
    (Nothing, Nothing) -> do
      unless (null ts) $ escapeAt o (t <> " is not a function")
      s <- fromJustAt o "cannot infer type" tgt
      lift $ modifyInfer $ \ic -> ic {
        icLocals = H.insert t (LINew o False s) (icLocals ic) }
      return (o, SVar t, s)
inferQExpr' _tgt (QUnquote (AtPos o _l)) = unimplementedAt o

inferQExprProv :: QExpr -> ElabM (Offset, SExpr, Sort)
inferQExprProv q = gets eProvableSorts >>= \case
  [s] -> inferQExpr (Just s) q
  _ -> do
    (o, e, s) <- inferQExpr Nothing q
    try (getCoeProv app1 s) >>= \case
      Just (s2, c) -> return (o, c e, s2)
      Nothing -> do
        reportErr $ ElabError ELError o o
          ("type error, expected provable sort, got " <> s) []
        mzero
