{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module MM0.Compiler.Elaborator (elaborate, elabLoad,
  ErrorLevel(..), ElabError(..), ElabConfig(..), toElabError) where

import Control.Monad.State
import Control.Monad.RWS.Strict
import Control.Monad.Trans.Maybe
import Data.List
import Data.Bits
import Data.Word8
import Data.Maybe
import Data.Default
import Data.Foldable
import System.IO.Error
import qualified Data.Map.Strict as M
import qualified Data.HashMap.Strict as H
import qualified Data.Set as S
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Mutable.Dynamic as VD
import qualified Data.Text as T
import qualified Data.Text.IO as T
import MM0.Compiler.Parser (parseAST)
import MM0.Compiler.AST
import MM0.Compiler.Env
import MM0.Compiler.MathParser
import MM0.Compiler.PrettyPrinter
import MM0.Util

elabLoad :: ElabConfig -> FilePath -> IO (Either T.Text Env)
elabLoad cfg name = tryIOError (T.readFile name) >>= \case
  Left err -> return $ Left $ T.pack $ show err
  Right str -> let ast = thd3 (parseAST name str) in
    Right . snd <$> elaborate cfg {ecName = name} [] ast

elaborate :: ElabConfig -> [ElabError] -> AST -> IO ([ElabError], Env)
elaborate cfg errs ast = do
  (_, errs', env) <- runElab (mapM_ elabStmt ast) cfg errs initialBindings
  return (errs', env)

elabStmt :: Span Stmt -> Elab ()
elabStmt (Span rd@(pos, _) s) = resuming $ withTimeout pos $ case s of
  Sort px x sd -> addSort rd (textToRange px x) x sd
  Decl vis dk px x bis ret v -> addDecl rd vis dk (textToRange px x) x bis ret v
  Notation (Delimiter cs Nothing) -> lift $ addDelimiters cs cs
  Notation (Delimiter ls (Just rs)) -> lift $ addDelimiters ls rs
  Notation (Prefix px x tk prec) -> addPrefix (textToRange px x) x tk prec
  Notation (Infix r px x tk prec) -> addInfix r (textToRange px x) x tk prec
  Notation (NNotation px x bis _ lits) -> addNotation (textToRange px x) x bis lits
  Notation (Coercion px x s1 s2) -> addCoercion (textToRange px x) x s1 s2
  Do lvs -> do
    ifMM0 $ reportAt pos ELWarning "(MM0 mode) do block not supported"
    mapM_ evalToplevel lvs
  Annot e stmt -> do
    ann <- evalAt def e
    lift $ elabStmt stmt
    () <$ call pos "annotate" [ann, nameOf stmt]
  Import (Span _ t) -> loadEnv rd t >>= put -- TODO: this just replaces the current env
  _ -> unimplementedAt pos

checkNew :: ErrorLevel -> Range -> T.Text -> (v -> Range) -> T.Text ->
  H.HashMap T.Text v -> ElabM (v -> H.HashMap T.Text v)
checkNew l o msg f k m = case H.lookup k m of
  Nothing -> return (\v -> H.insert k v m)
  Just a -> do
    reportErr $ ElabError l o msg [(f a, "previously declared here")]
    mzero

nameOf :: Span Stmt -> LispVal
nameOf (Span _ (Sort px x _)) = Atom False px x
nameOf (Span _ (Decl _ _ px x _ _ _)) = Atom False px x
nameOf (Span _ (Annot _ s)) = nameOf s
nameOf _ = Bool False

addSort :: Range -> Range -> T.Text -> SortData -> ElabM ()
addSort rd rx x sd = do
  ins <- gets eSorts >>= checkNew ELError rx
    ("duplicate sort declaration '" <> x <> "'") (\(_, (_, i), _) -> i) x
  n <- next
  modify $ \env -> env {
    eSorts = ins (n, (rd, rx), sd),
    eProvableSorts = (guard (sProvable sd) >> [x]) ++ eProvableSorts env }

inferDepType :: AtDepType -> ElabM ()
inferDepType (AtDepType (Span (o, _) t) ts) = do
  lift $ resuming $ do
    (_, _sd) <- try (now >>= getSort t) >>=
      fromJustAt o ("sort '" <> t <> "' not declared")
    -- TODO: check sd
    return ()
  modifyInfer $ \ic -> ic {
    icDependents = foldl' (\m (Span (i, _) x) ->
      H.alter (Just . maybe [i] (i:)) x m) (icDependents ic) ts }

inferBinder :: Binder -> ElabM (Maybe (Range, Local, InferResult))
inferBinder bi@(Binder os@(o, _) l oty) = case oty of
  Nothing -> do
    ifMM0 $ reportAt o ELWarning "(MM0 mode) missing type"
    Nothing <$ addVar True
  Just (TType ty) -> inferDepType ty >> Nothing <$ addVar False
  Just (TFormula f) -> do
    ir <- parseMath f >>= inferQExprProv
    return $ Just (os, l, ir)
  where

  addVar :: Bool -> ElabM ()
  addVar noType = do
    locals <- gets (icLocals . eInfer)
    locals' <- case localName l of
      Nothing -> do
        when noType $ escapeAt o "cannot infer variable type"
        return $ locals
      Just n -> do
        ins <- checkNew ELWarning os
          ("variable '" <> n <> "' shadows previous declaration")
          liOffset n locals
        return (ins (LIOld bi Nothing))
    modifyInfer $ \ic -> ic {icLocals = locals'}

addDecl :: Range -> Visibility -> DeclKind -> Range -> T.Text ->
  [Binder] -> Maybe [Type] -> Maybe AtLisp -> ElabM ()
addDecl rd vis dk rx@(px, _) x bis ret v = do
  mm0 <- asks efMM0
  when (mm0 && vis /= VisDefault) $
    reportSpan rx ELWarning "(MM0 mode) visibility modifiers not supported"
  let (bis', ret') = unArrow bis ret
  decl <- withInfer $ do
    fmlas <- catMaybes <$> mapM inferBinder bis'
    decl <- case (dk, ret', v) of
      (DKDef, Just (TType ty), Nothing) -> do
        inferDepType ty
        if mm0 then do
          (pbs, hs, _) <- buildBinders px True bis' fmlas
          unless (null hs) $ error "impossible"
          return $ DDef vis pbs (unDepType ty) Nothing
        else do
          reportSpan rx ELWarning "definition has no body; axiomatizing"
          (pbs, hs, _) <- buildBinders px True bis' fmlas
          unless (null hs) $ error "impossible"
          return $ DTerm pbs (unDepType ty)
      (DKDef, _, Just (Span _ (AFormula f))) -> do
        let ret'' = case ret' of Just (TType ty) -> Just ty; _ -> Nothing
        forM_ ret'' inferDepType
        IR _ v' s _ <- parseMath f >>=
          inferQExpr ((\(AtDepType s _) -> (unSpan s, False)) <$> ret'')
        (pbs, hs, dums) <- buildBinders px True bis' fmlas
        unless (null hs) $ error "impossible"
        vs <- case ret'' of
          Just (AtDepType (Span (o, _) _) avs) -> do
            vs' <- defcheckExpr pbs v'
            let vs1 = unSpan <$> avs
            let bad = foldr S.delete vs' vs1
            unless (S.null bad) $
              escapeAt o ("definition has undeclared free variable(s): " <>
                T.intercalate ", " (S.toList bad))
            return vs1
          Nothing -> do
            when mm0 $ reportSpan rx ELWarning "(MM0 mode) def has no return type"
            S.toList <$> defcheckExpr pbs v'
        return $ DDef vis pbs (DepType s vs) (Just (orderDummies dums v', v'))
      (DKDef, _, Just (Span (o, _) _)) -> unimplementedAt o
      (DKTerm, Just (TType ty), _) -> do
        inferDepType ty
        (pbs, hs, _) <- buildBinders px False bis' fmlas
        unless (null hs) $ error "impossible"
        return (DTerm pbs (unDepType ty))
      (DKAxiom, Just (TFormula f), _) -> do
        IR _ eret _ _ <- parseMath f >>= inferQExprProv
        (pbs, hs, _) <- buildBinders px False bis' fmlas
        return $ DAxiom pbs ((\(_, _, h) -> h) <$> hs) eret
      (DKTheorem, Just (TFormula f), _) -> do
        IR _ eret _ _ <- parseMath f >>= inferQExprProv
        (pbs, hs, _) <- buildBinders px False bis' fmlas
        case v of
          Nothing ->
            if mm0 then
              return $ DTheorem vis pbs ((\(_, v', h) -> (v', h)) <$> hs) eret mzero
            else do
              reportSpan rx ELWarning "theorem proof missing"
              return $ DAxiom pbs ((\(_, _, h) -> h) <$> hs) eret
          Just lv -> do
            when mm0 $ reportSpan rx ELWarning "(MM0 mode) theorem proofs not accepted"
            fork <- forkElabM $ withTimeout px $
              withTC (H.fromList $ (\bi -> (binderName bi, bi)) <$> pbs) $ do
                forM_ hs $ \((o, _), on, e) -> forM_ on $ \n ->
                  addSubproof n (sExprToLisp o e) (Atom False o n)
                elabLisp eret lv
            return $ DTheorem vis pbs ((\(_, v', h) -> (v', h)) <$> hs) eret fork
      _ -> unimplementedAt px
    checkVarRefs >> return decl
  insertDecl x decl rd rx ("duplicate " <> T.pack (show dk) <> " declaration '" <> x <> "'")

insertDecl :: T.Text -> Decl -> Range -> Range -> T.Text -> ElabM ()
insertDecl x decl rd rx err = do
  ins <- gets eDecls >>= checkNew ELError rx err (\(_, (_, i), _, _) -> i) x
  n <- next
  modify $ \env -> env {eDecls = ins (n, (rd, rx), decl, Nothing)}

unArrow :: [Binder] -> Maybe [Type] -> ([Binder], Maybe Type)
unArrow bis Nothing = (bis, Nothing)
unArrow bis (Just tys') = mapFst (bis ++) (go tys') where
  go [] = undefined
  go [ty] = ([], Just ty)
  go (ty:tys) = mapFst (Binder (tyOffset ty, tyOffset ty) LAnon (Just ty) :) (go tys)

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

addDeclNota :: Range -> T.Text -> Maybe DeclNota -> DeclNota -> ElabM ()
addDeclNota rx x old new = do
  forM_ old $ \no -> do
    i <- getDeclNotaOffset no
    reportErr $ ElabError ELWarning rx
      ("term '" <> x <> "' already has a notation")
      [(i, "previously declared here")]
  modify $ \env -> env {eDecls =
    H.adjust (\(s, o, d, _) -> (s, o, d, Just new)) x (eDecls env)}

addPrefix :: Range -> T.Text -> Const -> Prec -> ElabM ()
addPrefix rx@(px, _) x c@(Const o tk) prec = do
  (_, bis, _, no) <- try (now >>= getTerm x) >>=
    fromJustAt px ("term '" <> x <> "' not declared")
  insertPrec c prec
  insertPrefixInfo c (PrefixInfo (textToRange o tk) x (mkLiterals (length bis) prec 0))
  addDeclNota rx x no (NPrefix tk)

addInfix :: Bool -> Range -> T.Text -> Const -> Prec -> ElabM ()
addInfix r rx@(px, _) x c@(Const o tk) prec = do
  (_, bis, _, no) <- try (now >>= getTerm x) >>=
    fromJustAt px ("term '" <> x <> "' not declared")
  guardAt px ("'" <> x <> "' must be a binary operator") (length bis == 2)
  insertPrec c prec
  insertInfixInfo c (InfixInfo (textToRange o tk) x r)
  addDeclNota rx x no (NInfix tk)

addNotation :: Range -> T.Text -> [Binder] -> [AtPos Literal] -> ElabM ()
addNotation rx@(px, _) x bis = \lits -> do
  (_, bis', _, no) <- try (now >>= getTerm x) >>=
    fromJustAt px ("term '" <> x <> "' not declared")
  unless (length bis == length bis') $
    escapeAt px ("term '" <> x <> "' has " <> T.pack (show (length bis')) <>
      " arguments, expected " <> T.pack (show (length bis)))
  (c@(Const o tk), ti) <- processLits lits
  insertPrefixInfo c (PrefixInfo (textToRange o tk) x ti)
  addDeclNota rx x no (NPrefix tk)
  where

  binderMap :: H.HashMap VarName Int
  binderMap = go bis 0 H.empty where
    go [] _ m = m
    go (Binder _ l _ : bs) n m =
      go bs (n+1) $ maybe m (\v -> H.insert v n m) (localName l)

  processLits :: [AtPos Literal] -> ElabM (Const, [PLiteral])
  processLits (AtPos _ (NConst c p) : lits') =
      insertPrec c p >> (,) c <$> go lits' where
    go :: [AtPos Literal] -> ElabM [PLiteral]
    go [] = return []
    go (AtPos _ (NConst c'@(Const _ tk) q) : lits) =
      insertPrec c' q >> (PConst tk :) <$> go lits
    go (AtPos o (NVar v) : lits) = do
      q <- case lits of
        [] -> return p
        (AtPos _ (NConst _ (Prec q)) : _)
          | q < maxBound -> return (Prec (q + 1))
        (AtPos o' (NConst _ _) : _) ->
          escapeAt o' "notation infix prec max not allowed"
        (AtPos _ (NVar _) : _) -> return PrecMax
      n <- fromJustAt o "notation variable not found" (H.lookup v binderMap)
      (PVar n q :) <$> go lits
  processLits (AtPos o _ : _) = escapeAt o "notation must begin with a constant"
  processLits [] = error "empty notation"

addCoercion :: Range -> T.Text -> Sort -> Sort -> ElabM ()
addCoercion rx@(px, _) x s1 s2 = do
  try (now >>= getTerm x) >>= \case
    Nothing -> escapeAt px ("term '" <> x <> "' not declared")
    Just (_, [PReg _ (DepType s1' [])], DepType s2' [], no)
      | s1 == s1' && s2 == s2' -> do
        addCoe (Coe1 rx x) s1 s2
        addDeclNota rx x no (NCoe s1 s2)
    _ -> escapeAt px ("coercion '" <> x <> "' does not match declaration")

insertPrec :: Const -> Prec -> ElabM ()
insertPrec (Const o tk) p = do
  env <- get
  case H.lookup tk (pPrec (ePE env)) of
    Just (i, p') | p /= p' ->
      reportErr $ ElabError ELError (o, o)
        ("incompatible precedence for '" <> tk <> "'")
        [(i, "previously declared here")]
    _ -> lift $ modifyPE $ \e -> e {pPrec = H.insert tk (textToRange o tk, p) (pPrec e)}

checkToken :: Const -> ElabM ()
checkToken (Const _ tk) | T.length tk == 1 = return ()
checkToken (Const o tk) = do
  delims <- gets (pDelims . ePE)
  guardAt o ("invalid token '" <> tk <> "'")
    (T.all (not . (`testBit` 1) . delimVal delims) (T.tail tk) &&
     T.all (not . (`testBit` 0) . delimVal delims) (T.init tk))

insertPrefixInfo :: Const -> PrefixInfo -> ElabM ()
insertPrefixInfo c@(Const o tk) ti = do
  checkToken c
  env <- get
  ins <- checkNew ELError (textToRange o tk) ("token '" <> tk <> "' already declared")
    (\(PrefixInfo i _ _) -> i) tk (pPrefixes (ePE env))
  lift $ modifyPE $ \e -> e {pPrefixes = ins ti}

insertInfixInfo :: Const -> InfixInfo -> ElabM ()
insertInfixInfo c@(Const o tk) ti = do
  checkToken c
  env <- get
  ins <- checkNew ELError (textToRange o tk) ("token '" <> tk <> "' already declared")
    (\(InfixInfo i _ _) -> i) tk (pInfixes (ePE env))
  lift $ modifyPE $ \e -> e {pInfixes = ins ti}

app1 :: TermName -> SExpr -> SExpr
app1 t e = App t [e]

data InferResult = IR Range SExpr Sort Bool deriving (Show)
coerce :: Maybe (Sort, Bool) -> InferResult -> ElabM InferResult
coerce (Just (s2, bd2)) (IR o e s1 bd1) | (s1 == s2 || s2 == "") && (bd1 || not bd2) =
  return (IR o e s1 bd2)
coerce (Just (_, True)) (IR o _ _ _) =
  escapeSpan o "type error, expected bound variable, got expression"
coerce (Just (s2, False)) (IR o e s1 _) =
  try (getCoe app1 s1 s2) >>= \case
    Just c -> return (IR o (c e) s2 False)
    Nothing -> escapeSpan o ("type error, expected " <> s2 <>
      ", got " <> T.pack (show e) <> ": " <> s1)
coerce Nothing r = return r

inferQExpr :: Maybe (Sort, Bool) -> QExpr -> ElabM InferResult
inferQExpr tgt q = inferQExpr' tgt q >>= coerce tgt

inferQExpr' :: Maybe (Sort, Bool) -> QExpr -> ElabM InferResult
inferQExpr' tgt (QApp (Span os@(o, _) t) ts) = do
  var <- gets (H.lookup t . icLocals . eInfer)
  tm <- try (now >>= getTerm t)
  let returnVar :: Sort -> Bool -> ElabM a -> ElabM InferResult
      returnVar s bd m = do
        unless (null ts) $ escapeAt o (t <> " is not a function")
        (IR os (SVar t) s bd) <$ m
  case (var, tm) of
    (Just (LIOld (Binder _ l (Just (TType (AtDepType (Span _ s) _)))) _), _) ->
      returnVar s (isLCurly l) (return ())
    (Just (LIOld (Binder _ l _) (Just s)), _) ->
      returnVar s (isLCurly l) (return ())
    (Just (LIOld bi@(Binder _ l _) Nothing), _) -> do
      (s, _) <- fromJustAt o "cannot infer type" tgt
      returnVar s (isLCurly l) $ modifyInfer $ \ic -> ic {
        icLocals = H.insert t (LIOld bi (Just s)) (icLocals ic) }
    (_, Just (_, bis, DepType s _, _)) -> do
      let m = length ts
          n = length bis
          f bi t' = (\(IR _ e _ _) -> e) <$> inferQExpr (Just (hint bi)) t' where
            hint (PBound _ t2) = (t2, True)
            hint (PReg _ (DepType t2 _)) = (t2, False)
      unless (m == n) $ escapeAt o ("term '" <> t <> "' applied to " <>
        T.pack (show m) <> " arguments, expected " <> T.pack (show n))
      ts' <- zipWithM f bis ts
      return (IR os (App t ts') s False)
    (Just (LINew o1 bd1 s1), Nothing) -> do
      bd' <- case tgt of
        Just (s2, bd2) -> do
          unless (s1 == s2) $ escapeErr $ ElabError ELError os
            ("inferred two types " <> s1 <> ", " <> s2 <> " for " <> t)
            [(o1, "inferred " <> s1 <> " here"), (os, "inferred " <> s2 <> " here")]
          return (bd1 || bd2)
        _ -> return bd1
      returnVar s1 bd' $ when (bd1 /= bd') $ modifyInfer $ \ic -> ic {
        icLocals = H.insert t (LINew o1 bd' s1) (icLocals ic) }
    (Nothing, Nothing) -> do
      (s, bd) <- fromJustAt o "cannot infer type" tgt
      returnVar s bd $ modifyInfer $ \ic -> ic {
        icLocals = H.insert t (LINew os bd s) (icLocals ic) }
inferQExpr' _ (QUnquote (Span o e)) = asSExpr <$> eval o def e >>= \case
  Nothing -> escapeSpan o $ "invalid s-expr: " <> T.pack (show e)
  Just e'@(SVar v) -> gets (H.lookup v . icLocals . eInfer) >>= \case
    Just (LIOld (Binder _ l (Just (TType (AtDepType (Span _ s) _)))) _) ->
      return $ IR o e' s (isLCurly l)
    _ -> escapeSpan o $ "unknown variable '" <> v <> "'"
  Just e'@(App t _) -> try (now >>= getTerm t) >>= \case
    Just (_, _, DepType s _, _) -> return $ IR o e' s False
    _ -> escapeSpan o $ "unknown term constructor '" <> t <> "'"

inferQExprProv :: QExpr -> ElabM InferResult
inferQExprProv q = gets eProvableSorts >>= \case
  [s] -> inferQExpr (Just (s, False)) q
  _ -> do
    IR o e s _ <- inferQExpr Nothing q
    try (getCoeProv app1 s) >>= \case
      Just (s2, c) -> return (IR o (c e) s2 False)
      Nothing -> escapeSpan o ("type error, expected provable sort, got " <> s)

buildBinders :: Offset -> Bool -> [Binder] -> [(Range, Local, InferResult)] ->
  ElabM ([PBinder], [(Range, Maybe VarName, SExpr)], M.Map VarName Sort)
buildBinders px dum bis fs = do
  ic <- gets eInfer
  let locals = icLocals ic
      newvar :: VarName -> Range -> Bool -> Sort -> Binder
      newvar v o bd s = Binder o l (Just (TType (AtDepType (Span o s) []))) where
        l = if bd then
          if not dum || H.member v (icDependents ic) then LBound v else LDummy v
        else LReg v
      bis1 = mapMaybe f bis where
        f bi@(Binder _ l _) = case localName l of
          Nothing -> Just ("_", bi)
          Just v -> H.lookup v locals >>= \case
            LIOld (Binder _ _ (Just (TFormula _))) _ -> Nothing
            LIOld bi'@(Binder _ _ (Just (TType _))) _ -> Just (v, bi')
            LIOld bi'@(Binder _ _ Nothing) Nothing -> Just (v, bi')
            LIOld (Binder o l' Nothing) (Just t) ->
              Just (v, Binder o l' (Just (TType (AtDepType (Span o t) []))))
            LINew o bd s -> Just (v, newvar v o bd s)
      bisAdd = sortOn fst (mapMaybe f (H.toList locals)) where
        f (v, LINew o bd s) = Just (v, newvar v o bd s)
        f _ = Nothing
      bisNew = bisAdd ++ bis1 where
      bisDum = M.fromList (mapMaybe f bisNew) where
        f (v, Binder _ (LDummy _) (Just (TType (AtDepType (Span _ t) [])))) =
          Just (v, t)
        f _ = Nothing
      fmlas = mapMaybe (\(o, l, IR _ e _ _) -> Just (o, localName l, e)) fs
  bis' <- forM bisNew $ \case
    (v, Binder _ (LBound _) (Just (TType ty))) ->
      return $ Just $ PBound v (dSort (unDepType ty))
    (_, Binder _ (LDummy _) _) -> return Nothing
    (v, Binder _ _ (Just (TType ty))) ->
      return $ Just $ PReg v (unDepType ty)
    (_, Binder (o, _) _ Nothing) -> escapeAt o "could not infer type"
    _ -> return Nothing
  ifMM0 $ unless (null bisAdd) $ reportAt px ELWarning $ render' $
    "(MM0 mode) missing binders:" <> ppGroupedBinders (snd <$> bisAdd)
  return (catMaybes bis', fmlas, bisDum)

orderDummies :: M.Map VarName Sort -> SExpr -> [(VarName, Sort)]
orderDummies = \m e -> let (_, Endo f) = execRWS (go e) () m in f [] where
  go :: SExpr -> RWS () (Endo [(VarName, Sort)]) (M.Map VarName Sort) ()
  go (SVar v) = do
    m <- gets (M.lookup v)
    forM_ m $ \s -> tell (Endo ((v, s) :)) >> modify (M.delete v)
  go (App _ es) = mapM_ go es

checkVarRefs :: ElabM ()
checkVarRefs = do
  ic <- gets eInfer
  let errs = filter (not . (`H.member` icLocals ic) . fst) $ H.toList (icDependents ic)
  when (not (null errs)) $ do
    forM_ errs $ \(_, os) -> forM_ os $ \o ->
      reportAt o ELError "undefined variable"
    mzero

defcheckExpr :: [PBinder] -> SExpr -> ElabM (S.Set VarName)
defcheckExpr bis = defcheckExpr' where
  ctx = H.fromList (mapMaybe f bis) where
    f (PReg v (DepType _ vs)) = Just (v, vs)
    f _ = Nothing
  defcheckExpr' (SVar v) = return $
    maybe (S.singleton v) S.fromList (H.lookup v ctx)
  defcheckExpr' (App t es) = do
    (_, args, DepType _ rs, _) <- now >>= getTerm t
    (m, ev) <- defcheckArgs args es
    return (ev <> S.fromList ((m H.!) <$> rs))

  defcheckArgs :: [PBinder] -> [SExpr] ->
    ElabM (H.HashMap VarName VarName, S.Set VarName)
  defcheckArgs = \args es -> go args es H.empty S.empty where
    go [] [] m ev = return (m, ev)
    go (PBound x _ : args) (SVar v : es) m ev =
      go args es (H.insert x v m) ev
    go (PReg _ (DepType _ vs) : args) (e : es) m ev = do
      ev' <- defcheckExpr' e
      let ev2 = foldl' (\ev1 v -> S.delete (m H.! v) ev1) ev' vs
      go args es m (ev <> ev2)
    go _ _ _ _ = error "bad expr, should already have been caught"

-----------------------------
-- Lisp evaluation
-----------------------------

newtype LCtx = LCtx (H.HashMap T.Text LispVal)

instance Default LCtx where
  def = LCtx H.empty

lcInsert :: T.Text -> LispVal -> LCtx -> LCtx
lcInsert "_" _ ctx = ctx
lcInsert x v (LCtx ctx) = LCtx (H.insert x v ctx)

evalToplevel :: AtLisp -> ElabM ()
evalToplevel (Span rd (AList (Span (o, _) (AAtom _ "def") : es))) = do
  (Span rx x, v) <- evalDefine o def es
  unless (x == "_") $ lispDefine rd rx x v
evalToplevel (Span o e) = evalAndPrint o e

evalAndPrint :: Range -> LispAST -> ElabM ()
evalAndPrint o e = eval o def e >>= unRef >>= \case
  Undef -> return ()
  e' -> reportSpan o ELInfo $ T.pack $ show e'

evalAt :: LCtx -> AtLisp -> ElabM LispVal
evalAt ctx (Span o e) = eval o ctx e

eval :: Range -> LCtx -> LispAST -> ElabM LispVal
eval (o, _) ctx (AAtom _ e) = evalAtom o ctx e
eval _ _ (AString s) = return (String s)
eval _ _ (ANumber n) = return (Number n)
eval _ _ (ABool b) = return (Bool b)
eval _ _ (AList []) = return (List [])
eval _ ctx (AList (e : es)) = evalApp ctx e es
eval _ _ val@(ADottedList (Span (o, _) _) _ _) =
  escapeAt o $ "attempted to evaluate an improper list: " <> T.pack (show val)
eval _ ctx (AFormula f) = parseMath f >>= evalQExpr ctx

evalList :: a -> (ElabM LispVal -> ElabM a -> ElabM a) -> LCtx -> [AtLisp] -> ElabM a
evalList a _ _ [] = return a
evalList a f ctx (Span _ (AList (Span (o, _) (AAtom _ "def") : ds)) : es) = do
  (Span _ x, v) <- evalDefine o ctx ds
  evalList a f (lcInsert x v ctx) es
evalList a f ctx (e : es) = f (evalAt ctx e) (evalList a f ctx es)

eval1 :: LCtx -> [AtLisp] -> ElabM LispVal
eval1 ctx es = fromMaybe Undef <$>
  evalList Nothing (liftM2 $ \a b -> Just $ fromMaybe a b) ctx es

evals :: LCtx -> [AtLisp] -> ElabM [LispVal]
evals = evalList [] $ liftM2 (:)

evalAtom :: Offset -> LCtx -> T.Text -> ElabM LispVal
evalAtom o _ v@"_" = return $ Atom False o v
evalAtom o (LCtx ctx) v = case H.lookup v ctx of
  Just e -> return e
  Nothing -> try (lispLookupName v) >>= \case
    Just e -> return e
    Nothing -> escapeAt o $ "Reference to unbound variable '" <> v <> "'"

call :: Offset -> T.Text -> [LispVal] -> ElabM LispVal
call o v es = try (lispLookupName v) >>= \case
  Just e -> unRef e >>= \case
    Proc f -> f (o, o) es
    e' -> escapeAt o $ "not a function, cannot apply: " <> T.pack (show e')
  Nothing -> escapeAt o $ "Unknown function '" <> v <> "'"

evalApp :: LCtx -> AtLisp -> [AtLisp] -> ElabM LispVal
evalApp ctx (Span (o, _) (AAtom _ e)) es = evalAtom o ctx e >>= unRef >>= \case
  Syntax s -> evalSyntax o ctx s es
  Proc f -> evals ctx es >>= f (o, o + T.length e)
  v -> escapeAt o $ "not a function, cannot apply: " <> T.pack (show v)
evalApp ctx (Span o e) es = eval o ctx e >>= unRef >>= \case
  Proc f -> evals ctx es >>= f o
  v -> escapeAt (fst o) $ "not a function, cannot apply: " <> T.pack (show v)

evalSyntax :: Offset -> LCtx -> Syntax -> [AtLisp] -> ElabM LispVal
evalSyntax o _ Define _ = escapeAt o "def not permitted in expression context"
evalSyntax o _ Quote [] = escapeAt o "expected at least one argument"
evalSyntax _ ctx Quote (e : _) = quoteAt ctx e
evalSyntax _ ctx If (cond : t : es') = do
  cond' <- evalAt ctx cond >>= unRef
  if truthy cond' then evalAt ctx t else
    case es' of
      [] -> return Undef
      f : _ -> evalAt ctx f
evalSyntax o _ If _ = escapeAt o "expected at least two arguments"
evalSyntax _ ctx Lambda (vs : es) = do
  ls <- toLambdaSpec vs
  return (Proc (mkLambda ls ctx es))
evalSyntax o _ Lambda _ = escapeAt o "expected at least one argument"
evalSyntax o ctx Focus es = Undef <$ focus o ctx es
evalSyntax _ ctx Let es = do
  (xs, es') <- parseLet es
  let go [] ctx' = eval1 ctx' es'
      go ((Span _ x, f) : xs') ctx' = do
        v <- f ctx'
        go xs' (lcInsert x v ctx')
  go xs ctx
evalSyntax _ ctx Letrec es = do
  (xs, es') <- parseLet es
  ctx' <- go xs ctx (\_ -> return ())
  eval1 ctx' es' where
  go :: [(Span Ident, LCtx -> ElabM LispVal)] -> LCtx -> (LCtx -> ElabM ()) -> ElabM LCtx
  go [] ctx' f = ctx' <$ f ctx'
  go ((Span _ x, e) : xs) ctx' f = do
    a <- newRef Undef
    go xs (lcInsert x (Ref a) ctx') $
      \ctx2 -> f ctx2 >> e ctx2 >>= setRef a
evalSyntax o _ Match [] = escapeAt o "expected at least one argument"
evalSyntax o ctx Match (e : es) = do
  ms <- mapM (parseMatchBranch ctx) es
  evalAt ctx e >>= runMatch ms o
evalSyntax o ctx MatchFn es = do
  ms <- mapM (parseMatchBranch ctx) es
  return $ Proc $ \_ vs -> unary o vs >>= runMatch ms o
evalSyntax o ctx MatchFns es = do
  ms <- mapM (parseMatchBranch ctx) es
  return $ Proc $ \_ -> runMatch ms o . List

data LambdaSpec = LSExactly [Ident] | LSAtLeast [Ident] Ident

toLambdaSpec :: AtLisp -> ElabM LambdaSpec
toLambdaSpec (Span _ (AList es)) = LSExactly <$> mapM toIdent es
toLambdaSpec (Span _ (ADottedList e1 es e2)) =
  liftM2 LSAtLeast (mapM toIdent (e1 : es)) (toIdent e2)
toLambdaSpec e = LSAtLeast [] <$> toIdent e

mkCtx :: Offset -> LambdaSpec -> [LispVal] -> LCtx -> ElabM LCtx
mkCtx o (LSExactly xs') = \vs -> mkCtxList xs' vs 0 where
  mkCtxList [] [] _ ctx = return ctx
  mkCtxList (x:xs) (v:vs) n ctx =
    mkCtxList xs vs (n+1) (lcInsert x v ctx)
  mkCtxList [] vs n _ = escapeAt o $
    "expected " <> T.pack (show n) <> " arguments, got " <> T.pack (show (n + length vs))
  mkCtxList xs [] n _ = escapeAt o $
    "expected " <> T.pack (show (n + length xs)) <> " arguments, got " <> T.pack (show n)
mkCtx o (LSAtLeast xs' r) = \vs -> mkCtxImproper xs' vs 0 where
  mkCtxImproper [] vs _ ctx =
    return (lcInsert r (List vs) ctx)
  mkCtxImproper (x:xs) (v:vs) n ctx =
    mkCtxImproper xs vs (n+1) (lcInsert x v ctx)
  mkCtxImproper xs [] n _ = escapeAt o $
    "expected at least " <> T.pack (show (n + length xs)) <> " arguments, got " <> T.pack (show n)

mkLambda :: LambdaSpec -> LCtx -> [AtLisp] -> Proc
mkLambda ls ctx es (o, _) vs = do
  ctx' <- mkCtx o ls vs ctx
  eval1 ctx' es

parseDef :: ElabM (Span Ident, LCtx -> ElabM LispVal) ->
  [AtLisp] -> ElabM (Span Ident, LCtx -> ElabM LispVal)
parseDef _ (Span o (AAtom _ x) : es) = return (Span o x, \ctx -> eval1 ctx es)
parseDef _ (Span _ (AList (Span o (AAtom _ x) : xs)) : es) = do
  xs' <- mapM toIdent xs
  return (Span o x, \ctx -> return $ Proc $ mkLambda (LSExactly xs') ctx es)
parseDef _ (Span _ (ADottedList (Span o (AAtom _ x)) xs r) : es) = do
  xs' <- mapM toIdent xs
  r' <- toIdent r
  return (Span o x, \ctx -> return $ Proc $ mkLambda (LSAtLeast xs' r') ctx es)
parseDef err _ = err

evalDefine :: Offset -> LCtx -> [AtLisp] -> ElabM (Span Ident, LispVal)
evalDefine o ctx es = do
  (x, f) <- parseDef (escapeAt o "def: syntax error") es
  (,) x <$> f ctx

toIdent :: AtLisp -> ElabM Ident
toIdent (Span _ (AAtom _ x)) = return x
toIdent (Span (o, _) _) = escapeAt o "expected an identifier"

parseLetVar :: AtLisp -> ElabM (Span Ident, LCtx -> ElabM LispVal)
parseLetVar (Span (o, _) (AList ls)) = parseDef (escapeAt o "invalid syntax") ls
parseLetVar (Span (o, _) _) = escapeAt o "invalid syntax"

parseLet :: [AtLisp] -> ElabM ([(Span Ident, LCtx -> ElabM LispVal)], [AtLisp])
parseLet (Span _ (AList ls) : es) = flip (,) es <$> mapM parseLetVar ls
parseLet (Span (o, _) _ : _) = escapeAt o "invalid syntax"
parseLet _ = return ([], [])

runMatch :: [LispVal -> ElabM LispVal -> ElabM LispVal] -> Offset -> LispVal -> ElabM LispVal
runMatch [] o v = escapeAt o $! "match failed: " <> T.pack (show v)
runMatch (f : fs) o v = f v (runMatch fs o v)

parseMatchBranch :: LCtx -> AtLisp -> ElabM (LispVal -> ElabM LispVal -> ElabM LispVal)
parseMatchBranch ctx (Span _ (AList (pat :
    Span _ (AList [Span _ (AAtom _ "=>"), Span _ (AAtom _ x)]) : es))) = do
  f <- parsePatt ctx pat
  return $ \e k -> try (f e) >>= \case
    Nothing -> k
    Just g -> eval1 (lcInsert x (Proc $ \_ _ -> k) $ g ctx) es
parseMatchBranch ctx (Span _ (AList (pat : es))) = do
  f <- parsePatt ctx pat
  return $ \e k -> try (f e) >>= \case
    Nothing -> k
    Just g -> eval1 (g ctx) es
parseMatchBranch _ (Span (o, _) _) = escapeAt o "invalid syntax"

data ListPatt = LPCons (LispVal -> ElabM (LCtx -> LCtx)) ListPatt
  | LPNil | LPAtLeast Int

parseListPatt :: (AtLisp -> ElabM (LispVal -> ElabM (LCtx -> LCtx))) ->
  [AtLisp] -> ElabM (LispVal -> ElabM (LCtx -> LCtx))
parseListPatt p = \es -> do
  fs <- patts es
  return $ unRef >=> \case List vs -> go fs vs; _ -> mzero
  where
  patts :: [AtLisp] -> ElabM ListPatt
  patts [] = return LPNil
  patts (Span _ (AList [Span _ (AAtom _ "quote"), Span _ (AAtom _ x)]) : es) =
    LPCons (\case Atom _ _ x' | x == x' -> return id; _ -> mzero) <$> patts es
  patts [Span _ (AAtom _ "___")] = return (LPAtLeast 0)
  patts [Span _ (AAtom _ "...")] = return (LPAtLeast 0)
  patts [Span _ (AAtom _ "__"), Span _ (ANumber n)] = return (LPAtLeast $ fromIntegral n)
  patts (e : es) = liftM2 LPCons (p e) (patts es)
  go :: ListPatt -> [LispVal] -> ElabM (LCtx -> LCtx)
  go LPNil [] = return id
  go (LPCons f fs) (v:vs) = liftM2 (flip (.)) (f v) (go fs vs)
  go (LPAtLeast 0) _ = return id
  go (LPAtLeast n) vs | length vs >= n = return id
  go _ _ = mzero

parseDottedListPatt :: (AtLisp -> ElabM (LispVal -> ElabM (LCtx -> LCtx))) ->
  AtLisp -> [AtLisp] -> AtLisp -> ElabM (LispVal -> ElabM (LCtx -> LCtx))
parseDottedListPatt = \p l es r -> liftM2 go (mapM p (l : es)) (p r) where
  go [] fr v = fr v
  go (f:fs) fr v = lispUncons <$> unRef v >>= \case
    Just (vl, vr) -> liftM2 (flip (.)) (f vl) (go fs fr vr)
    Nothing -> mzero

lispUncons :: LispVal -> Maybe (LispVal, LispVal)
lispUncons (List (e : es)) = Just (e, List es)
lispUncons (DottedList l [] r) = Just (l, r)
lispUncons (DottedList l (e : es) r) = Just (l, DottedList e es r)
lispUncons _ = Nothing

parsePatt :: LCtx -> AtLisp -> ElabM (LispVal -> ElabM (LCtx -> LCtx))
parsePatt _ (Span _ (AAtom _ x)) = return $ \v -> return $ lcInsert x v
parsePatt _ (Span _ (ANumber n)) = return $ unRef >=> \case Number n' | n == n' -> return id; _ -> mzero
parsePatt _ (Span _ (AString s)) = return $ unRef >=> \case String s' | s == s' -> return id; _ -> mzero
parsePatt _ (Span _ (ABool b)) = return $ unRef >=> \case Bool b' | b == b' -> return id; _ -> mzero
parsePatt ctx (Span _ (AList [Span _ (AAtom _ "quote"), e])) = parseQuotePatt ctx e
parsePatt ctx (Span _ (AList (Span _ (AAtom _ "and") : es))) = go <$> mapM (parsePatt ctx) es where
  go [] _ = return id
  go (f:fs) v = liftM2 (flip (.)) (f v) (go fs v)
parsePatt ctx (Span _ (AList (Span _ (AAtom _ "or") : es))) = go <$> mapM (parsePatt ctx) es where
  go [] _ = mzero
  go (f:fs) v = try (f v) >>= \case
    Just a -> return a
    Nothing -> go fs v
parsePatt ctx (Span _ (AList (Span _ (AAtom _ "not") : es))) =
  mapM (parsePatt ctx) es <&> \fs v -> do
    forM_ fs $ \f -> try (f v) >>= \case Just _ -> mzero; Nothing -> return ()
    return id
parsePatt ctx (Span _ (AList (Span _ (AAtom _ "?") : Span os p : es))) =
  eval os ctx p >>= \case
    Proc f -> mapM (parsePatt ctx) es <&> \fs v -> do
      f os [v] >>= unRef >>= guard . truthy
      go fs v
    e -> escapeSpan os $ "not a function: " <> T.pack (show e)
  where
  go [] _ = return id
  go (f:fs) v = liftM2 (flip (.)) (f v) (go fs v)
parsePatt ctx (Span _ (AList es)) = parseListPatt (parsePatt ctx) es
parsePatt ctx (Span _ (ADottedList l es r)) = parseDottedListPatt (parsePatt ctx) l es r
parsePatt ctx (Span _ (AFormula f)) = parseMath f >>= parseQExprPatt ctx

parseQuotePatt :: LCtx -> AtLisp -> ElabM (LispVal -> ElabM (LCtx -> LCtx))
parseQuotePatt _ (Span _ (AAtom _ x)) = return $ unRef >=> \case Atom _ _ x' | x == x' -> return id; _ -> mzero
parseQuotePatt _ (Span _ (ANumber n)) = return $ unRef >=> \case Number n' | n == n' -> return id; _ -> mzero
parseQuotePatt _ (Span _ (AString s)) = return $ unRef >=> \case String s' | s == s' -> return id; _ -> mzero
parseQuotePatt _ (Span _ (ABool b))   = return $ unRef >=> \case Bool b' | b == b' -> return id; _ -> mzero
parseQuotePatt ctx (Span _ (AList [Span _ (AAtom _ "unquote"), e])) = parsePatt ctx e
parseQuotePatt ctx (Span _ (AList es)) = parseListPatt (parseQuotePatt ctx) es
parseQuotePatt ctx (Span _ (ADottedList l es r)) = parseDottedListPatt (parsePatt ctx) l es r
parseQuotePatt ctx (Span _ (AFormula f)) = parseMath f >>= parseQExprPatt ctx

parseQExprPatt :: LCtx -> QExpr -> ElabM (LispVal -> ElabM (LCtx -> LCtx))
parseQExprPatt _ (QApp (Span _ t) []) = return $ unRef >=> \case
  Atom _ _ t' | t == t' -> return id
  List [Atom _ _ t'] | t == t' -> return id
  _ -> mzero
parseQExprPatt ctx (QApp (Span _ t) es) = do
  fs <- mapM (parseQExprPatt ctx) es
  return $ unRef >=> \case List (Atom _ _ t' : vs) | t == t' -> go fs vs; _ -> mzero
  where
  go [] [] = return id
  go (f:fs) (v:vs) = liftM2 (flip (.)) (f v) (go fs vs)
  go _ _ = mzero
parseQExprPatt ctx (QUnquote e) = parsePatt ctx e

quoteAt :: LCtx -> AtLisp -> ElabM LispVal
quoteAt ctx (Span (o, _) e) = quote o ctx e

quote :: Offset -> LCtx -> LispAST -> ElabM LispVal
quote o _ (AAtom pt e) = return $ Atom pt o e
quote _ ctx (AList [Span _ (AAtom _ "unquote"), e]) = evalAt ctx e
quote _ ctx (AList es) = List <$> mapM (quoteAt ctx) es
quote _ ctx (ADottedList l es r) =
  liftM2 (flip (foldr cons)) (mapM (quoteAt ctx) (l : es)) (quoteAt ctx r)
quote _ _ (AString s) = return $ String s
quote _ _ (ANumber n) = return $ Number n
quote _ _ (ABool b) = return $ Bool b
quote _ _ (AFormula (Formula o f)) = return $ UnparsedFormula o f

asString :: Offset -> LispVal -> ElabM T.Text
asString _ (String s) = return s
asString o e = escapeAt o $ "expected a string, got " <> T.pack (show e)

asAtomString :: Offset -> LispVal -> ElabM T.Text
asAtomString _ (Atom _ _ s) = return s
asAtomString _ (String s) = return s
asAtomString o e = escapeAt o $ "expected an atom, got " <> T.pack (show e)

asInt :: Offset -> LispVal -> ElabM Integer
asInt _ (Number n) = return n
asInt o e = escapeAt o $ "expected an integer, got " <> T.pack (show e)

goalType :: Offset -> LispVal -> ElabM LispVal
goalType _ (Goal _ ty) = return ty
goalType o e = escapeAt o $ "expected a goal, got " <> T.pack (show e)

sExprSubst :: Offset -> H.HashMap VarName LispVal -> SExpr -> LispVal
sExprSubst o m = go where
  go (SVar v) = m H.! v
  go (App t es) = List (Atom False o t : (go <$> es))

inferType :: Offset -> LispVal -> ElabM LispVal
inferType _ (Goal _ ty) = return ty
inferType o (Atom _ _ h) = try (getSubproof h) >>= \case
  Just v -> return v
  Nothing -> escapeAt o $ "unknown hypothesis '" <> h <> "'"
inferType o (List (Atom _ _ t : es)) = try (now >>= getThm t) >>= \case
  Nothing -> escapeAt o $ "unknown theorem '" <> t <> "'"
  Just (_, bis, _, ret) ->
    let
      inferBis :: [PBinder] -> [LispVal] ->
        H.HashMap VarName LispVal -> ElabM LispVal
      inferBis (_ : _) [] _ = escapeAt o "not enough arguments"
      inferBis (bi : bis') (e : es') m = do
        inferBis bis' es' (H.insert (binderName bi) e m)
      inferBis [] _ m = return $ sExprSubst o m ret
    in inferBis bis es H.empty
inferType o (Ref g) = getRef g >>= inferType o
inferType o e = escapeAt o $ "not a proof: " <> T.pack (show e)

asSExpr :: LispVal -> Maybe SExpr
asSExpr (List (Atom _ _ t : ts)) = App t <$> mapM asSExpr ts
asSExpr (Atom _ _ x) = return $ SVar x
asSExpr _ = Nothing

asRef :: Offset -> LispVal -> ElabM (TVar LispVal)
asRef _ (Ref a) = return a
asRef o e = escapeAt o $ "not a ref-cell: " <> T.pack (show e)

unary :: Offset -> [LispVal] -> ElabM LispVal
unary _ [e] = return e
unary o es = escapeAt o $ "expected one argument, got " <> T.pack (show (length es))

evalFoldl1 :: Offset -> (a -> a -> a) -> [a] -> ElabM a
evalFoldl1 o _ [] = escapeAt o "expected at least one argument"
evalFoldl1 _ f es = return (foldl1 f es)

intBoolBinopProc :: (Integer -> Integer -> Bool) -> Proc
intBoolBinopProc f (o, _) es = mapM (asInt o) es >>= \case
    e : es' -> return $ Bool $ go e es'
    _ -> escapeAt o "expected at least one argument"
  where
  go :: Integer -> [Integer] -> Bool
  go _ [] = True
  go e1 (e2 : es') = f e1 e2 && go e2 es'

truthy :: LispVal -> Bool
truthy (Bool False) = False
truthy _ = True

isPair :: LispVal -> Bool
isPair (DottedList _ _ _) = True
isPair (List (_:_)) = True
isPair _ = False

isNull :: LispVal -> Bool
isNull (List []) = True
isNull _ = False

isInt :: LispVal -> Bool
isInt (Number _) = True
isInt _ = False

isBool :: LispVal -> Bool
isBool (Bool _) = True
isBool _ = False

isProc :: LispVal -> Bool
isProc (Proc _) = True
isProc _ = False

isAtom :: LispVal -> Bool
isAtom (Atom _ _ _) = True
isAtom _ = False

isString :: LispVal -> Bool
isString (String _) = True
isString _ = False

isMap :: LispVal -> Bool
isMap (AtomMap _) = True
isMap _ = False

isDef :: LispVal -> Bool
isDef Undef = False
isDef _ = True

isRef :: LispVal -> Bool
isRef (Ref _) = True
isRef _ = False

lispHd :: Offset -> LispVal -> ElabM LispVal
lispHd o (List []) = escapeAt o "evaluating 'hd ()'"
lispHd _ (List (e:_)) = return e
lispHd _ (DottedList e _ _) = return e
lispHd o _ = escapeAt o "expected a list"

lispTl :: Offset -> LispVal -> ElabM LispVal
lispTl o (List []) = escapeAt o "evaluating 'tl ()'"
lispTl _ (List (_:es)) = return (List es)
lispTl _ (DottedList _ [] e) = return e
lispTl _ (DottedList _ (e:es) t) = return (DottedList e es t)
lispTl o _ = escapeAt o "expected a list"

parseMapIns :: [LispVal] -> Maybe (H.HashMap T.Text LispVal -> H.HashMap T.Text LispVal)
parseMapIns [Atom _ _ s, v] = Just $ H.insert s v
parseMapIns [String s, v] = Just $ H.insert s v
parseMapIns [Atom _ _ s] = Just $ H.delete s
parseMapIns [String s] = Just $ H.delete s
parseMapIns _ = Nothing

initialBindings :: [(T.Text, LispVal)]
initialBindings = [
  ("def", Syntax Define), ("quote", Syntax Quote),
  ("fn", Syntax Lambda), ("if", Syntax If),
  ("let", Syntax Let), ("letrec", Syntax Letrec),
  ("focus", Syntax Focus), ("match", Syntax Match),
  ("match-fn", Syntax MatchFn), ("match-fn*", Syntax MatchFns) ] ++
  (mapSnd Proc <$> initialProcs) where

  initialProcs :: [(T.Text, Proc)]
  initialProcs = [
    ("display", \os@(o, _) es ->
      unary o es >>= asString o >>= reportSpan os ELInfo >> pure Undef),
    ("error", \os@(o, _) es -> unary o es >>= asString o >>= escapeSpan os),
    ("print", \os@(o, _) es -> unary o es >>= \e -> do
      reportSpan os ELInfo $! T.pack (show e)
      pure Undef),
    ("begin", \_ -> return . \case [] -> Undef; es -> last es),
    ("apply", \os@(o, _) -> \case
      Proc proc : e : es ->
        let args (List es') [] = return es'
            args e' [] = escapeAt o $ "not a list: " <> T.pack (show e')
            args e' (e2 : es') = (e':) <$> args e2 es'
        in args e es >>= proc os
      e : _ : _ -> escapeAt o $ "not a procedure: " <> T.pack (show e)
      _ -> escapeAt o "expected at least two arguments"),
    ("+", \(o, _) es -> Number . sum <$> mapM (unRef >=> asInt o) es),
    ("*", \(o, _) es -> Number . product <$> mapM (unRef >=> asInt o) es),
    ("max", \(o, _) es ->
      mapM (unRef >=> asInt o) es >>= evalFoldl1 o max >>= return . Number),
    ("min", \(o, _) es ->
      mapM (unRef >=> asInt o) es >>= evalFoldl1 o min >>= return . Number),
    ("-", \(o, _) es -> mapM (unRef >=> asInt o) es >>= \case
      [] -> escapeAt o "expected at least one argument"
      [n] -> return $ Number (-n)
      n : ns -> return $ Number (n - sum ns)),
    ("//", \(o, _) es ->
      mapM (unRef >=> asInt o) es >>= evalFoldl1 o div >>= return . Number),
    ("%", \(o, _) es ->
      mapM (unRef >=> asInt o) es >>= evalFoldl1 o mod >>= return . Number),
    ("<", intBoolBinopProc (<)),
    ("<=", intBoolBinopProc (<=)),
    (">", intBoolBinopProc (>)),
    (">=", intBoolBinopProc (>=)),
    ("=", intBoolBinopProc (==)),
    ("->string", \(o, _) es -> unary o es >>= \case
      Number n -> return $ String $ T.pack $ show n
      String s -> return $ String s
      Atom _ _ s -> return $ String s
      UnparsedFormula _ s -> return $ String s
      e -> return $ String $! T.pack $ show e),
    ("string->atom", \(o, _) es -> unary o es >>= asString o >>= return . Atom False o),
    ("string-append", \(o, _) -> mapM (asString o) >=> return . String . T.concat),
    ("not", \_ -> mapM unRef >=> \es -> return $ Bool $ not $ any truthy es),
    ("and", \_ -> mapM unRef >=> \es -> return $ Bool $ all truthy es),
    ("or", \_ -> mapM unRef >=> \es -> return $ Bool $ any truthy es),
    ("list", \_ -> return . List),
    ("cons", \_ -> \case
      [] -> return $ List []
      es' -> return $ foldr1 cons es'),
    ("hd", \(o, _) es -> unary o es >>= lispHd o),
    ("tl", \(o, _) es -> unary o es >>= lispTl o),
    ("map", \o -> \case
      [Proc f] -> f o []
      Proc f : List l : es -> do
        let unconses :: [[LispVal]] -> ElabM ([LispVal], [[LispVal]])
            unconses [] = return ([], [])
            unconses ([] : _) = escapeSpan o "mismatched input length"
            unconses ((a : l1) : ls) = unconses ls <&> \(l', ls') -> (a : l', l1 : ls')
            go :: [LispVal] -> [[LispVal]] -> ElabM [LispVal]
            go [] ls = if all null ls then return [] else escapeSpan o "mismatched input length"
            go (a : l1) ls = unconses ls >>= \(l', ls') -> liftM2 (:) (f o (a:l')) (go l1 ls')
        ls <- forM es $ \case List l' -> return l'; _ -> escapeSpan o "invalid arguments"
        List <$> go l ls
      _ -> escapeSpan o "invalid arguments"),
    ("bool?", \(o, _) es -> Bool . isBool <$> unary o es),
    ("atom?", \(o, _) es -> Bool . isAtom <$> unary o es),
    ("pair?", \(o, _) es -> Bool . isPair <$> unary o es),
    ("null?", \(o, _) es -> Bool . isNull <$> unary o es),
    ("number?", \(o, _) es -> Bool . isInt <$> unary o es),
    ("string?", \(o, _) es -> Bool . isString <$> unary o es),
    ("fn?", \(o, _) es -> Bool . isProc <$> unary o es),
    ("def?", \(o, _) es -> Bool . isDef <$> unary o es),
    ("ref?", \(o, _) es -> Bool . isRef <$> unary o es),
    ("ref!", \_ -> \case
      [] -> Ref <$> newRef Undef
      e:_ -> Ref <$> newRef e),
    ("get!", \(o, _) es -> unary o es >>= asRef o >>= getRef),
    ("set!", \(o, _) -> \case
      [e, v] -> asRef o e >>= \x -> Undef <$ setRef x v
      _ -> escapeAt o "expected two arguments"),
    ("async", \os@(o, _) -> \case
      Proc proc : es -> do
        res <- forkElabM $ proc os es
        return $ Proc $ \_ _ -> MaybeT (lift res)
      e : _ -> escapeAt o $ "not a procedure: " <> T.pack (show e)
      _ -> escapeAt o "expected at least one argument"),
    ("atom-map?", \(o, _) es -> Bool . isMap <$> unary o es),
    ("atom-map!", \(o, _) es -> do
      m' <- foldlM (\m -> \case
        List e -> case parseMapIns e of
          Just f -> return (f m)
          _ -> escapeAt o "invalid arguments"
        _ -> escapeAt o "invalid arguments") H.empty es
      Ref <$> newRef (AtomMap m')),
    ("lookup", \o -> \case
      e : k : es -> unRef e >>= \case
        AtomMap m -> do
          s <- asAtomString (fst o) k
          case H.lookup s m of
            Just v -> return v
            Nothing -> case fromMaybe Undef (headMaybe es) of
              Proc f -> f o []
              v -> return v
        _ -> escapeSpan o "not a map"
      _ -> escapeSpan o "expected two arguments"),
    ("insert!", \(o, _) -> \case
      Ref r : es -> case parseMapIns es of
        Nothing -> escapeAt o "expected three arguments"
        Just f -> Undef <$ modifyRef r (\case AtomMap m -> AtomMap (f m); e -> e)
      _ -> escapeAt o "expected a mutable map"),
    ("insert", \(o, _) -> \case
      em : es -> case parseMapIns es of
        Nothing -> escapeAt o "expected three arguments"
        Just f -> unRef em >>= \case
          AtomMap m -> return $ AtomMap (f m)
          _ -> escapeAt o "not a map"
      _ -> escapeAt o "expected three arguments"),

    -- MM0 specific
    ("set-timeout", \(o, _) es -> unary o es >>= unRef >>= asInt o >>= \n ->
      Undef <$ modify (\env -> env {eTimeout = 1000 * fromInteger n})),
    ("mvar?", \(o, _) es -> Bool . isMVar <$> unary o es),
    ("goal?", \(o, _) es -> Bool . isGoal <$> unary o es),
    ("mvar!", \(o, _) -> \case
      [Atom _ _ s, Bool bd] -> Ref <$> newMVar o s bd
      _ -> escapeAt o "invalid arguments"),
    ("pp", \(o, _) es -> unary o es >>= ppExpr >>= return . String . render),
    ("goal", \(o, _) es -> Goal o <$> unary o es),
    ("goal-type", \(o, _) es -> unary o es >>= unRef >>= goalType o),
    ("infer-type", \(o, _) es -> unary o es >>= inferType o),
    ("get-mvars", \_ _ -> List . fmap Ref . V.toList <$> (getTC >>= VD.freeze . tcMVars)),
    ("get-goals", \_ _ -> List . fmap Ref . V.toList . tcGoals <$> getTC),
    ("set-goals", \(o, _) es -> Undef <$ (mapM (asRef o) es >>= setGoals)),
    ("to-expr", \(o, _) es -> unary o es >>= parseRefine o >>= toExpr "" False),
    ("refine", \(o, _) es -> Undef <$ refine o es),
    ("have", \(o, _) -> \case
      [Atom _ px x, e] -> do
        ty <- Ref <$> newUnknownMVar o
        Undef <$ have o px x ty e
      [Atom _ px x, ty', e] -> do
        ty <- parseRefine o ty' >>= toExpr "" False
        Undef <$ have o px x ty e
      _ -> escapeAt o "invalid arguments"),
    ("stat", \o _ ->
      getStat >>= reportSpan o ELInfo . render >> pure Undef),
    ("get-decl", \os@(o, _) -> \case
      [Atom _ _ x] -> gets (H.lookup x . eDecls) >>= \case
        Just (_, (_, px), d, _) -> return $ declToLisp o (fst px) x d
        _ -> return Undef
      _ -> escapeSpan os "invalid arguments"),
    ("add-decl!", \o -> \case
      Atom _ _ "term" : es -> Undef <$ lispAddTerm o es
      Atom _ _ "def" : es -> Undef <$ lispAddTerm o es
      Atom _ _ "axiom" : es -> Undef <$ lispAddThm o es
      Atom _ _ "theorem" : es -> Undef <$ lispAddThm o es
      _ -> escapeSpan o "unknown decl kind"),
    ("add-term!", \o es -> Undef <$ lispAddTerm o es),
    ("add-thm!", \o es -> Undef <$ lispAddThm o es),

    -- redefinable configuration functions
    ("refine-extra-args", \(o, _) -> \case
      [_, e] -> return e
      _:e:_ -> e <$ reportAt o ELError "too many arguments"
      _ -> escapeAt o "expected at least two arguments")]

evalQExpr :: LCtx -> QExpr -> ElabM LispVal
evalQExpr ctx (QApp (Span (o, _) e) es) =
  List . (Atom False o e :) <$> mapM (evalQExpr ctx) es
evalQExpr ctx (QUnquote (Span o e)) = eval o ctx e

cleanBinder :: Range -> LispVal -> ElabM PBinder
cleanBinder _ (List [Atom _ _ x, Atom _ _ s]) = return $ PBound x s
cleanBinder o (List [Atom _ _ x, Atom _ _ s, List vs]) = PReg x . DepType s <$> mapM (cleanVar o) vs
cleanBinder o _ = escapeSpan o "invalid binder arguments"

cleanDepType :: Range -> LispVal -> ElabM DepType
cleanDepType _ (Atom _ _ s) = return $ DepType s []
cleanDepType o (List [Atom _ _ s, List vs]) = DepType s <$> mapM (cleanVar o) vs
cleanDepType o _ = escapeSpan o "invalid type arguments"

cleanVis :: Range -> LispVal -> ElabM Visibility
cleanVis _ (Atom _ _ "pub") = return Public
cleanVis _ (Atom _ _ "abstract") = return Abstract
cleanVis _ (Atom _ _ "local") = return Local
cleanVis _ (List []) = return VisDefault
cleanVis o _ = escapeSpan o "invalid visibility arguments"

cleanHyp :: Range -> LispVal -> ElabM (Maybe VarName, SExpr)
cleanHyp o (List [Atom _ _ "_", h]) = (,) Nothing <$> cleanTerm o h
cleanHyp o (List [Atom _ _ x, h]) = (,) (Just x) <$> cleanTerm o h
cleanHyp o _ = escapeSpan o "invalid hypothesis"

cleanDummy :: Range -> LispVal -> ElabM (VarName, Sort)
cleanDummy _ (List [Atom _ _ x, Atom _ _ s]) = return (x, s)
cleanDummy o _ = escapeSpan o "invalid dummy arguments"

lispTermDecl :: Range -> [LispVal] -> ElabM Decl
lispTermDecl o [List bis, ret] =
  liftM2 DTerm (mapM (cleanBinder o) bis) (cleanDepType o ret)
lispTermDecl o [List bis, ret, vis, List ds, val] = do
  bis' <- mapM (cleanBinder o) bis
  ret' <- cleanDepType o ret
  vis' <- cleanVis o vis
  DDef vis' bis' ret' <$> case val of
    List [] -> return Nothing
    _ -> do
      ds' <- mapM (cleanDummy o) ds
      v' <- cleanTerm o val
      return $ Just (ds', v')
lispTermDecl o _ = escapeSpan o "invalid term decl arguments"

lispThmDecl :: Range -> [LispVal] -> ElabM Decl
lispThmDecl o [List bis, List hs, ret] =
  liftM3 DAxiom (mapM (cleanBinder o) bis) (fmap snd <$> mapM (cleanHyp o) hs) (cleanTerm o ret)
lispThmDecl o [List bis, List hs, ret, vis, val] = do
  bis' <- mapM (cleanBinder o) bis
  hs' <- mapM (cleanHyp o) hs
  ret' <- cleanTerm o ret
  vis' <- cleanVis o vis
  case val of
    Proc f -> DTheorem vis' bis' hs' ret' <$> forkElabM (f o [] >>= cleanProofD o)
    _ -> DTheorem vis' bis' hs' ret' . return . Just <$> cleanProofD o val
lispThmDecl o _ = escapeSpan o "invalid theorem decl arguments"

lispAddTerm :: Range -> [LispVal] -> ElabM ()
lispAddTerm o (Atom _ px x : es) = do
  d <- lispTermDecl o es
  let r = textToRange px x
  insertDecl x d r r ("duplicate term/def declaration '" <> x <> "'")
lispAddTerm o _ = escapeSpan o "invalid arguments"

lispAddThm :: Range -> [LispVal] -> ElabM ()
lispAddThm o (Atom _ px x : es) = do
  d <- lispThmDecl o es
  let r = textToRange px x
  insertDecl x d r r ("duplicate axiom/theorem declaration '" <> x <> "'")
lispAddThm o _ = escapeSpan o "invalid arguments"

-----------------------------
-- Tactics
-----------------------------

tryRefine :: Offset -> LispVal -> ElabM ()
tryRefine _ Undef = return ()
tryRefine o e = refine o [e]

evalRefines :: Offset -> LCtx -> [AtLisp] -> ElabM ()
evalRefines o = evalList () (\e l -> e >>= tryRefine o >> l)

elabLisp :: SExpr -> AtLisp -> ElabM ([(VarName, Sort)], Proof)
elabLisp t e@(Span os@(o, _) _) = do
  g <- newRef (Goal o (sExprToLisp o t))
  modifyTC $ \tc -> tc {tcGoals = V.singleton g}
  evalAt def e >>= tryRefine o
  gs' <- tcGoals <$> getTC
  forM_ gs' $ \g' -> getRef g' >>= \case
    Goal o' ty -> do
      pp <- ppExpr ty
      reportAt o' ELError $ render' $ "|-" <+> doc pp
    _ -> return ()
  unless (V.null gs') mzero
  cleanProofD os (Ref g)

cleanProofD :: Range -> LispVal -> ElabM ([(VarName, Sort)], Proof)
cleanProofD o e = do
  p <- cleanProof o e
  m <- execStateT (inferDummiesProof o p) M.empty
  return (M.toList m, p)

inferDummiesProof :: Range -> Proof -> StateT (M.Map VarName Sort) ElabM ()
inferDummiesProof _ (PHyp _) = return ()
inferDummiesProof o (PThm t es ps) = do
  (_, bis, _, _) <- lift $ now >>= getThm t
  zipWithM_ (inferDummiesExpr o . Just . binderSort) bis es
  mapM_ (inferDummiesProof o) ps
inferDummiesProof o (PConv _ c p) = inferDummiesConv o Nothing c >> inferDummiesProof o p
inferDummiesProof o (PLet _ p1 p2) = inferDummiesProof o p1 >> inferDummiesProof o p2
inferDummiesProof _ PSorry = return ()

inferDummiesConv :: Range -> Maybe Sort -> Conv -> StateT (M.Map VarName Sort) ElabM ()
inferDummiesConv o s (CVar v) = inferDummiesVar o s v
inferDummiesConv o _ (CApp t cs) = do
  (_, bis, _, _) <- lift $ now >>= getTerm t
  zipWithM_ (inferDummiesConv o . Just . binderSort) bis cs
inferDummiesConv o s (CSym c) = inferDummiesConv o s c
inferDummiesConv o s (CUnfold t es _ c) = do
  (_, bis, _, _) <- lift $ now >>= getTerm t
  zipWithM_ (inferDummiesExpr o . Just . binderSort) bis es
  inferDummiesConv o s c

inferDummiesExpr :: Range -> Maybe Sort -> SExpr -> StateT (M.Map VarName Sort) ElabM ()
inferDummiesExpr o s (SVar v) = inferDummiesVar o s v
inferDummiesExpr o _ (App t es) = do
  (_, bis, _, _) <- lift $ now >>= getTerm t
  zipWithM_ (inferDummiesExpr o . Just . binderSort) bis es

inferDummiesVar :: Range -> Maybe Sort -> VarName -> StateT (M.Map VarName Sort) ElabM ()
inferDummiesVar o s v =
  H.lookup v . tcVars <$> lift getTC >>= \case
    Just _ -> return ()
    Nothing -> case s of
      Nothing -> lift $ escapeSpan o $ "cannot infer type for " <> v
      Just s' -> gets (M.lookup v) >>= \case
        Nothing -> modify (M.insert v s')
        Just s2 -> unless (s' == s2) $ lift $ escapeSpan o $
          "inferred two types " <> s' <> ", " <> s2 <> " for " <> v

cleanProof :: Range -> LispVal -> ElabM Proof
cleanProof o (Ref g) = getRef g >>= \case
  Goal o' ty -> do
    pp <- ppExpr ty
    escapeAt o' $ render' $ "??? |-" <+> doc pp
  e -> cleanProof o e
cleanProof _ (Atom _ _ h) = return $ PHyp h
cleanProof o (List [Atom _ _ ":conv", ty, conv, p]) =
  liftM3 PConv (cleanTerm o ty) (cleanConv o conv) (cleanProof o p)
cleanProof o (List [Atom _ _ ":let", Atom _ _ h, p1, p2]) =
  liftM2 (PLet h) (cleanProof o p1) (cleanProof o p2)
cleanProof o (List (Atom _ _ t : es)) = try (now >>= getThm t) >>= \case
  Nothing -> escapeSpan o $ "unknown theorem '" <> t <> "'"
  Just (_, bis, hs, _) -> do
    unless (length es == length bis + length hs) $
      escapeSpan o $ "incorrect number of arguments to " <> t <>
        "; expected " <> T.pack (show (length bis)) <>
        " + " <> T.pack (show (length hs)) <>
        ", got " <> T.pack (show es)
    let (es1, es2) = splitAt (length bis) es
    liftM2 (PThm t) (mapM (cleanTerm o) es1) (mapM (cleanProof o) es2)
cleanProof o e = escapeSpan o $ "bad proof: " <> T.pack (show e)

cleanTerm :: Range -> LispVal -> ElabM SExpr
cleanTerm o (Ref g) = getRef g >>= \case
  MVar n o' s bd -> escapeAt o' $ render $ ppMVar n s bd
  e -> cleanTerm o e
cleanTerm _ (Atom _ _ x) = return $ SVar x
cleanTerm o (List (Atom _ _ t : es)) = App t <$> mapM (cleanTerm o) es
cleanTerm o e = escapeSpan o $ "bad term: " <> T.pack (show e)

cleanConv :: Range -> LispVal -> ElabM Conv
cleanConv o (Ref g) = getRef g >>= \case
  MVar n o' s bd -> escapeAt o' $ render $ ppMVar n s bd
  e -> cleanConv o e
cleanConv _ (Atom _ _ x) = return $ CVar x
cleanConv o (List [Atom _ _ ":unfold", Atom _ _ t, List es, List ds, p]) =
  liftM3 (CUnfold t) (mapM (cleanTerm o) es) (mapM (cleanVar o) ds) (cleanConv o p)
cleanConv o (List [Atom _ _ ":sym", p]) = CSym <$> cleanConv o p
cleanConv o (List (Atom _ _ t : es)) = CApp t <$> mapM (cleanConv o) es
cleanConv o e = escapeSpan o $ "bad conv: " <> T.pack (show e)

cleanVar :: Range -> LispVal -> ElabM VarName
cleanVar o (Ref g) = getRef g >>= \case
  MVar n o' s bd -> escapeAt o' $ render $ ppMVar n s bd
  e -> cleanVar o e
cleanVar _ (Atom _ _ x) = return x
cleanVar o e = escapeSpan o $ "bad var: " <> T.pack (show e)

data InferMode = IMRegular | IMExplicit | IMBoundOnly deriving (Eq, Show)

imPopBd :: InferMode -> Bool -> Bool
imPopBd IMRegular _ = False
imPopBd IMExplicit _ = True
imPopBd IMBoundOnly bd = bd

data RefineExpr =
    RApp InferMode Offset T.Text [RefineExpr]
  | RExact Offset LispVal
  deriving (Show)

reOffset :: RefineExpr -> Offset
reOffset (RApp _ o _ _) = o
reOffset (RExact o _) = o

unconsIf :: Bool -> a -> [a] -> (a, [a])
unconsIf False a es = (a, es)
unconsIf True a [] = (a, [])
unconsIf True _ (e : es) = (e, es)

asAtom :: Offset -> LispVal -> ElabM (Offset, T.Text)
asAtom _ (Atom _ o t) = return (o, t)
asAtom o _ = escapeAt o "expected an 'atom"

parseRefine :: Offset -> LispVal -> ElabM RefineExpr
parseRefine _ (Atom _ o x) = return (RApp IMRegular o x [])
parseRefine o (List []) = return (RApp IMRegular o "_" [])
parseRefine _ (List [Atom _ o "!"]) = escapeAt o "expected at least one argument"
parseRefine _ (List (Atom _ o "!" : t : es)) =
  asAtom o t >>= \(o', t') -> RApp IMExplicit o' t' <$> mapM (parseRefine o') es
parseRefine _ (List [Atom _ o "!!"]) =
  escapeAt o "expected at least one argument"
parseRefine _ (List (Atom _ o "!!" : t : es)) =
  asAtom o t >>= \(o', t') -> RApp IMBoundOnly o' t' <$> mapM (parseRefine o') es
parseRefine _ (List [Atom _ o ":verb", e]) = return $ RExact o e
parseRefine o (List (t : es)) =
  asAtom o t >>= \(o', t') -> RApp IMRegular o' t' <$> mapM (parseRefine o') es
parseRefine o (UnparsedFormula o' f) =
  parseMath (Formula o' f) >>= evalQExpr def >>= parseRefine o
parseRefine o e = escapeAt o $ "syntax error in parseRefine: " <> T.pack (show e)

data UnifyResult = UnifyResult Bool LispVal

coerceTo :: Offset -> LispVal -> LispVal -> ElabM (LispVal -> LispVal)
coerceTo o tgt ty = unifyAt o tgt ty >>= \case
  UnifyResult False _ -> return id
  UnifyResult True u -> return (\p -> List [Atom False o ":conv", tgt, u, p])

coerceTo' :: Offset -> LispVal -> LispVal -> ElabM LispVal
coerceTo' o tgt p = (inferType o p >>= coerceTo o tgt) <*> return p

unifyAt :: Offset -> LispVal -> LispVal -> ElabM UnifyResult
unifyAt o e1 e2 = try (unify o e1 e2) >>= \case
  Just u -> return u
  Nothing -> do
    err <- render <$> unifyErr e1 e2
    reportAt o ELError err
    return $ UnifyResult False $ List [Atom False o ":error", String err]

unify :: Offset -> LispVal -> LispVal -> ElabM UnifyResult
unify o (Ref g) v = assign o False g v
unify o v (Ref g) = assign o True g v
unify o a@(Atom _ _ x) (Atom _ _ y) = do
  unless (x == y) $ escapeAt o $
    "variables do not match: " <> x <> " != " <> y
  return (UnifyResult False a)
unify o v1@(List (a1@(Atom _ _ t1) : es1)) v2@(List (a2@(Atom _ _ t2) : es2)) =
  if t1 == t2 then
    (\(b, l) -> UnifyResult b (List (a1 : l))) <$> go es1 es2
  else do
    decls <- gets eDecls
    case (H.lookup t1 decls, H.lookup t2 decls) of
      (Just (n1, _, _, _), Just (n2, _, DDef _ args2 _ (Just (ds2, val2)), _)) | n1 < n2 ->
        unfold o True a2 args2 ds2 val2 es2 v1
      (Just (_, _, DDef _ args1 _ (Just (ds1, val1)), _), _) ->
        unfold o False a1 args1 ds1 val1 es1 v2
      (_, Just (_, _, DDef _ args2 _ (Just (ds2, val2)), _)) ->
        unfold o True a2 args2 ds2 val2 es2 v1
      _ -> escapeAt o $ "terms do not match: " <> t1 <> " != " <> t2
  where
  unifyCons (UnifyResult b1 l) (b2, l2) = (b1 || b2, l : l2)
  go [] [] = return (False, [])
  go (e1 : es1') (e2 : es2') = liftM2 unifyCons (unify o e1 e2) (go es1' es2')
  go _ _ = escapeAt o $ "bad terms: " <> T.pack (show (t1, length es1, t2, length es2))
unify o (Atom _ _ v) e2@(List (Atom _ _ _ : _)) = do
  pp <- ppExpr e2
  escapeAt o $ "variable vs term: " <> v <> " != " <> render pp
unify o e1@(List (Atom _ _ _ : _)) (Atom _ _ v) = do
  pp <- ppExpr e1
  escapeAt o $ "term vs variable: " <> render pp <> " != " <> v
unify o e1 e2 = escapeAt o $ "bad terms: " <> T.pack (show (e1, e2))

assign :: Offset -> Bool -> TVar LispVal -> LispVal -> ElabM UnifyResult
assign o sym g = \v -> getRef g >>= \case
  MVar _ _ _ _ -> go v
  v' -> if sym then unify o v v' else unify o v' v
  where
  go (Ref g') | g == g' = return $ UnifyResult False (Ref g)
  go v@(Ref g') = getRef g' >>= \case
    v'@(Ref _) -> go v'
    _ -> check v
  go v = check v
  check v = try (occursCheck g v) >>= \case
    Just v' -> UnifyResult False v' <$ setRef g v'
    Nothing -> escapeAt o "occurs-check failed, can't build infinite assignment"

occursCheck :: TVar LispVal -> LispVal -> ElabM LispVal
occursCheck g (Ref g') | g == g' = mzero
occursCheck g e@(Ref g') = getRef g' >>= \case
  MVar _ _ _ _ -> return e
  e' -> occursCheck g e'
occursCheck g (List (t : es)) = List . (t :) <$> mapM (occursCheck g) es
occursCheck _ e = return e

unfold :: Offset -> Bool -> LispVal -> [PBinder] -> [(VarName, Sort)] ->
  SExpr -> [LispVal] -> LispVal -> ElabM UnifyResult
unfold o sym t bis ds val es e2 = buildSubst bis es H.empty where

  buildSubst :: [PBinder] -> [LispVal] -> H.HashMap VarName LispVal -> ElabM UnifyResult
  buildSubst (bi : bis') (e : es') m =
    buildSubst bis' es' (H.insert (binderName bi) e m)
  buildSubst [] [] m = buildDummies ds id m
  buildSubst _ _ _ = escapeAt o "incorrect arguments"

  buildDummies :: [(VarName, Sort)] -> ([LispVal] -> [LispVal]) ->
    H.HashMap VarName LispVal -> ElabM UnifyResult
  buildDummies ((x, s) : ds') q m = do
    v <- Ref <$> newMVar o s True
    buildDummies ds' (q . (v :)) (H.insert x v m)
  buildDummies [] q m = do
    UnifyResult _ p <- unify o (sExprSubst o m val) e2
    let p' = List [Atom False o ":unfold", t, List es, List (q []), p]
    return $ UnifyResult True $ if sym then List [Atom False o ":sym", p'] else p'

toExpr :: Sort -> Bool -> RefineExpr -> ElabM LispVal
toExpr _ _ (RExact _ e) = return e -- TODO: check type
toExpr s bd (RApp _ o "_" _) = Ref <$> newMVar o s bd
toExpr s bd (RApp _ o t es) =
  (if null es then H.lookup t . tcVars <$> getTC else return Nothing) >>= \case
    Just (PBound _ s') -> do
      unless (s == s') $ reportAt o ELError "variable has the wrong sort"
      return $ Atom False o t
    Just (PReg _ (DepType s' _)) -> do
      unless (s == s') $ reportAt o ELError "variable has the wrong sort"
      when bd $ reportAt o ELError "expected a bound variable"
      return $ Atom False o t
    Nothing -> (if bd then return Nothing else try (now >>= getTerm t)) >>= \case
      Nothing | null es -> do
        modifyTC $ \tc -> tc {tcVars = H.insert t (PBound t s) (tcVars tc)}
        return $ Atom False o t
      Nothing -> escapeAt o $ "unknown term '" <> t <> "'"
      Just (_, bis, ret, _) -> do
        let
          refineBis :: [PBinder] -> [RefineExpr] -> ElabM [LispVal]
          refineBis (bi : bis') rs =
            let (r, rs') = unconsIf True (RApp IMRegular o "_" []) rs in
            liftM2 (:)
              (toExpr (dSort $ binderType bi) (binderBound bi) r)
              (refineBis bis' rs')
          refineBis [] [] = return []
          refineBis [] (r:_) = [] <$ reportAt (reOffset r) ELError "too many arguments"
        es' <- refineBis bis es
        when bd $ reportAt o ELError "expected a bound variable"
        let e = List $ Atom False o t : es'
        if s == dSort ret || s == "" then return e else
          try (getCoe (\c v -> List [Atom False o c, v]) (dSort ret) s) >>= \case
            Just c -> return (c e)
            Nothing -> e <$ reportAt o ELError
              ("type error: expected " <> s <> ", got " <> dSort ret)

getGoals :: Offset -> ElabM [TVar LispVal]
getGoals o = try getTC >>= \case
  Just tc -> return $ V.toList $ tcGoals tc
  Nothing -> escapeAt o "not in a theorem context"

withGoals :: Offset -> (VD.IOVector (TVar LispVal) -> ElabM a) -> ElabM a
withGoals o m = do
  gv <- VD.new 0
  a <- m gv
  v <- VD.unsafeFreeze gv
  gs <- getGoals o
  setGoals (V.toList v ++ gs)
  return a

newGoal :: VD.IOVector (TVar LispVal) -> Offset -> LispVal -> ElabM (TVar LispVal)
newGoal gv o ty = do
  g <- newRef (Goal o ty)
  liftIO $ VD.pushBack gv g
  return g

refine :: Offset -> [LispVal] -> ElabM ()
refine o es = do
  withGoals o $ \gv -> do
    gs <- getGoals o
    let go :: [LispVal] -> [TVar LispVal] -> ElabM ()
        go [] gs' = setGoals gs'
        go _ [] = setGoals []
        go es1@(e:es') (g:gs') = do
          getRef g >>= \case
            Goal _ ty -> do
              parseRefine o e >>= refineProof gv ty >>= setRef g
              go es' gs'
            _ -> go es1 gs'
    go es gs
  cleanMVars

refineProof :: VD.IOVector (TVar LispVal) ->
  LispVal -> RefineExpr -> ElabM LispVal
refineProof gv = refinePf where
  refinePf :: LispVal -> RefineExpr -> ElabM LispVal
  refinePf ty (RExact o e) = coerceTo' o ty e
  refinePf ty (RApp _ o "?" _) = Ref <$> newRef (Goal o ty)
  refinePf ty (RApp _ o "_" []) = Ref <$> newGoal gv o ty
  refinePf ty (RApp _ o "_" es) = do
    mv <- Ref <$> newUnknownMVar o
    refineExtraArgs o mv ty es (Ref <$> newGoal gv o mv)
  refinePf ty (RApp im o t es) = try (getSubproof t) >>= \case
    Just v -> refineExtraArgs o v ty es (return $ Atom False o t)
    Nothing -> try (now >>= getThm t) >>= \case
      Just (_, bis, hs, ret) -> refinePfThm ty im o t es bis hs ret
      Nothing -> escapeAt o $ "unknown theorem/hypothesis '" <> t <> "'"

  refinePfThm :: LispVal -> InferMode -> Offset -> T.Text -> [RefineExpr] ->
    [PBinder] -> [SExpr] -> SExpr -> ElabM LispVal
  refinePfThm ty im o t es bis hs ret = refineBis bis es id H.empty where
    refineBis :: [PBinder] -> [RefineExpr] -> ([LispVal] -> [LispVal]) ->
      H.HashMap VarName LispVal -> ElabM LispVal
    refineBis (bi : bis') rs f m = do
      let bd = binderBound bi
          (r, rs') = unconsIf (imPopBd im bd) (RApp IMRegular o "_" []) rs
      e <- toExpr (dSort $ binderType bi) bd r
      refineBis bis' rs' (f . (e :)) (H.insert (binderName bi) e m)
    refineBis [] rs f m = refineHs hs rs f (return []) m

    refineHs :: [SExpr] -> [RefineExpr] -> ([LispVal] -> [LispVal]) -> ElabM [LispVal] ->
      H.HashMap VarName LispVal -> ElabM LispVal
    refineHs (e : es') rs f ps m = do
      let (r, rs') = unconsIf True (RApp IMRegular o "_" []) rs
      refineHs es' rs' f (liftM2 (flip (:)) ps (refinePf (sExprSubst o m e) r)) m
    refineHs [] rs f ps m =
      refineExtraArgs o (sExprSubst o m ret) ty rs
        (ps <&> \l -> List (Atom False o t : f (reverse l)))

  refineExtraArgs :: Offset -> LispVal -> LispVal -> [RefineExpr] -> ElabM LispVal -> ElabM LispVal
  refineExtraArgs o v ty [] m = coerceTo o ty v <*> m
  refineExtraArgs o _ ty rs@(r:_) m = do
    e <- m
    es <- forM rs $ \r' -> do
      mv <- newUnknownMVar o
      refinePf (Ref mv) r'
    e' <- call (reOffset r) "refine-extra-args" $ Proc callback : e : es
    coerceTo' o ty e'
    where
    callback (o', _) [ty', e'] = parseRefine o' e' >>= refinePf ty'
    callback (o', _) [e'] = do
      mv <- newUnknownMVar o'
      parseRefine o' e' >>= refinePf (Ref mv)
    callback (o', _) _ = escapeAt o' "expected two arguments"

focus :: Offset -> LCtx -> [AtLisp] -> ElabM ()
focus o ctx es = getGoals o >>= \case
  [] -> escapeAt o "no goals"
  g1 : gt -> do
    setGoals [g1]
    evalRefines o ctx es
    gs' <- getGoals o
    setGoals $ gs' ++ gt

have :: Offset -> Offset -> VarName -> LispVal -> LispVal -> ElabM ()
have o px x ty e = do
  gv <- VD.new 0
  p <- parseRefine o e >>= refineProof gv ty
  v <- VD.unsafeFreeze gv
  addSubproof x ty p
  gs <- getGoals o
  gs' <- forM gs $ \g -> getRef g >>= \case
    Goal o' ty' -> do
      g' <- newRef (Goal o' ty')
      setRef g (List [Atom False o ":let", Atom False px x, p, Ref g'])
      return (Just g')
    _ -> return Nothing
  setGoals (V.toList v ++ catMaybes gs')
