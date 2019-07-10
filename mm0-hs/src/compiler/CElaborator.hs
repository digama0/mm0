{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module CElaborator (elaborate, ErrorLevel(..), ElabError(..)) where

import Control.Monad.Fail
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad.RWS.Strict
import Data.List
import Data.Bits
import Data.Maybe
import Data.Word8
import Data.Default
import qualified Data.IntMap as I
import qualified Data.HashMap.Strict as H
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Vector.Unboxed as U
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Text as T
import Text.Megaparsec.Error
import CParser (ParseASTError, PosState, errorOffset)
import CAST
import CEnv
import CMathParser
import Util

elaborate :: [ParseASTError] -> AST -> IO (Env, [ElabError])
elaborate errs ast = do
  (_, env, errs) <- runElab (mapM_ elabStmt ast) (toElabError <$> errs)
  return (env, errs)

elabStmt :: AtPos Stmt -> Elab ()
elabStmt (AtPos pos s) = resuming $ case s of
  Sort px x sd -> addSort px x sd
  Decl vis dk px x bis ret v -> addDecl vis dk px x bis ret v
  Notation (Delimiter cs Nothing) -> lift $ addDelimiters cs cs
  Notation (Delimiter ls (Just rs)) -> lift $ addDelimiters ls rs
  Notation (Prefix px x tk prec) -> addPrefix px x tk prec
  Notation (Infix r px x tk prec) -> addInfix r px x tk prec
  _ -> reportAt pos ELWarning "unimplemented"

checkNew :: ErrorLevel -> Offset -> T.Text -> (v -> Offset) -> T.Text ->
  H.HashMap T.Text v -> ElabM (v -> H.HashMap T.Text v)
checkNew l o msg f k m = case H.lookup k m of
  Nothing -> return (\v -> H.insert k v m)
  Just a -> do
    reportErr $ ElabError l o o msg [(f a, f a, "previously declared here")]
    mzero

addSort :: Offset -> T.Text -> SortData -> ElabM ()
addSort px x sd = do
  env <- get
  ins <- checkNew ELError px ("duplicate sort declaration '" <> x <> "'")
    (\(_, i, _) -> i) x (eSorts env)
  n <- next
  put $ env {eSorts = ins (n, px, sd)}

inferDepType :: AtDepType -> ElabM ()
inferDepType (AtDepType (AtPos o t) ts) = do
  lift $ resuming $ do
    (_, sd) <- try (now >>= getSort t) >>=
      fromJustAt o ("sort '" <> t <> "' not declared")
    -- TODO: check sd
    return ()
  lift $ modifyInfer $ \ic -> ic {
    icDependents = foldl' (\m (AtPos o x) ->
      H.alter (Just . maybe [o] (o:)) x m) (icDependents ic) ts }

inferBinder :: T.Text -> Binder -> ElabM ()
inferBinder x bi@(Binder o l ty) = case ty of
  Nothing -> addVar True
  Just (TType ty) -> inferDepType ty >> addVar False
  Just (TFormula f) -> () <$ parseFormulaProv x f
  where
  addVar :: Bool -> ElabM ()
  addVar noType = do
    ic <- gets eInfer
    locals' <- case localName l of
      Nothing -> do
        when noType $ escapeAt o "cannot infer variable type"
        return $ icLocals ic
      Just n -> do
        ins <- checkNew ELWarning o
          ("variable '" <> n <> "' shadows previous declaration")
          liOffset n (icLocals ic)
        return (ins (LIOld bi Nothing))
    lift $ modifyInfer $ \ic -> ic {icLocals = locals'}

addDecl :: Visibility -> DeclKind -> Offset -> T.Text ->
  [Binder] -> Maybe [Type] -> Maybe LispVal -> ElabM ()
addDecl vis dk px x bis ret v = do
  let (bis', ret') = unArrow bis ret
  withInfer $ do
    mapM_ (inferBinder x) bis'
    case ret' of
      Nothing -> return ()
      Just (TType ty) -> inferDepType ty
      Just (TFormula f) -> () <$ parseFormulaProv x f
    return ()
  where

  unArrow :: [Binder] -> Maybe [Type] -> ([Binder], Maybe Type)
  unArrow bis Nothing = (bis, Nothing)
  unArrow bis (Just tys) = mapFst (bis ++) (go tys) where
    go [ty] = ([], Just ty)
    go (ty:tys) = mapFst (Binder (tyOffset ty) LAnon (Just ty) :) (go tys)

addDelimiters :: [Char] -> [Char] -> Elab ()
addDelimiters ls rs = modifyPE $ \e ->
  let delims@(Delims arr) = pDelims e
      f :: Word8 -> Char -> (Int, Word8)
      f w c = let i = fromEnum (toEnum (fromEnum c) :: Word8)
              in (i, (U.unsafeIndex arr i) .|. w)
  in e { pDelims = Delims $ arr U.// ((f 1 <$> ls) ++ (f 2 <$> rs)) }

mkLiterals :: Int -> Prec -> Int -> [PLiteral]
mkLiterals 0 _ _ = []
mkLiterals 1 p n = [PVar n p]
mkLiterals i p n = PVar n maxBound : mkLiterals (i-1) p (n+1)

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
