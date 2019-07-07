module CElaborator (elaborate) where

import Control.Concurrent.STM
import Control.Concurrent.STM.TVar
import Data.List
import Data.Maybe
import qualified Data.IntMap as I
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Text as T
import Text.Megaparsec.Error
import CParser (ParseASTError, PosState, errorOffset)
import CAST

type Errors = I.IntMap [ParseASTError]

insertErr :: ParseASTError -> Errors -> Errors
insertErr e = I.alter (Just . (e :) . fromMaybe []) (errorOffset e)

data Env = Env {
  initialPos :: PosState T.Text,
  errors :: Errors }

type Elab = IO

elaborate :: [ParseASTError] -> PosState T.Text -> AST -> IO Env
elaborate errs pos ast = do
  pEnv <- newTVarIO $ Env {
    initialPos = pos,
    errors = foldl' (flip insertErr) I.empty errs }
  elabAST pEnv ast

elabAST :: TVar Env -> AST -> Elab Env
elabAST pEnv = \ast -> mapM_ elabAtStmt ast >> readTVarIO pEnv where

  modifyEnv :: (Env -> Env) -> Elab ()
  modifyEnv = atomically . modifyTVar pEnv

  report :: ParseASTError -> Elab ()
  report e = modifyEnv (\env -> env {errors = insertErr e (errors env)})

  failAt :: Offset -> String -> Elab ()
  failAt o s = report $ FancyError o (S.singleton (ErrorFail s))

  elabAtStmt :: AtPos Stmt -> Elab ()
  elabAtStmt (AtPos pos s) = undefined
