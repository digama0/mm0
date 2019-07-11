module Compiler where

import System.IO
import System.Exit
import Data.List
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.List.NonEmpty as NE
import qualified Text.Megaparsec as M
import qualified Data.Set as S
import CParser
import CElaborator

compile :: [String] -> IO ()
compile args = do
  (name, mm0) <- case args of
    [] -> return ("", stdin)
    (mm0:_) -> (,) mm0 <$> openFile mm0 ReadMode
  str <- T.hGetContents mm0
  case parseAST name str of
    (errs, _, Nothing) -> do
      let errs' = M.ParseErrorBundle (NE.fromList errs) (initialPosState name str)
      die (M.errorBundlePretty errs')
    (errs, _, Just ast) -> elaborate errs ast >>= \case
      (_env, []) -> putStrLn "OK"
      (_env, errs2) -> do
        let errs' = M.ParseErrorBundle
              (NE.fromList (sortOn M.errorOffset (toParseError <$> errs2)))
              (initialPosState name str)
        die (M.errorBundlePretty errs')

toParseError :: ElabError -> ParseError
toParseError (ElabError el o _ msg _) =
  M.FancyError o (S.singleton (M.ErrorFail (show el ++ ": " ++ T.unpack msg)))
