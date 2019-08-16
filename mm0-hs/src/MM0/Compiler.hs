module MM0.Compiler where

import Control.Monad
import System.IO
import System.Exit
import Data.List
import Data.Maybe
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.List.NonEmpty as NE
import qualified Text.Megaparsec as M
import qualified Data.Set as S
import MM0.Compiler.Parser
import MM0.Compiler.Elaborator
import MM0.Compiler.Export

compile :: [String] -> IO ()
compile args = do
  (isMM0, rest) <- return $ case args of
    "--mm0" : rest -> (Just True, rest)
    "--mm1" : rest -> (Just False, rest)
    rest -> (Nothing, rest)
  (mmb, rest') <- return $ case rest of
    "-o" : mmb : rest' -> (Just mmb, rest')
    rest' -> (Nothing, rest')
  (name, mm0) <- case rest' of
    [] -> return ("", stdin)
    (mm0:_) -> (,) mm0 <$> openFile mm0 ReadMode
  let isMM0' = fromMaybe (isSuffixOf "mm0" name) isMM0
  str <- T.hGetContents mm0
  case parseAST name str of
    (errs, _, Nothing) -> do
      let errs' = M.ParseErrorBundle (NE.fromList errs) (initialPosState name str)
      die (M.errorBundlePretty errs')
    (errs, _, Just ast) -> elaborate isMM0' errs ast >>= \case
      (errs2, env) -> do
        unless (null errs2) $ do
          let errs' = M.ParseErrorBundle
                (NE.fromList (sortOn M.errorOffset (toParseError <$> errs2)))
                (initialPosState name str)
          hPutStrLn stderr (M.errorBundlePretty errs')
        when (all (\e -> eeLevel e /= ELError) errs2) $ do
          forM_ mmb $ flip export env

toParseError :: ElabError -> ParseError
toParseError (ElabError el (o, _) msg _) =
  M.FancyError o (S.singleton (M.ErrorFail (show el ++ ": " ++ T.unpack msg)))
