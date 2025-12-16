module MM0.Compiler where

import Control.Monad
import System.IO
import System.Exit
import Data.List
import Data.Maybe
import Data.Default
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
  (strip, mmb, rest1) <- return $ case args of
    "-S" : "-o" : mmb : rest1 -> (True, Just mmb, rest1)
    "-o" : mmb : rest1 -> (False, Just mmb, rest1)
    rest1 -> (False, Nothing, rest1)
  (isMM0, rest2) <- return $ case rest1 of
    "--mm0" : rest2 -> (Just True, rest2)
    "--mm1" : rest2 -> (Just False, rest2)
    rest2 -> (Nothing, rest2)
  (par, rest3) <- return $ case rest2 of
    "-j1" : rest3 -> (False, rest3)
    rest3 -> (True, rest3)
  (name, mm0) <- case rest3 of
    [] -> return ("", stdin)
    (mm0:_) -> (,) mm0 <$> openFile mm0 ReadMode
  let isMM0' = fromMaybe ("mm0" `isSuffixOf` name) isMM0
  str <- T.hGetContents mm0
  let (errs, _, ast) = parseAST name str
      cfg n = ElabConfig isMM0' par False name (load n)
      load 4 = \_ -> die "depth limit exceeded"
      load n = elabLoad (cfg (n+1))
  elaborate (cfg (0::Int)) (toElabError def name <$> errs) ast >>= \case
    (errs2, env) -> do
      unless (null errs2) $ do
        let errs' = M.ParseErrorBundle
              (NE.fromList (sortOn M.errorOffset (toParseError <$> errs2)))
              (initialPosState name str)
        hPutStrLn stderr (M.errorBundlePretty errs')
      when (any (\e -> eeLevel e == ELError) errs2) exitFailure
      forM_ mmb $ flip (export strip) env

toParseError :: ElabError -> ParseError
toParseError (ElabError el (_, (o, _)) _ msg _) =
  M.FancyError o $ S.singleton $ M.ErrorFail (show el ++ ": " ++ T.unpack msg)
