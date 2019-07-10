module Compiler where

import System.IO
import System.Exit
import qualified Data.Text.IO as T
import Data.List.NonEmpty (NonEmpty(..))
import Text.Megaparsec (ParseErrorBundle(..), errorBundlePretty)
import CParser

compile :: [String] -> IO ()
compile args = do
  (name, mm0) <- case args of
    [] -> return ("", stdin)
    (mm0:r) -> (,) mm0 <$> openFile mm0 ReadMode
  str <- T.hGetContents mm0
  case parseAST name str of
    (e : es, _, _) -> do
      let errs = ParseErrorBundle (e :| es) (initialPosState name str)
      die (errorBundlePretty errs)
    ([], _, Just _) -> putStrLn "OK"
