module Compiler where

import System.IO
import System.Exit
import qualified Data.Text.IO as T
import Text.Megaparsec (errorBundlePretty)
import CParser

compile :: [String] -> IO ()
compile args = do
  (name, mm0) <- case args of
    [] -> return ("", stdin)
    (mm0:r) -> (,) mm0 <$> openFile mm0 ReadMode
  str <- T.hGetContents mm0
  case parseAST name str of
    Left (err, _) -> die (errorBundlePretty err)
    Right _ -> putStrLn "OK"
