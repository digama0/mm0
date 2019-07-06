module Compiler where

import System.IO
import qualified Data.Text.IO as T
import Text.Megaparsec (errorBundlePretty)
import CParser

compile :: [String] -> IO ()
compile args = do
  mm0 <- case args of
    [] -> return stdin
    (mm0:r) -> openFile mm0 ReadMode
  str <- T.hGetContents mm0
  case parseAST str of
    Left (err, _) -> hPutStr stderr (errorBundlePretty err)
    Right _ -> putStrLn "OK"
