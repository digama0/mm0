module FromMM where

import System.IO
import System.Exit
import System.Environment
import qualified Data.ByteString.Lazy as B
import Util

fromMM :: [String] -> IO ()
fromMM [] = die "from-mm: no .mm file specified"
fromMM (mm:rest) = do
  s <- openFile mm ReadMode >>= B.hGetContents
  putStrLn "unimplemented"
