module FromMM where

import System.Exit
import qualified Data.ByteString.Lazy as B
import Util

fromMM :: [String] -> IO ()
fromMM [] = die "from-mm: no .mm file specified"
fromMM (mm:rest) = do
  ast <- openFile mm ReadMode >>= B.hGetContents >>= parseMM

parseMM :: String -> Either String AST
