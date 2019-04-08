module FromMM where

import System.IO
import System.Exit
import System.Environment
import qualified Data.ByteString.Lazy as B
import qualified Data.Map.Strict as M
import Util
import MMTypes
import MMParser

fromMM :: [String] -> IO ()
fromMM [] = die "from-mm: no .mm file specified"
fromMM (mm:rest) = do
  s <- openFile mm ReadMode >>= B.hGetContents
  st <- liftIO (parseMM s)
  putStrLn $ show (M.size (mStmts st)) ++ " statements"
  putStrLn $ show (mSorts st)
  putStrLn $ show (mPrim st)
