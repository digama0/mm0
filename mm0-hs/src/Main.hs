module Main (main) where

import System.Exit
import System.Environment
import Driver
import FromMM
import ToHolIO
import Compiler
import Server

main :: IO ()
main = getArgs >>= \case
  "verify" : rest -> verifyIO rest
  "show-bundled" : rest -> showBundled rest
  "from-mm" : rest -> fromMM rest
  "to-hol" : rest -> toHolIO rest
  "to-othy" : rest -> toOpenTheory rest
  "to-lean" : rest -> toLean rest
  "server" : rest -> server rest
  "compile" : rest -> compile rest
  _ -> die $ "incorrect args; use\n" ++
    "  mm0-hs verify MM0-FILE MMU-FILE\n" ++
    "  mm0-hs show-bundled MM-FILE\n" ++
    "  mm0-hs from-mm MM-FILE [-o MM0-FILE MMU-FILE]\n" ++
    "  mm0-hs to-hol MM0-FILE MMU-FILE\n" ++
    "  mm0-hs to-othy MM0-FILE MMU-FILE [-o ART-FILE]\n" ++
    "  mm0-hs to-lean MM0-FILE MMU-FILE [-o LEAN-FILE]\n" ++
    "  mm0-hs server [--debug]\n" ++
    "  mm0-hs compile [MM0/1-FILE]\n"
