module Test.Compiler where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Text as T
import MM0.Compiler.Env

compilerTests :: TestTree
compilerTests = testGroup "Compiler" [alphanumberTests]

alphanumberTests :: TestTree
alphanumberTests = testGroup "alphanumber" $
  map (\(a, b) -> testCase (show a ++ " -> " ++ T.unpack b) $ alphanumber a @?= b) $
    [(0, "a"), (1, "b"), (25, "z"), (26, "aa"), (26*2-1, "az"),
     (26*2, "ba"), (26*27-1, "zz"), (26*27, "aaa"), (26*27+1, "aab")]
