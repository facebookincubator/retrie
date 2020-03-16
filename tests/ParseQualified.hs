-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
module ParseQualified (parseQualifiedTest) where

import Retrie
import Retrie.Rewrites
import System.FilePath
import Test.HUnit

parseQualifiedTest :: Test
parseQualifiedTest = TestLabel "parseQualified" $ TestCase $ do
  assertEqual "parseQualified1"
    (parseQualified "My.Thing.foo")
    (mkRight "My.Thing" "foo")
  assertEqual "parseQualified2"
    (parseQualified "foo")
    (Left "unqualified function name: foo")
  assertEqual "parseQualified3"
    (parseQualified "My.<>")
    (mkRight "My" "<>")
  assertEqual "parseQualified4"
    (parseQualified "My.CategoryLibrary..")
    (mkRight "My.CategoryLibrary" ".")
  assertEqual "parseQualified5"
    (parseQualified "My.Strange.Operators..<.>.")
    (mkRight "My.Strange.Operators" ".<.>.")
  assertEqual "parseQualified6"
    (parseQualified "<|>")
    (Left "unqualified operator name: <|>")
  assertEqual "parseQualified7"
    (parseQualified "Bad.ModName:<>")
    (Left "malformed qualified operator: Bad.ModName:<>")
  where
    mkRight x y = Right
      (moduleNameSlashes (mkModuleName x) <.> "hs", mkFastString y)
