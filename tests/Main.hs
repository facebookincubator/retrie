-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
module Main (main) where

import Test.HUnit
import Test.Tasty
import Test.Tasty.HUnit

import qualified GHC.Paths as GHC.Paths
import Retrie
import AllTests

main :: IO ()
main = allTests GHC.Paths.libdir Silent >>= defaultMain . toTasty . TestLabel "retrie"

toTasty :: Test -> TestTree
toTasty (TestLabel lbl (TestCase io)) = testCase lbl io
toTasty (TestLabel lbl (TestList ts)) = testGroup lbl (map toTasty ts)
toTasty t = error $ "toTasty: unlabeled test " ++ show t
