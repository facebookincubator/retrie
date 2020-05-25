-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
module Targets
  ( basicTargetTest
  , targetedWithGroundTerms
  ) where

import qualified Data.HashSet as HashSet
import Data.List
import Fixity
import Retrie.GroundTerms
import Retrie.Options
import System.FilePath
import Test.HUnit
import Util

basicTargetTest :: Test
basicTargetTest = TestLabel "Target files without ground terms specified" $
  TestCase $ assertFileListEqual retrieTargetFiles [] retrieTargetFiles

targetedWithGroundTerms :: Test
targetedWithGroundTerms =
  TestLabel "Should filter to subset of target files with ground terms" $
  TestCase $ assertFileListEqual expectedFps gts targetFps
    where
      gts = [HashSet.fromList ["Groundterm"]]
      targetFps = retrieTargetFiles
      -- 'withFakeHgRepo' creates every file with its own name as the contents
      expectedFps = ["targeted/Groundterm.hs"]

assertFileListEqual
  :: [FilePath]
  -> [GroundTerms]
  -> [FilePath]
  -> Assertion
assertFileListEqual expected gts targetFps =
  withFakeHgRepo [] allFiles $ \dir -> do
    let opts = optionsWithTargetFiles dir targetFps
    filepaths <- getTargetFiles opts gts
    assertPermutationOf "Targeted files should be all of those specified"
      (map (dir </>) expected) filepaths
  where
    assertPermutationOf m as bs = assertEqual m (sort as) (sort bs)

retrieTargetFiles :: [FilePath]
retrieTargetFiles =
  [ "targeted/File.hs"
  , "targeted/Nested/File.hs"
  , "targeted/Groundterm.hs"
  ]

allFiles :: [FilePath]
allFiles =
  [ "foo/Foo.hs"
  , "foo/bar/Foobar.hs"
  , "bar/Bar.hs"
  , "bar/foo/Baz.hs"
  , "bar/ignore/Ignore.hs"
  , "targeted/File.c"
  ] ++ retrieTargetFiles

optionsWithTargetFiles :: FilePath -> [FilePath] -> Options
optionsWithTargetFiles dir targets = (defaultOptions dir)
  { targetFiles = map (dir </>) targets }
