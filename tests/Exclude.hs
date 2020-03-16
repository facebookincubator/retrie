-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE LambdaCase #-}

module Exclude (excludeTest) where

import Data.List (isPrefixOf, stripPrefix)
import Retrie
import Retrie.Options
import System.FilePath
import Test.HUnit
import Util

excludedPaths :: [FilePath]
excludedPaths = ["foo", "bar/ignore"]

allFiles :: [FilePath]
allFiles =
  [ "foo/Foo.hs"
  , "foo/bar/Foobar.hs"
  , "bar/Bar.hs"
  , "bar/foo/Baz.hs"
  , "bar/ignore/Ignore.hs"
  ]

excludeTest :: Verbosity -> Test
excludeTest v = TestLabel "exclude path prefixes" $
  TestCase $ do
    withFakeHgRepo [] allFiles $ \dir -> do
      let opts = optionsWithExtraIgnores dir v
      filepaths <- getTargetFiles opts []
      assertBool (unlines ["Expected ", show excludedPaths,
        "to be excluded, these were included : ", show filepaths])
        $ excludedPathsAreExcluded filepaths

      let relfilepaths = map (stripPrefix $ addTrailingPathSeparator dir)
                         filepaths
      assertBool (unlines ["Expected ", show includedPaths,
        " to be included, these were included: ", show relfilepaths])
        $ nonExcludedPathsAreIncluded relfilepaths

optionsWithExtraIgnores :: FilePath -> Verbosity -> Options
optionsWithExtraIgnores target v = (defaultOptions target)
  { extraIgnores = excludedPaths
  , verbosity = v
  }

-- Check that filepaths with prefixes in the excluded list are excluded
excludedPathsAreExcluded :: [FilePath] -> Bool
excludedPathsAreExcluded = all notPrefixOfAllExcluded

-- Check that filepaths without prefixes in the excluded list are not excluded
nonExcludedPathsAreIncluded :: [Maybe FilePath] -> Bool
nonExcludedPathsAreIncluded results = all (\case
      Nothing -> False
      Just relpath -> relpath `elem` includedPaths) results
    && length results == length includedPaths

includedPaths :: [FilePath]
includedPaths = filter notPrefixOfAllExcluded allFiles

-- Returns True if a filepath starts with an excluded prefix
notPrefixOfAllExcluded :: FilePath -> Bool
notPrefixOfAllExcluded file = all (\p -> not $ isPrefixOf p file) excludedPaths
