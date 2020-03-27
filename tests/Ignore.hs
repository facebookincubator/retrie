-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
module Ignore (ignoreTest) where

import Retrie.Util
import System.FilePath
import Test.HUnit
import Util

allFiles :: [FilePath]
allFiles = [ c:".hs" | c <- ['A'..'F'] ] ++
  [ "ignored-folder/A.thrift"
  , "ignored-folder/subfolder/Ctest.hs"
  , "ignored-folder/subfolder/subfolder2/Btest.hs"
  ]

ignoredFiles :: [FilePath]
ignoredFiles = ["B.hs", "C.hs", "ignored-folder/"]

ignoreTest :: Test
ignoreTest = TestLabel "ignore" $ TestList
  [ hgTest
  , gitTest
  , unifiedTest1
  , unifiedTest2
  ]

assertStuff :: FilePath -> Maybe (FilePath -> Bool) -> IO ()
assertStuff _ Nothing = assertFailure "pred was Nothing"
assertStuff repo (Just p) = do
  assertBool "B.hs ignored" $ p $ repo </> "B.hs"
  assertBool "C.hs ignored" $ p $ repo </> "C.hs"
  assertBool "A.hs not ignored" $ not $ p $ repo </> "A.hs"
  assertBool "Foo.hs not ignored" $ not $ p $ repo </> "Foo.hs"
  assertBool "subfolder ignored" $
    p $ repo </> "ignored-folder/subfolder/Ctest.hs"
  assertBool "deep subfolder ignored" $
    p $ repo </> "ignored-folder/subfolder/subfolder2/Btest.hs"

hgTest :: Test
hgTest = TestLabel "hg ignore" $ TestCase $
  withFakeHgRepo ignoredFiles allFiles $ \repo -> do
    maybePredicate <- hgIgnorePred Loud repo
    assertStuff repo maybePredicate
    case maybePredicate of
      Just p ->
        assertBool "subfolder non-hs file not ignored" $
          not $ p $ repo </> "ignored-folder/A.thrift"
      Nothing -> assertFailure "pred was Nothing"

gitTest :: Test
gitTest = TestLabel "git ignore" $ TestCase $
  withFakeGitRepo ignoredFiles allFiles $ \repo ->
    gitIgnorePred Loud repo >>= assertStuff repo

unifiedTest1 :: Test
unifiedTest1 = TestLabel "vcs ignore on git repo" $ TestCase $
  withFakeGitRepo ignoredFiles allFiles $ \repo ->
    vcsIgnorePred Loud repo >>= assertStuff repo

unifiedTest2 :: Test
unifiedTest2 = TestLabel "vcs ignore on hg repo" $ TestCase $
  withFakeHgRepo ignoredFiles allFiles $ \repo ->
    vcsIgnorePred Loud repo >>= assertStuff repo
