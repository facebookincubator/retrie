-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE RecordWildCards #-}
module AllTests (allTests) where

import Data.Maybe
import Fixity
import Retrie
import Retrie.Options
import System.Environment
import System.FilePath
import Test.HUnit

import Annotated
import CPP
import qualified Demo
import Dependent
import Exclude
import Golden
import GroundTerms
import Ignore
import ParseQualified
import Targets

allTests :: Verbosity -> IO Test
allTests rtVerbosity = do
  p <- getOptionsParser defaultFixityEnv
  rtDir <-
    fromMaybe (dropFileName __FILE__ </> "inputs")
      <$> lookupEnv "RETRIEINPUTSDIR"
  testFiles <- listDir rtDir
  focusTests <- getFocusTests
  return $ TestList
    [ annotatedTest
    , cppTest
    , dependentStmtTest rtDir p rtVerbosity
    , excludeTest rtVerbosity
    , TestLabel "golden" $ TestList
      [ TestLabel rtName $ TestCase $ runTest p RetrieTest{..}
      | testFile <- testFiles
      , takeExtension testFile == ".test"
      , let
          rtName = dropExtension testFile
          rtTest = testFile
          rtRetrie = return . apply . rewrites
      ]
    , TestLabel "custom Retrie" $ TestCase $
        runTest p RetrieTest
          { rtName = "custom Retrie"
          , rtTest = "Adhoc2.custom"
          , rtRetrie = \opts -> do
              rrs' <- parseRewrites opts
                [ Adhoc "forall f g xs. map f (map g xs) = map (f . g) xs"
                , Adhoc "forall p xs. length (filter p xs) = count p xs"
                ]
              return $ apply $ rewrites opts <> rrs'
          , ..
          }
    , TestLabel "README advanced rewrite demo" $ TestCase $
        runTest p RetrieTest
          { rtName = "README advanced rewrite demo"
          , rtTest = "Readme.custom"
          , rtRetrie = \opts -> do
              [rewrite] <-
                parseRewrites opts [Adhoc "forall arg. fooOld arg = fooNew arg"]
              return $ apply [setRewriteTransformer Demo.stringToFooArg rewrite]
          , ..
          }
    , TestLabel "query test" $ TestCase $ do
        is <- runQueryTest p RetrieTest
          { rtName = "query test"
          , rtTest = "Query.custom"
          , rtRetrie = \opts -> do
              qs <- parseQueries opts [(["x"], QExpr "succ x", 1::Int)]
              return $ do
                matches <- query qs
                return [ v | (_,_,v) <- matches ]
          , ..
          }
        assertEqual "found three succs" 3 (sum is)
    , TestLabel "groundterms can be found" $ TestList focusTests
    , groundTermsTest
    , ignoreTest
    , parseQualifiedTest
    , basicTargetTest
    , targetedWithGroundTerms
    ]
