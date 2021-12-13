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

allTests :: LibDir -> Verbosity -> IO Test
allTests libdir rtVerbosity = do
  p <- getOptionsParser defaultFixityEnv
  rtDir <-
    fromMaybe (dropFileName __FILE__ </> "inputs")
      <$> lookupEnv "RETRIEINPUTSDIR"
  testFiles <- listDir rtDir
  focusTests <- getFocusTests libdir
  return $ TestList
    [ annotatedTest
    , cppTest
    , dependentStmtTest libdir rtDir p rtVerbosity
    , excludeTest rtVerbosity
    , TestLabel "golden" $ TestList
      [ TestLabel rtName $ TestCase $ runTest libdir p RetrieTest{..}
      | testFile <- testFiles
      , takeExtension testFile == ".test"
      , let
          rtName = dropExtension testFile
          rtTest = testFile
          rtRetrie = return . apply . rewrites
      ]
    , TestLabel "custom Retrie" $ TestCase $
        runTest libdir p RetrieTest
          { rtName = "custom Retrie"
          , rtTest = "Adhoc2.custom"
          , rtRetrie = \opts -> do
              rrs' <- parseRewrites libdir opts
                [ Adhoc "forall f g xs. map f (map g xs) = map (f . g) xs"
                , Adhoc "forall p xs. length (filter p xs) = count p xs"
                ]
              return $ apply $ rewrites opts <> rrs'
          , ..
          }
    , TestLabel "README advanced rewrite demo" $ TestCase $
        runTest libdir p RetrieTest
          { rtName = "README advanced rewrite demo"
          , rtTest = "Readme.custom"
          , rtRetrie = \opts -> do
              [rewrite] <-
                parseRewrites libdir opts [Adhoc "forall arg. fooOld arg = fooNew arg"]
              return $ apply [setRewriteTransformer (Demo.stringToFooArg libdir) rewrite]
          , ..
          }
    , TestLabel "query test" $ TestCase $ do
        is <- runQueryTest libdir p RetrieTest
          { rtName = "query test"
          , rtTest = "Query.custom"
          , rtRetrie = \opts -> do
              qs <- parseQueries libdir opts [(["x"], QExpr "succ x", 1::Int)]
              return $ do
                matches <- query qs
                return [ v | (_,_,v) <- matches ]
          , ..
          }
        assertEqual "found three succs" 3 (sum is)
    , TestLabel "groundterms can be found" $ TestList focusTests
    , groundTermsTest libdir
    , ignoreTest
    , parseQualifiedTest
    , basicTargetTest
    , targetedWithGroundTerms
    ]
