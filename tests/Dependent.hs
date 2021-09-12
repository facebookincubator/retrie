-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE RecordWildCards #-}
module Dependent where

import Options.Applicative
import Test.HUnit

import Golden
import Retrie
import Retrie.Options

dependentStmtTest :: LibDir -> FilePath -> Parser ProtoOptions -> Verbosity -> Test
dependentStmtTest libdir rtDir p rtVerbosity =
  TestLabel "dependent stmt" $ TestCase $
    runTest libdir p RetrieTest
      { rtName = "dependent stmt"
      , rtTest = "DependentStmt.custom"
      , rtRetrie = \opts -> do
          rrs <- parseRewrites libdir opts [ Adhoc "forall x. foo x = baz x" ]
          stmt <- parseStmt libdir "y <- bar 54"
          let
            rr = toURewrite $
              Query emptyQs stmt
                (Template stmt mempty (Just rrs), defaultTransformer)

          return $ apply [rr]
      , rtVerbosity = Loud
      , ..
      }
