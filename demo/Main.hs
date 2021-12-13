-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE OverloadedStrings #-}
module Main where

import qualified GHC.Paths as GHC.Paths
import Retrie

-- | A script for rewriting calls to a function that takes a string to be
-- calls to a new function that takes an enumeration. See the README for
-- details. Running this would result in the following diff:
--
--  module MyModule where
--
--  baz, bar, quux :: IO ()
-- -baz = fooOld "foo"
-- +baz = fooNew Foo
-- -bar = fooOld "bar"
-- +bar = fooNew Bar
-- -quux = fooOld "quux"
-- +quux = fooNew (error "invalid argument: quux")
--

main :: IO ()
main = runScript GHC.Paths.libdir $ \opts -> do
  [rewrite] <- parseRewrites GHC.Paths.libdir opts [Adhoc "forall arg. fooOld arg = fooNew arg"]
  return $ apply [setRewriteTransformer stringToFooArg rewrite]

argMapping :: [(FastString, String)]
argMapping = [("foo", "Foo"), ("bar", "Bar")]

-- | This 'transform' receives the result of matching the left-hand side of the
-- equation. The returned 'MatchResult' is used to instantiate the right-hand
-- side of the equation. In this example we are just modifying the
-- substitution, but you can also modify the template, which contains the
-- right-hand side itself.
stringToFooArg :: MatchResultTransformer
stringToFooArg _ctxt match
  | MatchResult substitution template <- match
  , Just (HoleExpr expr) <- lookupSubst "arg" substitution
  , L _ (HsLit _ (HsString _ str)) <- astA expr = do
    newExpr <- case lookup str argMapping of
      Nothing ->
        parseExpr GHC.Paths.libdir $ "error \"invalid argument: " ++ unpackFS str ++ "\""
      Just constructor -> parseExpr GHC.Paths.libdir constructor
    return $
      MatchResult (extendSubst substitution "arg" (HoleExpr newExpr)) template
  | otherwise = return NoMatch
