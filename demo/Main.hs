-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Retrie
import Fixity

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
main = runScript $ \opts -> do
  [rewrite] <- parseRewrites opts{fixityEnv=defaultFixityEnv} [Adhoc "forall arg. fooOld arg = fooNew arg"]
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
#if __GLASGOW_HASKELL__ < 806
  , L _ (HsLit (HsString _ str)) <- astA expr = do
#else
  , L _ (HsLit _ (HsString _ str)) <- astA expr = do
#endif
    newExpr <- case lookup str argMapping of
      Nothing ->
        parseExpr $ "error \"invalid argument: " ++ unpackFS str ++ "\""
      Just constructor -> parseExpr constructor
    return $
      MatchResult (extendSubst substitution "arg" (HoleExpr newExpr)) template
  | otherwise = return NoMatch
