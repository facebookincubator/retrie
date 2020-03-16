-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
module Demo (stringToFooArg) where

import Retrie

argMapping :: [(FastString, String)]
argMapping = [("foo", "Foo"), ("bar", "Bar")]

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
