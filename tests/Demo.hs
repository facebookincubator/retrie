-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE OverloadedStrings #-}
module Demo (stringToFooArg) where

import Retrie

argMapping :: [(FastString, String)]
argMapping = [("foo", "Foo"), ("bar", "Bar")]

stringToFooArg :: LibDir -> MatchResultTransformer
stringToFooArg libdir _ctxt match
  | MatchResult substitution template <- match
  , Just (HoleExpr expr) <- lookupSubst "arg" substitution
  , L _ (HsLit _ (HsString _ str)) <- astA expr = do
    newExpr <- case lookup str argMapping of
      Nothing ->
        parseExpr libdir $ "error \"invalid argument: " ++ unpackFS str ++ "\""
      Just constructor -> parseExpr libdir constructor
    return $
      MatchResult (extendSubst substitution "arg" (HoleExpr newExpr)) template
  | otherwise = return NoMatch
