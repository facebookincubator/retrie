-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
module Retrie.GroundTerms
  ( GroundTerms
  , groundTerms
  ) where

import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet

import Retrie.ExactPrint
import Retrie.GHC
import Retrie.Quantifiers
import Retrie.SYB
import Retrie.Types

------------------------------------------------------------------------

-- | 'Ground Terms' are variables in the pattern that are not quantifiers.
-- We use a set of ground terms to save time during matching by filtering out
-- files which do not contain all the terms. We store one set of terms per
-- pattern because when filtering we must take care to only filter files which
-- do not match any of the patterns.
--
-- Example:
--
-- Patterns of 'forall x. foo (bar x) = ...' and 'forall y. baz (quux y) = ...'
--
-- groundTerms = [{'foo', 'bar'}, {'baz', 'quux'}]
--
-- Files will be found by unioning results of these commands:
--
-- grep -R --include "*.hs" -l foo dir | xargs grep -l bar
-- grep -R --include "*.hs" -l baz dir | xargs grep -l quux
--
-- If there are no ground terms (e.g. 'forall f x y. f x y = f y x')
-- we fall back to 'find dir -iname "*.hs"'. This case seems pathological.
type GroundTerms = HashSet String

groundTerms :: Data k => Query k v -> GroundTerms
groundTerms Query{..} = HashSet.fromList $ go $ astA qPattern
  where
    go :: GenericQ [String]
    go x
      -- 'x' contains a quantifier, so split it into subtrees
      | everything (||) isQuantifier x = concat $ gmapQ go x
      -- 'x' doesn't contain a quantifier, and can be exactprinted, so return
      -- the result of exactprinting
      | strs@(_:_) <- printer x = strs
      -- 'x' cannot be exactprinted, so recurse to find a printable child
      | otherwise = concat $ gmapQ go x

    isQuantifier :: GenericQ Bool
    isQuantifier = mkQ False exprIsQ `extQ` tyIsQ

    -- returns 'True' if expression is a var that is a quantifier
    exprIsQ :: HsExpr GhcPs -> Bool
    exprIsQ e | Just (L _ v) <- varRdrName e = isQ v qQuantifiers
    exprIsQ _ = False

    -- returns 'True' if type is a tyvar that is a quantifier
    tyIsQ :: HsType GhcPs -> Bool
    tyIsQ ty | Just (L _ v) <- tyvarRdrName ty = isQ v qQuantifiers
    tyIsQ _ = False

    -- exactprinter that only works for expressions and types
    printer :: GenericQ [String]
    printer = mkQ [] printExpr `extQ` printTy

    printExpr :: LHsExpr GhcPs -> [String]
    printExpr e = [exactPrint (setEntryDP e (SameLine 0))]

    printTy :: LHsType GhcPs -> [String]
    printTy t = [exactPrint (setEntryDP t (SameLine 0))]
