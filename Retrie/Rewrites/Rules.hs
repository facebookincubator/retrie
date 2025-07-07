-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE CPP #-}
{-# LANGUAGE RecordWildCards #-}
module Retrie.Rewrites.Rules (rulesToRewrites) where

import Data.Generics
import Data.Maybe

import Retrie.ExactPrint
import Retrie.GHC
import Retrie.Quantifiers
import Retrie.Types

rulesToRewrites
  :: [(FastString, Direction)]
  -> AnnotatedModule
#if __GLASGOW_HASKELL__ < 900
  -> IO (UniqFM [Rewrite (LHsExpr GhcPs)])
#else
  -> IO (UniqFM RuleName [Rewrite (LHsExpr GhcPs)])
#endif
rulesToRewrites specs am = fmap astA $ transformA am $ \ m -> do
  let
    fsMap = uniqBag specs

  uniqBag <$> sequence
    [ mkRuleRewrite dir info
    | info@RuleInfo{..} <- everything (++) (mkQ [] ruleInfo) m
    , dir <- fromMaybe [] (lookupUFM fsMap riName)
    ]

------------------------------------------------------------------------

mkRuleRewrite
  :: Direction
  -> RuleInfo
  -> TransformT IO (RuleName, Rewrite (LHsExpr GhcPs))
mkRuleRewrite RightToLeft (RuleInfo name qs lhs rhs) =
  mkRuleRewrite LeftToRight (RuleInfo name qs rhs lhs)
mkRuleRewrite _ RuleInfo{..} = do
  p <- pruneA (setEntryDP (makeDeltaAst riLHS) (SameLine 1))
  p <- pruneA riLHS
  t <- pruneA (setEntryDP (makeDeltaAst riRHS) (SameLine 1))
  -- lift $ debugPrint Loud "mkRuleRewrite:p,t" [showAstA p, showAstA t]
  -- lift $ debugPrint Loud "mkRuleRewrite:riQuantifiers" [showGhc riQuantifiers]
  return (riName, mkRewrite (mkQs riQuantifiers) p (getHasLoc p) t)
