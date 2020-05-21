-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE CPP #-}
{-# LANGUAGE RecordWildCards #-}
module Retrie.GHC
  ( module Retrie.GHC
  , module ApiAnnotation
  , module Bag
  , module BasicTypes
  , module FastString
  , module FastStringEnv
#if __GLASGOW_HASKELL__ < 810
  , module HsExpr
  , module HsSyn
#else
  , module ErrUtils
  , module GHC.Hs.Expr
  , module GHC.Hs
#endif
  , module Module
  , module Name
  , module OccName
  , module RdrName
  , module SrcLoc
  , module Unique
  , module UniqFM
  , module UniqSet
  ) where

import ApiAnnotation
import Bag
import BasicTypes
import FastString
import FastStringEnv
#if __GLASGOW_HASKELL__ < 810
import HsExpr
#if __GLASGOW_HASKELL__ < 806
import HsSyn hiding (HasDefault(..))
#else
import HsSyn
#endif
#else
import ErrUtils
import GHC.Hs.Expr
import GHC.Hs
#endif
import Module
import Name
import OccName
import RdrName
import SrcLoc
import Unique
import UniqFM
import UniqSet

import Data.Bifunctor (second)
import Data.Maybe

rdrFS :: RdrName -> FastString
rdrFS (Qual m n) = mconcat [moduleNameFS m, fsDot, occNameFS n]
rdrFS rdr = occNameFS (occName rdr)

fsDot :: FastString
fsDot = mkFastString "."

varRdrName :: HsExpr p -> Maybe (Located (IdP p))
#if __GLASGOW_HASKELL__ < 806
varRdrName (HsVar n) = Just n
#else
varRdrName (HsVar _ n) = Just n
#endif
varRdrName _ = Nothing

tyvarRdrName :: HsType p -> Maybe (Located (IdP p))
#if __GLASGOW_HASKELL__ < 806
tyvarRdrName (HsTyVar _ n) = Just n
#else
tyvarRdrName (HsTyVar _ _ n) = Just n
#endif
tyvarRdrName _ = Nothing

fixityDecls :: HsModule p -> [(Located (IdP p), Fixity)]
fixityDecls m =
  [ (nm, fixity)
#if __GLASGOW_HASKELL__ < 806
  | L _ (SigD (FixSig (FixitySig nms fixity))) <- hsmodDecls m
#else
  | L _ (SigD _ (FixSig _ (FixitySig _ nms fixity))) <- hsmodDecls m
#endif
  , nm <- nms
  ]

ruleInfo :: RuleDecl GhcPs -> [RuleInfo]
#if __GLASGOW_HASKELL__ < 808

#if __GLASGOW_HASKELL__ < 806
ruleInfo (HsRule (L _ (_, riName)) _ bs riLHS _ riRHS _) =
#else
ruleInfo XRuleDecl{} = []
ruleInfo (HsRule _ (L _ (_, riName)) _ bs riLHS riRHS) =
#endif
  [ RuleInfo { riQuantifiers = ruleBindersToQs bs, .. } ]

#else
ruleInfo (HsRule _ (L _ (_, riName)) _ tyBs valBs riLHS riRHS) =
  let
    riQuantifiers =
      map unLoc (tyBindersToLocatedRdrNames (fromMaybe [] tyBs)) ++
      ruleBindersToQs valBs
  in [ RuleInfo{..} ]
ruleInfo XRuleDecl{} = []
#endif

ruleBindersToQs :: [LRuleBndr GhcPs] -> [RdrName]
ruleBindersToQs bs = catMaybes
  [ case b of
#if __GLASGOW_HASKELL__ < 806
      RuleBndr (L _ v) -> Just v
      RuleBndrSig (L _ v) _ -> Just v
#else
      RuleBndr _ (L _ v) -> Just v
      RuleBndrSig _ (L _ v) _ -> Just v
      XRuleBndr{} -> Nothing
#endif
  | L _ b <- bs
  ]

tyBindersToLocatedRdrNames :: [LHsTyVarBndr GhcPs] -> [Located RdrName]
tyBindersToLocatedRdrNames vars = catMaybes
  [ case var of
#if __GLASGOW_HASKELL__ < 806
      UserTyVar v -> Just v
      KindedTyVar v _ -> Just v
#else
      UserTyVar _ v -> Just v
      KindedTyVar _ v _ -> Just v
      XTyVarBndr{} -> Nothing
#endif
  | L _ var <- vars ]

data RuleInfo = RuleInfo
  { riName :: RuleName
  , riQuantifiers :: [RdrName]
  , riLHS :: LHsExpr GhcPs
  , riRHS :: LHsExpr GhcPs
  }

#if __GLASGOW_HASKELL__ < 806
#elif __GLASGOW_HASKELL__ < 810
noExtField :: NoExt
noExtField = noExt
#endif

overlaps :: SrcSpan -> SrcSpan -> Bool
overlaps (RealSrcSpan s1) (RealSrcSpan s2) =
     srcSpanFile s1 == srcSpanFile s2 &&
     ((srcSpanStartLine s1, srcSpanStartCol s1) `within` s2 ||
      (srcSpanEndLine s1, srcSpanEndCol s1) `within` s2)
overlaps _ _ = False

within :: (Int, Int) -> RealSrcSpan -> Bool
within (l,p) s =
  srcSpanStartLine s <= l &&
  srcSpanStartCol s <= p  &&
  srcSpanEndLine s >= l   &&
  srcSpanEndCol s >= p

lineCount :: [SrcSpan] -> Int
lineCount ss = sum
  [ srcSpanEndLine s - srcSpanStartLine s + 1
  | RealSrcSpan s <- ss
  ]

showRdrs :: [RdrName] -> String
showRdrs = show . map (occNameString . occName)

uniqBag :: Uniquable a => [(a,b)] -> UniqFM [b]
uniqBag = listToUFM_C (++) . map (second pure)
