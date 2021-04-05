-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE CPP #-}
{-# LANGUAGE RecordWildCards #-}
module Retrie.GHC
  ( module Retrie.GHC
#if __GLASGOW_HASKELL__ < 900
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
#else
  -- GHC >= 9.0
  , module GHC.Data.Bag
  , module GHC.Data.FastString
  , module GHC.Data.FastString.Env
  , module GHC.Utils.Error
  , module GHC.Hs
  , module GHC.Parser.Annotation
  , module GHC.Types.Basic
  , module GHC.Types.Name
  , module GHC.Types.Name.Reader
  , module GHC.Types.SrcLoc
  , module GHC.Types.Unique
  , module GHC.Types.Unique.FM
  , module GHC.Types.Unique.Set
  , module GHC.Unit
#endif
  ) where

#if __GLASGOW_HASKELL__ < 900
import ApiAnnotation
import Bag
import BasicTypes
import FastString
import FastStringEnv
#if __GLASGOW_HASKELL__ < 810
import HsExpr
import HsSyn hiding (HsModule)
import qualified HsSyn as HS
#else
import ErrUtils
import GHC.Hs.Expr
import GHC.Hs hiding (HsModule)
import qualified GHC.Hs as HS
#endif
import Module
import Name
import OccName
import RdrName
import SrcLoc
import Unique
import UniqFM
import UniqSet
#else
-- GHC >= 9.0
import GHC.Data.Bag
import GHC.Data.FastString
import GHC.Data.FastString.Env
import GHC.Utils.Error
import GHC.Hs
import GHC.Parser.Annotation
import GHC.Types.Basic
import GHC.Types.Name
import GHC.Types.Name.Reader
import GHC.Types.SrcLoc
import GHC.Types.Unique
import GHC.Types.Unique.FM
import GHC.Types.Unique.Set
import GHC.Unit
#endif

import Data.Bifunctor (second)
import Data.Maybe

#if __GLASGOW_HASKELL__ < 900
type HsModule = HS.HsModule GhcPs
#endif

cLPat :: Located (Pat (GhcPass p)) -> LPat (GhcPass p)
#if __GLASGOW_HASKELL__ == 808
cLPat = composeSrcSpan
#else
cLPat = id
#endif

-- | Only returns located pat if there is a genuine location available.
dLPat :: LPat (GhcPass p) -> Maybe (Located (Pat (GhcPass p)))
#if __GLASGOW_HASKELL__ == 808
dLPat (XPat (L s p)) = Just $ L s $ stripSrcSpanPat p
dLPat _ = Nothing
#else
dLPat = Just
#endif

-- | Will always give a location, but it may be noSrcSpan.
dLPatUnsafe :: LPat (GhcPass p) -> Located (Pat (GhcPass p))
#if __GLASGOW_HASKELL__ == 808
dLPatUnsafe = dL
#else
dLPatUnsafe = id
#endif

#if __GLASGOW_HASKELL__ == 808
stripSrcSpanPat :: LPat (GhcPass p) -> Pat (GhcPass p)
stripSrcSpanPat (XPat (L _  p)) = stripSrcSpanPat p
stripSrcSpanPat p = p
#endif

rdrFS :: RdrName -> FastString
rdrFS (Qual m n) = mconcat [moduleNameFS m, fsDot, occNameFS n]
rdrFS rdr = occNameFS (occName rdr)

fsDot :: FastString
fsDot = mkFastString "."

varRdrName :: HsExpr p -> Maybe (Located (IdP p))
varRdrName (HsVar _ n) = Just n
varRdrName _ = Nothing

tyvarRdrName :: HsType p -> Maybe (Located (IdP p))
tyvarRdrName (HsTyVar _ _ n) = Just n
tyvarRdrName _ = Nothing

fixityDecls :: HsModule -> [(Located RdrName, Fixity)]
fixityDecls m =
  [ (nm, fixity)
  | L _ (SigD _ (FixSig _ (FixitySig _ nms fixity))) <- hsmodDecls m
  , nm <- nms
  ]

ruleInfo :: RuleDecl GhcPs -> [RuleInfo]
ruleInfo (HsRule _ (L _ (_, riName)) _ tyBs valBs riLHS riRHS) =
  let
    riQuantifiers =
      map unLoc (tyBindersToLocatedRdrNames (fromMaybe [] tyBs)) ++
      ruleBindersToQs valBs
  in [ RuleInfo{..} ]
#if __GLASGOW_HASKELL__ < 900
ruleInfo XRuleDecl{} = []
#endif

ruleBindersToQs :: [LRuleBndr GhcPs] -> [RdrName]
ruleBindersToQs bs = catMaybes
  [ case b of
      RuleBndr _ (L _ v) -> Just v
      RuleBndrSig _ (L _ v) _ -> Just v
#if __GLASGOW_HASKELL__ < 900
      XRuleBndr{} -> Nothing
#endif
  | L _ b <- bs
  ]

#if __GLASGOW_HASKELL__ < 900
tyBindersToLocatedRdrNames :: [LHsTyVarBndr GhcPs] -> [Located RdrName]
#else
tyBindersToLocatedRdrNames :: [LHsTyVarBndr () GhcPs] -> [Located RdrName]
#endif
tyBindersToLocatedRdrNames vars = catMaybes
  [ case var of
#if __GLASGOW_HASKELL__ < 900
      UserTyVar _ v -> Just v
      KindedTyVar _ v _ -> Just v
      XTyVarBndr{} -> Nothing
#else
      UserTyVar _ _ v -> Just v
      KindedTyVar _ _ v _ -> Just v
#endif
  | L _ var <- vars ]

data RuleInfo = RuleInfo
  { riName :: RuleName
  , riQuantifiers :: [RdrName]
  , riLHS :: LHsExpr GhcPs
  , riRHS :: LHsExpr GhcPs
  }

#if __GLASGOW_HASKELL__ < 810
noExtField :: NoExt
noExtField = noExt
#endif

overlaps :: SrcSpan -> SrcSpan -> Bool
overlaps ss1 ss2
  | Just s1 <- getRealSpan ss1, Just s2 <- getRealSpan ss2 =
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
  | Just s <- map getRealSpan ss
  ]

showRdrs :: [RdrName] -> String
showRdrs = show . map (occNameString . occName)

#if __GLASGOW_HASKELL__ < 900
uniqBag :: Uniquable a => [(a,b)] -> UniqFM [b]
#else
uniqBag :: Uniquable a => [(a,b)] -> UniqFM a [b]
#endif
uniqBag = listToUFM_C (++) . map (second pure)

getRealLoc :: SrcLoc -> Maybe RealSrcLoc
#if __GLASGOW_HASKELL__ < 900
getRealLoc (RealSrcLoc l) = Just l
#else
getRealLoc (RealSrcLoc l _) = Just l
#endif
getRealLoc _ = Nothing

getRealSpan :: SrcSpan -> Maybe RealSrcSpan
#if __GLASGOW_HASKELL__ < 900
getRealSpan (RealSrcSpan s) = Just s
#else
getRealSpan (RealSrcSpan s _) = Just s
#endif
getRealSpan _ = Nothing
