-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE CPP #-}
{-# LANGUAGE RecordWildCards #-}
module Retrie.GHC
  ( module Retrie.GHC
  , module GHC.Data.Bag
  , module GHC.Data.FastString
  , module GHC.Data.FastString.Env
  , module GHC.Driver.Errors
  , module GHC.Hs
  , module GHC.Hs.Expr
  , module GHC.Parser.Annotation
  , module GHC.Parser.Errors.Ppr
  , module GHC.Types.Basic
  , module GHC.Types.Error
  , module GHC.Types.Fixity
  , module GHC.Types.Name
  , module GHC.Types.Name.Occurrence
  , module GHC.Types.Name.Reader
  , module GHC.Types.SourceText
  , module GHC.Types.SrcLoc
  , module GHC.Types.Unique
  , module GHC.Types.Unique.FM
  , module GHC.Types.Unique.Set
  , module GHC.Unit.Module.Name
  ) where

import GHC
import GHC.Builtin.Names
import GHC.Data.Bag
import GHC.Data.FastString
import GHC.Data.FastString.Env
import GHC.Driver.Errors
import GHC.Hs
import GHC.Hs.Expr
import GHC.Parser.Annotation
import GHC.Parser.Errors.Ppr
import GHC.Types.Basic hiding (EP)
import GHC.Types.Error
import GHC.Types.Fixity
import GHC.Types.Name
import GHC.Types.Name.Occurrence
import GHC.Types.Name.Reader
import GHC.Types.SourceText
import GHC.Types.SrcLoc
import GHC.Types.Unique
import GHC.Types.Unique.FM
import GHC.Types.Unique.Set
import GHC.Unit.Module.Name

import Data.Bifunctor (second)
import Data.Maybe

cLPat :: LPat (GhcPass p) -> LPat (GhcPass p)
cLPat = id

-- | Only returns located pat if there is a genuine location available.
dLPat :: LPat (GhcPass p) -> Maybe (LPat (GhcPass p))
dLPat = Just

-- | Will always give a location, but it may be noSrcSpan.
dLPatUnsafe :: LPat (GhcPass p) -> LPat (GhcPass p)
dLPatUnsafe = id

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

varRdrName :: HsExpr p -> Maybe (LIdP p)
varRdrName (HsVar _ n) = Just n
varRdrName _ = Nothing

tyvarRdrName :: HsType p -> Maybe (LIdP p)
tyvarRdrName (HsTyVar _ _ n) = Just n
tyvarRdrName _ = Nothing

-- fixityDecls :: HsModule -> [(LIdP p, Fixity)]
fixityDecls :: HsModule -> [(LocatedN RdrName, Fixity)]
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

ruleBindersToQs :: [LRuleBndr GhcPs] -> [RdrName]
ruleBindersToQs bs = catMaybes
  [ case b of
      RuleBndr _ (L _ v) -> Just v
      RuleBndrSig _ (L _ v) _ -> Just v
  | L _ b <- bs
  ]

tyBindersToLocatedRdrNames :: [LHsTyVarBndr s GhcPs] -> [LocatedN RdrName]
tyBindersToLocatedRdrNames vars = catMaybes
  [ case var of
      UserTyVar _ _ v -> Just v
      KindedTyVar _ _ v _ -> Just v
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
overlaps (RealSrcSpan s1 _) (RealSrcSpan s2 _) =
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
  | RealSrcSpan s _ <- ss
  ]

showRdrs :: [RdrName] -> String
showRdrs = show . map (occNameString . occName)

uniqBag :: Uniquable a => [(a,b)] -> UniqFM a [b]
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
