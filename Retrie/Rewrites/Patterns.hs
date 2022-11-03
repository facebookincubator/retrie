-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
module Retrie.Rewrites.Patterns (patternSynonymsToRewrites) where

import Control.Monad.State (StateT(runStateT), lift)
import Control.Monad
import Control.Monad.IO.Class
import Data.Maybe
import Data.Void

import Retrie.ExactPrint
import Retrie.Expr
import Retrie.GHC
import Retrie.Quantifiers
import Retrie.Rewrites.Function
import Retrie.Types
import Retrie.Universe
import Retrie.Util

patternSynonymsToRewrites
  :: LibDir
  -> [(FastString, Direction)]
  -> AnnotatedModule
  -> IO (UniqFM FastString [Rewrite Universe])
patternSynonymsToRewrites libdir specs am = fmap astA $ transformA am $ \(L _ m) -> do
  let
    fsMap = uniqBag specs
  imports <- getImports libdir RightToLeft (hsmodName m)
  rrs <- sequence
      [ do
          patRewrite <- mkPatRewrite dir imports nm params lrhs
          expRewrites <- mkExpRewrite dir imports nm params rhs patdir
          return (rdr, toURewrite patRewrite : map toURewrite expRewrites)
      | L _ (ValD _ (PatSynBind _ (PSB _ nm params rhs patdir))) <- hsmodDecls m
      , let rdr = rdrFS (unLoc nm)
      , dir <- fromMaybe [] (lookupUFM fsMap rdr)
      , Just lrhs <- [dLPat rhs]
      ]

  return $ listToUFM_C (++) rrs

mkPatRewrite
  :: Direction
  -> AnnotatedImports
  -> LocatedN RdrName
  -> HsConDetails Void (LocatedN RdrName) [RecordPatSynField GhcPs]
  -> LPat GhcPs
  -> TransformT IO (Rewrite (LPat GhcPs))
mkPatRewrite dir imports patName params rhs = do
  lhs <- asPat patName params

  (pat, temp) <- case dir of
    LeftToRight -> return (lhs, rhs)
    RightToLeft -> do
      let lhs' = setEntryDP lhs (SameLine 0)
      -- Patterns from lhs have wonky annotations,
      -- the space will be attached to the name, not to the ConPatIn ast node
      let lhs'' = setEntryDPTunderConPatIn lhs' (SameLine 0)
      return (rhs, lhs'')

  p <- pruneA pat
  t <- pruneA temp
  let bs = collectPatBinders CollNoDictBinders (cLPat temp)
  return $ addRewriteImports imports $ mkRewrite (mkQs bs) p t

  where
    setEntryDPTunderConPatIn :: LPat GhcPs -> DeltaPos -> LPat GhcPs
    setEntryDPTunderConPatIn (L l (ConPat x nm args)) dp
      = (L l (ConPat x (setEntryDP nm dp) args))
    setEntryDPTunderConPatIn p _ = p

asPat
  :: Monad m
  => LocatedN RdrName
  -> HsConDetails Void (LocatedN RdrName) [RecordPatSynField GhcPs]
  -> TransformT m (LPat GhcPs)
asPat patName params = do
  params' <- bitraverseHsConDetails convertTyVars mkVarPat convertFields params
  mkConPatIn patName params'
  where

    convertTyVars :: (Monad m) => [Void] -> TransformT m [HsPatSigType GhcPs]
    convertTyVars _ = return []

    convertFields :: (Monad m) => [RecordPatSynField GhcPs]
                      -> TransformT m (HsRecFields GhcPs (LPat GhcPs))
    convertFields fields =
      HsRecFields <$> traverse convertField fields <*> pure Nothing

    convertField :: (Monad m) => RecordPatSynField GhcPs
                      -> TransformT m (LHsRecField GhcPs (LPat GhcPs))
    convertField RecordPatSynField{..} = do
#if __GLASGOW_HASKELL__ < 904
      hsRecFieldLbl <- mkLoc $ recordPatSynField
      hsRecFieldArg <- mkVarPat recordPatSynPatVar
      let hsRecPun = False
      let hsRecFieldAnn = noAnn
      mkLocA (SameLine 0) HsRecField{..}
#else
      s <- uniqueSrcSpanT
      an <- mkEpAnn (SameLine 0) NoEpAnns
      let srcspan = SrcSpanAnn an s
          hfbLHS = L srcspan recordPatSynField
      hfbRHS <- mkVarPat recordPatSynPatVar
      let hfbPun = False
          hfbAnn = noAnn
      mkLocA (SameLine 0) HsFieldBind{..}
#endif

mkExpRewrite
  :: Direction
  -> AnnotatedImports
  -> LocatedN RdrName
  -> HsConDetails Void (LocatedN RdrName) [RecordPatSynField GhcPs]
  -> LPat GhcPs
  -> HsPatSynDir GhcPs
  -> TransformT IO [Rewrite (LHsExpr GhcPs)]
mkExpRewrite dir imports patName params rhs patDir = do
  fe <- mkLocatedHsVar patName
  -- lift $ debugPrint Loud "mkExpRewrite:fe="  [showAst fe]
  let altsFromParams = case params of
        PrefixCon _tyargs names -> buildMatch names rhs
        InfixCon a1 a2 -> buildMatch [a1, a2] rhs
        RecCon{} -> missingSyntax "RecCon"
  alts <- case patDir of
    ExplicitBidirectional MG{mg_alts} -> pure $ unLoc mg_alts
    ImplicitBidirectional -> altsFromParams
    _ -> pure []
  fmap concat $ forM alts $ matchToRewrites fe imports dir

buildMatch
  :: MonadIO m
  => [LocatedN RdrName]
  -> LPat GhcPs
  -> TransformT m [LMatch GhcPs (LHsExpr GhcPs)]
buildMatch names rhs = do
  pats <- traverse mkVarPat names
  let bs = collectPatBinders CollNoDictBinders rhs
  (rhsExpr,(_,_bs')) <- runStateT (patToExpr rhs) (wildSupply bs, bs)
  let alt = mkMatch PatSyn pats rhsExpr emptyLocalBinds
  return [alt]
