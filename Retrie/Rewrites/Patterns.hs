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

import Control.Monad.State (StateT(runStateT))
import Control.Monad
import Data.Maybe

import Retrie.ExactPrint
import Retrie.Expr
import Retrie.GHC
import Retrie.Quantifiers
import Retrie.Rewrites.Function
import Retrie.Types
import Retrie.Universe
import Retrie.Util

patternSynonymsToRewrites
  :: [(FastString, Direction)]
  -> AnnotatedModule
  -> IO (UniqFM [Rewrite Universe])
patternSynonymsToRewrites specs am = fmap astA $ transformA am $ \(L _ m) -> do
  let
    fsMap = uniqBag specs
  imports <- getImports RightToLeft (hsmodName m)
  rrs <- sequence
      [ do
          patRewrite <- mkPatRewrite dir imports nm params lrhs
          expRewrites <- mkExpRewrite dir imports nm params rhs patdir
          return (rdr, toURewrite patRewrite : map toURewrite expRewrites)
#if __GLASGOW_HASKELL__ < 806
      | L _ (ValD (PatSynBind (PSB nm _ params rhs patdir))) <- hsmodDecls m
#else
      | L _ (ValD _ (PatSynBind _ (PSB _ nm params rhs patdir))) <- hsmodDecls m
#endif
      , let rdr = rdrFS (unLoc nm)
      , dir <- fromMaybe [] (lookupUFM fsMap rdr)
      , Just lrhs <- [dLPat rhs]
      ]

  return $ listToUFM_C (++) rrs

mkPatRewrite
  :: Direction
  -> AnnotatedImports
  -> LRdrName
  -> HsConDetails LRdrName [RecordPatSynField LRdrName]
  -> Located (Pat GhcPs)
  -> TransformT IO (Rewrite (Located (Pat GhcPs)))
mkPatRewrite dir imports patName params rhs = do
  lhs <- asPat patName params

  (pat, temp) <- case dir of
    LeftToRight -> return (lhs, rhs)
    RightToLeft -> do
      setEntryDPT lhs (DP (0,0))
      -- Patterns from lhs have wonky annotations,
      -- the space will be attached to the name, not to the ConPatIn ast node
      setEntryDPTunderConPatIn lhs (DP (0,0))
      return (rhs, lhs)

  p <- pruneA pat
  t <- pruneA temp
  let bs = collectPatBinders (cLPat temp)
  return $ addRewriteImports imports $ mkRewrite (mkQs bs) p t

  where
    setEntryDPTunderConPatIn
      :: Monad m => Located (Pat GhcPs) -> DeltaPos -> TransformT m ()
    setEntryDPTunderConPatIn (L _ (ConPatIn nm _)) = setEntryDPT nm
    setEntryDPTunderConPatIn _ = const $ return ()

asPat
  :: Monad m
  => LRdrName
  -> HsConDetails LRdrName [RecordPatSynField LRdrName]
  -> TransformT m (Located (Pat GhcPs))
asPat patName params = do
  params' <- bitraverseHsConDetails mkVarPat convertFields params
  mkConPatIn patName params'
  where

    convertFields fields =
      HsRecFields <$> traverse convertField fields <*> pure Nothing

    convertField RecordPatSynField{..} = do
      hsRecFieldLbl <- mkLoc $ mkFieldOcc recordPatSynSelectorId
      hsRecFieldArg <- mkVarPat recordPatSynPatVar
      let hsRecPun = False
      mkLoc HsRecField{..}


mkExpRewrite
  :: Direction
  -> AnnotatedImports
  -> LRdrName
  -> HsConDetails LRdrName [RecordPatSynField LRdrName]
  -> LPat GhcPs
  -> HsPatSynDir GhcPs
  -> TransformT IO [Rewrite (LHsExpr GhcPs)]
mkExpRewrite dir imports patName params rhs patDir = do
  fe <- mkLocatedHsVar patName
  let altsFromParams = case params of
        PrefixCon names -> buildMatch names rhs
        InfixCon a1 a2 -> buildMatch [a1, a2] rhs
        RecCon{} -> missingSyntax "RecCon"
  alts <- case patDir of
    ExplicitBidirectional MG{mg_alts} -> pure $ unLoc mg_alts
    ImplicitBidirectional -> altsFromParams
    _ -> pure []
  fmap concat $ forM alts $ matchToRewrites fe imports dir

buildMatch
  :: Monad m
  => [Located (IdP GhcPs)]
  -> LPat GhcPs
  -> TransformT m [LMatch GhcPs (LHsExpr GhcPs)]
buildMatch names rhs = do
  pats <- traverse mkVarPat names
  let bs = collectPatBinders rhs
  (rhsExpr,(_,_bs')) <- runStateT (patToExpr rhs) (wildSupply bs, bs)
  let alt = mkMatch PatSyn pats rhsExpr (noLoc emptyLocalBinds)
  return [alt]
