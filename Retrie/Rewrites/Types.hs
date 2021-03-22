-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
module Retrie.Rewrites.Types where

import Control.Monad
import Data.Maybe

import Retrie.ExactPrint
import Retrie.Expr
import Retrie.GHC
import Retrie.Quantifiers
import Retrie.Types

typeSynonymsToRewrites
  :: [(FastString, Direction)]
  -> AnnotatedModule
  -> IO (UniqFM [Rewrite (LHsType GhcPs)])
typeSynonymsToRewrites specs am = fmap astA $ transformA am $ \ m -> do
  let
    fsMap = uniqBag specs
    tySyns =
      [ (rdr, (dir, (nm, hsq_explicit vars, rhs)))
        -- only hsq_explicit is available pre-renaming
      | L _ (TyClD _ (SynDecl _ nm vars _ rhs)) <- hsmodDecls $ unLoc m
      , let rdr = rdrFS (unLoc nm)
      , dir <- fromMaybe [] (lookupUFM fsMap rdr)
      ]
  fmap uniqBag $
    forM tySyns $ \(rdr, args) -> (rdr,) <$> uncurry mkTypeRewrite args

------------------------------------------------------------------------

-- | Compile a list of RULES into a list of rewrites.
mkTypeRewrite
  :: Direction
  -> (Located RdrName, [LHsTyVarBndr GhcPs], LHsType GhcPs)
  -> TransformT IO (Rewrite (LHsType GhcPs))
mkTypeRewrite d (lhsName, vars, rhs) = do
  setEntryDPT lhsName $ DP (0,0)
  tc <- mkTyVar lhsName
  let
    lvs = tyBindersToLocatedRdrNames vars
  args <- forM lvs $ \ lv -> do
    tv <- mkTyVar lv
    setEntryDPT tv (DP (0,1))
    return tv
  lhsApps <- mkHsAppsTy (tc:args)
  let
    (pat, tmp) = case d of
      LeftToRight -> (lhsApps, rhs)
      RightToLeft -> (rhs, lhsApps)
  p <- pruneA pat
  t <- pruneA tmp
  return $ mkRewrite (mkQs $ map unLoc lvs) p t
