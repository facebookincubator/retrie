-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE CPP #-}
{-# LANGUAGE TupleSections #-}
module Retrie.Rewrites.Function
  ( dfnsToRewrites
  , getImports
  , matchToRewrites
  ) where

import Control.Monad
import Control.Monad.State.Lazy
import Data.List
import Data.Maybe
import Data.Traversable

import Retrie.ExactPrint
import Retrie.Expr
import Retrie.GHC
import Retrie.Quantifiers
import Retrie.Types
import Retrie.Util

dfnsToRewrites
  :: LibDir
  -> [(FastString, Direction)]
  -> AnnotatedModule
  -> IO (UniqFM FastString [Rewrite (LHsExpr GhcPs)])
dfnsToRewrites libdir specs am = fmap astA $ transformA am $ \ (L _ m) -> do
  let
    fsMap = uniqBag specs

  rrs <- sequence
    [ do
        fe <- mkLocatedHsVar fRdrName
        -- lift $ debugPrint Loud "dfnsToRewrites:ef="  [showAst fe]
        imps <- getImports libdir dir (hsmodName m)
        -- lift $ debugPrint Loud "dfnsToRewrites:imps="  [showAst imps]
        (fName,) . concat <$>
          forM (unLoc $ mg_alts $ fun_matches f) (matchToRewrites fe imps dir)
    | L _ (ValD _ f@FunBind{}) <- hsmodDecls m
    , let fRdrName = fun_id f
    , let fName = occNameFS (occName (unLoc fRdrName))
    , dir <- fromMaybe [] (lookupUFM fsMap fName)
    ]

  return $ listToUFM_C (++) rrs

------------------------------------------------------------------------

getImports
  :: LibDir -> Direction -> Maybe (LocatedA ModuleName) -> TransformT IO AnnotatedImports
getImports libdir RightToLeft (Just (L _ mn)) = -- See Note [fold only]
  TransformT $ lift $ liftIO $ parseImports libdir ["import " ++ moduleNameString mn]
getImports _ _ _ = return mempty

matchToRewrites
  :: LHsExpr GhcPs
  -> AnnotatedImports
  -> Direction
  -> LMatch GhcPs (LHsExpr GhcPs)
  -> TransformT IO [Rewrite (LHsExpr GhcPs)]
matchToRewrites e imps dir (L _ alt') = do
  -- lift $ debugPrint Loud "matchToRewrites:e="  [showAst e]
  let alt = makeDeltaAst alt'
  -- let alt = alt'
  -- lift $ debugPrint Loud "matchToRewrites:alt="  [showAst alt]
  let
    pats = m_pats alt
    grhss = m_grhss alt
    grhss_loc = grhssLoc alt'
  -- lift $ debugPrint Loud "matchToRewrites:alt'="  [showAst alt']
  lift $ debugPrint Loud "matchToRewrites:grhss_loc="  [showAst grhss_loc]
  qss <- for (zip (inits pats) (tails pats)) $
    makeFunctionQuery e imps dir grhss grhss_loc mkApps
  qs <- backtickRules e imps dir grhss grhss_loc pats
  return $ qs ++ concat qss

grhssLoc :: Match GhcPs (LHsExpr GhcPs) -> SrcSpan
grhssLoc m = loc
    where
      GRHSs _ grhss _ = m_grhss m
      loc = case grhss of
          [] -> noSrcSpan
          (h:_) -> combineSrcSpans (getHasLoc h) (getHasLoc (last grhss))

type AppBuilder =
  LHsExpr GhcPs -> [LHsExpr GhcPs] -> TransformT IO (LHsExpr GhcPs)

irrefutablePat :: LPat GhcPs -> Bool
irrefutablePat = go . unLoc
  where
    go WildPat{} = True
    go VarPat{} = True
    go (LazyPat _ p) = irrefutablePat p
#if __GLASGOW_HASKELL__ <= 904 || __GLASGOW_HASKELL__ >= 910
    go (AsPat _ _ p) = irrefutablePat p
#else
    go (AsPat _ _ _ p) = irrefutablePat p
#endif
#if __GLASGOW_HASKELL__ < 904 || __GLASGOW_HASKELL__ >= 910
    go (ParPat _ p) = irrefutablePat p
#else
    go (ParPat _ _ p _) = irrefutablePat p
#endif
    go (BangPat _ p) = irrefutablePat p
    go _ = False

makeFunctionQuery
  :: LHsExpr GhcPs
  -> AnnotatedImports
  -> Direction
  -> GRHSs GhcPs (LHsExpr GhcPs)
  -> SrcSpan
  -> AppBuilder
  -> ([LPat GhcPs], [LPat GhcPs])
  -> TransformT IO [Rewrite (LHsExpr GhcPs)]
makeFunctionQuery e imps dir grhss grhss_loc mkAppFn (argpats, bndpats)
  | any (not . irrefutablePat) bndpats = return []
  | otherwise = do
    let
      GRHSs _ rhss lbs = grhss
      bs = collectPatsBinders CollNoDictBinders argpats
    -- See Note [Wildcards]
    (es,(_,bs')) <- runStateT (mapM patToExpr argpats) (wildSupply bs, bs)
    -- lift $ debugPrint Loud "makeFunctionQuery:e="  [showAst e]
    -- lift $ debugPrint Loud "makeFunctionQuery:argpats="  [showAst argpats]
    -- lift $ debugPrint Loud "makeFunctionQuery:es="  [showAst es]
    -- lift $ debugPrint Loud "makeFunctionQuery:grhss_loc="  [showGhc grhss_loc]
    lhs <- mkAppFn e es
    for rhss $ \ grhs -> do
      le <- mkLet lbs (grhsToExpr grhs)
      rhs <- mkLams bndpats le
      let
        (pat, pat_loc, temp) =
          case dir of
            LeftToRight -> (lhs, getHasLoc lhs, rhs)
            RightToLeft -> (rhs, grhss_loc, lhs)
      -- p <- pruneA (setEntryDP (makeDeltaAst pat) (SameLine 1))
      p <- pruneA pat
      t <- pruneA (setEntryDP (makeDeltaAst temp) (SameLine 1))
      -- return $ addRewriteImports imps $ mkRewrite (mkQs bs') p (getHasLoc p) t
      return $ addRewriteImports imps $ mkRewrite (mkQs bs') p (pat_loc
                                                               `debug` ("makeFunctionQuery:loc" ++ (showGhc pat_loc))) t

backtickRules
  :: LHsExpr GhcPs
  -> AnnotatedImports
  -> Direction
  -> GRHSs GhcPs (LHsExpr GhcPs)
  -> SrcSpan
  -> [LPat GhcPs]
  -> TransformT IO [Rewrite (LHsExpr GhcPs)]
backtickRules e imps dir@LeftToRight grhss grhss_loc ps@[p1, p2] = do
  let
    both, left, right :: AppBuilder
    both op [l, r] = mkLocA (SameLine 1) (OpApp noAnn l op r)
    both _ _ = fail "backtickRules - both: impossible!"

    left op [l] = mkLocA (SameLine 1) (SectionL
#if __GLASGOW_HASKELL__ >= 910
                                         NoExtField
#else
                                         noAnn
#endif
                                         l op)
    left _ _ = fail "backtickRules - left: impossible!"

    right op [r] = mkLocA (SameLine 1) (SectionR
#if __GLASGOW_HASKELL__ >= 910
                                         NoExtField
#else
                                         noAnn
#endif
                                         op r)
    right _ _ = fail "backtickRules - right: impossible!"
  qs <- makeFunctionQuery e imps dir grhss grhss_loc both (ps, [])
  qsl <- makeFunctionQuery e imps dir grhss grhss_loc left ([p1], [p2])
  qsr <- makeFunctionQuery e imps dir grhss grhss_loc right ([p2], [p1])
  return $ qs ++ qsl ++ qsr
backtickRules _ _ _ _ _ _ = return []

-- Note [fold only]
-- Currently we only generate imports for folds, because it is easy.
-- (We only need to add an import for the module defining the folded
-- function.) Generating the imports for unfolds will require some
-- sort of analysis with haskell-names and is a TODO.
