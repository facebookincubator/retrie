-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE CPP #-}
{-# LANGUAGE TupleSections #-}
module Retrie.Rewrites.Function (dfnsToRewrites) where

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
  :: [(FastString, Direction)]
  -> AnnotatedModule
  -> IO (UniqFM [Rewrite (LHsExpr GhcPs)])
dfnsToRewrites specs am = fmap astA $ transformA am $ \ (L _ m) -> do
  let
    fsMap = uniqBag specs

  rrs <- sequence
    [ do
        fe <- mkLocatedHsVar fRdrName
        imps <- getImports dir (hsmodName m)
        (fName,) . concat <$>
          forM (unLoc $ mg_alts $ fun_matches f) (matchToRewrites fe imps dir)
#if __GLASGOW_HASKELL__ < 806
    | L _ (ValD f@FunBind{}) <- hsmodDecls m
#else
    | L _ (ValD _ f@FunBind{}) <- hsmodDecls m
#endif
    , let fRdrName = fun_id f
    , let fName = occNameFS (occName (unLoc fRdrName))
    , dir <- fromMaybe [] (lookupUFM fsMap fName)
    ]

  return $ listToUFM_C (++) rrs

------------------------------------------------------------------------

getImports
  :: Direction -> Maybe (Located ModuleName) -> TransformT IO AnnotatedImports
getImports RightToLeft (Just (L _ mn)) = -- See Note [fold only]
  lift $ liftIO $ parseImports ["import " ++ moduleNameString mn]
getImports _ _ = return mempty

matchToRewrites
  :: LHsExpr GhcPs
  -> AnnotatedImports
  -> Direction
  -> LMatch GhcPs (LHsExpr GhcPs)
  -> TransformT IO [Rewrite (LHsExpr GhcPs)]
matchToRewrites e imps dir (L _ alt) = do
  let
    pats = m_pats alt
    grhss = m_grhss alt
  qss <- for (zip (inits pats) (tails pats)) $
    makeFunctionQuery e imps dir grhss mkApps
  qs <- backtickRules e imps dir grhss pats
  return $ qs ++ concat qss

type AppBuilder =
  LHsExpr GhcPs -> [LHsExpr GhcPs] -> TransformT IO (LHsExpr GhcPs)

makeFunctionQuery
  :: LHsExpr GhcPs
  -> AnnotatedImports
  -> Direction
  -> GRHSs GhcPs (LHsExpr GhcPs)
  -> AppBuilder
  -> ([LPat GhcPs], [LPat GhcPs])
  -> TransformT IO [Rewrite (LHsExpr GhcPs)]
makeFunctionQuery e imps dir grhss mkAppFn (argpats, bndpats) = do
  let
#if __GLASGOW_HASKELL__ < 806
    GRHSs rhss lbs = grhss
#else
    GRHSs _ rhss lbs = grhss
#endif
    bs = collectPatsBinders argpats
  -- See Note [Wildcards]
  (es,(_,bs')) <- runStateT (mapM patToExpr argpats) (wildSupply bs, bs)
  lhs <- mkAppFn e es
  for rhss $ \ grhs -> do
    le <- mkLet (unLoc lbs) (grhsToExpr grhs)
    rhs <- mkLams bndpats le
    let
      (pat, temp) =
        case dir of
          LeftToRight -> (lhs,rhs)
          RightToLeft -> (rhs,lhs)
    p <- pruneA pat
    t <- pruneA temp
    return $ addRewriteImports imps $ mkRewrite (mkQs bs') p t

backtickRules
  :: LHsExpr GhcPs
  -> AnnotatedImports
  -> Direction
  -> GRHSs GhcPs (LHsExpr GhcPs)
  -> [LPat GhcPs]
  -> TransformT IO [Rewrite (LHsExpr GhcPs)]
backtickRules e imps dir@LeftToRight grhss ps@[p1, p2] = do
  let
    both, left, right :: AppBuilder
#if __GLASGOW_HASKELL__ < 806
    both op [l, r] = mkLoc (OpApp l op PlaceHolder r)
    both _ _ = fail "backtickRules - both: impossible!"

    left op [l] = mkLoc (SectionL l op)
    left _ _ = fail "backtickRules - left: impossible!"

    right op [r] = mkLoc (SectionR op r)
    right _ _ = fail "backtickRules - right: impossible!"
#else
    both op [l, r] = mkLoc (OpApp noExtField l op r)
    both _ _ = fail "backtickRules - both: impossible!"

    left op [l] = mkLoc (SectionL noExtField l op)
    left _ _ = fail "backtickRules - left: impossible!"

    right op [r] = mkLoc (SectionR noExtField op r)
    right _ _ = fail "backtickRules - right: impossible!"
#endif
  qs <- makeFunctionQuery e imps dir grhss both (ps, [])
  qsl <- makeFunctionQuery e imps dir grhss left ([p1], [p2])
  qsr <- makeFunctionQuery e imps dir grhss right ([p2], [p1])
  return $ qs ++ qsl ++ qsr
backtickRules _ _ _ _ _ = return []

-- Note [fold only]
-- Currently we only generate imports for folds, because it is easy.
-- (We only need to add an import for the module defining the folded
-- function.) Generating the imports for unfolds will require some
-- sort of analysis with haskell-names and is a TODO.
