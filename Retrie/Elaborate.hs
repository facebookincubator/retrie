-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}
module Retrie.Elaborate
  ( defaultElaborations
  , elaborateRewritesInternal
  ) where

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import "list-t" ListT
import Data.Maybe

import Retrie.Context
import Retrie.ExactPrint
import Retrie.Expr
import Retrie.Fixity
import Retrie.GHC
import Retrie.Quantifiers
import Retrie.Rewrites
import Retrie.Subst
import Retrie.Substitution
import Retrie.SYB
import Retrie.Types
import Retrie.Universe

defaultElaborations :: [RewriteSpec]
defaultElaborations =
  [ Adhoc "forall f x. f $ x = f (x)"
  ]

elaborateRewritesInternal
  :: FixityEnv
  -> [Rewrite Universe]
  -> [Rewrite Universe]
  -> IO [Rewrite Universe]
elaborateRewritesInternal _ [] rewrites = return rewrites
elaborateRewritesInternal fixityEnv elaborations rewrites =
  concat <$> mapM (elaborateOne fixityEnv elaborator) rewrites
  where
    elaborator = foldMap mkRewriter elaborations

elaborateOne :: FixityEnv -> Rewriter -> Rewrite Universe -> IO [Rewrite Universe]
elaborateOne fixityEnv elaborator rr = do
  patterns <-
    transformA (qPattern rr) $ toList .
      everywhereMWithContextBut topDown
        (const False) (\c i x -> lift $ updateContext c i x) elaborate ctxt
  return [ rr { qPattern = pattern } | pattern <- sequenceA patterns ]
  where
    ctxt = emptyContext fixityEnv elaborator mempty

elaborate
  :: (Data a, MonadIO m) => Context -> a -> ListT (TransformT m) a
elaborate c =
  mkM (elaborateImpl @(HsExpr GhcPs) c)
    `extM` (elaborateImpl @(Stmt GhcPs (LHsExpr GhcPs)) c)
    `extM` (elaborateImpl @(HsType GhcPs) c)
    `extM` (elaboratePat c)

elaboratePat :: MonadIO m => Context -> LPat GhcPs -> ListT (TransformT m) (LPat GhcPs)
-- We need to ensure we have a location available at the top level so we can
-- transfer annotations. This ensures we don't try to rewrite a naked Pat.
elaboratePat c p
  | Just lp <- dLPat p = cLPat <$> elaborateImpl c lp
  | otherwise = return p

elaborateImpl
  :: forall ast m. (Data ast, ExactPrint ast, Matchable (LocatedA ast), MonadIO m)
  => Context -> LocatedA ast -> ListT (TransformT m) (LocatedA ast)
elaborateImpl ctxt e = do
  elaborations <- lift $ do
    matches <- runMatcher ctxt (ctxtRewriter ctxt) (getUnparened e)
    validMatches <- allMatches ctxt matches
    forM [ (sub, tmpl) | MatchResult sub tmpl <- validMatches ] $ \(sub, Template{..}) -> do
      -- graft template into target
      t' <- graftA tTemplate
      -- substitute for quantifiers in grafted template
      r <- subst sub ctxt t'
      -- copy appropriate annotations from old expression to template
      -- addAllAnnsT e r
      -- add parens to template if needed
      (mkM (parenify ctxt) `extM` parenifyT ctxt `extM` parenifyP ctxt) r

  fromFoldable (e : elaborations)

-- | Find the first 'valid' match.
-- Runs the user's 'MatchResultTransformer' and sanity checks the result.
allMatches
  :: (Matchable ast, MonadIO m)
  => Context
  -> [(Substitution, RewriterResult Universe)]
  -> TransformT m [MatchResult ast]
allMatches _ [] = return []
allMatches ctxt matchResults = do
  results <-
    forM matchResults $ \(sub, RewriterResult{..}) -> do
      result <- lift $ liftIO $ rrTransformer ctxt $ MatchResult sub rrTemplate
      return (rrQuantifiers, result)
  return
    [ project <$> result
    | (quantifiers, result@(MatchResult sub' _)) <- results
      -- Check that all quantifiers from the original rewrite have mappings
      -- in the resulting substitution. This is mostly to prevent a bad
      -- user-defined MatchResultTransformer from causing havok.
    , isJust $ sequence [ lookupSubst q sub' | q <- qList quantifiers ]
    ]
