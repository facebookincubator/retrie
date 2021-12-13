-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Retrie.Query
  ( QuerySpec(..)
  , parseQuerySpecs
  , genericQ
  ) where

import Retrie.ExactPrint
import Retrie.Fixity
import Retrie.GHC
import Retrie.Quantifiers
import Retrie.Substitution
import Retrie.SYB
import Retrie.Types
import Retrie.Universe

-- | Specifies which parser to use in 'Retrie.parseQueries'.
data QuerySpec
  = QExpr String
  | QType String
  | QStmt String

parseQuerySpecs
  :: LibDir
  -> FixityEnv
  -> [(Quantifiers, QuerySpec, v)]
  -> IO [Query Universe v]
parseQuerySpecs libdir' fixityEnv =
  mapM $ \(qQuantifiers, querySpec, qResult) -> do
    qPattern <- parse libdir' querySpec
    return Query{..}
  where
    parse libdir (QExpr s) = do
      e <- parseExpr libdir s
      fmap inject <$> transformA e (fix fixityEnv)
    parse libdir (QType s) = fmap inject <$> parseType libdir s
    parse libdir (QStmt s) = do
      stmt <- parseStmt libdir s
      fmap inject <$> transformA stmt (fix fixityEnv)

genericQ
  :: Typeable a
  => Matcher v
  -> Context
  -> a
  -> TransformT IO [(Context, Substitution, v)]
genericQ m ctxt =
  mkQ (return []) (genericQImpl @(LHsExpr GhcPs) m ctxt)
    `extQ` (genericQImpl @(LStmt GhcPs (LHsExpr GhcPs)) m ctxt)
    `extQ` (genericQImpl @(LHsType GhcPs) m ctxt)

genericQImpl
  :: forall ast v. Matchable ast
  => Matcher v
  -> Context
  -> ast
  -> TransformT IO [(Context, Substitution, v)]
genericQImpl m ctxt ast = do
  pairs <- runMatcher ctxt m ast
  return [ (ctxt, sub, v) | (sub, v) <- pairs ]
