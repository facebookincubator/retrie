-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--

-- | This module provides the external interface for using Retrie as a library.
-- All other modules should be considered internal, with APIs that are subject
-- to change without notice.
{-# LANGUAGE RecordWildCards #-}
module Retrie
  ( -- * Scripting
    runScript
  , runScriptWithModifiedOptions
    -- ** Parsing Rewrites
    -- *** Imports
  , parseImports
    -- *** Queries
  , parseQueries
  , QuerySpec(..)
    -- *** Rewrites
  , parseRewrites
  , RewriteSpec(..)
  , QualifiedName
    -- ** Retrie Computations
  , Retrie

    -- *** Applying Rewrites
  , apply
  , applyWithStrategy
  , applyWithUpdate
  , applyWithUpdateAndStrategy
  , addImports
    -- *** Control Flow
  , ifChanged
  , iterateR
    -- *** Focusing
  , focus
    -- *** Querying the AST
  , query
  , queryWithUpdate
    -- *** Traversal Strategies
  , bottomUp
  , topDown
  , topDownPrune
    -- * Advanced Scripting
    -- $advanced
    -- ** Side Conditions
  , MatchResultTransformer
  , defaultTransformer
  , MatchResult(..)
    -- * Annotated ASTs
  , Annotated
  , astA
  -- ** Type Synonyms
  , AnnotatedHsDecl
  , AnnotatedHsExpr
  , AnnotatedHsType
  , AnnotatedImports
  , AnnotatedModule
  , AnnotatedPat
  , AnnotatedStmt
    -- ** Parsing
    -- | Note: These parsers do not re-associate infix operators.
    -- To do so, use 'Retrie.ExactPrint.fix'. For example:
    --
    -- > do
    -- >   expr <- parseExpr "f <$> x <*> y"
    -- >   e <- transformA expr (fix (fixityEnv opts))
    --
  , LibDir
  , parseDecl
  , parseExpr
  , parsePattern
  , parseStmt
  , parseType
  -- ** Operations
  , transformA
  , graftA
  , pruneA
  , trimA
  , printA
    -- ** Util
    -- | Collection of miscellaneous helpers for manipulating the GHC AST.
  , module Retrie.Expr
    -- * Types
    -- ** Context
  , Context(..)
  , ContextUpdater
  , updateContext
    -- ** Options
  , Options
  , Options_(..)
  , Verbosity(..)
    -- ** Quantifiers
  , module Retrie.Quantifiers
    -- ** Queries
  , Query(..)
    -- ** Rewrites
  , Rewrite
  , Template(..)
  , mkRewrite
  , ppRewrite
  , addRewriteImports
  , setRewriteTransformer
    -- ** Substitution
  , subst
    -- | See "Retrie.Substitution" for the 'Substitution' type.
  , module Retrie.Substitution
    -- ** Universe
  , Universe
  , Matchable(..)
  , toURewrite
  , fromURewrite
    -- * GHC API
    -- | "Retrie.GHC" re-exports the GHC API, with some helpers for consistency
    -- across versions.
  , module Retrie.GHC
  ) where

import Retrie.Context
import Retrie.ExactPrint.Annotated hiding (unsafeMkA)
import Retrie.ExactPrint
import Retrie.Expr
import Retrie.Fixity
import Retrie.GHC
import Retrie.Monad
import Retrie.Options
import Retrie.Quantifiers
import Retrie.Query
  ( QuerySpec(..)
  , parseQuerySpecs
  )
import Retrie.Rewrites
import Retrie.Run
import Retrie.Subst
import Retrie.Substitution
import Retrie.SYB
import Retrie.Types
import Retrie.Universe
import Retrie.Util

-- | Create 'Rewrite's from string specifications of rewrites.
parseRewrites :: LibDir -> Options -> [RewriteSpec] -> IO [Rewrite Universe]
parseRewrites = parseRewritesInternal

-- | Create 'Query's from string specifications of expressions/types/statements.
parseQueries
  :: LibDir -> Options -> [(Quantifiers, QuerySpec, v)] -> IO [Query Universe v]
parseQueries libdir Options{..} = parseQuerySpecs libdir fixityEnv

-- $advanced
-- For advanced rewriting, Retrie provides the notion of a
-- 'MatchResultTransformer'. This is a callback function that is provided the
-- result of matching the left-hand side of an equation. Whatever the callback
-- returns is used to perform the actual rewrite.
--
-- The callback has access to the 'Context' of the match, the generated
-- 'Substitution', and 'IO'. Helper libraries such as 'Annotated' and 'subst'
-- make it possible to define complex transformers without too much tedium.
--
-- Transformers can check side conditions by examining the 'MatchResult' and
-- returning 'NoMatch' when conditions do not hold.
