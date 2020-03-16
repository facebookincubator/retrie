-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Retrie.SYB
  ( everywhereMWithContextBut
  , GenericCU
  , GenericMC
  , Strategy
  , topDown
  , bottomUp
  , everythingMWithContextBut
  , GenericMCQ
  , module Data.Generics
  ) where

import Control.Monad
import Data.Generics hiding (Fixity(..))

-- | Monadic rewrite with context
type GenericMC m c = forall a. Data a => c -> a -> m a

-- | Context update:
-- Given current context, child number, and parent, create new context
type GenericCU m c = forall a. Data a => c -> Int -> a -> m c

-- | Monadic traversal with pruning and context propagation.
everywhereMWithContextBut
  :: forall m c. Monad m
  => Strategy m    -- ^ Traversal order (see 'topDown' and 'bottomUp')
  -> GenericQ Bool -- ^ Short-circuiting stop condition
  -> GenericCU m c -- ^ Context update function
  -> GenericMC m c -- ^ Context-aware rewrite
  -> GenericMC m c
everywhereMWithContextBut strategy stop upd f = go
  where
    go :: GenericMC m c
    go ctxt x
      | stop x    = return x
      | otherwise = strategy (f ctxt) (h ctxt) x

    h ctxt parent = gforMIndexed parent $ \i child -> do
      ctxt' <- upd ctxt i parent
      go ctxt' child

type GenericMCQ m c r = forall a. Data a => c -> a -> m r

-- | Monadic query with pruning and context propagation.
everythingMWithContextBut
  :: forall m c r. (Monad m, Monoid r)
  => GenericQ Bool -- ^ Short-circuiting stop condition
  -> GenericCU m c -- ^ Context update function
  -> GenericMCQ m c r -- ^ Context-aware query
  -> GenericMCQ m c r
everythingMWithContextBut stop upd q = go
  where
    go :: GenericMCQ m c r
    go ctxt x
      | stop x = return mempty
      | otherwise = do
        r <- q ctxt x
        rs <- gforQIndexed x $ \i child -> do
          ctxt' <- upd ctxt i x
          go ctxt' child
        return $ mconcat (r:rs)

-- | Traversal strategy.
-- Given a rewrite on the node and a rewrite on the node's children, define
-- a composite rewrite.
type Strategy m = forall a. Monad m => (a -> m a) -> (a -> m a) -> a -> m a

-- | Perform a top-down traversal.
topDown :: Strategy m
topDown p cs = p >=> cs

-- | Perform a bottom-up traversal.
bottomUp :: Strategy m
bottomUp p cs = cs >=> p

-- | 'gmapM' with arguments flipped and providing zero-based index of child
-- to mapped function.
gforMIndexed
  :: (Monad m, Data a) => a -> (forall d. Data d => Int -> d -> m d) -> m a
gforMIndexed x f = snd (gmapAccumM (accumIndex f) (-1) x)
-- -1 is constructor, 0 is first child

accumIndex :: (Int -> a -> b) -> Int -> a -> (Int, b)
accumIndex f i y = let !i' = i+1 in (i', f i' y)

gforQIndexed
  :: (Monad m, Data a) => a -> (forall d. Data d => Int -> d -> m r) -> m [r]
gforQIndexed x f = sequence $ snd $ gmapAccumQ (accumIndex f) (-1) x
