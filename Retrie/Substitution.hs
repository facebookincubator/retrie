-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE CPP #-}
module Retrie.Substitution
  ( Substitution
  , HoleVal(..)
  , emptySubst
  , extendSubst
  , lookupSubst
  , deleteSubst
  , foldSubst
  ) where

import Retrie.ExactPrint
import Retrie.GHC

-- | A 'Substitution' is essentially a map from variable name to 'HoleVal'.
newtype Substitution = Substitution (UniqFM FastString (FastString, HoleVal))
-- See Note [Why not RdrNames?] for explanation of use of FastString

instance Show Substitution where
  show (Substitution m) = show (eltsUFM m)

-- | Sum type of possible substitution values.
data HoleVal
  = HoleExpr AnnotatedHsExpr -- ^ 'HsExpr'
  | HolePat AnnotatedPat -- ^ 'Pat'
  | HoleType AnnotatedHsType -- ^ 'HsType'
  | HoleRdr RdrName -- ^ Alpha-renamed binder.

instance Show HoleVal where
  show (HoleExpr e) = "HoleExpr " ++ printA e
  show (HolePat p) = "HolePat " ++ printA p
  show (HoleType t) = "HoleType " ++ printA t
  show (HoleRdr r) = "HoleRdr " ++ unpackFS (rdrFS r)

-- | The empty substitution.
emptySubst :: Substitution
emptySubst = Substitution emptyUFM

-- | Lookup a value in the substitution.
lookupSubst :: FastString -> Substitution -> Maybe HoleVal
lookupSubst k (Substitution m) = snd <$> lookupUFM m k

-- | Extend the substitution. If the key already exists, its value is replaced.
extendSubst :: Substitution -> FastString -> HoleVal -> Substitution
extendSubst (Substitution m) k v = Substitution (addToUFM m k (k,v))

-- | Delete from the substitution.
deleteSubst :: Substitution -> [FastString] -> Substitution
deleteSubst (Substitution m) ks = Substitution (delListFromUFM m ks)

-- | Fold over the substitution.
foldSubst :: ((FastString, HoleVal) -> a -> a) -> a -> Substitution -> a
foldSubst f x (Substitution m) = foldUFM f x m
