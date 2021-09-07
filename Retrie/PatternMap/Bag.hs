-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE CPP #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
module Retrie.PatternMap.Bag where

import qualified Data.Map as M
import qualified Data.IntMap as I

import Retrie.AlphaEnv
import qualified Retrie.GHC as GHC
import Retrie.PatternMap.Class
import Retrie.Quantifiers
import Retrie.Substitution

data BoolMap a
  = EmptyBoolMap
  | BoolMap
      { bmTrue :: MaybeMap a
      , bmFalse :: MaybeMap a
      }
  deriving (Functor)

instance PatternMap BoolMap where
  type Key BoolMap = Bool

  mEmpty :: BoolMap a
  mEmpty = EmptyBoolMap

  mUnion :: BoolMap a -> BoolMap a -> BoolMap a
  mUnion EmptyBoolMap m = m
  mUnion m EmptyBoolMap = m
  mUnion m1 m2 = BoolMap
    { bmTrue = unionOn bmTrue m1 m2
    , bmFalse = unionOn bmFalse m1 m2
    }

  mAlter
    :: AlphaEnv -> Quantifiers -> Key BoolMap -> A a -> BoolMap a -> BoolMap a
  mAlter env qs b f EmptyBoolMap = mAlter env qs b f (BoolMap mEmpty mEmpty)
  mAlter env qs b f m@BoolMap{}
    | b = m { bmTrue = mAlter env qs () f (bmTrue m) }
    | otherwise = m { bmFalse = mAlter env qs () f (bmFalse m) }

  mMatch
    :: MatchEnv
    -> Key BoolMap
    -> (Substitution, BoolMap a)
    -> [(Substitution, a)]
  mMatch _ _ (_, EmptyBoolMap) = []
  mMatch env b hs@(_, BoolMap{})
    | b = mapFor bmTrue hs >>= mMatch env ()
    | otherwise = mapFor bmFalse hs >>= mMatch env ()

------------------------------------------------------------------------

newtype IntMap a = IntMap { unIntMap :: I.IntMap [a] }
  deriving (Functor)

instance PatternMap IntMap where
  type Key IntMap = I.Key

  mEmpty :: IntMap a
  mEmpty = IntMap I.empty

  mUnion :: IntMap a -> IntMap a -> IntMap a
  mUnion (IntMap m1) (IntMap m2) = IntMap $ I.unionWith (++) m1 m2

  mAlter :: AlphaEnv -> Quantifiers -> Key IntMap -> A a -> IntMap a -> IntMap a
  mAlter _ _ i f (IntMap m) = IntMap $ I.alter (toAList f) i m

  mMatch
    :: MatchEnv
    -> Key IntMap
    -> (Substitution, IntMap a)
    -> [(Substitution, a)]
  mMatch _ i = maybeListMap (I.lookup i . unIntMap)

------------------------------------------------------------------------

newtype Map k a = Map { unMap :: M.Map k [a] }
  deriving (Functor)

mapAssocs :: Map k v -> [(k,v)]
mapAssocs (Map m) = [ (k,v) | (k,vs) <- M.assocs m, v <- vs ]

instance Ord k => PatternMap (Map k) where
  type Key (Map k) = k

  mEmpty :: Map k a
  mEmpty = Map M.empty

  mUnion :: Map k a -> Map k a -> Map k a
  mUnion (Map m1) (Map m2) = Map $ M.unionWith (++) m1 m2

  mAlter :: AlphaEnv -> Quantifiers -> Key (Map k) -> A a -> Map k a -> Map k a
  mAlter _ _ k f (Map m) = Map $ M.alter (toAList f) k m

  mMatch
    :: MatchEnv
    -> Key (Map k)
    -> (Substitution, Map k a)
    -> [(Substitution, a)]
  mMatch _ k = maybeListMap (M.lookup k . unMap)

------------------------------------------------------------------------

-- Note [OccEnv]
--
-- We avoid using OccEnv because the Uniquable instance for OccName
-- takes the NameSpace of the OccName into account, which we rarely actually
-- want. (Doing so requires creating new RdrNames with the proper namespace,
-- which is a bunch of fiddling for no obvious gain for our uses.) Instead
-- we just use a map based on the FastString name.

newtype FSEnv a =
  FSEnv { _unFSEnv :: UniqFM a } -- this is the UniqFM below, NOT GHC's UniqFM
  deriving (Functor)

instance PatternMap FSEnv where
  type Key FSEnv = GHC.FastString

  mEmpty :: FSEnv a
  mEmpty = FSEnv mEmpty

  mUnion :: FSEnv a -> FSEnv a -> FSEnv a
  mUnion (FSEnv m1) (FSEnv m2) = FSEnv (mUnion m1 m2)

  mAlter :: AlphaEnv -> Quantifiers -> Key FSEnv -> A a -> FSEnv a -> FSEnv a
  mAlter env qs fs f (FSEnv m) = FSEnv (mAlter env qs (GHC.getUnique fs) f m)

  mMatch :: MatchEnv -> Key FSEnv -> (Substitution, FSEnv a) -> [(Substitution, a)]
  mMatch env fs (hs, FSEnv m) = mMatch env (GHC.getUnique fs) (hs, m)

------------------------------------------------------------------------

newtype UniqFM a = UniqFM { unUniqFM :: GHC.UniqFM GHC.Unique [a] }
  deriving (Functor)

instance PatternMap UniqFM where
  type Key UniqFM = GHC.Unique

  mEmpty :: UniqFM a
  mEmpty = UniqFM GHC.emptyUFM

  mUnion :: UniqFM a -> UniqFM a -> UniqFM a
  mUnion (UniqFM m1) (UniqFM m2) = UniqFM $ GHC.plusUFM_C (++) m1 m2

  mAlter :: AlphaEnv -> Quantifiers -> Key UniqFM -> A a -> UniqFM a -> UniqFM a
  mAlter _ _ k f (UniqFM m) = UniqFM $ GHC.alterUFM (toAList f) m k

  mMatch
    :: MatchEnv
    -> Key UniqFM
    -> (Substitution, UniqFM a)
    -> [(Substitution, a)]
  mMatch _ k = maybeListMap (flip GHC.lookupUFM_Directly k . unUniqFM)

------------------------------------------------------------------------
