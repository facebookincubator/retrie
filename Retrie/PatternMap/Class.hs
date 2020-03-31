-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
module Retrie.PatternMap.Class where

import Control.Monad
import Data.Maybe

import Retrie.AlphaEnv
import Retrie.ExactPrint
import Retrie.GHC
import Retrie.Quantifiers
import Retrie.Substitution

------------------------------------------------------------------------

data MatchEnv = ME
  { meAlphaEnv :: AlphaEnv
  , mePruneA :: forall a. a -> Annotated a
  }

extendMatchEnv :: MatchEnv -> [RdrName] -> MatchEnv
extendMatchEnv me bs =
  me { meAlphaEnv = foldr extendAlphaEnvInternal (meAlphaEnv me) bs }

pruneMatchEnv :: Int -> MatchEnv -> MatchEnv
pruneMatchEnv i me = me { meAlphaEnv = pruneAlphaEnv i (meAlphaEnv me) }

------------------------------------------------------------------------

-- TODO: Maybe a -> a ??? -- we never need to delete
type A a = Maybe a -> Maybe a

missingSyntax :: String -> a
missingSyntax constructor = error $ unlines
  [ "Missing syntax support: " ++ constructor
  , "Please file an issue at https://github.com/facebookincubator/retrie/issues"
  , "with an example of the rewrite you are attempting and we'll add it."
  ]

toA :: PatternMap m => (m a -> m a) -> A (m a)
toA f = Just . f . fromMaybe mEmpty

toAList :: A a -> A [a]
toAList f Nothing = (:[]) <$> f Nothing
toAList f (Just xs) = Just $ mapMaybe (f . Just) xs

unionOn :: PatternMap m => (a -> m b) -> a -> a -> m b
unionOn f m1 m2 = mUnion (f m1) (f m2)

------------------------------------------------------------------------

class PatternMap m where
  type Key m :: *

  mEmpty :: m a
  mUnion :: m a -> m a -> m a

  mAlter :: AlphaEnv -> Quantifiers -> Key m -> A a -> m a -> m a
  mMatch :: MatchEnv -> Key m -> (Substitution, m a) -> [(Substitution, a)]

-- Useful to get the chain started in mMatch
mapFor :: (b -> c) -> (a, b) -> [(a, c)]
mapFor f (hs,m) = [(hs, f m)]

-- Useful for using existing lookup functions in mMatch
maybeMap :: (b -> Maybe c) -> (a, b) -> [(a, c)]
maybeMap f (hs,m) = maybeToList $ (hs,) <$> f m

maybeListMap :: (b -> Maybe [c]) -> (a, b) -> [(a, c)]
maybeListMap f (hs, m) = [ (a, c) | (a, cs) <- maybeMap f (hs, m), c <- cs ]

------------------------------------------------------------------------

newtype MaybeMap a = MaybeMap [a]
  deriving (Functor)

instance PatternMap MaybeMap where
  type Key MaybeMap = ()

  mEmpty :: MaybeMap a
  mEmpty = MaybeMap []

  mUnion :: MaybeMap a -> MaybeMap a -> MaybeMap a
  mUnion (MaybeMap m1) (MaybeMap m2) = MaybeMap $ m1 ++ m2

  mAlter :: AlphaEnv -> Quantifiers -> Key MaybeMap -> A a -> MaybeMap a -> MaybeMap a
  mAlter _ _ () f (MaybeMap []) = MaybeMap $ maybeToList $ f Nothing
  mAlter _ _ () f (MaybeMap xs) = MaybeMap $ mapMaybe (f . Just) xs

  mMatch
    :: MatchEnv
    -> Key MaybeMap
    -> (Substitution, MaybeMap a)
    -> [(Substitution, a)]
  mMatch _ () (hs, MaybeMap xs) = map (hs,) xs

------------------------------------------------------------------------

data ListMap m a = ListMap
  { lmNil  :: MaybeMap a
  , lmCons :: m (ListMap m a)
  }
  deriving (Functor)

instance PatternMap m => PatternMap (ListMap m) where
  type Key (ListMap m) = [Key m]

  mEmpty :: ListMap m a
  mEmpty = ListMap mEmpty mEmpty

  mUnion :: ListMap m a -> ListMap m a -> ListMap m a
  mUnion m1 m2 = ListMap
    { lmNil = unionOn lmNil m1 m2
    , lmCons = unionOn lmCons m1 m2
    }

  mAlter :: AlphaEnv -> Quantifiers -> Key (ListMap m) -> A a -> ListMap m a -> ListMap m a
  mAlter env vs []     f m = m { lmNil  = mAlter env vs () f (lmNil m) }
  mAlter env vs (x:xs) f m = m { lmCons = mAlter env vs x (toA (mAlter env vs xs f)) (lmCons m) }

  mMatch :: MatchEnv -> Key (ListMap m) -> (Substitution, ListMap m a) -> [(Substitution, a)]
  mMatch env []     = mapFor lmNil >=> mMatch env ()
  mMatch env (x:xs) = mapFor lmCons >=> mMatch env x >=> mMatch env xs

------------------------------------------------------------------------

findMatch :: PatternMap m => MatchEnv -> Key m -> m a -> [(Substitution, a)]
findMatch env k m = mMatch env k (emptySubst, m)

insertMatch :: PatternMap m => AlphaEnv -> Quantifiers -> Key m -> a -> m a -> m a
insertMatch env vs k x = mAlter env vs k (const (Just x))
