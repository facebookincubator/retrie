-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
module Retrie.Quantifiers
  ( Quantifiers
  , emptyQs
  , exceptQ
  , isQ
  , mkQs
  , mkFSQs
  , qList
  , qSet
  , unionQ
  ) where

import GHC.Exts (IsList(..))
import Retrie.GHC

------------------------------------------------------------------------

-- Note [Why not RdrNames?]
-- RdrNames carry their namespace in their OccName. The unification of holes
-- already handles the namespace more finely, so the extra distinction inside the
-- RdrName is just a pain when manipulating the substitution, checking for
-- equality, etc.

-- Thus, Quantifiers are keyed on FastString (an OccName is a namespace plus
-- FastString, so this is just the OccName without its namespace).

instance IsList Quantifiers where
  type Item Quantifiers = String

  fromList = mkFSQs . map mkFastString
  toList = map unpackFS . qList

-- | 'Quantifiers' is a set of variable names. If you enable the
-- "OverloadedLists" language extension, you can construct using a literal
-- list of strings.
newtype Quantifiers = Quantifiers
  { qSet :: UniqSet FastString
    -- ^ Convert to a 'UniqSet'.
  }
instance Show Quantifiers where
  show qs = "Quantifiers " ++ show (qList qs)

-- | Construct from GHC's 'RdrName's.
mkQs :: [RdrName] -> Quantifiers
mkQs = mkFSQs . map rdrFS

-- | Construct from 'FastString's.
mkFSQs :: [FastString] -> Quantifiers
mkFSQs = Quantifiers . mkUniqSet

-- | The empty set.
emptyQs :: Quantifiers
emptyQs = Quantifiers emptyUniqSet

-- | Existence check.
isQ :: RdrName -> Quantifiers -> Bool
isQ r (Quantifiers s) = elementOfUniqSet (rdrFS r) s

-- | Set union.
unionQ :: Quantifiers -> Quantifiers -> Quantifiers
unionQ (Quantifiers s) (Quantifiers t) = Quantifiers $ unionUniqSets s t

-- | Remove a set of 'RdrName's from the set.
exceptQ :: Quantifiers -> [RdrName] -> Quantifiers
exceptQ (Quantifiers s) rs =
  Quantifiers $ delListFromUniqSet s (map rdrFS rs)

-- | Convert to a list.
qList :: Quantifiers -> [FastString]
qList (Quantifiers s) = nonDetEltsUniqSet s
