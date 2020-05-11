-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
module Retrie.FreeVars
  ( FreeVars
  , elemFVs
  , freeVars
  , substFVs
  ) where

import Data.Generics hiding (Fixity)

import Retrie.ExactPrint.Annotated
import Retrie.GHC
import Retrie.Quantifiers
import Retrie.Substitution

--------------------------------------------------------------------------------

newtype FreeVars = FreeVars (UniqSet FastString)

emptyFVs :: FreeVars
emptyFVs = FreeVars emptyUniqSet

instance Semigroup FreeVars where
  (<>) = mappend

instance Monoid FreeVars where
  mempty = emptyFVs
  mappend (FreeVars s1) (FreeVars s2) = FreeVars $ s1 <> s2

instance Show FreeVars where
  show (FreeVars m) = show (nonDetEltsUniqSet m)

substFVs :: Substitution -> FreeVars
substFVs = foldSubst (f . snd) emptyFVs
  where
    f (HoleExpr e) fvs = freeVars emptyQs (astA e) <> fvs
    f (HoleRdr rdr) fvs = rdrFV rdr <> fvs
    f _ fvs = fvs -- TODO(anfarmer) types?

-- | This is an over-approximation, but that is fine for our purposes.
freeVars :: (Data a, Typeable a) => Quantifiers -> a -> FreeVars
freeVars qs = everything (<>) (mkQ emptyFVs fvsExpr `extQ` fvsType)
  where
    fvsExpr :: HsExpr GhcPs -> FreeVars
    fvsExpr e
      | Just (L _ rdr) <- varRdrName e
      , not $ isQ rdr qs = rdrFV rdr
    fvsExpr _ = emptyFVs

    fvsType :: HsType GhcPs -> FreeVars
    fvsType ty
      | Just (L _ rdr) <- tyvarRdrName ty
      , not $ isQ rdr qs = rdrFV rdr
    fvsType _ = emptyFVs

elemFVs :: RdrName -> FreeVars -> Bool
elemFVs rdr (FreeVars m) = elementOfUniqSet (rdrFS rdr) m

rdrFV :: RdrName -> FreeVars
rdrFV = FreeVars . unitUniqSet . rdrFS
