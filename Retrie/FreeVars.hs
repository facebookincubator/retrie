-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
module Retrie.FreeVars
  ( FreeVars
  , substFVs
  , elemFVs
  , capturesFVs
  ) where

import Data.Generics hiding (Fixity)

import Retrie.ExactPrint.Annotated
import Retrie.GHC
import Retrie.Quantifiers
import Retrie.Substitution

--------------------------------------------------------------------------------

newtype FreeVars = FreeVars (OccEnv FastString)

emptyFVs :: FreeVars
emptyFVs = FreeVars emptyOccEnv

instance Semigroup FreeVars where
  (<>) = mappend

instance Monoid FreeVars where
  mempty = emptyFVs
  mappend (FreeVars m1) (FreeVars m2) = FreeVars $ plusOccEnv m2 m1

instance Show FreeVars where
  show (FreeVars m) = show (occEnvElts m)

substFVs :: Substitution -> FreeVars
substFVs = foldSubst (f . snd) emptyFVs
  where
    f (HoleExpr e) fvs = freeVars emptyQs (astA e) <> fvs
    f (HoleRdr rdr) fvs = rdrFV rdr <> fvs
    f _ fvs = fvs -- TODO(anfarmer) types?

capturesFVs :: (Data a, Typeable a) => Quantifiers -> [RdrName] -> a -> Bool
capturesFVs qs binders thing = any (`elemOccEnv` fvEnv) $ map occName binders
  where
    FreeVars fvEnv = freeVars qs thing

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
elemFVs rdr (FreeVars m) = elemOccEnv (occName rdr) m

rdrFV :: RdrName -> FreeVars
rdrFV rdr = FreeVars $ unitOccEnv (occName rdr) (rdrFS rdr)
