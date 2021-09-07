-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE RankNTypes #-}
module Retrie.Fixity
  ( FixityEnv
  , mkFixityEnv
  , lookupOp
  , lookupOpRdrName
  , Fixity(..)
  , FixityDirection(..)
  , extendFixityEnv
  , ppFixityEnv
  ) where

import Retrie.GHC

newtype FixityEnv = FixityEnv
  { unFixityEnv :: FastStringEnv (FastString, Fixity) }

instance Semigroup FixityEnv where
  -- | 'mappend' for 'FixityEnv' is right-biased
  (<>) = mappend

instance Monoid FixityEnv where
  mempty = mkFixityEnv []
  -- | 'mappend' for 'FixityEnv' is right-biased
  mappend (FixityEnv e1) (FixityEnv e2) = FixityEnv (plusFsEnv e1 e2)

lookupOp :: LHsExpr GhcPs -> FixityEnv -> Fixity
lookupOp (L _ e) | Just n <- varRdrName e = lookupOpRdrName n
lookupOp _ = error "lookupOp: called with non-variable!"

lookupOpRdrName :: LocatedN RdrName -> FixityEnv -> Fixity
lookupOpRdrName (L _ n) (FixityEnv env) =
  maybe defaultFixity snd $ lookupFsEnv env (occNameFS $ occName n)

mkFixityEnv :: [(FastString, (FastString, Fixity))] -> FixityEnv
mkFixityEnv = FixityEnv . mkFsEnv

extendFixityEnv :: [(FastString, Fixity)] -> FixityEnv -> FixityEnv
extendFixityEnv l (FixityEnv env) =
  FixityEnv $ extendFsEnvList env [ (fs, p) | p@(fs,_) <- l ]

ppFixityEnv :: FixityEnv -> String
ppFixityEnv = unlines . map ppFixity . eltsUFM . unFixityEnv
  where
    ppFixity (fs, Fixity _ p d) = unwords
      [ case d of
          InfixN -> "infix"
          InfixL -> "infixl"
          InfixR -> "infixr"
      , show p
      , unpackFS fs
      ]
