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
  , defaultFixityEnv
  , extendFixityEnv
  , ppFixityEnv
  ) where

-- Note [HSE]
-- GHC's parser parses all operator applications left-associatived,
-- then fixes up the associativity in the renamer, since fixity info isn't
-- known until after name resolution.
--
-- Ideally, we'd run the module through the renamer and let it do its thing,
-- but ghc-exactprint cannot roundtrip renamed modules.
--
-- The next best thing we can do is reassociate the operators ourselves, but
-- we need fixity info. Ideally (#2) we'd rename the module and then extract
-- the info from the FixityEnv. That is a TODO. For now, lets just reuse the
-- list of base package fixities in HSE.
import qualified Language.Haskell.Exts as HSE

import Data.Default

import Retrie.GHC

newtype FixityEnv = FixityEnv
  { unFixityEnv :: FastStringEnv (FastString, Fixity) }

instance Default FixityEnv where
  def = defaultFixityEnv

defaultFixityEnv :: FixityEnv
defaultFixityEnv = mkFixityEnv HSE.baseFixities

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

lookupOpRdrName :: Located RdrName -> FixityEnv -> Fixity
lookupOpRdrName (L _ n) (FixityEnv env) =
  maybe defaultFixity snd $ lookupFsEnv env (occNameFS $ occName n)

mkFixityEnv :: [HSE.Fixity] -> FixityEnv
mkFixityEnv = FixityEnv . mkFsEnv . map hseToGHC

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

hseToGHC :: HSE.Fixity -> (FastString, (FastString, Fixity))
hseToGHC (HSE.Fixity assoc p nm) = (fs, (fs, Fixity (SourceText nm') p (dir assoc)))
  where
    dir (HSE.AssocNone _)  = InfixN
    dir (HSE.AssocLeft _)  = InfixL
    dir (HSE.AssocRight _) = InfixR

    nm' = case nm of
      HSE.Qual _ _ n -> nameStr n
      HSE.UnQual _ n -> nameStr n
      _             -> "SpecialCon"

    fs = mkFastString nm'

    nameStr (HSE.Ident _ s)  = s
    nameStr (HSE.Symbol _ s) = s
