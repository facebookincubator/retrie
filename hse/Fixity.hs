-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
module Fixity
  ( defaultFixityEnv
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

import Retrie.Fixity
import Retrie.GHC

defaultFixityEnv :: FixityEnv
defaultFixityEnv = mkFixityEnv $ map hseToGHC HSE.baseFixities

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