-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Retrie.Universe
  ( Universe
  , printU
  , Matchable(..)
  , UMap(..)
  ) where

import Control.Monad
import Data.Data

import Retrie.AlphaEnv
import Retrie.ExactPrint
import Retrie.GHC
import Retrie.PatternMap.Class
import Retrie.PatternMap.Instances
import Retrie.Quantifiers
import Retrie.Substitution

-- | A sum type to collect all possible top-level rewritable types.
data Universe
  = ULHsExpr (LHsExpr GhcPs)
  | ULStmt (LStmt GhcPs (LHsExpr GhcPs))
  | ULType (LHsType GhcPs)
  | ULPat (LPat GhcPs)
  deriving (Data)

-- | Exactprint an annotated 'Universe'.
printU :: Annotated Universe -> String
printU u = exactPrintU (astA u)

-- | Primitive exactprint for 'Universe'.
exactPrintU :: Universe -> String
exactPrintU (ULHsExpr e) = exactPrint e
exactPrintU (ULStmt s) = exactPrint s
exactPrintU (ULType t) = exactPrint t
exactPrintU (ULPat p) = exactPrint p

-------------------------------------------------------------------------------

-- | Class of types which can be injected into the 'Universe' type.
class Matchable ast where
  -- | Inject an AST into 'Universe'
  inject :: ast -> Universe

  -- | Project an AST from a 'Universe'.
  -- Can fail if universe contains the wrong type.
  project :: Universe -> ast

  -- | Get the original location of the AST.
  getOrigin :: ast -> SrcSpan

instance Matchable Universe where
  inject = id
  project = id
  getOrigin (ULHsExpr e) = getOrigin e
  getOrigin (ULStmt s) = getOrigin s
  getOrigin (ULType t) = getOrigin t
  getOrigin (ULPat p) = getOrigin p

instance Matchable (LocatedA (HsExpr GhcPs)) where
  inject = ULHsExpr
  project (ULHsExpr x) = x
  project _ = error "project LHsExpr"
  getOrigin e = getLocA e

instance Matchable (LocatedA (Stmt GhcPs (LocatedA (HsExpr GhcPs)))) where
  inject = ULStmt
  project (ULStmt x) = x
  project _ = error "project LStmt"
  getOrigin e = getLocA e

instance Matchable (LocatedA (HsType GhcPs)) where
  inject = ULType
  project (ULType t) = t
  project _ = error "project ULType"
  getOrigin e = getLocA e

instance Matchable (LocatedA (Pat GhcPs)) where
  inject = ULPat
  project (ULPat p) = p
  project _ = error "project ULPat"
  getOrigin = getLocA

-------------------------------------------------------------------------------

-- | The pattern map for 'Universe'.
data UMap a = UMap
  { umExpr :: EMap a
  , umStmt :: SMap a
  , umType :: TyMap a
  , umPat  :: PatMap a
  }
  deriving (Functor)

instance PatternMap UMap where
  type Key UMap = Universe

  mEmpty :: UMap a
  mEmpty = UMap mEmpty mEmpty mEmpty mEmpty

  mUnion :: UMap a -> UMap a -> UMap a
  mUnion m1 m2 = UMap
    (unionOn umExpr m1 m2)
    (unionOn umStmt m1 m2)
    (unionOn umType m1 m2)
    (unionOn umPat m1 m2)

  mAlter :: AlphaEnv -> Quantifiers -> Universe -> A a -> UMap a -> UMap a
  mAlter env vs u f m = go u
    where
      go (ULHsExpr e) = m { umExpr = mAlter env vs e f (umExpr m) }
      go (ULStmt s) = m { umStmt = mAlter env vs s f (umStmt m) }
      go (ULType t) = m { umType = mAlter env vs t f (umType m) }
      go (ULPat p) = m { umPat  = mAlter env vs (cLPat p) f (umPat m) }

  mMatch :: MatchEnv -> Universe -> (Substitution, UMap a) -> [(Substitution, a)]
  mMatch env = go
    where
      go (ULHsExpr e) = mapFor umExpr >=> mMatch env e
      go (ULStmt s) = mapFor umStmt >=> mMatch env s
      go (ULType t) = mapFor umType >=> mMatch env t
      go (ULPat p) = mapFor umPat >=> mMatch env (cLPat p)
