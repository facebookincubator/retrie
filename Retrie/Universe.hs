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
  deriving (Data)

-- | Exactprint an annotated 'Universe'.
printU :: Annotated Universe -> String
printU u = exactPrintU (astA u) (annsA u)

-- | Primitive exactprint for 'Universe'.
exactPrintU :: Universe -> Anns -> String
exactPrintU (ULHsExpr e) anns = exactPrint e anns
exactPrintU (ULStmt s) anns = exactPrint s anns
exactPrintU (ULType t) anns = exactPrint t anns

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

instance Matchable (LHsExpr GhcPs) where
  inject = ULHsExpr
  project (ULHsExpr x) = x
  project _ = error "project LHsExpr"
  getOrigin e = getLoc e

instance Matchable (LStmt GhcPs (LHsExpr GhcPs)) where
  inject = ULStmt
  project (ULStmt x) = x
  project _ = error "project LStmt"
  getOrigin e = getLoc e

instance Matchable (LHsType GhcPs) where
  inject = ULType
  project (ULType t) = t
  project _ = error "project ULType"
  getOrigin e = getLoc e

-------------------------------------------------------------------------------

-- | The pattern map for 'Universe'.
data UMap a = UMap
  { umExpr :: EMap a
  , umStmt :: SMap a
  , umType :: TyMap a
  }
  deriving (Functor)

instance PatternMap UMap where
  type Key UMap = Universe

  mEmpty :: UMap a
  mEmpty = UMap mEmpty mEmpty mEmpty

  mUnion :: UMap a -> UMap a -> UMap a
  mUnion (UMap x1 x2 x3) (UMap y1 y2 y3) =
    UMap (mUnion x1 y1) (mUnion x2 y2) (mUnion x3 y3)

  mAlter :: AlphaEnv -> Quantifiers -> Universe -> A a -> UMap a -> UMap a
  mAlter env vs u f m = go u
    where
      go (ULHsExpr e) = m { umExpr = mAlter env vs e f (umExpr m) }
      go (ULStmt s)   = m { umStmt = mAlter env vs s f (umStmt m) }
      go (ULType t)   = m { umType = mAlter env vs t f (umType m) }

  mMatch :: MatchEnv -> Universe -> (Substitution, UMap a) -> [(Substitution, a)]
  mMatch env = go
    where
      go (ULHsExpr e) = mapFor umExpr >=> mMatch env e
      go (ULStmt s)   = mapFor umStmt >=> mMatch env s
      go (ULType t)   = mapFor umType >=> mMatch env t

