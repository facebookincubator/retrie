-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
module Retrie.AlphaEnv
  ( AlphaEnv
  , alphaEnvOffset
  , emptyAlphaEnv
  , extendAlphaEnv
  , lookupAlphaEnv
  , pruneAlphaEnv
  -- ** For Internal Use Only
  , extendAlphaEnvInternal
  ) where

import Retrie.GHC

-- | Environment used to implement alpha-equivalence checking. As we pass a
-- binder we map it to a de-bruijn index. When we later encounter a variable
-- occurrence, we look it up in the map, and if present, use the index for
-- matching, rather than the name.
data AlphaEnv = AE
  { _aeNext :: !Int -- ^ Name supply for de-bruijn indices
  , aeEnv :: OccEnv Int -- ^ Map from OccName of binder to de-bruijn index
  , aeOffset :: !Int -- ^ Initial index offset, see Note [AlphaEnv Offset]
  }

-- Note [AlphaEnv Offset]
-- The offset is used to prevent matching under a local binding. This is best
-- explained by example. Consider this code:
--
--   let map f xs = xs
--   in map (g . h) xs
--
-- If we were to apply the map fusion rule [map (f . g) xs = map f (map g xs)]
-- to this module, we would not want to match in the body of the 'let', because
-- 'map' no longer means what it meant where the rewrite was specified.
--
-- Without the offset, de-bruijn indexing would start at the redex that matches
-- the rewrite [map (g . h) xs] and would be blind to the fact that 'map' was
-- locally redefined.
--
-- To solve this, we carry an AlphaEnv in the Context from the very top of the
-- traversal, and bump this offset each time we extend the environment. Then,
-- during matching, when we encounter 'map', it will have an index (a negative
-- one, see 'lookupAlphaEnv'), so we know it has been locally redefined and the
-- negative index will prevent it from matching any other index (because all
-- indices in the constructed PatternMap are positive).

alphaEnvOffset :: AlphaEnv -> Int
alphaEnvOffset = aeOffset

emptyAlphaEnv :: AlphaEnv
emptyAlphaEnv = AE 0 emptyOccEnv 0

-- | For internal use of PatternMap methods.
extendAlphaEnvInternal :: RdrName -> AlphaEnv -> AlphaEnv
extendAlphaEnvInternal nm (AE i env off) =
  AE (i+1) (extendOccEnv env (occName nm) i) off

-- | For external use to build an initial AlphaEnv for mMatch.
-- We add local bindings to the AlphaEnv and track an offset which
-- we subtract in lookupAlphaEnv. This prevents locally-bound variable
-- occurrences from unifying with free variables in the pattern.
extendAlphaEnv :: RdrName -> AlphaEnv -> AlphaEnv
extendAlphaEnv nm e = e' { aeOffset = aeOffset e' + 1 }
  where e' = extendAlphaEnvInternal nm e

pruneAlphaEnv :: Int -> AlphaEnv -> AlphaEnv
pruneAlphaEnv i ae = ae { aeEnv = filterOccEnv (>= i) (aeEnv ae) }

lookupAlphaEnv :: RdrName -> AlphaEnv -> Maybe Int
lookupAlphaEnv nm (AE _ env off) =
  (-) <$> lookupOccEnv env (occName nm) <*> pure off
