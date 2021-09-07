-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Annotated (annotatedTest) where

import Control.Monad.State.Lazy
import Data.Data
import Data.Generics
-- import qualified Data.Map as M
-- import qualified Data.Set as S
-- import Data.Maybe
import qualified GHC.Paths as GHC.Paths
import Test.HUnit

import Retrie.ExactPrint
import Retrie.GHC

annotatedTest :: Test
annotatedTest = TestLabel "Annotated" $ TestList
  [ increasingSeedTest
  -- , elemsPostGraftTest
  , inverseTest
  , uniqueSrcSpanTest
  , trimTest
  ]

exprs :: [String]
exprs =
  [  "3 + x"
  , "let _ = \\_ -> 4 in 7"
  , "case x of { y -> y }"
  , "let x = y in z"
  , unlines
    [ "case (3, 4) of"
    , "  (x, 5) -> (5, x)"
    , "  (_, y) -> (y, y)"
    ]
  , unlines
    [ "let f :: Int -> Int"
    , "    f x = x + 3"
    , "    y = 4"
    , "in f y + f y"
    ]
  ]

types :: [String]
types =
  [ "Int -> Int"
  , "Data a => a -> Int"
  , "(Eq a, Eq b) => (a -> b, b -> a)"
  ]

-- Run test on all ASTs parsed from the above lists
forAst :: (forall a. Data a => Annotated a -> IO ()) -> IO ()
forAst f = do
  let libdir = GHC.Paths.libdir
  mapM_ (parseExpr libdir >=> f) exprs
  mapM_ (parseType libdir >=> f) types

-- Repeat a single transformation multiple times on an ast. The ast returned
-- from the previous transformation is passed to the next transformation.
testChainedTransforms :: (forall a. Data a => a -> TransformT IO a) -> IO ()
testChainedTransforms f = forAst $ \at -> do
  _ <- fmap astA $ transformA at (f >=> f >=> f >=> f)
  return ()

increasingSeedTest :: Test
increasingSeedTest = TestLabel "graft increases seed" $ TestCase $
  testChainedTransforms transform
  where
    transform :: Data a => a -> TransformT IO a
    transform = transformWithSeedIncreaseCheck . (pruneA >=> graftA)

-- Following a graft, the annotation map in the state has the expected elements
-- elemsPostGraftTest :: Test
-- elemsPostGraftTest = TestLabel "Expected elems in map" $ TestCase $
--   testChainedTransforms transform
--   where
--     transform :: Data a => a -> TransformT IO a
--     transform t = do
--       annsPreGraft <- gets fst
--       at <- pruneA t
--       t' <- graftA at
--       annsPostGraft <- gets fst
--       lift $ liftIO $ do
--         assertCountMaintained annsPreGraft t annsPostGraft
--         assertNoOverwrite annsPreGraft annsPostGraft
--         assertExactPrintAnns annsPreGraft annsPostGraft
--       return t'

inverseTest :: Test
inverseTest = TestLabel "graftA and pruneA are inverse" $ TestCase $
  testChainedTransforms transform
  where
    transform :: Data a => a -> TransformT IO a
    transform t = do
      -- anns <- gets fst
      at <- pruneA t
      t' <- graftA at
      -- anns' <- gets fst
      -- lift $ liftIO $
      --   assertAstsEqual "ast pre-graft is same as ast post-graft"
      --     (anns, t)
      --     (anns', t')
      return t'

uniqueSrcSpanTest :: Test
uniqueSrcSpanTest = TestLabel "unique src span" $ TestCase $
  fmap astA $ transformA (mempty :: Annotated ()) $ \() -> do
    ss <- transformWithSeedIncreaseCheck uniqueSrcSpanT
    lift $ liftIO $ assertGoodSrcSpan ss

trimTest :: Test
trimTest = TestLabel "trimA" $ TestCase $
  forAst $ \at ->
    let at' = trimA at in
    assertLocsReplaced (astA at')

transformWithSeedIncreaseCheck :: TransformT IO a -> TransformT IO a
transformWithSeedIncreaseCheck m = do
  seed <- get
  x <- m
  seed' <- get
  lift $ liftIO $ assertBool "transform increases seed" (seed' > seed)
  return x

-- Creates a query that returns the result of applying q to the argument (if the
-- argument is a GenLocated node containing a SrcSpan), otherwise returning
-- the provided default value.
locatedQ :: forall b. b -> (forall a. Data a => Located a -> b) -> GenericQ b
locatedQ defaultVal q = const defaultVal `ext2Q` query
  where
    query :: (Data loc, Data a) => GenLocated loc a -> b
    query (L l t) =
      case cast l :: Maybe SrcSpan of
        Nothing -> defaultVal
        Just ss -> q (L ss t)

-- -- Structure of HsExpr AST, including constructor names and annotations
-- -- associated with SrcSpan locations.
-- data ConTree = ConNode AnnConName (Maybe Annotation) [ConTree]
--   deriving (Eq, Show)

-- -- Assert ast equality (up to src span location labeling)
-- assertAstsEqual :: Data a => String -> (Anns, a) -> (Anns, a) -> IO ()
-- assertAstsEqual msg (anns1, t1) (anns2, t2) =
--   assertEqual msg (conTree anns1 t1) (conTree anns2 t2)
--   where
--     conTree :: Data a => Anns -> a -> ConTree
--     conTree anns = loop
--       where
--         loop :: Data a => a -> ConTree
--         loop t = ConNode (annGetConstr t) (annQ t) (gmapQ loop t)

--         annQ :: GenericQ (Maybe Annotation)
--         annQ = locatedQ Nothing $ \loc -> M.lookup (mkAnnKey loc) anns

-- Assert that all locations in the updated ast are generated by uniqueSrcSpanT
assertLocsReplaced :: Data a => a -> IO ()
assertLocsReplaced = everything (>>) assertReplaced
  where
    assertReplaced :: GenericQ (IO ())
    assertReplaced = locatedQ (return ()) $ \(L ss _) -> assertGoodSrcSpan ss

-- -- Assert that every location in the ast has been added to the pre-graft
-- -- annotations to form the post-graft annotations.
-- assertCountMaintained :: Data a => Anns -> a -> Anns -> IO ()
-- assertCountMaintained annsPreGraft t annsPostGraft =
--   let numAnnsAdded = everything (+) countIfInAnns t in
--   assertEqual
--     "sum of pre-graft size and # of SrcSpan sites in AST equals post-graft size"
--     (M.size annsPreGraft + numAnnsAdded)
--     (M.size annsPostGraft)
--   where
--     countIfInAnns :: GenericQ Int
--     countIfInAnns = locatedQ 0 $ \loc ->
--       if M.member (mkAnnKey loc) annsPreGraft then 1 else 0

-- -- Check that no data in pre-graft map was overwritten.
-- assertNoOverwrite :: Anns -> Anns -> IO ()
-- assertNoOverwrite annsPreGraft annsPostGraft =
--   assertEqual "pre-graft keys correspond to same data as post-graft"
--     dataPreGraft
--     dataPostGraft
--   where
--     dataPreGraft = M.toList annsPreGraft
--     dataPostGraft = mapMaybe (\(k, _) -> do
--         v <- M.lookup k annsPostGraft
--         return (k, v))
--       dataPreGraft

-- -- Assert that the annotation keys corresponding to newly-added data are of the
-- -- expected form.
-- assertExactPrintAnns :: Anns -> Anns -> IO ()
-- assertExactPrintAnns annsPreGraft annsPostGraft =
--   forM_ newKeys $ \(AnnKey ss _) ->
-- #if __GLASGOW_HASKELL__ < 900
--     assertGoodSrcSpan ss
-- #else
--     assertGoodRealSrcSpan ss
-- #endif
--   where
--     newKeys :: S.Set AnnKey
--     newKeys = M.keysSet annsPostGraft `S.difference` M.keysSet annsPreGraft

assertGoodSrcSpan :: SrcSpan -> IO ()
assertGoodSrcSpan srcSpan =
  case getRealSpan srcSpan of
    Just rss -> assertGoodRealSrcSpan rss
    Nothing ->
      assertFailure "only real src spans should be generated"

assertGoodRealSrcSpan :: RealSrcSpan -> IO ()
assertGoodRealSrcSpan rss = do
  assertGoodSrcLoc (realSrcSpanStart rss)
  assertGoodSrcLoc (realSrcSpanEnd rss)

assertGoodSrcLoc :: RealSrcLoc -> IO ()
assertGoodSrcLoc srcLoc = do
  let
    file = unpackFS $ srcLocFile srcLoc
    line = srcLocLine srcLoc
  assertEqual "srcLoc file is correctly named" "ghc-exactprint" file
  assertEqual "srcLoc line is correctly placed" (-1) line
