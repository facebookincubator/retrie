-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
-- | Provides consistent interface with ghc-exactprint.
module Retrie.ExactPrint
  ( -- * Fixity re-association
    fix
    -- * Parsers
  , parseContent
  , parseContentNoFixity
  , parseDecl
  , parseExpr
  , parseImports
  , parsePattern
  , parseStmt
  , parseType
    -- * Primitive Transformations
  , addAllAnnsT
  , cloneT
  , setEntryDPT
  , swapEntryDPT
  , transferAnnsT
  , transferEntryAnnsT
  , transferEntryDPT
    -- * Utils
  , debugDump
  , debugParse
  , hasComments
  , isComma
    -- * Annotated AST
  , module Retrie.ExactPrint.Annotated
    -- * ghc-exactprint re-exports
  , module Language.Haskell.GHC.ExactPrint
  , module Language.Haskell.GHC.ExactPrint.Annotate
  , module Language.Haskell.GHC.ExactPrint.Types
  , module Language.Haskell.GHC.ExactPrint.Utils
  ) where

import Control.Exception
import Control.Monad.State.Lazy hiding (fix)
import Data.Function (on)
import Data.List (transpose)
import Data.Maybe
import qualified Data.Map as M
import Text.Printf

import Language.Haskell.GHC.ExactPrint hiding
  ( cloneT
  , setEntryDP
  , setEntryDPT
  , transferEntryDPT
  , transferEntryDP
  )
import Language.Haskell.GHC.ExactPrint.Annotate (Annotate)
import qualified Language.Haskell.GHC.ExactPrint.Parsers as Parsers
import Language.Haskell.GHC.ExactPrint.Types
  ( AnnConName(..)
  , DeltaPos(..)
  , KeywordId(..)
  , annGetConstr
  , annNone
  , emptyAnns
  , mkAnnKey
  )
import Language.Haskell.GHC.ExactPrint.Utils (annLeadingCommentEntryDelta, showGhc)

import Retrie.ExactPrint.Annotated
import Retrie.Fixity
import Retrie.GHC
import Retrie.SYB

-- Fixity traversal -----------------------------------------------------------

-- | Re-associate AST using given 'FixityEnv'. (The GHC parser has no knowledge
-- of operator fixity, because that requires running the renamer, so it parses
-- all operators as left-associated.)
fix :: (Data ast, Monad m) => FixityEnv -> ast -> TransformT m ast
fix env = fixAssociativity >=> fixEntryDP
  where
    fixAssociativity = everywhereM (mkM (fixOneExpr env) `extM` fixOnePat env)
    fixEntryDP = everywhereM (mkM fixOneEntryExpr `extM` fixOneEntryPat)

-- Should (x op1 y) op2 z be reassociated as x op1 (y op2 z)?
associatesRight :: Fixity -> Fixity -> Bool
associatesRight (Fixity _ p1 a1) (Fixity _ p2 _a2) =
  p2 > p1 || p1 == p2 && a1 == InfixR

-- We know GHC produces left-associated chains, so 'z' is never an
-- operator application. We also know that this will be applied bottom-up
-- by 'everywhere', so we can assume the children are already fixed.
fixOneExpr
  :: Monad m
  => FixityEnv
  -> LHsExpr GhcPs
  -> TransformT m (LHsExpr GhcPs)
#if __GLASGOW_HASKELL__ < 806
fixOneExpr env (L l2 (OpApp ap1@(L l1 (OpApp x op1 f1 y)) op2 f2 z))
  | associatesRight (lookupOp op1 env) (lookupOp op2 env) = do
    let ap2' = L l2 $ OpApp y op2 f2 z
    swapEntryDPT ap1 ap2'
    transferAnnsT isComma ap2' ap1
    rhs <- fixOneExpr env ap2'
    return $ L l1 $ OpApp x op1 f1 rhs
#else
fixOneExpr env (L l2 (OpApp x2 ap1@(L l1 (OpApp x1 x op1 y)) op2 z))
  | associatesRight (lookupOp op1 env) (lookupOp op2 env) = do
    let ap2' = L l2 $ OpApp x2 y op2 z
    swapEntryDPT ap1 ap2'
    transferAnnsT isComma ap2' ap1
    rhs <- fixOneExpr env ap2'
    return $ L l1 $ OpApp x1 x op1 rhs
#endif
fixOneExpr _ e = return e

fixOnePat :: Monad m => FixityEnv -> LPat GhcPs -> TransformT m (LPat GhcPs)
#if __GLASGOW_HASKELL__ == 808
fixOnePat env (dL -> L l2 (ConPatIn op2 (InfixCon (dL -> ap1@(L l1 (ConPatIn op1 (InfixCon x y)))) z)))
  | associatesRight (lookupOpRdrName op1 env) (lookupOpRdrName op2 env) = do
    let ap2' = L l2 (ConPatIn op2 (InfixCon y z))
    swapEntryDPT ap1 ap2'
    transferAnnsT isComma ap2' ap1
    rhs <- fixOnePat env (composeSrcSpan ap2')
    return $ cL l1 (ConPatIn op1 (InfixCon x rhs))
#else
fixOnePat env (L l2 (ConPatIn op2 (InfixCon ap1@(L l1 (ConPatIn op1 (InfixCon x y))) z)))
  | associatesRight (lookupOpRdrName op1 env) (lookupOpRdrName op2 env) = do
    let ap2' = L l2 (ConPatIn op2 (InfixCon y z))
    swapEntryDPT ap1 ap2'
    transferAnnsT isComma ap2' ap1
    rhs <- fixOnePat env ap2'
    return $ L l1 (ConPatIn op1 (InfixCon x rhs))
#endif
fixOnePat _ e = return e

-- Move leading whitespace from the left child of an operator application
-- to the application itself. We need this so we have correct offsets when
-- substituting into patterns and don't end up with extra leading spaces.
-- We can assume it is run bottom-up, and that precedence is already fixed.
fixOneEntry
  :: (Monad m, Data a)
  => Located a -- ^ Overall application
  -> Located a -- ^ Left child
  -> TransformT m (Located a)
fixOneEntry e x = do
  anns <- getAnnsT
  let
    zeros = DP (0,0)
    (DP (xr,xc), DP (actualRow,_)) =
      case M.lookup (mkAnnKey x) anns of
        Nothing -> (zeros, zeros)
        Just ann -> (annLeadingCommentEntryDelta ann, annEntryDelta ann)
    DP (er,ec) =
      maybe zeros annLeadingCommentEntryDelta $ M.lookup (mkAnnKey e) anns
  when (actualRow == 0) $ do
    setEntryDPT e $ DP (er, xc + ec)
    setEntryDPT x $ DP (xr, 0)
  return e

fixOneEntryExpr :: Monad m => LHsExpr GhcPs -> TransformT m (LHsExpr GhcPs)
#if __GLASGOW_HASKELL__ < 806
fixOneEntryExpr e@(L _ (OpApp x _ _ _)) = fixOneEntry e x
#else
fixOneEntryExpr e@(L _ (OpApp _ x _ _)) = fixOneEntry e x
#endif
fixOneEntryExpr e = return e

fixOneEntryPat :: Monad m => LPat GhcPs -> TransformT m (LPat GhcPs)
#if __GLASGOW_HASKELL__ == 808
fixOneEntryPat p@(ConPatIn _ (InfixCon x _)) =
  composeSrcSpan <$> fixOneEntry (dL p) (dL x)
#else
fixOneEntryPat p@(L _ (ConPatIn _ (InfixCon x _))) = fixOneEntry p x
#endif
fixOneEntryPat p = return p

-------------------------------------------------------------------------------

swapEntryDPT
  :: (Data a, Data b, Monad m)
  => Located a -> Located b -> TransformT m ()
swapEntryDPT a b = modifyAnnsT $ \ anns ->
  let akey = mkAnnKey a
      bkey = mkAnnKey b
      aann = fromMaybe annNone $ M.lookup akey anns
      bann = fromMaybe annNone $ M.lookup bkey anns
  in M.insert akey
      aann { annEntryDelta = annEntryDelta bann
           , annPriorComments = annPriorComments bann } $
     M.insert bkey
      bann { annEntryDelta = annEntryDelta aann
           , annPriorComments = annPriorComments aann } anns

-------------------------------------------------------------------------------

-- Compatibility module with ghc-exactprint

parseContentNoFixity :: FilePath -> String -> IO AnnotatedModule
parseContentNoFixity fp str = do
  r <- Parsers.parseModuleFromString fp str
  case r of
    Left msg -> do
#if __GLASGOW_HASKELL__ < 810
      fail $ show msg
#else
      join $ Parsers.withDynFlags $ \dflags -> printBagOfErrors dflags msg
      fail "parse failed"
#endif
    Right (anns, m) -> return $ unsafeMkA m anns 0

parseContent :: FixityEnv -> FilePath -> String -> IO AnnotatedModule
parseContent fixities fp =
  parseContentNoFixity fp >=> (`transformA` fix fixities)

-- | Parse import statements. Each string must be a full import statement,
-- including the keyword 'import'. Supports full import syntax.
parseImports :: [String] -> IO AnnotatedImports
parseImports []      = return mempty
parseImports imports = do
  -- imports start on second line, so delta offsets are correct
  am <- parseContentNoFixity "parseImports" $ "\n" ++ unlines imports
  ais <- transformA am $ pure . hsmodImports . unLoc
  return $ trimA ais

-- | Parse a top-level 'HsDecl'.
parseDecl :: String -> IO AnnotatedHsDecl
parseDecl = parseHelper "parseDecl" Parsers.parseDecl

-- | Parse a 'HsExpr'.
parseExpr :: String -> IO AnnotatedHsExpr
parseExpr = parseHelper "parseExpr" Parsers.parseExpr

-- | Parse a 'Pat'.
parsePattern :: String -> IO AnnotatedPat
parsePattern = parseHelper "parsePattern" p
  where
#if __GLASGOW_HASKELL__ < 808
    p = Parsers.parsePattern
#else
    p flags fp str = fmap dL <$> Parsers.parsePattern flags fp str
#endif

-- | Parse a 'Stmt'.
parseStmt :: String -> IO AnnotatedStmt
parseStmt = parseHelper "parseStmt" Parsers.parseStmt

-- | Parse a 'HsType'.
parseType :: String -> IO AnnotatedHsType
parseType = parseHelper "parseType" Parsers.parseType

parseHelper :: FilePath -> Parsers.Parser a -> String -> IO (Annotated a)
parseHelper fp parser str = join $ Parsers.withDynFlags $ \dflags ->
  case parser dflags fp str of
#if __GLASGOW_HASKELL__ < 810
    Left (_, msg) -> throwIO $ ErrorCall msg
#else
    Left errBag -> do
      printBagOfErrors dflags errBag
      throwIO $ ErrorCall "parse failed"
#endif
    Right (anns, x) -> return $ unsafeMkA x anns 0

-------------------------------------------------------------------------------

debugDump :: Annotate a => Annotated (Located a) -> IO ()
debugDump ax = do
  let
    str = printA ax
    maxCol = maximum $ map length $ lines str
    (tens, ones) =
      case transpose [printf "%2d" i | i <- [1 .. maxCol]] of
        [ts, os] -> (ts, os)
        _ -> ("", "")
  putStrLn $ unlines
    [ show k ++ "\n  " ++ show v | (k,v) <- M.toList (annsA ax) ]
  putStrLn tens
  putStrLn ones
  putStrLn str

cloneT :: (Data a, Typeable a, Monad m) => a -> TransformT m a
cloneT e = getAnnsT >>= flip graftT e

-- The following definitions are all the same as the ones from ghc-exactprint,
-- but the types are liberalized from 'Transform a' to 'TransformT m a'.
transferEntryAnnsT
  :: (Data a, Data b, Monad m)
  => (KeywordId -> Bool)        -- transfer Anns matching predicate
  -> Located a                  -- from
  -> Located b                  -- to
  -> TransformT m ()
transferEntryAnnsT p a b = do
  transferEntryDPT a b
  transferAnnsT p a b

-- | 'Transform' monad version of 'transferEntryDP'
transferEntryDPT
  :: (Data a, Data b, Monad m)
  => Located a -> Located b -> TransformT m ()
transferEntryDPT a b =
  modifyAnnsT (transferEntryDP a b)

-- This function fails if b is not in Anns, which seems dumb, since we are inserting it.
transferEntryDP :: (Data a, Data b) => Located a -> Located b -> Anns -> Anns
transferEntryDP a b anns = setEntryDP b dp anns'
  where
    maybeAnns = do -- Maybe monad
      anA <- M.lookup (mkAnnKey a) anns
      let anB = M.findWithDefault annNone (mkAnnKey b) anns
          anB' = anB { annEntryDelta = DP (0,0) }
      return (M.insert (mkAnnKey b) anB' anns, annLeadingCommentEntryDelta anA)
    (anns',dp) = fromMaybe
                  (error $ "transferEntryDP: lookup failed: " ++ show (mkAnnKey a))
                  maybeAnns

addAllAnnsT
  :: (Data a, Data b, Monad m)
  => Located a -> Located b -> TransformT m ()
addAllAnnsT a b =
  modifyAnnsT (addAllAnns a b)

addAllAnns :: (Data a, Data b) => Located a -> Located b -> Anns -> Anns
addAllAnns a b anns =
  fromMaybe
    (error $ "addAllAnns: lookup failed: " ++ show (mkAnnKey a)
      ++ " or " ++ show (mkAnnKey b))
    $ do ann <- M.lookup (mkAnnKey a) anns
         case M.lookup (mkAnnKey b) anns of
           Just ann' -> return $ M.insert (mkAnnKey b) (ann `annAdd` ann') anns
           Nothing -> return $ M.insert (mkAnnKey b) ann anns
  where annAdd ann ann' = ann'
          { annEntryDelta = annEntryDelta ann
          , annPriorComments = ((++) `on` annPriorComments) ann ann'
          , annFollowingComments = ((++) `on` annFollowingComments) ann ann'
          , annsDP = ((++) `on` annsDP) ann ann'
          }

isComma :: KeywordId -> Bool
isComma (G AnnComma) = True
isComma _ = False

isCommentKeyword :: KeywordId -> Bool
isCommentKeyword (AnnComment _) = True
isCommentKeyword _ = False

isCommentAnnotation :: Annotation -> Bool
isCommentAnnotation Ann{..} =
  (not . null $ annPriorComments)
  || (not . null $ annFollowingComments)
  || any (isCommentKeyword . fst) annsDP

hasComments :: (Data a, Monad m) => Located a -> TransformT m Bool
hasComments e = do
  anns <- getAnnsT
  let b = isCommentAnnotation <$> M.lookup (mkAnnKey e) anns
  return $ fromMaybe False b

transferAnnsT
  :: (Data a, Data b, Monad m)
  => (KeywordId -> Bool)        -- transfer Anns matching predicate
  -> Located a                  -- from
  -> Located b                  -- to
  -> TransformT m ()
transferAnnsT p a b = modifyAnnsT f
  where
    bKey = mkAnnKey b
    f anns = fromMaybe anns $ do
      anA <- M.lookup (mkAnnKey a) anns
      anB <- M.lookup bKey anns
      let anB' = anB { annsDP = annsDP anB ++ filter (p . fst) (annsDP anA) }
      return $ M.insert bKey anB' anns

-- | 'Transform' monad version of 'getEntryDP'
setEntryDPT
  :: (Data a, Monad m)
  => Located a -> DeltaPos -> TransformT m ()
setEntryDPT ast dp = do
  modifyAnnsT (setEntryDP ast dp)

-- | The setEntryDP that comes with exactprint does some really confusing
-- entry math around comments that I'm not convinced is either correct or useful.
setEntryDP :: Data a => Located a -> DeltaPos -> Anns -> Anns
setEntryDP x dp anns = M.alter (Just . f . fromMaybe annNone) k anns
  where
    k = mkAnnKey x
    f ann = case annPriorComments ann of
              []       -> ann { annEntryDelta = dp }
              (c,_):cs -> ann { annPriorComments = (c,dp):cs }

-- Useful for figuring out what annotations should be on something.
debugParse :: FixityEnv -> String -> IO ()
debugParse fixityEnv s = do
  writeFile "debug.txt" s
  r <- parseModule "debug.txt"
  case r of
    Left _ -> putStrLn "parse failed"
    Right (anns, modl) -> do
      let m = unsafeMkA modl anns 0
      putStrLn "parseModule"
      debugDump m
      void $ transformDebug m
  where
    transformDebug =
      run "fixOneExpr D.def" (fixOneExpr fixityEnv)
        >=> run "fixOnePat D.def" (fixOnePat fixityEnv)
        >=> run "fixOneEntryExpr" fixOneEntryExpr
        >=> run "fixOneEntryPat" fixOneEntryPat

    run wat f m = do
      putStrLn wat
      m' <- transformA m (everywhereM (mkM f))
      debugDump m'
      return m'
