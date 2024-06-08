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
  , Parsers.LibDir
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
  , swapEntryDPT
  , transferAnnsT
  , transferEntryAnnsT
  , transferEntryDPT
  , transferAnchor
    -- * Utils
  , debugDump
  , debugParse
  , debug
  , hasComments
  , isComma
    -- * Annotated AST
  , module Retrie.ExactPrint.Annotated
    -- * ghc-exactprint re-exports
  , module Language.Haskell.GHC.ExactPrint
  , module Language.Haskell.GHC.ExactPrint.Types
  , module Language.Haskell.GHC.ExactPrint.Utils
  , module Language.Haskell.GHC.ExactPrint.Transform
  ) where

import Control.Exception
import Control.Monad
import Control.Monad.State.Lazy
#if __GLASGOW_HASKELL__ < 910
   hiding (fix)
#endif
import Data.List (transpose)
import Text.Printf

import Language.Haskell.GHC.ExactPrint hiding
  (
   setEntryDP
  , transferEntryDP
  )
import Language.Haskell.GHC.ExactPrint.Utils hiding (debug)
import qualified Language.Haskell.GHC.ExactPrint.Parsers as Parsers
import Language.Haskell.GHC.ExactPrint.Types
  ( showGhc
  )
import Language.Haskell.GHC.ExactPrint.Transform

import Retrie.ExactPrint.Annotated
import Retrie.Fixity
import Retrie.GHC
import Retrie.SYB hiding (ext1)
-- #if __GLASGOW_HASKELL__ < 910
import Retrie.Util
-- #endif

import GHC.Stack
import Debug.Trace

debug :: c -> String -> c
debug c s = trace s c

-- Fixity traversal -----------------------------------------------------------

-- | Re-associate AST using given 'FixityEnv'. (The GHC parser has no knowledge
-- of operator fixity, because that requires running the renamer, so it parses
-- all operators as left-associated.)
fix :: (Data ast, MonadIO m) => FixityEnv -> ast -> TransformT m ast
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
  :: MonadIO m
  => FixityEnv
  -> LHsExpr GhcPs
  -> TransformT m (LHsExpr GhcPs)
fixOneExpr env (L l2 (OpApp x2 ap1@(L l1 (OpApp x1 x op1 y)) op2 z))
{-
  pre
  x   is [print]   4:8-12
  op1 is [$]       4:14
  y   is [foo]     4:16-18
  op2 is [`bar`]   4:20-24
  z   is [[1..10]] 4:26-32

  (L l2 (OpApp _
          (L l1 (OpApp _ x op1 y))
          op2
          z))
  -- post
  (L l2 (OpApp _
          x
          op1
          (L new_loc (OpApp _ y op2 z)))
-}

  | associatesRight (lookupOp op1 env) (lookupOp op2 env) = do
    -- lift $ liftIO $ debugPrint Loud "fixOneExpr:(l1,l2)="  [showAst (l1,l2)]
    -- We need a location from start of y to end of z
    -- let ap2' = L (stripComments l2) $ OpApp x2 y op2 z
    let ap2' :: LHsExpr GhcPs = L (noAnnSrcSpan (combineSrcSpans (locA y) (locA z)) ) $ OpApp x2 y op2 z
    -- (_ap1_0, ap2'_0) <- swapEntryDPT ap1 ap2'
    (_ap1_0, ap2'_0) <- return (ap1, ap2')
    -- lift $ liftIO $ debugPrint Loud "fixOneExpr:recursing"  []
    -- rhs <- fixOneExpr env ap2'_0
    rhs <- return ap2'_0
    -- lift $ liftIO $ debugPrint Loud "fixOneExpr:returning"  [showAst (L l2 $ OpApp x1 x op1 rhs)]
    return $ L l2 $ OpApp x1 x op1 rhs
fixOneExpr _ e = return e

fixOnePat :: Monad m => FixityEnv -> LPat GhcPs -> TransformT m (LPat GhcPs)
fixOnePat env (dLPat -> Just (L l2 (ConPat x2 op2 (InfixCon (dLPat -> Just ap1@(L l1 (ConPat ext1 op1 (InfixCon x y)))) z))))
  | associatesRight (lookupOpRdrName op1 env) (lookupOpRdrName op2 env) = do
    let ap2' = L l2 (ConPat x2 op2 (InfixCon y z))
    (_ap1_0, ap2'_0) <- swapEntryDPT ap1 ap2'
    rhs <- fixOnePat env (cLPat ap2'_0)
    return $ cLPat $ L l1 (ConPat ext1 op1 (InfixCon x rhs))
fixOnePat _ e = return e

-- TODO: move to ghc-exactprint
#if __GLASGOW_HASKELL__ >= 910
stripComments :: EpAnn an -> EpAnn an
stripComments (EpAnn anc an _) = EpAnn anc an emptyComments
#else
stripComments :: SrcAnn an -> SrcAnn an
stripComments (SrcSpanAnn EpAnnNotUsed l) = SrcSpanAnn EpAnnNotUsed l
stripComments (SrcSpanAnn (EpAnn anc an _) l) = SrcSpanAnn (EpAnn anc an emptyComments) l
#endif

-- Move leading whitespace from the left child of an operator application
-- to the application itself. We need this so we have correct offsets when
-- substituting into patterns and don't end up with extra leading spaces.
-- We can assume it is run bottom-up, and that precedence is already fixed.
fixOneEntry
  :: (MonadIO m, Data a)
  => LocatedA a -- ^ Overall application
  -> LocatedA a -- ^ Left child
  -> TransformT m (LocatedA a, LocatedA a)
fixOneEntry e x = do
  -- We assume that ghc-exactprint has converted all Anchor's to use their delta variants.
  -- Get the dp for the x component
  let xdp = entryDP x
  let xr = getDeltaLine xdp
  let xc = deltaColumn xdp
  -- Get the dp for the e component
  let edp = entryDP e
  let er = getDeltaLine edp
  let ec = deltaColumn edp
  case xdp of
    SameLine _n -> do
      lift $ liftIO $ debugPrint Loud "fixOneEntry:(xdp,edp)="  [showAst (xdp,edp)]
      lift $ liftIO $ debugPrint Loud "fixOneEntry:(dpx,dpe)="  [showAst ((deltaPos er (xc + ec)),(deltaPos xr 0))]
      lift $ liftIO $ debugPrint Loud "fixOneEntry:e'="  [showAst e]
      lift $ liftIO $ debugPrint Loud "fixOneEntry:e'="  [showAst (setEntryDP e (deltaPos er (xc + ec)))]
      return ( setEntryDP e (deltaPos er (xc + ec))
             , setEntryDP x (deltaPos xr 0))
    _ -> return (e,x)

-- TODO: move this somewhere more appropriate
entryDP :: LocatedA a -> DeltaPos
#if __GLASGOW_HASKELL__ >= 910
entryDP = getEntryDP
#else
entryDP (L (SrcSpanAnn EpAnnNotUsed _) _) = SameLine 1
entryDP (L (SrcSpanAnn (EpAnn anc _ _) _) _)
  = case anchor_op anc of
      UnchangedAnchor -> SameLine 1
      MovedAnchor dp -> dp
#endif


fixOneEntryExpr :: MonadIO m => LHsExpr GhcPs -> TransformT m (LHsExpr GhcPs)
#if __GLASGOW_HASKELL__ >= 910
fixOneEntryExpr e = return e
#else
fixOneEntryExpr e@(L _l (OpApp a x b c)) = do
  -- lift $ liftIO $ debugPrint Loud "fixOneEntryExpr:(e,x)="  [showAst (e,x)]
  (e',x') <- fixOneEntry e x
  -- lift $ liftIO $ debugPrint Loud "fixOneEntryExpr:(e',x')="  [showAst (e',x')]
  -- lift $ liftIO $ debugPrint Loud "fixOneEntryExpr:returning="  [showAst (L (getLoc e') (OpApp a x' b c))]
  return (L (getLoc e') (OpApp a x' b c))
#endif

fixOneEntryPat :: MonadIO m => LPat GhcPs -> TransformT m (LPat GhcPs)
#if __GLASGOW_HASKELL__ >= 910
fixOneEntryPat pat = return pat
#else
fixOneEntryPat pat
#if __GLASGOW_HASKELL__ < 900
  | Just p@(L l (ConPatIn a (InfixCon x b))) <- dLPat pat = do
#else
  | Just p@(L _l (ConPat a b (InfixCon x c))) <- dLPat pat = do
#endif
    (p', x') <- fixOneEntry p (dLPatUnsafe x)
    return (cLPat $ (L (getLoc p') (ConPat a b (InfixCon x' c))))
  | otherwise = return pat
#endif

-------------------------------------------------------------------------------


-- Swap entryDP and prior comments between the two args
swapEntryDPT
  :: (Data a, Data b, Monad m
#if __GLASGOW_HASKELL__ < 910
     , Monoid a1, Monoid a2
#endif
     , Typeable a1, Typeable a2)
  => LocatedAn a1 a -> LocatedAn a2 b -> TransformT m (LocatedAn a1 a, LocatedAn a2 b)
swapEntryDPT a b = do
  b' <- transferEntryDP a b
  a' <- transferEntryDP b a
  return (a',b')

-------------------------------------------------------------------------------

-- Compatibility module with ghc-exactprint

parseContentNoFixity :: Parsers.LibDir -> FilePath -> String -> IO AnnotatedModule
parseContentNoFixity libdir fp str = join $ Parsers.withDynFlags libdir $ \dflags -> do
  r <- Parsers.parseModuleFromString libdir fp str
  case r of
    Left msg -> do
#if __GLASGOW_HASKELL__ < 900
      fail $ show msg
#elif __GLASGOW_HASKELL__ < 904
      fail $ show $ bagToList msg
#else
      fail $ showSDoc dflags $ ppr msg
#endif
    Right m -> return $ unsafeMkA
#if __GLASGOW_HASKELL__ < 910
                          (makeDeltaAst m)
#else
                          m
#endif
                          0

parseContent :: Parsers.LibDir -> FixityEnv -> FilePath -> String -> IO AnnotatedModule
parseContent libdir fixities fp =
  parseContentNoFixity libdir fp >=> (`transformA` fix fixities)

-- | Parse import statements. Each string must be a full import statement,
-- including the keyword 'import'. Supports full import syntax.
parseImports :: Parsers.LibDir -> [String] -> IO AnnotatedImports
parseImports _      []      = return mempty
parseImports libdir imports = do
  -- imports start on second line, so delta offsets are correct
  am <- parseContentNoFixity libdir "parseImports" $ "\n" ++ unlines imports
  ais <- transformA am $ pure . hsmodImports . unLoc
  return $ trimA ais

-- | Parse a top-level 'HsDecl'.
parseDecl :: Parsers.LibDir -> String -> IO AnnotatedHsDecl
parseDecl libdir str = parseHelper libdir "parseDecl" Parsers.parseDecl str

-- | Parse a 'HsExpr'.
parseExpr :: Parsers.LibDir -> String -> IO AnnotatedHsExpr
parseExpr libdir str = parseHelper libdir "parseExpr" Parsers.parseExpr str

-- | Parse a 'Pat'.
parsePattern :: Parsers.LibDir -> String -> IO AnnotatedPat
parsePattern libdir str = parseHelper libdir "parsePattern" Parsers.parsePattern str

-- | Parse a 'Stmt'.
parseStmt :: Parsers.LibDir -> String -> IO AnnotatedStmt
parseStmt libdir str = do
  -- debugPrint Loud "parseStmt:for" [str]
  res <- parseHelper libdir "parseStmt" Parsers.parseStmt str
  return (setEntryDPA res (DifferentLine 1 0))


-- | Parse a 'HsType'.
parseType :: Parsers.LibDir -> String -> IO AnnotatedHsType
parseType libdir str = parseHelper libdir "parseType" Parsers.parseType str

parseHelper :: (ExactPrint a)
  => Parsers.LibDir -> FilePath -> Parsers.Parser a -> String -> IO (Annotated a)
parseHelper libdir fp parser str = join $ Parsers.withDynFlags libdir $ \dflags ->
  case parser dflags fp str of
#if __GLASGOW_HASKELL__ < 900
    Left (_, msg) -> throwIO $ ErrorCall msg
#elif __GLASGOW_HASKELL__ < 904
    Left errBag -> throwIO $ ErrorCall (show $ bagToList errBag)
#else
    Left msg -> throwIO $ ErrorCall (showSDoc dflags $ ppr msg)
#endif
    Right x -> return $ unsafeMkA x 0


-------------------------------------------------------------------------------

debugDump :: (Data a, ExactPrint a) => Annotated a -> IO ()
debugDump ax = do
  let
    str = printA ax
    maxCol = maximum $ map length $ lines str
    (tens, ones) =
      case transpose [printf "%2d" i | i <- [1 .. maxCol]] of
        [ts, os] -> (ts, os)
        _ -> ("", "")
  -- putStrLn $ unlines
  --   [ show k ++ "\n  " ++ show v | (k,v) <- M.toList (annsA ax) ]
  putStrLn tens
  putStrLn ones
  putStrLn str
  putStrLn "------------------------------------"
  putStrLn $ showAstA ax
  putStrLn "------------------------------------"

-- The following definitions are all the same as the ones from ghc-exactprint,
-- but the types are liberalized from 'Transform a' to 'TransformT m a'.
transferEntryAnnsT
  :: (HasCallStack, Data a, Data b, Monad m)
  => (TrailingAnn -> Bool)  -- transfer Anns matching predicate
  -> LocatedA a             -- from
  -> LocatedA b             -- to
  -> TransformT m (LocatedA b)
transferEntryAnnsT p a b = do
  b' <- transferEntryDP a b
  transferAnnsT p a b'

-- | 'Transform' monad version of 'transferEntryDP'
transferEntryDPT
  :: (HasCallStack, Data a, Data b, Monad m)
  => Located a -> Located b -> TransformT m ()
transferEntryDPT _a _b = error "transferEntryDPT"


addAllAnnsT
  :: (HasCallStack
#if __GLASGOW_HASKELL__ < 910
     , Monoid an
#endif
     , Data a, Data b, MonadIO m, Typeable an)
  => LocatedAn an a -> LocatedAn an b -> TransformT m (LocatedAn an b)
addAllAnnsT a b = do
  -- AZ: to start with, just transfer the entry DP from a to b
  transferEntryDP a b


transferAnchor :: ExactPrint b => LocatedA a -> LocatedA b -> LocatedA b
#if __GLASGOW_HASKELL__ >= 910
transferAnchor (L (EpAnn anc _ _) _) lb = setAnnotationAnchor lb anc [] emptyComments
#else
transferAnchor (L (SrcSpanAnn EpAnnNotUsed l)    _) lb = setAnchorAn lb (spanAsAnchor l) emptyComments
transferAnchor (L (SrcSpanAnn (EpAnn anc _ _) _) _) lb = setAnchorAn lb anc              emptyComments
#endif


isComma :: TrailingAnn -> Bool
isComma (AddCommaAnn _) = True
isComma _ = False

-- isCommentKeyword :: AnnKeywordId -> Bool
-- isCommentKeyword _ = False


hasComments :: LocatedAn an a -> Bool
#if __GLASGOW_HASKELL__ >= 910
hasComments (L (EpAnn _anc _ cs) _)
#else
hasComments (L (SrcSpanAnn EpAnnNotUsed _) _) = False
hasComments (L (SrcSpanAnn (EpAnn anc _ cs) _) _)
#endif
  = case cs of
      EpaComments [] -> False
      EpaCommentsBalanced [] [] -> False
      _ -> True

transferAnnsT
  :: (Data a, Data b, Monad m)
  => (TrailingAnn -> Bool)      -- transfer Anns matching predicate
  -> LocatedA a                 -- from
  -> LocatedA b                 -- to
  -> TransformT m (LocatedA b)
#if __GLASGOW_HASKELL__ >= 910
transferAnnsT p (L (EpAnn _anc (AnnListItem ts) _cs) _a) (L an b) = do
  let ps = filter p ts
  let an' = case an of
        EpAnn ancb (AnnListItem tsb) csb -> EpAnn ancb (AnnListItem (tsb++ps)) csb
  return (L an' b)
#else
transferAnnsT p (L (SrcSpanAnn EpAnnNotUsed _) _) b = return b
transferAnnsT p (L (SrcSpanAnn (EpAnn anc (AnnListItem ts) cs) l) a) (L (SrcSpanAnn an lb) b) = do
  let ps = filter p ts
  let an' = case an of
        EpAnnNotUsed -> EpAnn (spanAsAnchor lb) (AnnListItem ps) emptyComments
        EpAnn ancb (AnnListItem tsb) csb -> EpAnn ancb (AnnListItem (tsb++ps)) csb
  return (L (SrcSpanAnn an' lb) b)
#endif

-- Useful for figuring out what annotations should be on something.
-- If you don't care about fixities, pass 'mempty' as the FixityEnv.
-- String should be the entire module contents.
debugParse :: Parsers.LibDir -> FixityEnv -> String -> IO ()
debugParse libdir fixityEnv s = do
  writeFile "debug.txt" s
  r <- parseModule libdir "debug.txt"
  case r of
    Left _ -> putStrLn "parse failed"
    Right modl -> do
#if __GLASGOW_HASKELL__ < 910
      let m = unsafeMkA (makeDeltaAst modl) 0
#else
      let m = unsafeMkA modl 0
#endif
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
