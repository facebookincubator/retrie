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
  -- , cloneT
  -- , setEntryDPT
  , swapEntryDPT
  , transferAnnsT
  , transferEntryAnnsT
  , transferEntryDPT
  -- , tryTransferEntryDPT
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
  -- , module Language.Haskell.GHC.ExactPrint.Annotate
  , module Language.Haskell.GHC.ExactPrint.Types
  , module Language.Haskell.GHC.ExactPrint.Utils
  , module Language.Haskell.GHC.ExactPrint.Transform
  ) where

import Control.Exception
import Control.Monad.State.Lazy hiding (fix)
-- import Data.Function (on)
import Data.List (transpose)
-- import Data.Maybe
-- import qualified Data.Map as M
import Text.Printf

import Language.Haskell.GHC.ExactPrint hiding
  (
   setEntryDP
  , transferEntryDP
  )
-- import Language.Haskell.GHC.ExactPrint.ExactPrint (ExactPrint)
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
import Retrie.Util

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
  | associatesRight (lookupOp op1 env) (lookupOp op2 env) = do
    -- lift $ liftIO $ debugPrint Loud "fixOneExpr:(l1,l2)="  [showAst (l1,l2)]
    let ap2' = L (stripComments l2) $ OpApp x2 y op2 z
    (ap1_0, ap2'_0) <- swapEntryDPT ap1 ap2'
    ap1_1 <- transferAnnsT isComma ap2'_0 ap1_0
    -- lift $ liftIO $ debugPrint Loud "fixOneExpr:recursing"  []
    rhs <- fixOneExpr env ap2'_0
    -- lift $ liftIO $ debugPrint Loud "fixOneExpr:returning"  [showAst (L l2 $ OpApp x1 x op1 rhs)]
    -- return $ L l1 $ OpApp x1 x op1 rhs
    return $ L l2 $ OpApp x1 x op1 rhs
fixOneExpr _ e = return e

fixOnePat :: Monad m => FixityEnv -> LPat GhcPs -> TransformT m (LPat GhcPs)
fixOnePat env (dLPat -> Just (L l2 (ConPat ext2 op2 (InfixCon (dLPat -> Just ap1@(L l1 (ConPat ext1 op1 (InfixCon x y)))) z))))
  | associatesRight (lookupOpRdrName op1 env) (lookupOpRdrName op2 env) = do
    let ap2' = L l2 (ConPat ext2 op2 (InfixCon y z))
    (ap1_0, ap2'_0) <- swapEntryDPT ap1 ap2'
    ap1_1 <- transferAnnsT isComma ap2' ap1
    rhs <- fixOnePat env (cLPat ap2'_0)
    return $ cLPat $ L l1 (ConPat ext1 op1 (InfixCon x rhs))
fixOnePat _ e = return e

-- TODO: move to ghc-exactprint
stripComments :: SrcAnn an -> SrcAnn an
stripComments (SrcSpanAnn EpAnnNotUsed l) = SrcSpanAnn EpAnnNotUsed l
stripComments (SrcSpanAnn (EpAnn anc an _) l) = SrcSpanAnn (EpAnn anc an emptyComments) l

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
  -- lift $ liftIO $ debugPrint Loud "fixOneEntry:(e,x)="  [showAst (e,x)]
  -- -- anns <- getAnnsT
  -- let
  --   zeros = SameLine 0
  --   (xdp, ard) =
  --     case M.lookup (mkAnnKey x) anns of
  --       Nothing -> (zeros, zeros)
  --       Just ann -> (annLeadingCommentEntryDelta ann, annEntryDelta ann)
  --   xr = getDeltaLine xdp
  --   xc = deltaColumn xdp
  --   actualRow = getDeltaLine ard
  --   edp =
  --     maybe zeros annLeadingCommentEntryDelta $ M.lookup (mkAnnKey e) anns
  --   er = getDeltaLine edp
  --   ec = deltaColumn edp
  -- when (actualRow == 0) $ do
  --   setEntryDPT e $ deltaPos (er, xc + ec)
  --   setEntryDPT x $ deltaPos (xr, 0)

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
    SameLine n -> do
      -- lift $ liftIO $ debugPrint Loud "fixOneEntry:(xdp,edp)="  [showAst (xdp,edp)]
      -- lift $ liftIO $ debugPrint Loud "fixOneEntry:(dpx,dpe)="  [showAst ((deltaPos er (xc + ec)),(deltaPos xr 0))]
      -- lift $ liftIO $ debugPrint Loud "fixOneEntry:e'="  [showAst e]
      -- lift $ liftIO $ debugPrint Loud "fixOneEntry:e'="  [showAst (setEntryDP e (deltaPos er (xc + ec)))]
      return ( setEntryDP e (deltaPos er (xc + ec))
             , setEntryDP x (deltaPos xr 0))
    _ -> return (e,x)

  -- anns <- getAnnsT
  -- let
  --   zeros = DP (0,0)
  --   (DP (xr,xc), DP (actualRow,_)) =
  --     case M.lookup (mkAnnKey x) anns of
  --       Nothing -> (zeros, zeros)
  --       Just ann -> (annLeadingCommentEntryDelta ann, annEntryDelta ann)
  --   DP (er,ec) =
  --     maybe zeros annLeadingCommentEntryDelta $ M.lookup (mkAnnKey e) anns
  -- when (actualRow == 0) $ do
  --   setEntryDPT e $ DP (er, xc + ec)
  --   setEntryDPT x $ DP (xr, 0)
  -- return e

-- TODO: move this somewhere more appropriate
entryDP :: LocatedA a -> DeltaPos
entryDP (L (SrcSpanAnn EpAnnNotUsed _) _) = SameLine 1
entryDP (L (SrcSpanAnn (EpAnn anc _ _) _) _)
  = case anchor_op anc of
      UnchangedAnchor -> SameLine 1
      MovedAnchor dp -> dp


fixOneEntryExpr :: MonadIO m => LHsExpr GhcPs -> TransformT m (LHsExpr GhcPs)
fixOneEntryExpr e@(L l (OpApp a x b c)) = do
  -- lift $ liftIO $ debugPrint Loud "fixOneEntryExpr:(e,x)="  [showAst (e,x)]
  (e',x') <- fixOneEntry e x
  -- lift $ liftIO $ debugPrint Loud "fixOneEntryExpr:(e',x')="  [showAst (e',x')]
  -- lift $ liftIO $ debugPrint Loud "fixOneEntryExpr:returning="  [showAst (L (getLoc e') (OpApp a x' b c))]
  return (L (getLoc e') (OpApp a x' b c))
fixOneEntryExpr e = return e

fixOneEntryPat :: MonadIO m => LPat GhcPs -> TransformT m (LPat GhcPs)
fixOneEntryPat pat
#if __GLASGOW_HASKELL__ < 900
  | Just p@(L l (ConPatIn a (InfixCon x b))) <- dLPat pat = do
#else
  | Just p@(L l (ConPat a b (InfixCon x c))) <- dLPat pat = do
#endif
    (p', x') <- fixOneEntry p (dLPatUnsafe x)
    return (cLPat $ (L (getLoc p') (ConPat a b (InfixCon x' c))))
  | otherwise = return pat

-------------------------------------------------------------------------------


-- Swap entryDP and prior comments between the two args
swapEntryDPT
  :: (Data a, Data b, Monad m, Monoid a1, Monoid a2, Typeable a1, Typeable a2)
  => LocatedAn a1 a -> LocatedAn a2 b -> TransformT m (LocatedAn a1 a, LocatedAn a2 b)
swapEntryDPT a b = do
  b' <- transferEntryDP a b
  a' <- transferEntryDP b a
  return (a',b')

-- swapEntryDPT
--   :: (Data a, Data b, Monad m)
--   => LocatedAn a1 a -> LocatedAn a2 b -> TransformT m ()
-- swapEntryDPT a b =
--   modifyAnnsT $ \ anns ->
--   let akey = mkAnnKey a
--       bkey = mkAnnKey b
--       aann = fromMaybe annNone $ M.lookup akey anns
--       bann = fromMaybe annNone $ M.lookup bkey anns
--   in M.insert akey
--       aann { annEntryDelta = annEntryDelta bann
--            , annPriorComments = annPriorComments bann } $
--      M.insert bkey
--       bann { annEntryDelta = annEntryDelta aann
--            , annPriorComments = annPriorComments aann } anns

-------------------------------------------------------------------------------

-- Compatibility module with ghc-exactprint

parseContentNoFixity :: Parsers.LibDir -> FilePath -> String -> IO AnnotatedModule
parseContentNoFixity libdir fp str = do
  r <- Parsers.parseModuleFromString libdir fp str
  case r of
    Left msg -> do
#if __GLASGOW_HASKELL__ < 810
      fail $ show msg
#else
      fail $ show $ bagToList msg
#endif
    Right m -> return $ unsafeMkA (makeDeltaAst m) 0

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
-- parsePattern libdir str = parseHelper libdir "parsePattern" p str
--   where
--     p flags fp str' = fmap dLPatUnsafe <$> Parsers.parsePattern flags fp str'
parsePattern libdir str = parseHelper libdir "parsePattern" Parsers.parsePattern str

-- | Parse a 'Stmt'.
parseStmt :: Parsers.LibDir -> String -> IO AnnotatedStmt
parseStmt libdir str = do
  -- debugPrint Loud "parseStmt:for" [str]
  res <- parseHelper libdir "parseStmt" Parsers.parseStmt str
  return (setEntryDPA res (DifferentLine 1 0))
  -- return res


-- | Parse a 'HsType'.
parseType :: Parsers.LibDir -> String -> IO AnnotatedHsType
parseType libdir str = parseHelper libdir "parseType" Parsers.parseType str

parseHelper :: (ExactPrint a)
  => Parsers.LibDir -> FilePath -> Parsers.Parser a -> String -> IO (Annotated a)
parseHelper libdir fp parser str = join $ Parsers.withDynFlags libdir $ \dflags ->
  case parser dflags fp str of
#if __GLASGOW_HASKELL__ < 810
    Left (_, msg) -> throwIO $ ErrorCall msg
#else
    Left errBag -> throwIO $ ErrorCall (show $ bagToList errBag)
#endif
    Right x -> return $ unsafeMkA (makeDeltaAst x) 0

-- type Parser a = GHC.DynFlags -> FilePath -> String -> ParseResult a


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

-- cloneT :: (Data a, Typeable a, Monad m) => a -> TransformT m a
-- cloneT e = getAnnsT >>= flip graftT e

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
-- transferEntryDPT a b = modifyAnnsT (transferEntryDP a b)
transferEntryDPT _a _b = error "transferEntryDPT"

-- tryTransferEntryDPT
--   :: (Data a, Data b, Monad m)
--   => Located a -> Located b -> TransformT m ()
-- tryTransferEntryDPT a b = modifyAnnsT $ \anns ->
--   if M.member (mkAnnKey a) anns
--     then transferEntryDP a b anns
--     else anns

-- This function fails if b is not in Anns, which seems dumb, since we are inserting it.
-- transferEntryDP :: (HasCallStack, Data a, Data b) => Located a -> Located b -> Anns -> Anns
-- transferEntryDP a b anns = setEntryDP b dp anns'
--   where
--     maybeAnns = do -- Maybe monad
--       anA <- M.lookup (mkAnnKey a) anns
--       let anB = M.findWithDefault annNone (mkAnnKey b) anns
--           anB' = anB { annEntryDelta = DP (0,0) }
--       return (M.insert (mkAnnKey b) anB' anns, annLeadingCommentEntryDelta anA)
--     (anns',dp) = fromMaybe
--                   (error $ "transferEntryDP: lookup failed: " ++ show (mkAnnKey a))
--                   maybeAnns

addAllAnnsT
  :: (HasCallStack, Monoid an, Data a, Data b, MonadIO m, Typeable an)
  => LocatedAn an a -> LocatedAn an b -> TransformT m (LocatedAn an b)
addAllAnnsT a b = do
  -- AZ: to start with, just transfer the entry DP from a to b
  transferEntryDP a b


-- addAllAnnsT
--   :: (HasCallStack, Data a, Data b, Monad m)
--   => Located a -> Located b -> TransformT m ()
-- addAllAnnsT a b = modifyAnnsT (addAllAnns a b)

-- addAllAnns :: (HasCallStack, Data a, Data b) => Located a -> Located b -> Anns -> Anns
-- addAllAnns a b anns =
--   fromMaybe
--     (error $ "addAllAnns: lookup failed: " ++ show (mkAnnKey a)
--       ++ " or " ++ show (mkAnnKey b))
--     $ do ann <- M.lookup (mkAnnKey a) anns
--          case M.lookup (mkAnnKey b) anns of
--            Just ann' -> return $ M.insert (mkAnnKey b) (ann `annAdd` ann') anns
--            Nothing -> return $ M.insert (mkAnnKey b) ann anns
--   where annAdd ann ann' = ann'
--           { annEntryDelta = annEntryDelta ann
--           , annPriorComments = ((++) `on` annPriorComments) ann ann'
--           , annFollowingComments = ((++) `on` annFollowingComments) ann ann'
--           , annsDP = ((++) `on` annsDP) ann ann'
--           }

transferAnchor :: LocatedA a -> LocatedA b -> LocatedA b
transferAnchor (L (SrcSpanAnn EpAnnNotUsed l)    _) lb = setAnchorAn lb (spanAsAnchor l) emptyComments
transferAnchor (L (SrcSpanAnn (EpAnn anc _ _) _) _) lb = setAnchorAn lb anc              emptyComments


isComma :: TrailingAnn -> Bool
isComma (AddCommaAnn _) = True
isComma _ = False

isCommentKeyword :: AnnKeywordId -> Bool
-- isCommentKeyword (AnnComment _) = True
isCommentKeyword _ = False

-- isCommentAnnotation :: Annotation -> Bool
-- isCommentAnnotation Ann{..} =
--   (not . null $ annPriorComments)
--   || (not . null $ annFollowingComments)
--   || any (isCommentKeyword . fst) annsDP

hasComments :: LocatedAn an a -> Bool
hasComments (L (SrcSpanAnn EpAnnNotUsed _) _) = False
hasComments (L (SrcSpanAnn (EpAnn anc _ cs) _) _)
  = case cs of
      EpaComments [] -> False
      EpaCommentsBalanced [] [] -> False
      _ -> True

-- hasComments :: (Data a, Monad m) => Located a -> TransformT m Bool
-- hasComments e = do
--   anns <- getAnnsT
--   let b = isCommentAnnotation <$> M.lookup (mkAnnKey e) anns
--   return $ fromMaybe False b

-- transferAnnsT
--   :: (Data a, Data b, Monad m)
--   => (KeywordId -> Bool)        -- transfer Anns matching predicate
--   -> Located a                  -- from
--   -> Located b                  -- to
--   -> TransformT m ()
-- transferAnnsT p a b = modifyAnnsT f
--   where
--     bKey = mkAnnKey b
--     f anns = fromMaybe anns $ do
--       anA <- M.lookup (mkAnnKey a) anns
--       anB <- M.lookup bKey anns
--       let anB' = anB { annsDP = annsDP anB ++ filter (p . fst) (annsDP anA) }
--       return $ M.insert bKey anB' anns

transferAnnsT
  :: (Data a, Data b, Monad m)
  => (TrailingAnn -> Bool)      -- transfer Anns matching predicate
  -> LocatedA a                 -- from
  -> LocatedA b                 -- to
  -> TransformT m (LocatedA b)
transferAnnsT p (L (SrcSpanAnn EpAnnNotUsed _) _) b = return b
transferAnnsT p (L (SrcSpanAnn (EpAnn anc (AnnListItem ts) cs) l) a) (L (SrcSpanAnn an lb) b) = do
  let ps = filter p ts
  let an' = case an of
        EpAnnNotUsed -> EpAnn (spanAsAnchor lb) (AnnListItem ps) emptyComments
        EpAnn ancb (AnnListItem tsb) csb -> EpAnn ancb (AnnListItem (tsb++ps)) csb
  return (L (SrcSpanAnn an' lb) b)


-- -- | 'Transform' monad version of 'setEntryDP',
-- --   which sets the entry 'DeltaPos' for an annotation.
-- setEntryDPT
--   :: (Data a, Monad m)
--   => Located a -> DeltaPos -> TransformT m ()
-- setEntryDPT ast dp = do
--   modifyAnnsT (setEntryDP ast dp)

-- -- | Set the true entry 'DeltaPos' from the annotation of a
-- --   given AST element.
-- setEntryDP :: Data a => Located a -> DeltaPos -> Anns -> Anns
-- --  The setEntryDP that comes with exactprint does some really confusing
-- --  entry math around comments that I'm unconvinced is either correct or useful.
-- setEntryDP x dp anns = M.alter (Just . f . fromMaybe annNone) k anns
--   where
--     k = mkAnnKey x
--     f ann = case annPriorComments ann of
--               []       -> ann { annEntryDelta = dp }
--               (c,_):cs -> ann { annPriorComments = (c,dp):cs }

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
      let m = unsafeMkA (makeDeltaAst modl) 0
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
