-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE CPP #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
module Retrie.Expr
  ( grhsToExpr
  , mkApps
  , mkHsAppsTy
  , mkLams
  , mkLet
  , mkLoc
  , mkLocatedHsVar
  , mkTyVar
  , parenify
  , parenifyT
  , patToExpr
  , patToExprA
  , unparen
  , unparenT
  , wildSupply
  ) where

import Control.Monad.State.Lazy
import Data.Functor.Identity
import qualified Data.Map as M
import Data.Maybe

import Retrie.AlphaEnv
import Retrie.ExactPrint
import Retrie.Fixity
import Retrie.GHC
import Retrie.SYB
import Retrie.Types

-------------------------------------------------------------------------------

mkLocatedHsVar :: Monad m => Located RdrName -> TransformT m (LHsExpr GhcPs)
mkLocatedHsVar v = do
  -- This special casing for [] is gross, but this is apparently how the
  -- annotations work.
  let anns =
        case occNameString (occName (unLoc v)) of
          "[]" -> [(G AnnOpenS, DP (0,0)), (G AnnCloseS, DP (0,0))]
          _    -> [(G AnnVal, DP (0,0))]
  r <- setAnnsFor v anns
#if __GLASGOW_HASKELL__ < 806
  lv@(L _ v') <- cloneT (noLoc (HsVar r))
#else
  lv@(L _ v') <- cloneT (noLoc (HsVar noExtField r))
#endif
  case v' of
#if __GLASGOW_HASKELL__ < 806
    HsVar x ->
#else
    HsVar _ x ->
#endif
      swapEntryDPT x lv
    _ -> return ()
  return lv

-------------------------------------------------------------------------------

setAnnsFor :: (Data e, Monad m)
           => Located e -> [(KeywordId, DeltaPos)] -> TransformT m (Located e)
setAnnsFor e anns = modifyAnnsT (M.alter f (mkAnnKey e)) >> return e
  where f Nothing  = Just annNone { annsDP = anns }
        f (Just a) = Just a { annsDP = M.toList
                                     $ M.union (M.fromList anns)
                                               (M.fromList (annsDP a)) }

mkLoc :: (Data e, Monad m) => e -> TransformT m (Located e)
mkLoc e = do
  le <- L <$> uniqueSrcSpanT <*> pure e
  setAnnsFor le []

-------------------------------------------------------------------------------

mkLams
  :: [LPat GhcPs]
  -> LHsExpr GhcPs
  -> TransformT IO (LHsExpr GhcPs)
mkLams [] e = return e
mkLams vs e = do
  let
    mg =
#if __GLASGOW_HASKELL__ < 806
      mkMatchGroup Generated [mkMatch LambdaExpr vs e (noLoc EmptyLocalBinds)]
#else
      mkMatchGroup Generated [mkMatch LambdaExpr vs e (noLoc (EmptyLocalBinds noExtField))]
#endif
  m' <- case unLoc $ mg_alts mg of
    [m] -> setAnnsFor m [(G AnnLam, DP (0,0)),(G AnnRarrow, DP (0,1))]
    _   -> fail "mkLams: lambda expression can only have a single match!"
#if __GLASGOW_HASKELL__ < 806
  cloneT $ noLoc $ HsLam mg { mg_alts = noLoc [m'] }
#else
  cloneT $ noLoc $ HsLam noExtField mg { mg_alts = noLoc [m'] }
#endif

mkLet :: Monad m => HsLocalBinds GhcPs -> LHsExpr GhcPs -> TransformT m (LHsExpr GhcPs)
mkLet EmptyLocalBinds{} e = return e
mkLet lbs e = do
  llbs <- mkLoc lbs
#if __GLASGOW_HASKELL__ < 806
  le <- mkLoc $ HsLet llbs e
#else
  le <- mkLoc $ HsLet noExtField llbs e
#endif
  setAnnsFor le [(G AnnLet, DP (0,0)), (G AnnIn, DP (1,1))]

mkApps :: Monad m => LHsExpr GhcPs -> [LHsExpr GhcPs] -> TransformT m (LHsExpr GhcPs)
mkApps e []     = return e
mkApps f (a:as) = do
#if __GLASGOW_HASKELL__ < 806
  f' <- mkLoc (HsApp f a)
#else
  f' <- mkLoc (HsApp noExtField f a)
#endif
  mkApps f' as

-- GHC never generates HsAppTy in the parser, using HsAppsTy to keep a list
-- of types.
mkHsAppsTy :: Monad m => [LHsType GhcPs] -> TransformT m (LHsType GhcPs)
#if __GLASGOW_HASKELL__ < 806
mkHsAppsTy ts = do
  ts' <- mapM (mkLoc . HsAppPrefix) ts
  mkLoc (HsAppsTy ts')
#else
mkHsAppsTy [] = error "mkHsAppsTy: empty list"
mkHsAppsTy (t:ts) = foldM (\t1 t2 -> mkLoc (HsAppTy noExtField t1 t2)) t ts
#endif

mkTyVar :: Monad m => Located RdrName -> TransformT m (LHsType GhcPs)
mkTyVar nm = do
#if __GLASGOW_HASKELL__ < 806
  tv <- mkLoc (HsTyVar NotPromoted nm)
#else
  tv <- mkLoc (HsTyVar noExtField NotPromoted nm)
#endif
  _ <- setAnnsFor nm [(G AnnVal, DP (0,0))]
  swapEntryDPT tv nm
  return tv

-------------------------------------------------------------------------------

-- Note [Wildcards]
-- We need to invent unique binders for wildcard patterns and feed
-- them in as quantified variables for the matcher (they will match
-- some expression and be discarded). We do this hackily here, by
-- generating a supply of w1, w2, etc variables, and filter out any
-- other binders we know about. However, we should also filter out
-- the free variables of the expression, to avoid capture. Haven't found
-- a free variable computation on HsExpr though. :-(

type PatQ m = StateT ([RdrName], [RdrName]) (TransformT m)

newWildVar :: Monad m => PatQ m RdrName
newWildVar = do
  (s, u) <- get
  case s of
    (r:s') -> do
      put (s', r:u)
      return r
    [] -> error "impossible: empty wild supply"

wildSupply :: [RdrName] -> [RdrName]
wildSupply used = wildSupplyP (`notElem` used)

wildSupplyAlphaEnv :: AlphaEnv -> [RdrName]
wildSupplyAlphaEnv env = wildSupplyP (\ nm -> isNothing (lookupAlphaEnv nm env))

wildSupplyP :: (RdrName -> Bool) -> [RdrName]
wildSupplyP p =
  [ r | i <- [0..]
      , let r = mkVarUnqual (mkFastString ('w' : show (i :: Int)))
      , p r ]

patToExprA :: AlphaEnv -> AnnotatedPat -> AnnotatedHsExpr
patToExprA env pat = runIdentity $ transformA pat $ \ p ->
  fst <$> runStateT
#if __GLASGOW_HASKELL__ < 808
    (patToExpr p)
#else
    (patToExpr (composeSrcSpan p))
#endif
    (wildSupplyAlphaEnv env, [])

patToExpr :: Monad m => LPat GhcPs -> PatQ m (LHsExpr GhcPs)
#if __GLASGOW_HASKELL__ < 808
patToExpr lp@(L _ p) = do
#else
patToExpr (dL -> lp@(L _ p)) = do
#endif
  e <- go p
  lift $ transferEntryDPT lp e
  return e
  where
    go WildPat{} = newWildVar >>= lift . mkLocatedHsVar . noLoc
    go (ConPatIn con ds) = conPatHelper con ds
#if __GLASGOW_HASKELL__ < 806
    go (LazyPat pat) = patToExpr pat
    go (BangPat pat) = patToExpr pat
    go (ListPat ps ty mb) = do
      ps' <- mapM patToExpr ps
      lift $ do
        el <- mkLoc $ ExplicitList ty (snd <$> mb) ps'
        setAnnsFor el [(G AnnOpenS, DP (0,0)), (G AnnCloseS, DP (0,0))]
    go (LitPat lit) = lift $ do
      lit' <- cloneT lit
      mkLoc $ HsLit lit'
    go (NPat llit mbNeg _ _) = lift $ do
      L _ lit <- cloneT llit
      e <- mkLoc $ HsOverLit lit
      negE <- maybe (return e) (mkLoc . NegApp e) mbNeg
      addAllAnnsT llit negE
      return negE
    go PArrPat{} = error "patToExpr PArrPat"
    go (ParPat p') = lift . mkParen HsPar =<< patToExpr p'
    go SigPatIn{} = error "patToExpr SigPatIn"
    go SigPatOut{} = error "patToExpr SigPatOut"
    go (TuplePat ps boxity _) = do
      es <- forM ps $ \pat -> do
        e <- patToExpr pat
        lift $ mkLoc $ Present e
      lift $ mkLoc $ ExplicitTuple es boxity
    go (VarPat i) = lift $ mkLocatedHsVar i
#else
    go (LazyPat _ pat) = patToExpr pat
    go (BangPat _ pat) = patToExpr pat
    go (ListPat _ ps) = do
      ps' <- mapM patToExpr ps
      lift $ do
        el <- mkLoc $ ExplicitList noExtField Nothing ps'
        setAnnsFor el [(G AnnOpenS, DP (0,0)), (G AnnCloseS, DP (0,0))]
    go (LitPat _ lit) = lift $ do
      lit' <- cloneT lit
      mkLoc $ HsLit noExtField lit'
    go (NPat _ llit mbNeg _) = lift $ do
      L _ lit <- cloneT llit
      e <- mkLoc $ HsOverLit noExtField lit
      negE <- maybe (return e) (mkLoc . NegApp noExtField e) mbNeg
      addAllAnnsT llit negE
      return negE
    go (ParPat _ p') = lift . mkParen (HsPar noExtField) =<< patToExpr p'
    go SigPat{} = error "patToExpr SigPat"
    go (TuplePat _ ps boxity) = do
      es <- forM ps $ \pat -> do
        e <- patToExpr pat
        lift $ mkLoc $ Present noExtField e
      lift $ mkLoc $ ExplicitTuple noExtField es boxity
    go (VarPat _ i) = lift $ mkLocatedHsVar i
    go XPat{} = error "patToExpr XPat"
#endif
    go AsPat{} = error "patToExpr AsPat"
    go ConPatOut{} = error "patToExpr ConPatOut" -- only exists post-tc
    go CoPat{} = error "patToExpr CoPat"
    go NPlusKPat{} = error "patToExpr NPlusKPat"
    go SplicePat{} = error "patToExpr SplicePat"
    go SumPat{} = error "patToExpr SumPat"
    go ViewPat{} = error "patToExpr ViewPat"

conPatHelper :: Monad m
             => Located RdrName
             -> HsConPatDetails GhcPs
             -> PatQ m (LHsExpr GhcPs)
conPatHelper con (InfixCon x y) =
#if __GLASGOW_HASKELL__ < 806
  lift . mkLoc =<< OpApp <$> patToExpr x
                         <*> lift (mkLocatedHsVar con)
                         <*> pure PlaceHolder
                         <*> patToExpr y
#else
  lift . mkLoc =<< OpApp <$> pure noExtField
                         <*> patToExpr x
                         <*> lift (mkLocatedHsVar con)
                         <*> patToExpr y
#endif
conPatHelper con (PrefixCon xs) = do
  f <- lift $ mkLocatedHsVar con
  as <- mapM patToExpr xs
  lift $ mkApps f as
conPatHelper _ _ = error "conPatHelper RecCon"

-------------------------------------------------------------------------------

grhsToExpr :: LGRHS p (LHsExpr p) -> LHsExpr p
#if __GLASGOW_HASKELL__ < 806
grhsToExpr (L _ (GRHS [] e)) = e
grhsToExpr (L _ (GRHS (_:_) e)) = e -- not sure about this
#else
grhsToExpr (L _ (GRHS _ [] e)) = e
grhsToExpr (L _ (GRHS _ (_:_) e)) = e -- not sure about this
grhsToExpr _ = error "grhsToExpr"
#endif

-------------------------------------------------------------------------------

precedence :: FixityEnv -> HsExpr GhcPs -> Maybe Fixity
precedence _        (HsApp {})       = Just $ Fixity (SourceText "HsApp") 10 InfixL
#if __GLASGOW_HASKELL__ < 806
precedence fixities (OpApp _ op _ _) = Just $ lookupOp op fixities
#else
precedence fixities (OpApp _ _ op _) = Just $ lookupOp op fixities
#endif
precedence _        _                = Nothing

parenify
  :: Monad m => Context -> LHsExpr GhcPs -> TransformT m (LHsExpr GhcPs)
parenify Context{..} le@(L _ e)
  | needed ctxtParentPrec (precedence ctxtFixityEnv e) && needsParens e =
#if __GLASGOW_HASKELL__ < 806
    mkParen HsPar le
#else
    mkParen (HsPar noExtField) le
#endif
  | otherwise = return le
  where
           {- parent -}               {- child -}
    needed (HasPrec (Fixity _ p1 d1)) (Just (Fixity _ p2 d2)) =
      p1 > p2 || (p1 == p2 && (d1 /= d2 || d2 == InfixN))
    needed NeverParen _ = False
    needed _ Nothing = True
    needed _ _ = False

unparen :: LHsExpr GhcPs -> LHsExpr GhcPs
#if __GLASGOW_HASKELL__ < 806
unparen (L _ (HsPar e)) = e
#else
unparen (L _ (HsPar _ e)) = e
#endif
unparen e = e

-- | hsExprNeedsParens is not always up-to-date, so this allows us to override
needsParens :: HsExpr GhcPs -> Bool
#if __GLASGOW_HASKELL__ < 806
needsParens RecordCon{} = False
needsParens RecordUpd{} = False
needsParens HsSpliceE{} = False
needsParens (HsWrap _ e) = hsExprNeedsParens e
needsParens e = hsExprNeedsParens e
#else
needsParens = hsExprNeedsParens (PprPrec 10)
#endif

mkParen :: (Data x, Monad m) => (Located x -> x) -> Located x -> TransformT m (Located x)
mkParen k e = do
  pe <- mkLoc (k e)
  _ <- setAnnsFor pe [(G AnnOpenP, DP (0,0)), (G AnnCloseP, DP (0,0))]
  swapEntryDPT e pe
  return pe

parenifyT
  :: Monad m => Context -> LHsType GhcPs -> TransformT m (LHsType GhcPs)
parenifyT Context{..} lty@(L _ ty)
#if __GLASGOW_HASKELL__ < 806
  | needed ty = mkParen HsParTy lty
#else
  | needed ty = mkParen (HsParTy noExtField) lty
#endif
  | otherwise = return lty
  where
#if __GLASGOW_HASKELL__ < 806
    needed HsTyVar{}   = False
    needed HsListTy{}  = False
    needed HsPArrTy{}  = False
    needed HsTupleTy{} = False
    needed HsParTy{}   = False
    needed HsTyLit{}   = False
    needed (HsAppsTy tys)
      | HasPrec _ <- ctxtParentPrec = length tys > 1
      | otherwise = False
    needed _           = True
#else
    needed HsAppTy{}
      | IsHsAppsTy <- ctxtParentPrec = True
      | otherwise = False
    needed t = hsTypeNeedsParens (PprPrec 10) t
#endif

unparenT :: LHsType GhcPs -> LHsType GhcPs
#if __GLASGOW_HASKELL__ < 806
unparenT (L _ (HsParTy ty)) = ty
#else
unparenT (L _ (HsParTy _ ty)) = ty
#endif
unparenT ty = ty
