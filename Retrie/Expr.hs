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
  ( bitraverseHsConDetails
  , getUnparened
  , grhsToExpr
  , mkApps
  , mkConPatIn
  , mkHsAppsTy
  , mkLams
  , mkLet
  , mkLoc
  , mkLocatedHsVar
  , mkVarPat
  , mkTyVar
  , parenify
  , parenifyT
  , parenifyP
  , patToExpr
  , patToExprA
  , setAnnsFor
  , unparen
  , unparenP
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
  lv@(L _ v') <- cloneT (noLoc (HsVar noExtField r))
  case v' of
    HsVar _ x ->
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
      mkMatchGroup Generated [mkMatch LambdaExpr vs e (noLoc emptyLocalBinds)]
  m' <- case unLoc $ mg_alts mg of
    [m] -> setAnnsFor m [(G AnnLam, DP (0,0)),(G AnnRarrow, DP (0,1))]
    _   -> fail "mkLams: lambda expression can only have a single match!"
  cloneT $ noLoc $ HsLam noExtField mg { mg_alts = noLoc [m'] }

mkLet :: Monad m => HsLocalBinds GhcPs -> LHsExpr GhcPs -> TransformT m (LHsExpr GhcPs)
mkLet EmptyLocalBinds{} e = return e
mkLet lbs e = do
  llbs <- mkLoc lbs
  le <- mkLoc $ HsLet noExtField llbs e
  setAnnsFor le [(G AnnLet, DP (0,0)), (G AnnIn, DP (1,1))]

mkApps :: Monad m => LHsExpr GhcPs -> [LHsExpr GhcPs] -> TransformT m (LHsExpr GhcPs)
mkApps e []     = return e
mkApps f (a:as) = do
  f' <- mkLoc (HsApp noExtField f a)
  mkApps f' as

-- GHC never generates HsAppTy in the parser, using HsAppsTy to keep a list
-- of types.
mkHsAppsTy :: Monad m => [LHsType GhcPs] -> TransformT m (LHsType GhcPs)
mkHsAppsTy [] = error "mkHsAppsTy: empty list"
mkHsAppsTy (t:ts) = foldM (\t1 t2 -> mkLoc (HsAppTy noExtField t1 t2)) t ts

mkTyVar :: Monad m => Located RdrName -> TransformT m (LHsType GhcPs)
mkTyVar nm = do
  tv <- mkLoc (HsTyVar noExtField NotPromoted nm)
  _ <- setAnnsFor nm [(G AnnVal, DP (0,0))]
  swapEntryDPT tv nm
  return tv

mkVarPat :: Monad m => Located RdrName -> TransformT m (LPat GhcPs)
mkVarPat nm = cLPat <$> mkLoc (VarPat noExtField nm)

mkConPatIn
  :: Monad m
  => Located RdrName
  -> HsConPatDetails GhcPs
  -> TransformT m (Located (Pat GhcPs))
mkConPatIn patName params = do
#if __GLASGOW_HASKELL__ < 900
  p <- mkLoc $ ConPatIn patName params
#else
  p <- mkLoc $ ConPat noExtField patName params
#endif
  setEntryDPT p (DP (0,0))
  return p

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
  fst <$> runStateT (patToExpr $ cLPat p) (wildSupplyAlphaEnv env, [])

patToExpr :: Monad m => LPat GhcPs -> PatQ m (LHsExpr GhcPs)
patToExpr orig = case dLPat orig of
  Nothing -> error "patToExpr: called on unlocated Pat!"
  Just lp@(L _ p) -> do
    e <- go p
    lift $ transferEntryDPT lp e
    return e
  where
    go WildPat{} = newWildVar >>= lift . mkLocatedHsVar . noLoc
#if __GLASGOW_HASKELL__ < 900
    go XPat{} = error "patToExpr XPat"
    go CoPat{} = error "patToExpr CoPat"
    go (ConPatIn con ds) = conPatHelper con ds
    go ConPatOut{} = error "patToExpr ConPatOut" -- only exists post-tc
#else
    go (ConPat _ con ds) = conPatHelper con ds
#endif
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
    go AsPat{} = error "patToExpr AsPat"
    go NPlusKPat{} = error "patToExpr NPlusKPat"
    go SplicePat{} = error "patToExpr SplicePat"
    go SumPat{} = error "patToExpr SumPat"
    go ViewPat{} = error "patToExpr ViewPat"

conPatHelper :: Monad m
             => Located RdrName
             -> HsConPatDetails GhcPs
             -> PatQ m (LHsExpr GhcPs)
conPatHelper con (InfixCon x y) =
  lift . mkLoc =<< OpApp <$> pure noExtField
                         <*> patToExpr x
                         <*> lift (mkLocatedHsVar con)
                         <*> patToExpr y
conPatHelper con (PrefixCon xs) = do
  f <- lift $ mkLocatedHsVar con
  as <- mapM patToExpr xs
  lift $ mkApps f as
conPatHelper _ _ = error "conPatHelper RecCon"

-------------------------------------------------------------------------------

grhsToExpr :: LGRHS p (LHsExpr p) -> LHsExpr p
grhsToExpr (L _ (GRHS _ [] e)) = e
grhsToExpr (L _ (GRHS _ (_:_) e)) = e -- not sure about this
grhsToExpr _ = error "grhsToExpr"

-------------------------------------------------------------------------------

precedence :: FixityEnv -> HsExpr GhcPs -> Maybe Fixity
precedence _        (HsApp {})       = Just $ Fixity (SourceText "HsApp") 10 InfixL
precedence fixities (OpApp _ _ op _) = Just $ lookupOp op fixities
precedence _        _                = Nothing

parenify
  :: Monad m => Context -> LHsExpr GhcPs -> TransformT m (LHsExpr GhcPs)
parenify Context{..} le@(L _ e)
  | needed ctxtParentPrec (precedence ctxtFixityEnv e) && needsParens e =
    mkParen (HsPar noExtField) le
  | otherwise = return le
  where
           {- parent -}               {- child -}
    needed (HasPrec (Fixity _ p1 d1)) (Just (Fixity _ p2 d2)) =
      p1 > p2 || (p1 == p2 && (d1 /= d2 || d2 == InfixN))
    needed NeverParen _ = False
    needed _ Nothing = True
    needed _ _ = False

getUnparened :: Data k => k -> k
getUnparened = mkT unparen `extT` unparenT `extT` unparenP

unparen :: LHsExpr GhcPs -> LHsExpr GhcPs
unparen (L _ (HsPar _ e)) = e
unparen e = e

-- | hsExprNeedsParens is not always up-to-date, so this allows us to override
needsParens :: HsExpr GhcPs -> Bool
needsParens = hsExprNeedsParens (PprPrec 10)

mkParen :: (Data x, Monad m) => (Located x -> x) -> Located x -> TransformT m (Located x)
mkParen k e = do
  pe <- mkLoc (k e)
  _ <- setAnnsFor pe [(G AnnOpenP, DP (0,0)), (G AnnCloseP, DP (0,0))]
  swapEntryDPT e pe
  return pe

-- This explicitly operates on 'Located (Pat GhcPs)' instead of 'LPat GhcPs'
-- because it is applied at that type by SYB.
parenifyP
  :: Monad m
  => Context
  -> Located (Pat GhcPs)
  -> TransformT m (Located (Pat GhcPs))
parenifyP Context{..} p@(L _ pat)
  | IsLhs <- ctxtParentPrec
  , needed pat =
    mkParen (ParPat noExtField . cLPat) p
  | otherwise = return p
  where
    needed BangPat{}                          = False
    needed LazyPat{}                          = False
    needed ListPat{}                          = False
    needed LitPat{}                           = False
    needed ParPat{}                           = False
    needed SumPat{}                           = False
    needed TuplePat{}                         = False
    needed VarPat{}                           = False
    needed WildPat{}                          = False
#if __GLASGOW_HASKELL__ < 900
    needed (ConPatIn _ (PrefixCon []))        = False
    needed ConPatOut{pat_args = PrefixCon []} = False
#else
    needed (ConPat _ _ (PrefixCon []))        = False
#endif
    needed _                                  = True

parenifyT
  :: Monad m => Context -> LHsType GhcPs -> TransformT m (LHsType GhcPs)
parenifyT Context{..} lty@(L _ ty)
  | needed ty = mkParen (HsParTy noExtField) lty
  | otherwise = return lty
  where
    needed HsAppTy{}
      | IsHsAppsTy <- ctxtParentPrec = True
      | otherwise = False
    needed t = hsTypeNeedsParens (PprPrec 10) t

unparenT :: LHsType GhcPs -> LHsType GhcPs
unparenT (L _ (HsParTy _ ty)) = ty
unparenT ty = ty

-- This explicitly operates on 'Located (Pat GhcPs)' instead of 'LPat GhcPs'
-- to ensure 'dLPat' was called on the input.
unparenP :: Located (Pat GhcPs) -> Located (Pat GhcPs)
unparenP (L _ (ParPat _ p)) | Just lp <- dLPat p = lp
unparenP p = p

--------------------------------------------------------------------

bitraverseHsConDetails
  :: Applicative m
  => (arg -> m arg')
  -> (rec -> m rec')
  -> HsConDetails arg rec
  -> m (HsConDetails arg' rec')
bitraverseHsConDetails argf _ (PrefixCon args) =
  PrefixCon <$> (argf `traverse` args)
bitraverseHsConDetails _ recf (RecCon r) =
  RecCon <$> recf r
bitraverseHsConDetails argf _ (InfixCon a1 a2) =
  InfixCon <$> argf a1 <*> argf a2
