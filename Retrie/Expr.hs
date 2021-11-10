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
  , mkLocA
  , mkLocatedHsVar
  , mkVarPat
  , mkTyVar
  , parenify
  , parenifyT
  , parenifyP
  , patToExpr
  , patToExprA
  -- , setAnnsFor
  , unparen
  , unparenP
  , unparenT
  , wildSupply
  ) where

import Control.Monad.State.Lazy
import Data.Functor.Identity
-- import qualified Data.Map as M
import Data.Maybe
-- import Data.Void

import Retrie.AlphaEnv
import Retrie.ExactPrint
import Retrie.Fixity
import Retrie.GHC
import Retrie.SYB
import Retrie.Types

-------------------------------------------------------------------------------

mkLocatedHsVar :: Monad m => LocatedN RdrName -> TransformT m (LHsExpr GhcPs)
mkLocatedHsVar n@(L l _) = do
  -- This special casing for [] is gross, but this is apparently how the
  -- annotations work.
  -- let anns =
  --       case occNameString (occName (unLoc v)) of
  --         "[]" -> [(G AnnOpenS, DP (0,0)), (G AnnCloseS, DP (0,0))]
  --         _    -> [(G AnnVal, DP (0,0))]
  -- r <- setAnnsFor v anns
  return (L (l2l l)  (HsVar noExtField n))

-------------------------------------------------------------------------------

-- setAnnsFor :: (Data e, Monad m)
--            => Located e -> [(KeywordId, DeltaPos)] -> TransformT m (Located e)
-- setAnnsFor e anns = modifyAnnsT (M.alter f (mkAnnKey e)) >> return e
--   where f Nothing  = Just annNone { annsDP = anns }
--         f (Just a) = Just a { annsDP = M.toList
--                                      $ M.union (M.fromList anns)
--                                                (M.fromList (annsDP a)) }

mkLoc :: (Data e, Monad m) => e -> TransformT m (Located e)
mkLoc e = do
  L <$> uniqueSrcSpanT <*> pure e

-- ++AZ++:TODO: move to ghc-exactprint
mkLocA :: (Data e, Monad m, Monoid an)
  => DeltaPos -> e -> TransformT m (LocatedAn an e)
mkLocA dp e = do
  l <- uniqueSrcSpanT
  let anc = Anchor (realSrcSpan l) (MovedAnchor dp)
  return (L (SrcSpanAnn (EpAnn anc mempty emptyComments) l) e)

-- ++AZ++:TODO: move to ghc-exactprint
mkLocAA :: (Data e, Monad m) => DeltaPos -> an -> e -> TransformT m (LocatedAn an e)
mkLocAA dp an e = do
  l <- uniqueSrcSpanT
  let anc = Anchor (realSrcSpan l) (MovedAnchor dp)
  return (L (SrcSpanAnn (EpAnn anc an emptyComments) l) e)


-- ++AZ++:TODO: move to ghc-exactprint
mkEpAnn :: Monad m => DeltaPos -> an -> TransformT m (EpAnn an)
mkEpAnn dp an = do
  l <- uniqueSrcSpanT
  return $ EpAnn (Anchor (realSrcSpan l) (MovedAnchor dp)) an emptyComments

-------------------------------------------------------------------------------

mkLams
  :: [LPat GhcPs]
  -> LHsExpr GhcPs
  -> TransformT IO (LHsExpr GhcPs)
mkLams [] e = return e
mkLams vs e = do
  matches <- mkLocA (SameLine 1) [mkMatch LambdaExpr vs e emptyLocalBinds]
  let
    mg =
      mkMatchGroup Generated matches
  -- m' <- case unLoc $ mg_alts mg of
  --   [m] -> setAnnsFor m [(G AnnLam, DP (0,0)),(G AnnRarrow, DP (0,1))]
  --   _   -> fail "mkLams: lambda expression can only have a single match!"
  -- cloneT $ noLoc $ HsLam noExtField mg { mg_alts = noLoc [m'] }
  mkLocA (SameLine 1) $ HsLam noExtField mg

mkLet :: Monad m => HsLocalBinds GhcPs -> LHsExpr GhcPs -> TransformT m (LHsExpr GhcPs)
mkLet EmptyLocalBinds{} e = return e
mkLet lbs e = do
  an <- mkEpAnn (DifferentLine 1 5)
                (AnnsLet {
                   alLet = EpaDelta (SameLine 0) [],
                   alIn = EpaDelta (DifferentLine 1 1) []
                 })
  le <- mkLocA (SameLine 1) $ HsLet an lbs e
  return le



mkApps :: Monad m => LHsExpr GhcPs -> [LHsExpr GhcPs] -> TransformT m (LHsExpr GhcPs)
mkApps e []     = return e
mkApps f (a:as) = do
  f' <- mkLocA (SameLine 1) (HsApp noAnn f a)
  mkApps f' as

-- GHC never generates HsAppTy in the parser, using HsAppsTy to keep a list
-- of types.
mkHsAppsTy :: Monad m => [LHsType GhcPs] -> TransformT m (LHsType GhcPs)
mkHsAppsTy [] = error "mkHsAppsTy: empty list"
mkHsAppsTy (t:ts) = foldM (\t1 t2 -> mkLocA (SameLine 1) (HsAppTy noExtField t1 t2)) t ts

mkTyVar :: Monad m => LocatedN RdrName -> TransformT m (LHsType GhcPs)
mkTyVar nm = do
  tv <- mkLocA (SameLine 1) (HsTyVar noAnn NotPromoted nm)
  -- _ <- setAnnsFor nm [(G AnnVal, DP (0,0))]
  (tv', nm') <- swapEntryDPT tv nm
  return tv'

mkVarPat :: Monad m => LocatedN RdrName -> TransformT m (LPat GhcPs)
mkVarPat nm = cLPat <$> mkLocA (SameLine 1) (VarPat noExtField nm)

-- type HsConPatDetails p = HsConDetails (HsPatSigType (NoGhcTc p)) (LPat p) (HsRecFields p (LPat p))

mkConPatIn
  :: Monad m
  => LocatedN RdrName
  -> HsConPatDetails GhcPs
  -- -> HsConDetails Void (LocatedN RdrName) [RecordPatSynField GhcPs]
  -> TransformT m (LPat GhcPs)
mkConPatIn patName params = do
  p <- mkLocA (SameLine 0) $ ConPat noAnn patName params
  -- setEntryDPT p (DP (0,0))
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
    lift $ transferEntryDP lp e
  where
    -- go :: Pat GhcPs -> PatQ m (LHsExpr GhcPs)
    go WildPat{} = do
      w <- newWildVar
      v <- lift $ mkLocA (SameLine 1) w
      lift $ mkLocatedHsVar v
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
        an <- mkEpAnn (SameLine 1)
                      (AnnList Nothing (Just (AddEpAnn AnnOpenS d0)) (Just (AddEpAnn AnnCloseS d0)) [] [])
        el <- mkLocA (SameLine 1) $ ExplicitList an ps'
        -- setAnnsFor el [(G AnnOpenS, DP (0,0)), (G AnnCloseS, DP (0,0))]
        return el
    go (LitPat _ lit) = lift $ do
      -- lit' <- cloneT lit
      mkLocA (SameLine 1) $ HsLit noAnn lit
    go (NPat _ llit mbNeg _) = lift $ do
      -- L _ lit <- cloneT llit
      e <- mkLocA (SameLine 1) $ HsOverLit noAnn (unLoc llit)
      negE <- maybe (return e) (mkLocA (SameLine 0) . NegApp noAnn e) mbNeg
      -- addAllAnnsT llit negE
      return negE
    go (ParPat an p') = do
      p <- patToExpr p'
      lift $ mkLocA (SameLine 1) (HsPar an p)
    go SigPat{} = error "patToExpr SigPat"
    go (TuplePat an ps boxity) = do
      es <- forM ps $ \pat -> do
        e <- patToExpr pat
        return $ Present noAnn e
      lift $ mkLocA (SameLine 1) $ ExplicitTuple an es boxity
    go (VarPat _ i) = lift $ mkLocatedHsVar i
    go AsPat{} = error "patToExpr AsPat"
    go NPlusKPat{} = error "patToExpr NPlusKPat"
    go SplicePat{} = error "patToExpr SplicePat"
    go SumPat{} = error "patToExpr SumPat"
    go ViewPat{} = error "patToExpr ViewPat"

conPatHelper :: Monad m
             => LocatedN RdrName
             -> HsConPatDetails GhcPs
             -> PatQ m (LHsExpr GhcPs)
conPatHelper con (InfixCon x y) =
  lift . mkLocA (SameLine 1)
               =<< OpApp <$> pure noAnn
                         <*> patToExpr x
                         <*> lift (mkLocatedHsVar con)
                         <*> patToExpr y
conPatHelper con (PrefixCon tyargs xs) = do
  f <- lift $ mkLocatedHsVar con
  as <- mapM patToExpr xs
  lift $ mkApps f as
conPatHelper _ _ = error "conPatHelper RecCon"

-------------------------------------------------------------------------------

grhsToExpr :: LGRHS GhcPs (LHsExpr GhcPs) -> LHsExpr GhcPs
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
    mkParen' (\an -> HsPar an le)
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

mkParen :: (Data x, Monad m, Monoid an)
  => (LocatedAn an x -> x) -> LocatedAn an x -> TransformT m (LocatedAn an x)
mkParen k e = do
  pe <- mkLocA (SameLine 1) (k e)
  -- _ <- setAnnsFor pe [(G AnnOpenP, DP (0,0)), (G AnnCloseP, DP (0,0))]
  (e0,pe0) <- swapEntryDPT e pe
  return pe0

mkParen' :: (Data x, Monad m, Monoid an)
         => (EpAnn AnnParen -> x) -> TransformT m (LocatedAn an x)
mkParen' k = do
  let an = AnnParen AnnParens d0 d0
  l <- uniqueSrcSpanT
  let anc = Anchor (realSrcSpan l) (MovedAnchor (SameLine 1))
  pe <- mkLocA (SameLine 0) (k (EpAnn anc an emptyComments))
  return pe

-- This explicitly operates on 'Located (Pat GhcPs)' instead of 'LPat GhcPs'
-- because it is applied at that type by SYB.
parenifyP
  :: Monad m
  => Context
  -> LPat GhcPs
  -> TransformT m (LPat GhcPs)
parenifyP Context{..} p@(L _ pat)
  | IsLhs <- ctxtParentPrec
  , needed pat =
    mkParen' (\an -> ParPat an (setEntryDP p (SameLine 0)))
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
    needed (ConPat _ _ (PrefixCon _ []))      = False
#endif
    needed _                                  = True

parenifyT
  :: Monad m => Context -> LHsType GhcPs -> TransformT m (LHsType GhcPs)
parenifyT Context{..} lty@(L _ ty)
  | needed ty = mkParen' (\an -> HsParTy an (setEntryDP lty (SameLine 0)))
  | otherwise = return lty
  where
    needed HsAppTy{}
      | IsHsAppsTy <- ctxtParentPrec = True
      | otherwise = False
    needed t = hsTypeNeedsParens (PprPrec 10) t

unparenT :: LHsType GhcPs -> LHsType GhcPs
unparenT (L _ (HsParTy _ ty)) = ty
unparenT ty = ty

unparenP :: LPat GhcPs -> LPat GhcPs
unparenP (L _ (ParPat _ p)) = p
unparenP p = p

--------------------------------------------------------------------

bitraverseHsConDetails
  :: Applicative m
  => ([tyarg] -> m [tyarg'])
  -> (arg -> m arg')
  -> (rec -> m rec')
  -> HsConDetails tyarg arg rec
  -> m (HsConDetails tyarg' arg' rec')
bitraverseHsConDetails argt argf _ (PrefixCon tyargs args) =
  PrefixCon <$> (argt tyargs) <*> (argf `traverse` args)
bitraverseHsConDetails _ _ recf (RecCon r) =
  RecCon <$> recf r
bitraverseHsConDetails _ argf _ (InfixCon a1 a2) =
  InfixCon <$> argf a1 <*> argf a2
