-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE CPP #-}
{-# LANGUAGE ViewPatterns #-}
module Retrie.Subst (subst) where

import Control.Monad.Writer.Strict
import Data.Generics

import Retrie.Context
import Retrie.ExactPrint
import Retrie.Expr
import Retrie.GHC
import Retrie.Substitution
import Retrie.SYB
import Retrie.Types
import Retrie.Util

------------------------------------------------------------------------

-- | Perform the given 'Substitution' on an AST, avoiding variable capture
-- by alpha-renaming binders as needed.
subst
  :: (MonadIO m, Data ast)
  => Substitution
  -> Context
  -> ast
  -> TransformT m ast
subst sub ctxt =
  everywhereMWithContextBut bottomUp (const False) updateContext f ctxt'
  where
    ctxt' = ctxt { ctxtSubst = Just sub }
    f c =
      mkM (substExpr c)
        `extM` substPat c
        `extM` substType c
        `extM` substHsMatchContext c
        `extM` substBind c

lookupHoleVar :: RdrName -> Context -> Maybe HoleVal
lookupHoleVar rdr ctxt = do
  sub <- ctxtSubst ctxt
  lookupSubst (rdrFS rdr) sub

substExpr
  :: MonadIO m
  => Context
  -> LHsExpr GhcPs
  -> TransformT m (LHsExpr GhcPs)
substExpr ctxt e@(L l1 (HsVar x (L l2 v))) =
  case lookupHoleVar v ctxt of
    Just (HoleExpr eA) -> do
      -- lift $ liftIO $ debugPrint Loud "substExpr:HoleExpr:e" [showAst e]
      -- lift $ liftIO $ debugPrint Loud "substExpr:HoleExpr:eA" [showAst eA]
      e0 <- graftA (unparen <$> eA)
      let comments = hasComments e0
      -- unless comments $ transferEntryDPT e e'
      e1 <- if comments
               then return e0
               else transferEntryDP e e0
      e2 <- transferAnnsT isComma e e1
      -- let e'' = setEntryDP e' (SameLine 1)
      -- lift $ liftIO $ debugPrint Loud "substExpr:HoleExpr:e2" [showAst e2]
      parenify ctxt e2
    Just (HoleRdr rdr) ->
      return $ L l1 $ HsVar x $ L l2 rdr
    _ -> return e
substExpr _ e = return e

substPat
  :: MonadIO m
  => Context
  -> LPat GhcPs
  -> TransformT m (LPat GhcPs)
substPat ctxt (dLPat -> Just p@(L l1 (VarPat x _vl@(L l2 v)))) = fmap cLPat $
  case lookupHoleVar v ctxt of
    Just (HolePat pA) -> do
      -- lift $ liftIO $ debugPrint Loud "substPat:HolePat:p" [showAst p]
      -- lift $ liftIO $ debugPrint Loud "substPat:HolePat:pA" [showAst pA]
      p' <- graftA (unparenP <$> pA)
      p0 <- transferEntryAnnsT isComma p p'
      -- the relevant entry delta is sometimes attached to
      -- the OccName and not to the VarPat.
      -- This seems to be the case only when the pattern comes from a lhs,
      -- whereas it has no annotations in patterns found in rhs's.
      -- tryTransferEntryDPT vl p'
      parenifyP ctxt p0
    Just (HoleRdr rdr) ->
      return $ L l1 $ VarPat x $ L l2 rdr
    _ -> return p
substPat _ p = return p

substType
  :: MonadIO m
  => Context
  -> LHsType GhcPs
  -> TransformT m (LHsType GhcPs)
substType ctxt ty
  | Just (L _ v) <- tyvarRdrName (unLoc ty)
  , Just (HoleType tyA) <- lookupHoleVar v ctxt = do
    -- lift $ liftIO $ debugPrint Loud "substType:HoleType:ty" [showAst ty]
    -- lift $ liftIO $ debugPrint Loud "substType:HoleType:tyA" [showAst tyA]
    ty' <- graftA (unparenT <$> tyA)
    ty0 <- transferEntryAnnsT isComma ty ty'
    parenifyT ctxt ty0
substType _ ty = return ty

-- You might reasonably think that we would replace the RdrName in FunBind...
-- but no, exactprint only cares about the RdrName in the MatchGroup matches,
-- which are here. In case that changes in the future, we define substBind too.
substHsMatchContext
  :: Monad m
  => Context
#if __GLASGOW_HASKELL__ < 900
  -> HsMatchContext RdrName
  -> TransformT m (HsMatchContext RdrName)
#else
  -> HsMatchContext GhcPs
  -> TransformT m (HsMatchContext GhcPs)
#endif
substHsMatchContext ctxt (FunRhs (L l v) f s)
  | Just (HoleRdr rdr) <- lookupHoleVar v ctxt =
    return $ FunRhs (L l rdr) f s
substHsMatchContext _ other = return other

substBind
  :: Monad m
  => Context
  -> HsBind GhcPs
  -> TransformT m (HsBind GhcPs)
substBind ctxt fb@FunBind{}
  | L l v <- fun_id fb
  , Just (HoleRdr rdr) <- lookupHoleVar v ctxt =
    return fb { fun_id = L l rdr }
substBind _ other = return other
