{-# LANGUAGE CPP #-}
module Retrie.ExactPrint.Compat
    (
      ExactPrint(..)
    , exactPrint
    , parseModule
    , makeDeltaAst
    , E.showAst
    , E.TransformT(..)
    , E.setEntryDP
    , E.getEntryDP
    , E.d0
    , E.uniqueSrcSpanT
#if __GLASGOW_HASKELL__ >= 910
    , E.addCommentOrigDeltas
    , transferEntryDP
    , E.splitCommentsStart
    , E.splitCommentsEnd
#else
    , E.transferEntryDP
#endif
    ) where

import qualified Language.Haskell.GHC.ExactPrint.Utils as E
import qualified Language.Haskell.GHC.ExactPrint.Transform as E
import Language.Haskell.GHC.ExactPrint (ExactPrint(..), parseModule, exactPrint, makeDeltaAst)

#if __GLASGOW_HASKELL__ >= 910
transferEntryDP a b = pure $ E.transferEntryDP a b
#else

#endif
