{-# LANGUAGE RecordWildCards #-}
-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
module Retrie.Rewrites
  ( RewriteSpec(..)
  , QualifiedName
  , parseRewriteSpecs
  , parseQualified
  , parseAdhocs
  ) where

import Control.Exception
import qualified Data.Map as Map
import Data.Maybe
import Data.Data hiding (Fixity)
import qualified Data.Text as Text
import Data.Traversable
import System.FilePath

import Retrie.CPP
import Retrie.ExactPrint
import Retrie.Fixity
import Retrie.GHC
import Retrie.Rewrites.Function
import Retrie.Rewrites.Patterns
import Retrie.Rewrites.Rules
import Retrie.Rewrites.Types
import Retrie.Types
import Retrie.Universe
import Retrie.Util

-- | A qualified name. (e.g. @"Module.Name.functionName"@)
type QualifiedName = String

-- | Possible ways to specify rewrites to 'parseRewrites'.
data RewriteSpec
  = Adhoc String
    -- ^ Equation in RULES-format. (e.g. @"forall x. succ (pred x) = x"@)
    -- Will be applied left-to-right.
  | AdhocPattern String
    -- ^ Equation in pattern-synonym format, _without_ the keyword 'pattern'.
  | AdhocType String
    -- ^ Equation in type-synonym format, _without_ the keyword 'type'.
  | Fold QualifiedName
    -- ^ Fold a function definition. The inverse of unfolding/inlining.
    -- Replaces instances of the function body with calls to the function.
  | RuleBackward QualifiedName
    -- ^ Apply a GHC RULE right-to-left.
  | RuleForward QualifiedName
    -- ^ Apply a GHC RULE left-to-right.
  | TypeBackward QualifiedName
    -- ^ Apply a type synonym right-to-left.
  | TypeForward QualifiedName
    -- ^ Apply a type synonym left-to-right.
  | Unfold QualifiedName
    -- ^ Unfold, or inline, a function definition.
  | PatternForward QualifiedName
    -- ^ Unfold a pattern synonym
  | PatternBackward QualifiedName
    -- ^ Fold a pattern synonym, replacing instances of the rhs with the synonym


data ClassifiedRewrites = ClassifiedRewrites
  { adhocRules :: [String]
  , adhocPatterns :: [String]
  , adhocTypes :: [String]
  , fileBased :: [(FilePath, [(FileBasedTy,[(FastString, Direction)])])]
  }

instance Monoid ClassifiedRewrites where
  mempty = ClassifiedRewrites [] [] [] []

instance Semigroup ClassifiedRewrites where
  ClassifiedRewrites a b c d <> ClassifiedRewrites a' b' c' d' =
    ClassifiedRewrites (a <> a') (b <> b') (c <> c') (d <> d')

parseRewriteSpecs
  :: LibDir
  -> (FilePath -> IO (CPP AnnotatedModule))
  -> FixityEnv
  -> [RewriteSpec]
  -> IO [Rewrite Universe]
parseRewriteSpecs libdir parser fixityEnv specs = do
  ClassifiedRewrites{..} <- mconcat <$> sequence
    [ case spec of
        Adhoc rule -> return mempty{adhocRules = [rule]}
        AdhocPattern pSyn -> return mempty{adhocPatterns = [pSyn]}
        AdhocType tySyn -> return mempty{adhocTypes = [tySyn]}
        Fold name -> mkFileBased FoldUnfold RightToLeft name
        RuleBackward name -> mkFileBased Rule RightToLeft name
        RuleForward name -> mkFileBased Rule LeftToRight name
        TypeBackward name -> mkFileBased Type RightToLeft name
        TypeForward name -> mkFileBased Type LeftToRight name
        PatternBackward name -> mkFileBased Pattern RightToLeft name
        PatternForward name -> mkFileBased Pattern LeftToRight name
        Unfold name -> mkFileBased FoldUnfold LeftToRight name
    | spec <- specs
    ]
  fbRewrites <- parseFileBased libdir parser fileBased
  adhocExpressionRewrites <- parseAdhocs libdir fixityEnv adhocRules
  -- debugPrint Loud "parseRewriteSpecs" (["adhocExpressionRewrites:" ++ show adhocRules]  ++ map (\r -> showAst ((astA . qPattern) r)) adhocExpressionRewrites)
  adhocTypeRewrites <- parseAdhocTypes libdir fixityEnv adhocTypes
  -- debugPrint Loud "parseRewriteSpecs" (["adhocTypeRewrites:"] ++ map (\r -> showAst ((astA . qPattern) r)) adhocTypeRewrites)
  adhocPatternRewrites <- parseAdhocPatterns libdir fixityEnv adhocPatterns
  -- debugPrint Loud "parseRewriteSpecs" (["adhocPatternRewrites:"] ++ map (\r -> showAst ((astA . qPattern) r)) adhocPatternRewrites)
  return $
    fbRewrites ++
    adhocExpressionRewrites ++
    adhocTypeRewrites ++
    adhocPatternRewrites
  where
    mkFileBased ty dir name =
      case parseQualified name of
        Left err -> throwIO $ ErrorCall $ "parseRewriteSpecs: " ++ err
        Right (fp, fs) -> return mempty{fileBased = [(fp, [(ty, [(fs, dir)])])]}

data FileBasedTy = FoldUnfold | Rule | Type | Pattern
  deriving (Eq, Ord)

parseFileBased
  :: LibDir
  -> (FilePath -> IO (CPP AnnotatedModule))
  -> [(FilePath, [(FileBasedTy, [(FastString, Direction)])])]
  -> IO [Rewrite Universe]
parseFileBased _ _ [] = return []
parseFileBased libdir parser specs = concat <$> mapM (uncurry goFile) (gather specs)
  where
    gather :: Ord a => [(a,[b])] -> [(a,[b])]
    gather = Map.toList . Map.fromListWith (++)

    goFile
      :: FilePath
      -> [(FileBasedTy, [(FastString, Direction)])]
      -> IO [Rewrite Universe]
    goFile fp rules = do
      cpp <- parser fp
      concat <$> mapM (uncurry $ constructRewrites libdir cpp) (gather rules)

parseAdhocs :: LibDir -> FixityEnv -> [String] -> IO [Rewrite Universe]
parseAdhocs _ _ [] = return []
parseAdhocs libdir fixities adhocs = do
  -- debugPrint Loud "parseAdhocs:adhocs" adhocs
  -- debugPrint Loud "parseAdhocs:adhocRules" (map show adhocRules)
  cpp <-
    parseCPP (parseContent libdir fixities "parseAdhocs") (Text.unlines adhocRules)
  -- debugPrint Loud "parseAdhocs:cpp" [showCpp cpp]
  constructRewrites libdir cpp Rule adhocSpecs
  where
    -- In search mode, there is no need to specify a right-hand side, but we
    -- need one to parse as a RULE, so add it if necessary.
    addRHS s
      | '=' `elem` s = s
      | otherwise = s ++ " = undefined"
    (adhocSpecs, adhocRules) = unzip
      [ ( (mkFastString nm, LeftToRight)
        , "{-# RULES \"" <> Text.pack nm <> "\" " <> Text.pack s <> " #-}"
        )
      | (i,s) <- zip [1..] $ map addRHS adhocs
      , let nm = "adhoc" ++ show (i::Int)
      ]


showCpp :: (Data ast, ExactPrint ast) => CPP (Annotated ast) -> String
showCpp (NoCPP c) = showAstA c
showCpp (CPP{}) = "CPP{}"

parseAdhocTypes :: LibDir -> FixityEnv -> [String] -> IO [Rewrite Universe]
parseAdhocTypes _ _ [] = return []
parseAdhocTypes libdir fixities tySyns = do
  print adhocTySyns
  cpp <-
    parseCPP (parseContent libdir fixities "parseAdhocTypes") (Text.unlines adhocTySyns)
  constructRewrites libdir cpp Type adhocSpecs
  where
    (adhocSpecs, adhocTySyns) = unzip
      [ ( (mkFastString nm, LeftToRight), "type " <> Text.pack s)
      | s <- tySyns
      , Just nm <- [listToMaybe $ words s]
      ]

parseAdhocPatterns :: LibDir -> FixityEnv -> [String] -> IO [Rewrite Universe]
parseAdhocPatterns _ _ [] = return []
parseAdhocPatterns libdir fixities patSyns = do
  cpp <-
    parseCPP (parseContent libdir fixities "parseAdhocPatterns")
             (Text.unlines $ pragma : adhocPatSyns)
  constructRewrites libdir cpp Pattern adhocSpecs
  where
    pragma = "{-# LANGUAGE PatternSynonyms #-}"
    (adhocSpecs, adhocPatSyns) = unzip
      [ ( (mkFastString nm, LeftToRight), "pattern " <> Text.pack s)
      | s <- patSyns
      , Just nm <- [listToMaybe $ words s]
      ]

constructRewrites
  :: LibDir
  -> CPP AnnotatedModule
  -> FileBasedTy
  -> [(FastString, Direction)]
  -> IO [Rewrite Universe]
constructRewrites libdir cpp ty specs = do
  cppM <- traverse (tyBuilder libdir ty specs) cpp
  let
    names = nonDetEltsUniqSet $ mkUniqSet $ map fst specs

    nameOf FoldUnfold = "definition"
    nameOf Rule = "rule"
    nameOf Type = "type synonym"
    nameOf Pattern = "pattern synonym"

    m = foldr (plusUFM_C (++)) emptyUFM cppM

  fmap concat $ forM names $ \fs ->
    case lookupUFM m fs of
      Nothing ->
        fail $ "could not find " ++ nameOf ty ++ " named " ++ unpackFS fs
      Just rrs -> do
        -- debugPrint Loud "constructRewrites:cppM" ["enter"]
        return rrs

tyBuilder
  :: LibDir
  -> FileBasedTy
  -> [(FastString, Direction)]
  -> AnnotatedModule
#if __GLASGOW_HASKELL__ < 900
  -> IO (UniqFM [Rewrite Universe])
#else
  -> IO (UniqFM FastString [Rewrite Universe])
#endif
tyBuilder libdir FoldUnfold specs am = promote <$> dfnsToRewrites libdir specs am
tyBuilder _libdir Rule specs am = promote <$> rulesToRewrites specs am
tyBuilder _libdir Type specs am = promote <$> typeSynonymsToRewrites specs am
tyBuilder libdir Pattern specs am = patternSynonymsToRewrites libdir specs am

#if __GLASGOW_HASKELL__ < 900
promote :: Matchable a => UniqFM [Rewrite a] -> UniqFM [Rewrite Universe]
#else
promote :: Matchable a => UniqFM k [Rewrite a] -> UniqFM k [Rewrite Universe]
#endif
promote = fmap (map toURewrite)

parseQualified :: String -> Either String (FilePath, FastString)
parseQualified [] = Left "qualified name is empty"
parseQualified fqName =
  case span isHsSymbol reversed of
    (_,[]) -> mkError "unqualified operator name"
    ([],_) ->
      case span (/='.') reversed of
        (_,[]) -> mkError "unqualified function name"
        (rname,_:rmod) -> mkResult (reverse rmod) (reverse rname)
    (rop,rmod) ->
      case reverse rop of
        '.':op -> mkResult (reverse rmod) op
        _ -> mkError "malformed qualified operator"
  where
    reversed = reverse fqName
    mkError str = Left $ str ++ ": " ++ fqName
    mkResult moduleNameStr occNameStr = Right
      -- 'moduleNameSlashes' gives us system-dependent path separator
      ( moduleNameSlashes (mkModuleName moduleNameStr) <.> "hs"
      , mkFastString occNameStr
      )

isHsSymbol :: Char -> Bool
isHsSymbol = (`elem` symbols)
  -- see https://www.haskell.org/onlinereport/lexemes.html
  where
    symbols :: String
    symbols = "!#$%&*+./<=>?@\\^|-~"
