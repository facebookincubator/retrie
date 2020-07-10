-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE OverloadedStrings #-}
module Retrie.Rewrites
  ( RewriteSpec(..)
  , QualifiedName
  , parseRewriteSpecs
  , parseQualified
  , parseAdhocs
  ) where

import Control.Exception
import Data.Either (partitionEithers)
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Text as Text
import Data.Traversable
import System.FilePath

import Retrie.CPP
import Retrie.ExactPrint
import Retrie.Fixity
import Retrie.GHC
import Retrie.Rewrites.Function
import Retrie.Rewrites.Rules
import Retrie.Rewrites.Types
import Retrie.Types
import Retrie.Universe

-- | A qualified name. (e.g. @"Module.Name.functionName"@)
type QualifiedName = String

-- | Possible ways to specify rewrites to 'parseRewrites'.
data RewriteSpec
  = Adhoc String
    -- ^ Equation in RULES-format. (e.g. @"forall x. succ (pred x) = x"@)
    -- Will be applied left-to-right.
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

parseRewriteSpecs
  :: (FilePath -> IO (CPP AnnotatedModule))
  -> FixityEnv
  -> [RewriteSpec]
  -> IO [Rewrite Universe]
parseRewriteSpecs parser fixityEnv specs = do
  (adhocs, fileBased) <- partitionEithers <$> sequence
    [ case spec of
        Adhoc rule -> return $ Left $ Left rule
        AdhocType tySyn -> return $ Left $ Right tySyn
        Fold name -> mkFileBased FoldUnfold RightToLeft name
        RuleBackward name -> mkFileBased Rule RightToLeft name
        RuleForward name -> mkFileBased Rule LeftToRight name
        TypeBackward name -> mkFileBased Type RightToLeft name
        TypeForward name -> mkFileBased Type LeftToRight name
        Unfold name -> mkFileBased FoldUnfold LeftToRight name
    | spec <- specs
    ]
  let (adhocRules, adhocTypes) = partitionEithers adhocs
  fbRewrites <- parseFileBased parser fileBased
  adhocExpressionRewrites <- parseAdhocs fixityEnv adhocRules
  adhocTypeRewrites <- parseAdhocTypes fixityEnv adhocTypes
  return $ fbRewrites ++ adhocExpressionRewrites ++ adhocTypeRewrites
  where
    mkFileBased ty dir name =
      case parseQualified name of
        Left err -> throwIO $ ErrorCall $ "parseRewriteSpecs: " ++ err
        Right (fp, fs) -> return $ Right (fp, [(ty, [(fs, dir)])])

data FileBasedTy = FoldUnfold | Rule | Type
  deriving (Eq, Ord)

parseFileBased
  :: (FilePath -> IO (CPP AnnotatedModule))
  -> [(FilePath, [(FileBasedTy, [(FastString, Direction)])])]
  -> IO [Rewrite Universe]
parseFileBased _ [] = return []
parseFileBased parser specs = concat <$> mapM (uncurry goFile) (gather specs)
  where
    gather :: Ord a => [(a,[b])] -> [(a,[b])]
    gather = Map.toList . Map.fromListWith (++)

    goFile
      :: FilePath
      -> [(FileBasedTy, [(FastString, Direction)])]
      -> IO [Rewrite Universe]
    goFile fp rules = do
      cpp <- parser fp
      concat <$> mapM (uncurry $ constructRewrites cpp) (gather rules)

parseAdhocs :: FixityEnv -> [String] -> IO [Rewrite Universe]
parseAdhocs _ [] = return []
parseAdhocs fixities adhocs = do
  cpp <-
    parseCPP (parseContent fixities "parseAdhocs") (Text.unlines adhocRules)
  constructRewrites cpp Rule adhocSpecs
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

parseAdhocTypes :: FixityEnv -> [String] -> IO [Rewrite Universe]
parseAdhocTypes _ [] = return []
parseAdhocTypes fixities tySyns = do
  print adhocTySyns
  cpp <-
    parseCPP (parseContent fixities "parseAdhocTypes") (Text.unlines adhocTySyns)
  constructRewrites cpp Type adhocSpecs
  where
    (adhocSpecs, adhocTySyns) = unzip
      [ ( (mkFastString nm, LeftToRight), "type " <> Text.pack s)
      | s <- tySyns
      , Just nm <- [listToMaybe $ words s]
      ]

constructRewrites
  :: CPP AnnotatedModule
  -> FileBasedTy
  -> [(FastString, Direction)]
  -> IO [Rewrite Universe]
constructRewrites cpp ty specs = do
  cppM <- traverse (tyBuilder ty specs) cpp
  let
    names = nonDetEltsUniqSet $ mkUniqSet $ map fst specs

    nameOf FoldUnfold = "definition"
    nameOf Rule = "rule"
    nameOf Type = "type synonym"

    m = foldr (plusUFM_C (++)) emptyUFM cppM

  fmap concat $ forM names $ \fs ->
    case lookupUFM m fs of
      Nothing ->
        fail $ "could not find " ++ nameOf ty ++ " named " ++ unpackFS fs
      Just rrs -> return rrs

tyBuilder
  :: FileBasedTy
  -> [(FastString, Direction)]
  -> AnnotatedModule
  -> IO (UniqFM [Rewrite Universe])
tyBuilder FoldUnfold specs am = promote <$> dfnsToRewrites specs am
tyBuilder Rule specs am = promote <$> rulesToRewrites specs am
tyBuilder Type specs am = promote <$> typeSynonymsToRewrites specs am

promote :: Matchable a => UniqFM [Rewrite a] -> UniqFM [Rewrite Universe]
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
