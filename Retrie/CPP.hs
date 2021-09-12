-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
module Retrie.CPP
  ( CPP(..)
  , addImportsCPP
  , parseCPPFile
  , parseCPP
  , printCPP
    -- ** Internal interface exported for tests
  , cppFork
  ) where

import Data.Char (isSpace)
import Data.Function (on)
import Data.Functor.Identity
import Data.List (nubBy, sortOn)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import Debug.Trace
import Retrie.ExactPrint
import Retrie.GHC
import Retrie.Replace

-- Note [CPP]
-- We can't just run the pre-processor on files and then rewrite them, because
-- the rewrites will apply to a module that never exists as code! Exactprint
-- has no support for roundtripping CPP, because the GHC parser doesn't
-- actually parse it (it looks for the pragma and then delegates to the
-- pre-processor).
--
-- To solve this, we instead generate all possible versions of the module
-- (exponential in the number of #if directives :-P). We then apply rewrites
-- to all versions, and collect all the 'Replacement's that they generate.
-- We can then use these to splice results back into the original file.
--
-- Suprisingly, this works. It depends on a few observations:
--
-- * We don't need to actually evaluate any CPP directives. This is because
--   we want all versions of the file.
--
-- * Since we don't need to evaluate, we can simply replace all CPP directives
--   with blank lines and the locations of all AST elements in each version of
--   the module will be exactly the same as in the original module. This is the
--   key to splicing properly.
--
-- * Replacements can be spliced in directly with no smarts about binders, etc,
--   because retrie did the instantiation during matching.
--

-- The CPP Type ----------------------------------------------------------------

data CPP a
  = NoCPP a
  | CPP Text [AnnotatedImports] [a]

instance Functor CPP where
  fmap f (NoCPP x) = NoCPP (f x)
  fmap f (CPP orig is xs) = CPP orig is (map f xs)

instance Foldable CPP where
  foldMap f (NoCPP x) = f x
  foldMap f (CPP _ _ xs) = foldMap f xs

instance Traversable CPP where
  traverse f (NoCPP x) = NoCPP <$> f x
  traverse f (CPP orig is xs) = CPP orig is <$> traverse f xs

addImportsCPP
  :: [AnnotatedImports]
  -> CPP AnnotatedModule
  -> CPP AnnotatedModule
addImportsCPP is (NoCPP m) =
  NoCPP $ runIdentity $ transformA m $ insertImports is
addImportsCPP is (CPP orig is' ms) = CPP orig (is++is') ms

-- Parsing a CPP Module --------------------------------------------------------

parseCPPFile
  :: (FilePath -> String -> IO AnnotatedModule)
  -> FilePath
  -> IO (CPP AnnotatedModule)
parseCPPFile p fp =
  -- read file strictly
  Text.readFile fp >>= parseCPP (p fp)

parseCPP
  :: Monad m
  => (String -> m AnnotatedModule)
  -> Text -> m (CPP AnnotatedModule)
parseCPP p orig
  | any isCPP (Text.lines orig) =
    CPP orig [] <$> mapM (p . Text.unpack) (cppFork orig)
  | otherwise = NoCPP <$> p (Text.unpack orig)

-- Printing a CPP Module -------------------------------------------------------

printCPP :: [Replacement] -> CPP AnnotatedModule -> String
printCPP _ (NoCPP m) = printA m
-- printCPP _ (NoCPP m) = error $ "printCPP:m=" ++ showAstA m
printCPP repls (CPP orig is ms) = Text.unpack $ Text.unlines $
  case is of
    [] -> splice "" 1 1 sorted origLines
    _ ->
      splice
        (Text.unlines newHeader)
        (length revHeader + 1)
        1
        sorted
        (reverse revDecls)
  where
    sorted = sortOn fst
      [ (r, replReplacement)
      | Replacement{..} <- repls
      , Just r <- [getRealSpan replLocation]
      ]

    origLines = Text.lines orig
    mbName = unLoc <$> hsmodName (unLoc $ astA $ head ms)
    importLines = runIdentity $ fmap astA $ transformA (filterAndFlatten mbName is) $
      mapM $ fmap (Text.pack . dropWhile isSpace . printA) . pruneA

    p t = isImport t || isModule t || isPragma t
    (revDecls, revHeader) = break p (reverse origLines)
    newHeader = reverse revHeader ++ importLines

splice :: Text -> Int -> Int -> [(RealSrcSpan, String)] -> [Text] -> [Text]
splice _ _ _ _ [] = []
splice prefix _ _ [] (t:ts) = prefix <> t : ts
splice prefix l c rs@((r, repl):rs') ts@(t:ts')
  | srcSpanStartLine r > l =
      -- Next rewrite is not on this line. Output line.
      prefix <> t : splice "" (l+1) 1 rs ts'
  | srcSpanStartLine r < l || srcSpanStartCol r < c =
      -- Next rewrite starts before current position. This happens when
      -- the same rewrite is made in multiple versions of the CPP'd module.
      -- Drop the duplicate rewrite and keep going.
      splice prefix l c rs' ts
  | (old, ln:lns) <- splitAt (srcSpanEndLine r - l) ts =
      -- The next rewrite starts on this line.
      let
        start = srcSpanStartCol r
        end = srcSpanEndCol r

        prefix' = prefix <> Text.take (start - c) t <> Text.pack repl
        ln' = Text.drop (end - c) ln

        -- For an example of how this can happen, see the CPPConflict test.
        errMsg = unlines
          [ "Refusing to rewrite across CPP directives."
          , ""
          , "Location: " ++ locStr
          , ""
          , "Original:"
          , ""
          , Text.unpack orig
          , ""
          , "Replacement:"
          , ""
          , repl
          ]
        orig =
          Text.unlines $ (prefix <> t : drop 1 old) ++ [Text.take (end - c) ln]
        locStr = unpackFS (srcSpanFile r) ++ ":" ++ show l ++ ":" ++ show start
      in
        if any isCPP old
        then trace errMsg $ splice prefix l c rs' ts
        else splice prefix' (srcSpanEndLine r) end rs' (ln':lns)
  | otherwise = error "printCPP: impossible replacement past end of file"

-- Forking the module ----------------------------------------------------------

cppFork :: Text -> [Text]
cppFork = cppTreeToList . mkCPPTree

-- | Tree representing the module. Each #endif becomes a Node.
data CPPTree
  = Node [Text] CPPTree CPPTree
  | Leaf [Text]

-- | Stack type used to keep track of how many #ifs we are nested into.
-- Controls whether we emit lines into each version of the module.
data CPPBranch
  = CPPTrue -- print until an 'else'
  | CPPFalse -- print blanks until an 'else' or 'endif'
  | CPPOmit -- print blanks until an 'endif'

-- | Build CPPTree from lines of the module.
mkCPPTree :: Text -> CPPTree
mkCPPTree = go False [] [] . reverse . Text.lines
  -- We reverse the lines once up front, then process the module from bottom
  -- to top, branching at #endifs. If we were to process from top to bottom,
  -- we'd have to reverse each version later, rather than reversing the original
  -- once. This also makes it easy to spot import statements and stop branching
  -- since we don't care about differences in imports.
  where
    go :: Bool -> [CPPBranch] -> [Text] -> [Text] -> CPPTree
    go _ _ suffix [] = Leaf suffix
    go True [] suffix ls =
      Leaf (blankifyAndReverse suffix ls) -- See Note [Imports]
    go seenImport st suffix (l:ls) =
      case extractCPPCond l of
        Just If -> -- pops from stack
          case st of
            (_:st') -> emptyLine st'
            [] -> error "mkCPPTree: if with empty stack"
        Just ElIf -> -- stack same size
          case st of
            (CPPOmit:_) -> emptyLine st
            (CPPFalse:st') -> emptyLine (CPPOmit:st')
            (CPPTrue:st') -> -- See Note [ElIf]
              let
                omittedSuffix = replicate (length suffix) ""
              in
                Node
                  []
                  (emptyLine (CPPOmit:st'))
                  (go seenImport (CPPTrue:st') ("":omittedSuffix) ls)
            [] -> error "mkCPPTree: else with empty stack"
        Just Else -> -- stack same size
          case st of
            (CPPOmit:_) -> emptyLine st
            (CPPTrue:st') -> emptyLine (CPPFalse:st')
            (CPPFalse:st') -> emptyLine (CPPTrue:st')
            [] -> error "mkCPPTree: else with empty stack"
        Just EndIf -> -- push to stack
          case st of
            (CPPOmit:_) -> emptyLine (CPPOmit:st)
            (CPPFalse:_) -> emptyLine (CPPOmit:st)
            _ ->
              Node
                suffix
                (go seenImport (CPPTrue:st) [""] ls)
                (go seenImport (CPPFalse:st) [""] ls)
        Nothing -> -- stack same size
          case st of
            (CPPOmit:_) -> go seenImport' st ("":suffix) ls
            (CPPFalse:_) -> go seenImport' st ("":suffix) ls
            _ -> go seenImport' st (blankCPP l:suffix) ls
      where
        emptyLine st' = go seenImport st' ("":suffix) ls
        seenImport' = seenImport || isImport l

    blankifyAndReverse :: [Text] -> [Text] -> [Text]
    blankifyAndReverse suffix [] = suffix
    blankifyAndReverse suffix (l:ls) = blankifyAndReverse (blankCPP l:suffix) ls

-- Note [Imports]
-- If we have seen an import statement, and have an empty stack, that means all
-- conditionals above this point only control imports/exports, etc. Retrie
-- doesn't match in those places anyway, and the imports don't matter because
-- we only parse, no renaming. As a micro-optimization, we can stop branching.
-- This saves forking the module in the common case that CPP is used to choose
-- imports. We have to wait for stack to be empty because we might have seen an
-- import in one branch, but there is a decl in the other branch.

-- Note [ElIf]
-- The way we handle #elif is pretty subtle. Some observations:
-- If we're on the CPPOmit branch, keep omitting up to the next #if, like usual.
-- If we're on the CPPFalse branch, we didn't show the #elif, but either we
-- showed the #else, or this whole #if might not output anything. So either way,
-- we need to omit up to the next #if.
-- If we're on the CPPTrue branch, we definitely showed the #elif, so we need to
-- fork with a Node. One side of the branch omits up to the next #if. The other
-- side is as if we have omitted everything from the last #endif, and we
-- continue showing up from here. This will show whatever is above the #elif.
-- It is crucial we do this branching on the CPPTrue branch, so any #elif
-- above this point is also handled correctly.

-- | Expand CPPTree into 2^h-1 versions of the module.
cppTreeToList :: CPPTree -> [Text]
cppTreeToList t = go [] t []
  where
    go rest (Leaf suffix) = (Text.unlines (suffix ++ rest) :)
    go rest (Node suffix l r) =
      let rest' = suffix ++ rest -- right-nested
      in go rest' l . go rest' r

-- Spotting CPP directives -----------------------------------------------------

data CPPCond = If | ElIf | Else | EndIf

extractCPPCond :: Text -> Maybe CPPCond
extractCPPCond t
  | Just ('#',t') <- Text.uncons t =
    case Text.words t' of
      ("if":_) -> Just If
      ("else":_) -> Just Else
      ("elif":_) -> Just ElIf
      ("endif":_) -> Just EndIf
      _ -> Nothing
  | otherwise = Nothing

blankCPP :: Text -> Text
blankCPP t
  | isCPP t = ""
  | otherwise = t

isCPP :: Text -> Bool
isCPP = Text.isPrefixOf "#"

isImport :: Text -> Bool
isImport = Text.isPrefixOf "import"

isModule :: Text -> Bool
isModule = Text.isPrefixOf "module"

isPragma :: Text -> Bool
isPragma = Text.isPrefixOf "{-#"

-------------------------------------------------------------------------------
-- This would make more sense in Retrie.Expr, but that creates an import cycle.
-- Ironic, I know.

insertImports
  :: Monad m
  => [AnnotatedImports]   -- ^ imports and their annotations
  -> Located HsModule     -- ^ target module
  -> TransformT m (Located HsModule)
insertImports is (L l m) = do
  imps <- graftA $ filterAndFlatten (unLoc <$> hsmodName m) is
  let
    deduped = nubBy (eqImportDecl `on` unLoc) $ hsmodImports m ++ imps
  return $ L l m { hsmodImports = deduped }

filterAndFlatten :: Maybe ModuleName -> [AnnotatedImports] -> AnnotatedImports
filterAndFlatten mbName is =
  runIdentity $ transformA (mconcat is) $ return . externalImps mbName
  where
    externalImps :: Maybe ModuleName -> [LImportDecl GhcPs] -> [LImportDecl GhcPs]
    externalImps (Just mn) = filter ((/= mn) . unLoc . ideclName . unLoc)
    externalImps _ = id

eqImportDecl :: ImportDecl GhcPs -> ImportDecl GhcPs -> Bool
eqImportDecl x y =
  ((==) `on` unLoc . ideclName) x y
  && ((==) `on` ideclQualified) x y
  && ((==) `on` ideclAs) x y
  && ((==) `on` ideclHiding) x y
  && ((==) `on` ideclPkgQual) x y
  && ((==) `on` ideclSource) x y
  && ((==) `on` ideclSafe) x y
  -- intentionally leave out ideclImplicit and ideclSourceSrc
  -- former doesn't matter for this check, latter is prone to whitespace issues
