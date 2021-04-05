-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE CPP #-}
module Retrie.Pretty
  ( noColor
  , addColor
  , ppSrcSpan
  , ColoriseFun
  , strip
  , ppRepl
  , linesMap
  ) where

import Data.Char
import Data.List
import Data.Maybe
import qualified Data.HashMap.Strict as HashMap
import System.Console.ANSI

import Retrie.GHC

type ColoriseFun = ColorIntensity -> Color -> String -> String

noColor :: ColoriseFun
noColor _ _ = id

addColor :: ColoriseFun
addColor intensity color x = mconcat
  [ setSGRCode [SetColor Foreground intensity color]
  , x
  , setSGRCode [Reset]
  ]

-- | Pretty print location of the file.
ppSrcSpan :: ColoriseFun -> SrcSpan -> String
ppSrcSpan colorise spn = case srcSpanStart spn of
  UnhelpfulLoc x -> unpackFS x
#if __GLASGOW_HASKELL__ < 900
  RealSrcLoc loc -> intercalate (colorise Dull Cyan ":")
#else
  RealSrcLoc loc _ -> intercalate (colorise Dull Cyan ":")
#endif
    [ colorise Dull Magenta $ unpackFS $ srcLocFile loc
    , colorise Dull Green $ show $ srcLocLine loc
    , colorise Dull Green $ show $ srcLocCol loc
    , ""
    ]

-- | Get lines covering span and replace span with replacement string.
ppRepl :: HashMap.HashMap Int String -> SrcSpan -> String -> [String]
ppRepl lMap spn replacement = fromMaybe [replacement] $ do
  startPos <- getRealLoc $ srcSpanStart spn
  endPos <- getRealLoc $ srcSpanEnd spn
  startLine <- getLine' startPos
  endLine <- getLine' endPos
  return $ lines $ mconcat
    [ take (srcLocCol startPos - 1) startLine
    , dropWhile isSpace replacement
    , drop (srcLocCol endPos - 1) endLine
    ]
  where
    getLine' pos = HashMap.lookup (srcLocLine pos) lMap

-- | Return HashMap from line number to line of a file.
linesMap :: String -> IO (HashMap.HashMap Int String)
linesMap fp = HashMap.fromList . zip [1..] . lines <$> readFile fp

strip :: String -> String
strip = dropWhileEnd isSpace . dropWhile isSpace
