-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE ScopedTypeVariables #-}
module Retrie.Util where

import Control.Applicative
import Control.Concurrent.Async
import Control.Exception
import Data.Bifunctor (second)
import Data.List
import System.Exit
import System.FilePath
import System.Process

import Retrie.GHC

overlaps :: SrcSpan -> SrcSpan -> Bool
overlaps (RealSrcSpan s1) (RealSrcSpan s2) =
     srcSpanFile s1 == srcSpanFile s2 &&
     ((srcSpanStartLine s1, srcSpanStartCol s1) `within` s2 ||
      (srcSpanEndLine s1, srcSpanEndCol s1) `within` s2)
overlaps _ _ = False

within :: (Int, Int) -> RealSrcSpan -> Bool
within (l,p) s =
  srcSpanStartLine s <= l &&
  srcSpanStartCol s <= p  &&
  srcSpanEndLine s >= l   &&
  srcSpanEndCol s >= p

lineCount :: [SrcSpan] -> Int
lineCount ss = sum
  [ srcSpanEndLine s - srcSpanStartLine s + 1
  | RealSrcSpan s <- ss
  ]

showRdrs :: [RdrName] -> String
showRdrs = show . map (occNameString . occName)

data Verbosity = Silent | Normal | Loud
  deriving (Eq, Ord, Show)

debugPrint :: Verbosity -> String -> [String] -> IO ()
debugPrint verbosity header ls
  | verbosity < Loud = return ()
  | otherwise = mapM_ putStrLn (header:ls)

-- | Returns predicate which says whether filepath is ignored by VCS.
vcsIgnorePred :: FilePath -> IO (Maybe (FilePath -> Bool))
vcsIgnorePred fp = do
  (gitPred, hgPred) <- concurrently (gitIgnorePred fp) (hgIgnorePred fp)
  return $ gitPred <|> hgPred

-- | Read .gitignore in dir and if successful, return predicate for whether
-- given repo path should be ignored.
gitIgnorePred :: FilePath -> IO (Maybe (FilePath -> Bool))
gitIgnorePred targetDir = do
  let
    cmd =
      (proc "git"
        [ "ls-files"
        , "--ignored"
        , "--exclude-standard"
        , "--others"
        , "--directory"
        , targetDir
        ])
      { cwd = Just targetDir }
  (ec, fps, _) <- readCreateProcessWithExitCode cmd ""
  case ec of
    ExitSuccess -> do
      let
        (ifiles, idirs) = partition hasExtension
          [ normalise $ targetDir </> dropTrailingPathSeparator f
          | f <- lines fps ]
      return $ Just (\fp -> fp `elem` ifiles || any (`isPrefixOf` fp) idirs)
    ExitFailure _ -> return Nothing

-- | Read .hgignore in dir and if successful, return predicate for whether
-- given repo path should be ignored.
hgIgnorePred :: FilePath -> IO (Maybe (FilePath -> Bool))
hgIgnorePred targetDir = do
  let
    cmd =
      (proc "hg"
        [ "status"
        , "--ignored"
        , "--no-status"
        , "-I"
        , "re:.*\\.hs$"
        ])
      { cwd = Just targetDir }
  (ec, fps, _) <- readCreateProcessWithExitCode cmd ""
  case ec of
    ExitSuccess -> do
      let
        (ifiles, dirs) = partition hasExtension
          [ normalise $ targetDir </> dropTrailingPathSeparator f
          | f <- lines fps ]
        -- .hg looks like an extension, so have to add this after the partition
        idirs = normalise (targetDir </> ".hg") : dirs
      return $ Just $ \fp -> fp `elem` ifiles || any (`isPrefixOf` fp) idirs
    ExitFailure _ -> return Nothing

-- | Like 'try', but rethrows async exceptions.
trySync :: IO a -> IO (Either SomeException a)
trySync io = catch (Right <$> io) $ \e ->
  case fromException e of
    Just (_ :: SomeAsyncException) -> throwIO e
    Nothing -> return (Left e)

uniqBag :: Uniquable a => [(a,b)] -> UniqFM [b]
uniqBag = listToUFM_C (++) . map (second pure)
