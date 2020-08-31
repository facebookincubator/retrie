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
import Control.Monad
import Data.List
import System.Exit
import System.FilePath
import System.Process
import System.IO (hPutStrLn, stderr)

data Verbosity = Silent | Normal | Loud
  deriving (Eq, Ord, Show)

debugPrint :: Verbosity -> String -> [String] -> IO ()
debugPrint verbosity header ls
  | verbosity < Loud = return ()
  | otherwise = mapM_ putStrLn (header:ls)

-- | Returns predicate which says whether filepath is ignored by VCS.
vcsIgnorePred :: Verbosity -> FilePath -> IO (Maybe (FilePath -> Bool))
vcsIgnorePred verbosity fp = do
  -- We just try to run both 'git' and 'hg' here. Only one should succeed,
  -- because a directory can't be both a git repo and an hg repo.
  -- If both fail, then the whole predicate is Nothing and we keep going
  -- without ignoring any files. Not ideal, but ignoring is just a convenience
  -- to save wasted time rewriting ignored files, so not the end of the world.
  (gitPred, hgPred) <-
    concurrently (gitIgnorePred verbosity fp) (hgIgnorePred verbosity fp)
  return $ gitPred <|> hgPred

-- | Read .gitignore in dir and if successful, return predicate for whether
-- given repo path should be ignored.
gitIgnorePred :: Verbosity -> FilePath -> IO (Maybe (FilePath -> Bool))
gitIgnorePred verbosity targetDir = ignoreWorker "gitIgnorePred: " verbosity targetDir id $
  proc "git"
    [ "ls-files"
    , "--ignored"
    , "--exclude-standard"
    , "--others"
    , "--directory"
    , targetDir
    ]

-- | Read .hgignore in dir and if successful, return predicate for whether
-- given repo path should be ignored.
hgIgnorePred :: Verbosity -> FilePath -> IO (Maybe (FilePath -> Bool))
hgIgnorePred verbosity targetDir =
  -- .hg looks like an extension, so have to add this after the partition
  ignoreWorker "hgIgnorePred: " verbosity targetDir (normalise (targetDir </> ".hg") :) $
    proc "hg"
      [ "status"
      , "--ignored"
      , "--no-status"
      , "-I"
      , "re:.*\\.hs$"
      ]

ignoreWorker
  :: String
  -> Verbosity
  -> FilePath
  -> ([FilePath] -> [FilePath])
  -> CreateProcess
  -> IO (Maybe (FilePath -> Bool))
ignoreWorker prefix verbosity targetDir extraDirs cmd = handle (handler prefix verbosity) $ do
  let command = cmd { cwd = Just targetDir }
  (ec, fps, err) <- readCreateProcessWithExitCode command ""
  case ec of
    ExitSuccess -> do
      let
        (ifiles, dirs) = partition hasExtension
          [ normalise $ targetDir </> dropTrailingPathSeparator f
          | f <- lines fps ]
        idirs = extraDirs dirs
      return $ Just $ \fp -> fp `elem` ifiles || any (`isPrefixOf` fp) idirs
    ExitFailure _ -> do
      when (verbosity > Normal) $ putErrStrLn $ prefix ++ err
      return Nothing

handler :: String -> Verbosity -> IOError -> IO (Maybe a)
handler prefix verbosity err = do
  when (verbosity > Normal) $ putErrStrLn $ prefix ++ show err
  return Nothing

putErrStrLn :: String -> IO ()
putErrStrLn = hPutStrLn stderr

-- | Like 'try', but rethrows async exceptions.
trySync :: IO a -> IO (Either SomeException a)
trySync io = catch (Right <$> io) $ \e ->
  case fromException e of
    Just (_ :: SomeAsyncException) -> throwIO e
    Nothing -> return (Left e)

missingSyntax :: String -> a
missingSyntax constructor = error $ unlines
  [ "Missing syntax support: " ++ constructor
  , "Please file an issue at https://github.com/facebookincubator/retrie/issues"
  , "with an example of the rewrite you are attempting and we'll add it."
  ]
