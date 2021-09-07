-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE RecordWildCards #-}
module Golden
  ( RetrieTest(..)
  , runQueryTest
  , runTest
  , displayAndAssertEqual
  , withTmpCopyOfInputs
  , listDir
  ) where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad
import Data.Bifunctor (second)
import Data.Char (isSpace)
import Data.List (intersperse)
import Options.Applicative
import Retrie
import Retrie.Options hiding (parseOptions)
import Retrie.Run
import System.Directory
import System.FilePath
import System.IO.Temp
import System.Process
import Test.HUnit

data RetrieTest a = RetrieTest
  { rtDir :: FilePath
  , rtName :: String
  , rtTest :: FilePath
  , rtVerbosity :: Verbosity
  , rtRetrie :: Options -> IO (Retrie a)
  }

parseOptions
  :: LibDir
  -> Parser ProtoOptions
  -> FilePath
  -> RetrieTest a
  -> IO Options
parseOptions libdir p dir RetrieTest{..} = do
  flags <- takeFlags <$> readFileNoComments (rtDir </> rtTest)
  case runParserOnString p flags of
    Nothing   ->
      fail $ unwords [rtName, " options did not parse: ", flags]
    Just opts -> do
      resolveOptions libdir opts { targetDir = dir, verbosity = rtVerbosity }

runParserOnString :: Parser a -> String -> Maybe a
runParserOnString p args = getParseResult $
  execParserPure (prefs mempty) (info p fullDesc) (quotedWords args)
  where
    recurse (w,s) = w : quotedWords s
    -- Mimic shell's ability to group tokens with double quotes.
    quotedWords s =
      case dropWhile isSpace s of
        "" -> []
        ('"':cs) -> recurse . second tail $ break (=='"') cs
        s' -> recurse $ break isSpace s'

runTestWrapper
  :: LibDir
  -> Parser ProtoOptions
  -> RetrieTest a
  -> (Options -> IO b)
  -> IO b
runTestWrapper libdir p t@RetrieTest{..} f =
  withTmpCopyOfInputs rtDir $ \dir -> do
    -- Make the Rewrites from the temp file, to get correct SrcSpan's
    opts <- parseOptions libdir p dir t
    f opts { targetFiles = [dir </> replaceExtension rtTest ".hs"] }

runQueryTest
  :: Monoid a
  => LibDir
  -> Parser ProtoOptions
  -> RetrieTest a
  -> IO a
runQueryTest libdir p t@RetrieTest{..} =
  runTestWrapper libdir p t $ \opts -> do
    let writeFn _fp _locs _res = return
    retrie <- rtRetrie opts
    -- A 'writeFn' is only executed if the module changes, so add empty imports
    -- to trip the Changed flag.
    fmap mconcat $ run libdir writeFn id opts $ do
      r <- retrie
      addImports mempty
      return r

runTest :: LibDir -> Parser ProtoOptions -> RetrieTest () -> IO ()
runTest libdir p t@RetrieTest{..} =
  runTestWrapper libdir p t $ \opts@Options{..} -> do
    let
      writeFn fp _locs res _ = writeFile fp res
      [tmpFile] = targetFiles
    before <- evaluate . force =<< readFile tmpFile
    retrie <- rtRetrie opts
    void $ run libdir writeFn id opts $ iterateR iterateN retrie
    res <- readFile tmpFile
    expected <- readFile $ targetDir </> replaceExtension rtTest ".expected"
    displayAndAssertEqual before expected res

displayAndAssertEqual :: String -> String -> String -> IO ()
displayAndAssertEqual before expected res
  | expected == res = return ()
  | otherwise = do
      let bars = replicate 60 '='
      d <- diff expected res
      putStrLn $ unlines $ intersperse bars
        [ ""
        , "Original:", before
        , "Expected:", expected
        , "Got:", res
        , "Diff:", d
        , ""
        ]
      assertFailure "file contents differ"

diff :: String -> String -> IO String
diff s1 s2 = withSystemTempDirectory "diff" $ \dir -> do
  let
    aFile = dir </> "a.txt"
    bFile = dir </> "b.txt"
  writeFile aFile s1
  writeFile bFile s2
  (_ec, so, _) <- readProcessWithExitCode "diff" [aFile, bFile] ""
  return so

-- Copies input dir, mapping *.test to *.hs,
-- and provides a filepath to the root
-- of the copy. Deletes the copy when done.
withTmpCopyOfInputs :: FilePath -> (FilePath -> IO a) -> IO a
withTmpCopyOfInputs inputsDir comp = do
  fs <- listDir inputsDir
  withSystemTempDirectory "inputs" $ \dir -> do
    forM_ fs $ \f -> do
      if takeExtension f `elem` [".test", ".custom"]
        then splitAndCopyTest inputsDir f dir
        else copyFile (inputsDir </> f) (dir </> f)
    comp dir

splitAndCopyTest :: FilePath -> FilePath -> FilePath -> IO ()
splitAndCopyTest inputsDir testFile dstDir = do
  (hs, expected) <- splitTest <$> readFileNoComments (inputsDir </> testFile)
  writeFile (dstDir </> replaceExtension testFile ".hs") hs
  writeFile (dstDir </> replaceExtension testFile ".expected") expected

splitTest :: String -> (String, String)
splitTest = go ([],[]) . takeWhile (/="===") . reverse . lines
  where
    go (hs,ex) [] = (unlines hs, unlines ex)
    go (hs,ex) ([]:ls) = go ([]:hs,[]:ex) ls
    go (hs,ex) ((' ':ln):ls) = go (ln:hs,ln:ex) ls
    go (hs,ex) (('-':ln):ls) = go (ln:hs,ex) ls
    go (hs,ex) (('+':ln):ls) = go (hs,ln:ex) ls
    go _ (ln:_) = error $
      "Malformed test file. " ++
      "Each line must start with a space, +, -, #, or be empty.\n" ++ ln

takeFlags :: String -> String
takeFlags = unwords . takeWhile (/="===") . lines

readFileNoComments :: FilePath -> IO String
readFileNoComments path =
  unlines . filter notComment . lines <$> readFile path
  where
    notComment ('#':_) = False
    notComment _ = True

-- This is 'listDirectory' in 'directory >= 1.2.5.0'
listDir :: FilePath -> IO [FilePath]
listDir path =
  filter f <$> getDirectoryContents path
  where f filename = filename /= "." && filename /= ".."
