-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
module Retrie.Run
  ( runScript
  , runScriptWithModifiedOptions
  , execute
  , run
  , WriteFn
  , writeCountLines
  , writeDiff
  , writeSearch
  , writeExtract
  ) where

import Control.Monad.State.Strict
import Data.Char
import Data.List
import Data.Monoid
import System.Console.ANSI

import Retrie.CPP
import Retrie.ExactPrint
import Retrie.GHC
import Retrie.Monad
import Retrie.Options
import Retrie.Pretty
import Retrie.Replace
import Retrie.Util

-- | Define a custom refactoring script.
-- A script is an 'IO' action that defines a 'Retrie' computation. The 'IO'
-- action is run once, and the resulting 'Retrie' computation is run once
-- for each target file. Typically, rewrite parsing/construction is done in
-- the 'IO' action, so it is performed only once. Example:
--
-- > module Main where
-- >
-- > main :: IO ()
-- > main = runScript $ \opts -> do
-- >   rr <- parseRewrites opts ["forall f g xs. map f (map g xs) = map (f . g) xs"]
-- >   return $ apply rr
--
-- To run the script, compile the program and execute it.
runScript :: LibDir -> (Options -> IO (Retrie ())) -> IO ()
runScript libdir f = runScriptWithModifiedOptions libdir (\opts -> (opts,) <$> f opts)

-- | Define a custom refactoring script and run it with modified options.
-- This is the same as 'runScript', but the returned 'Options' will be used
-- during rewriting.
runScriptWithModifiedOptions :: LibDir -> (Options -> IO (Options, Retrie ())) -> IO ()
runScriptWithModifiedOptions libdir f = do
  opts <- parseOptions libdir mempty
  (opts', retrie) <- f opts
  execute libdir opts' retrie

-- | Implements retrie's iteration and execution modes.
execute :: LibDir -> Options -> Retrie () -> IO ()
execute libdir opts@Options{..} retrie0 = do
  let retrie = iterateR iterateN retrie0
  case executionMode of
    ExecDryRun -> void $ run libdir (writeDiff opts) id opts retrie
    ExecExtract -> void $ run libdir (writeExtract opts) id opts retrie
    ExecRewrite -> do
      s <- mconcat <$> run libdir writeCountLines id opts retrie
      when (verbosity > Silent) $
        putStrLn $ "Done! " ++ show (getSum s) ++ " lines changed."
    ExecSearch -> void $ run libdir (writeSearch opts) id opts retrie

-- | Callback function to actually write the resulting file back out.
-- Is given list of changed spans, module contents, and user-defined data.
type WriteFn a b = [Replacement] -> String -> CPP AnnotatedModule -> a -> IO b

-- | Primitive means of running a 'Retrie' computation.
run
  :: Monoid b
  => LibDir
  -> (FilePath -> WriteFn a b)
     -- ^ write action when a file changes, unchanged files result in 'mempty'
  -> (IO b -> IO c)            -- ^ wrap per-file rewrite action
  -> Options -> Retrie a -> IO [c]
run libdir writeFn wrapper opts@Options{..} r = do
  fps <- getTargetFiles opts (getGroundTerms r)
  forFn opts fps $ \ fp -> wrapper $ do
    debugPrint verbosity "Processing:" [fp]
    p <- trySync $ parseCPPFile (parseContent libdir fixityEnv) fp
    case p of
      Left ex -> do
        when (verbosity > Silent) $ print ex
        return mempty
      Right cpp -> runOneModule (writeFn fp) opts r cpp

-- | Run a 'Retrie' computation on the given parsed module, writing
-- changes with the given write action.
runOneModule
  :: Monoid b
  => WriteFn a b
     -- ^ write action if the module changes, unchanged module returns 'mempty'
  -> Options
  -> Retrie a
  -> CPP AnnotatedModule
  -> IO b
runOneModule writeFn Options{..} r cpp = do
  debugPrint Loud "runOneModule" ["enter"]
  (x, cpp', changed) <- runRetrie fixityEnv r cpp
  case changed of
    NoChange -> return mempty
    Change repls imports -> do
      debugPrint Loud "runOneModule" ["change", show repls]
      let cpp'' = addImportsCPP (additionalImports:imports) cpp'
      writeFn repls (printCPP repls cpp'') cpp'' x

-- isCpp :: CPP AnnotatedModule -> String
-- isCpp (NoCPP m) = "NoCPP:" ++ showAstA m
-- isCpp (CPP{}) = "CPP"

-- | Write action which counts changed lines using 'diff'
writeCountLines :: FilePath -> WriteFn a (Sum Int)
writeCountLines fp reps str _ _ = do
  let lc = lineCount $ map replLocation reps
  putStrLn $ "Writing: " ++ fp ++ " (" ++ show lc ++ " lines changed)"
  writeFile fp str
  return $ Sum lc

-- | Print the lines before replacement and after replacement.
writeDiff :: Options -> FilePath -> WriteFn a (Sum Int)
writeDiff Options{..} fp repls _ _ _ = do
  fl <- linesMap fp
  forM_ repls $ \Replacement{..} -> do
    let ppLines lineStart color = unlines
          . map (lineStart ++)
          . ppRepl fl replLocation
          . colorise Vivid color
    putStrLn $ mconcat
      [ ppSrcSpan colorise replLocation
      , "\n"
      , ppLines "- " Red replOriginal
      , ppLines "+ " Green replReplacement
      ]
  return $ Sum $ lineCount $ map replLocation repls

-- | Print lines that match the query and highligh the matched string.
writeSearch :: Options -> FilePath -> WriteFn a ()
writeSearch Options{..} fp repls _ _ _ = do
  fl <- linesMap fp
  forM_ repls $ \Replacement{..} ->
    putStrLn $ mconcat
      [ ppSrcSpan colorise replLocation
      , ppLine
        $ ppRepl fl replLocation
        $ colorise Vivid Red replOriginal
      ]
  where
    ppLine [] = ""
    ppLine [x] = strip x
    ppLine xs = '\n': dropWhileEnd isSpace (unlines xs)

-- | Print only replacement.
writeExtract :: Options -> FilePath -> WriteFn a ()
writeExtract Options{..} _ repls _ _ _ = do
  forM_ repls $ \Replacement{..} -> do
    putStrLn $ mconcat
      [ ppSrcSpan colorise replLocation
      , strip replReplacement
      ]
