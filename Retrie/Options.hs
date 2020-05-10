-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
module Retrie.Options
  ( -- * Options
    Options
  , Options_(..)
  , ExecutionMode(..)
  , defaultOptions
  , parseOptions
    -- * Internal
  , buildGrepChain
  , forFn
  , getOptionsParser
  , getTargetFiles
  , parseRewritesInternal
  , parseVerbosity
  , ProtoOptions
  , resolveOptions
  ) where

import Control.Concurrent.Async (mapConcurrently)
import Control.Monad (when)
import Data.Bool
import Data.Char (isAlphaNum, isSpace)
import Data.Default as D
import Data.Foldable (toList)
import Data.Functor.Identity
import Data.List
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.Traversable
import Options.Applicative
import System.Directory
import System.FilePath
import System.Process
import System.Random.Shuffle

import Retrie.CPP
import Retrie.Debug
import Retrie.ExactPrint
import Retrie.Fixity
import Retrie.GroundTerms
import Retrie.GHC
import Retrie.Pretty
import Retrie.Rewrites
import Retrie.Types
import Retrie.Universe
import Retrie.Util
import System.Exit (ExitCode(ExitFailure))

-- | Command-line options.
type Options = Options_ [Rewrite Universe] AnnotatedImports

-- | Parse options using the given 'FixityEnv'.
parseOptions :: FixityEnv -> IO Options
parseOptions fixityEnv = do
  p <- getOptionsParser fixityEnv
  opts <- execParser (info (p <**> helper) fullDesc)
  resolveOptions opts

-- | Create 'Rewrite's from string specifications of rewrites.
-- We expose this from "Retrie" with a nicer type signature as
-- 'Retrie.Options.parseRewrites'. We have it here so we can use it with
-- 'ProtoOptions'.
parseRewritesInternal :: Options_ a b -> [RewriteSpec] -> IO [Rewrite Universe]
parseRewritesInternal Options{..} = parseRewriteSpecs parser fixityEnv
  where
    parser fp = parseCPPFile (parseContent fixityEnv) (targetDir </> fp)

-- | Controls the ultimate action taken by 'apply'. The default action is
-- 'ExecRewrite'.
data ExecutionMode
  = ExecDryRun -- ^ Pretend to do rewrites, show diff.
  | ExecRewrite -- ^ Perform rewrites.
  | ExecExtract -- ^ Print the resulting expression for each match.
  | ExecSearch -- ^ Print the matched expressions.
  deriving (Show)

data Options_ rewrites imports = Options
  { additionalImports :: imports
    -- ^ Imports specified by the command-line flag '--import'.
  , colorise :: ColoriseFun
    -- ^ Function used to colorize results of certain execution modes.
  , executionMode :: ExecutionMode
    -- ^ Controls behavior of 'apply'. See 'ExecutionMode'.
  , extraIgnores :: [FilePath]
    -- ^ Specific files that should be ignored. Paths should be relative to
    -- 'targetDir'.
  , fixityEnv :: FixityEnv
    -- ^ Fixity information for operators used during parsing (of rewrites and
    -- target modules). Defaults to base fixities.
  , iterateN :: Int
    -- ^ Iterate the given rewrites or 'Retrie' computation up to this many
    -- times. Iteration may stop before the limit if no changes are made during
    -- a given iteration.
  , randomOrder :: Bool
    -- ^ Whether to randomize the order of target modules before rewriting them.
  , rewrites :: rewrites
    -- ^ Rewrites specified by command-line flags such as '--adhoc'.
  , roundtrips :: [RoundTrip]
    -- ^ Paths that should be roundtripped through ghc-exactprint to debug.
    -- Specified by the '--roundtrip' command-line flag.
  , singleThreaded :: Bool
    -- ^ Whether to concurrently rewrite target modules.
    -- Mostly useful for viewing debugging output without interleaving it.
  , targetDir :: FilePath
    -- ^ Directory that contains the code being targeted for rewriting.
  , targetFiles :: [FilePath]
    -- ^ Instead of targeting all Haskell files in 'targetDir', only target
    -- specific files. Paths should be relative to 'targetDir'.
  , verbosity :: Verbosity
    -- ^ How much should be output on 'stdout'.
  }

-- | Construct default options for the given target directory.
defaultOptions
  :: (Default rewrites, Default imports)
  => FilePath -> Options_ rewrites imports
defaultOptions fp = Options
  { additionalImports = D.def
  , colorise = noColor
  , executionMode = ExecRewrite
  , extraIgnores = []
  , fixityEnv = D.def
  , iterateN = 1
  , randomOrder = False
  , rewrites = D.def
  , roundtrips = []
  , singleThreaded = False
  , targetDir = fp
  , targetFiles = []
  , verbosity = Normal
  }

-- | Get the options parser. The returned 'ProtoOptions' should be passed
-- to 'resolveOptions' to get final 'Options'.
getOptionsParser :: FixityEnv -> IO (Parser ProtoOptions)
getOptionsParser fEnv = do
  dOpts <- defaultOptions <$> getCurrentDirectory
  return $ buildParser dOpts { fixityEnv = fEnv }

buildParser :: ProtoOptions -> Parser ProtoOptions
buildParser dOpts = do
  singleThreaded <- switch $ mconcat
    [ long "single-threaded"
    , showDefault
    , help "Don't try to parallelize things (for debugging)."
    ]
  targetDir <- option str $ mconcat
    [ long "target"
    , short 't'
    , metavar "PATH"
    , action "directory" -- complete with directory
    , value (targetDir dOpts)
    , showDefault
    , help "Path to target with rewrites."
    ]
  targetFiles <- many $ option str $ mconcat
    [ long "target-file"
    , metavar "PATH"
    , action "file" -- complete with filenames
    , help "Target specific file for rewriting."
    ]
  verbosity <- parseVerbosity (verbosity dOpts)
  additionalImports <- many $ option str $ mconcat
    [ long "import"
    , metavar "IMPORT"
    , help
        "Add given import statement to modules that are modified by a rewrite."
    ]
  extraIgnores <- many $ option str $ mconcat
    [ long "ignore"
    , metavar "PATH"
    , action "file" -- complete with filenames
    , help "Ignore specific file while rewriting."
    ]
  colorise <- fmap (bool noColor addColor) $ switch $ mconcat
    [ long "color"
    , help "Highlight matches with color."
    ]
  randomOrder <- switch $ mconcat
    [ long "random-order"
    , help "Randomize the order of targeted modules."
    ]
  iterateN <- option auto $ mconcat
    [ long "iterate"
    , short 'i'
    , metavar "N"
    , value 1
    , help "Iterate rewrites up to N times."
    ]

  executionMode <- parseMode
  rewrites <- parseRewriteSpecOptions
  roundtrips <- parseRoundtrips
  return Options{ fixityEnv = fixityEnv dOpts, ..}

parseRewriteSpecOptions :: Parser [RewriteSpec]
parseRewriteSpecOptions = concat <$> traverse many
  [ fmap Unfold $ option str $ mconcat
      [ long "unfold"
      , short 'u'
      , metavar "NAME"
      , help "Unfold given fully-qualified name."
      ]
  , fmap Fold $ option str $ mconcat
      [ long "fold"
      , short 'f'
      , metavar "NAME"
      , help "Fold given fully-qualified name."
      ]
  , fmap RuleForward $ option str $ mconcat
      [ long "rule-forward"
      , short 'l'
      , metavar "NAME"
      , help "Apply fully-qualified RULE name left-to-right."
      ]
  , fmap RuleBackward $ option str $ mconcat
      [ long "rule-backward"
      , short 'r'
      , metavar "NAME"
      , help "Apply fully-qualified RULE name right-to-left."
      ]
  , fmap TypeForward $ option str $ mconcat
      [ long "type-forward"
      , metavar "NAME"
      , help "Apply fully-qualified type synonym name left-to-right."
      ]
  , fmap TypeBackward $ option str $ mconcat
      [ long "type-backward"
      , metavar "NAME"
      , help "Apply fully-qualified type synonym name right-to-left."
      ]
  , fmap Adhoc $ option str $ mconcat
      [ long "adhoc"
      , metavar "EQUATION"
      , help "Apply an adhoc equation of the form: forall vs. lhs = rhs"
      ]
  ]

parseMode :: Parser ExecutionMode
parseMode =
  parseDryRun <|>
  parseExtract <|>
  parseSearch <|>
  pure ExecRewrite

parseDryRun :: Parser ExecutionMode
parseDryRun = flag' ExecDryRun $ mconcat
  [ long "dry-run"
  , help "Don't overwrite files. Print rewrite results."
  ]

parseExtract :: Parser ExecutionMode
parseExtract = flag' ExecExtract $ mconcat
  [ long "extract"
  , help "Find the left-hand side, display the instantiated right-hand side."
  ]

parseSearch :: Parser ExecutionMode
parseSearch = flag' ExecSearch $ mconcat
  [ long "search"
  , help "Search for left-hand side of the rewrite and show matches."
  ]

-- | Parser for 'Verbosity'.
parseVerbosity :: Verbosity -> Parser Verbosity
parseVerbosity defaultV = option (eitherReader verbosityReader) $ mconcat
  [ long "verbosity"
  , short 'v'
  , value defaultV
  , showDefault
  , help verbosityHelp
  ]

verbosityReader :: String -> Either String Verbosity
verbosityReader "0" = Right Silent
verbosityReader "1" = Right Normal
verbosityReader "2" = Right Loud
verbosityReader _ =
  Left $ "invalid verbosity. Valid values: " ++ verbosityHelp

verbosityHelp :: String
verbosityHelp = "0: silent, 1: normal, 2: loud (implies --single-threaded)"

-------------------------------------------------------------------------------

-- | Options that have been parsed, but not fully resolved.
type ProtoOptions = Options_ [RewriteSpec] [String]

-- | Resolve 'ProtoOptions' into 'Options'. Parses rewrites into 'Rewrite's,
-- parses imports, validates options, and extends 'fixityEnv' with any
-- declared fixities in the target directory.
resolveOptions :: ProtoOptions -> IO Options
resolveOptions protoOpts = do
  opts@Options{..} <- addLocalFixities protoOpts
  parsedImports <- parseImports additionalImports
  debugPrint verbosity "Imports:" $
    runIdentity $ fmap astA $ transformA parsedImports $ \ imps -> do
      anns <- getAnnsT
      return $ map (`exactPrint` anns) imps
  rrs <- parseRewritesInternal opts rewrites
  return Options
    { rewrites          = rrs
    , additionalImports = parsedImports
    , singleThreaded    = singleThreaded || verbosity == Loud
    , ..
    }

-- | Find all fixity declarations in targetDir and add them to fixity env.
addLocalFixities :: Options_ a b -> IO (Options_ a b)
addLocalFixities opts = do
  -- do not limit search for infix decls to only targetFiles
  let opts' = opts { targetFiles = [] }
  -- "infix" will find infixl and infixr as well
  files <- getTargetFiles opts' [HashSet.singleton "infix"]

  fixFns <- forFn opts files $ \ fp -> do
    ms <- toList <$> parseCPPFile parseContentNoFixity fp
    return $ extendFixityEnv
      [ (rdrFS nm, fixity)
      | m <- ms
      , (L _ nm, fixity) <- fixityDecls (unLoc (astA m))
      ]

  return opts { fixityEnv = foldr ($) (fixityEnv opts) fixFns }

-- | 'forM', but concurrency and input order controled by 'Options'.
forFn :: Options_ x y -> [a] -> (a -> IO b) -> IO [b]
forFn Options{..} c f
  | randomOrder = fn f =<< shuffleM c
  | otherwise = fn f c
  where
    fn
      | singleThreaded = mapM
      | otherwise = mapConcurrently

-- | Find all files to target for rewriting.
getTargetFiles :: Options_ a b -> [GroundTerms] -> IO [FilePath]
-- Always include at least one set of ground terms
-- This selects all files if the list of rewrites is empty
getTargetFiles opts [] = getTargetFiles opts [mempty]
getTargetFiles Options{..} gtss = do
  ignorePred <- maybe onIgnoreErr return =<< vcsIgnorePred verbosity targetDir
  let ignore fp = ignorePred fp || extraIgnorePred fp
  fpSets <- forM (dedup gtss) $ \ gts -> do
    -- See Note [Ground Terms]
    fps <-
      case buildGrepChain targetDir gts targetFiles of
        Left fs -> return fs
        Right (stdin, cmd) -> doCmd targetDir verbosity stdin (unwords cmd)

    let
      r = filter (not . ignore)
        $ map (normalise . (targetDir </>)) fps
    debugPrint verbosity "Files:" r
    return $ HashSet.fromList r

  return $ HashSet.toList $ mconcat fpSets
  where
    dedup = HashSet.toList . HashSet.fromList
    extraIgnorePred =
      let fps = [ normalise (targetDir </> f) | f <- extraIgnores ]
      in \fp -> any (`isPrefixOf` fp) fps
    onIgnoreErr = do
      when (verbosity > Silent) $
        putStrLn "Reading VCS ignore failed! Continuing without ignoring."
      return $ const False

-- | Either returns an exact list of target paths, or a command for finding
-- them.
buildGrepChain
  :: FilePath
  -> HashSet String
  -> [FilePath]
  -> Either [FilePath] (String, [String])
buildGrepChain targetDir gts =
  -- Limit the size of the shell command we build by only selecting
  -- up to 10 ground terms. The goal is to filter file list down to
  -- a manageable size. It doesn't have to be exact.
  filterFiles (take 10 $ filter p $ HashSet.toList gts)
  where
    p [] = False
    p (c:cs)
      | isSpace c = p cs
      | otherwise = isAlphaNum c

    hsExtension = "\"*.hs\""

    filterFiles [] [] = Right ("", findCmd) -- all .hs files
    filterFiles [] fs = Left fs -- targetFiles
    -- start with all .hs files and filter
    filterFiles (g:gs) [] =
      Right ("", intercalate ["|"] $ firstCmd g : filterChain gs)
    -- start with targetFiles and filter
    filterFiles gs fs =
      Right (unlines fs, intercalate ["|"] $ filterChain gs)

    findCmd = ["find", addTrailingPathSeparator targetDir, "-iname", hsExtension]

    firstCmd g =
      ["grep", "-R", "--include=" ++ hsExtension, "-l", esc g, targetDir]

    filterChain gs = [ ["xargs", "grep", "-l", esc gt] | gt <- gs ]

    esc s = "'" ++ intercalate "[[:space:]]\\+" (words s) ++ "'"

doCmd :: FilePath -> Verbosity -> String -> String -> IO [FilePath]
doCmd targetDir verbosity inp shellCmd = do
  debugPrint verbosity "stdin:" [inp]
  debugPrint verbosity "shellCmd:" [shellCmd]
  let cmd = (shell shellCmd) { cwd = Just targetDir }
  (ec, fps, err) <- readCreateProcessWithExitCode cmd inp
  case ec of
    -- A grep exit code 1 means no lines matched, not an actual failure
    ExitFailure n | n > 1 ->
      fail $ "grep failed with exit code " <> show n <> ": \n" <> err
    _ -> do
      debugPrint verbosity "stdout:" [fps]
      return $ lines fps
