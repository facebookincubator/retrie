-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE ApplicativeDo #-}
module Retrie.Debug
  ( RoundTrip(..)
  , parseRoundtrips
  , doRoundtrips
  ) where

import Options.Applicative
import System.FilePath

import Retrie.CPP
import Retrie.ExactPrint
import Retrie.Fixity

data RoundTrip = RoundTrip Bool FilePath {- True = with fixities -}

parseRoundtrips :: Parser [RoundTrip]
parseRoundtrips = concat <$> traverse many
  [ RoundTrip True <$> option str
      (  long "roundtrip" <> metavar "PATH"
      <> help "Roundtrip file through ghc-exactprint and fixity adjustment.")
  , RoundTrip False <$> option str
      (  long "roundtrip-no-fixity" <> metavar "PATH"
      <> help "Roundtrip file through ghc-exactprint only.")
  ]

doRoundtrips :: LibDir -> FixityEnv -> FilePath -> [RoundTrip] -> IO ()
doRoundtrips libdir fixities targetDir = mapM_ $ \ (RoundTrip doFix fp) -> do
  let path = targetDir </> fp
  cpp <-
    if doFix
    then parseCPPFile (parseContent libdir fixities) path
    else parseCPPFile (parseContentNoFixity libdir) path
  writeFile path $ printCPP [] cpp
