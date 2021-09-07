-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE OverloadedStrings #-}
module GroundTerms
  ( getFocusTests
  , groundTermsTest
  ) where

import Control.Monad
import Control.Monad.IO.Class
import qualified Data.HashSet as HashSet
import Data.Text (Text)
import Fixity
import Retrie.CPP
import Retrie.ExactPrint
import Retrie.GroundTerms
import Retrie.Monad
import Retrie.Options
import Retrie.Rewrites
import Retrie.Types
import Retrie.Universe
import Test.HUnit

groundTermsTest :: LibDir -> Test
groundTermsTest libdir = TestLabel "ground terms" $ TestList
  [ gtTest libdir "map"
      ""
      []
      [Adhoc "forall f g xs. map f (map g xs) = map (f . g) xs"]
      [["map"]]
      [GrepCommands [] ["grep -R --include=\"*.hs\" -l 'map' '~/si_sigma'"]]
  , gtTest libdir "isSpace"
      ""
      []
      [Adhoc "forall xs. or (map isSpace xs) = any isSpace xs"]
      [["or", "map isSpace"]]
      [GrepCommands [] ["grep -R --include=\"*.hs\" -l 'or' '~/si_sigma'", "grep -l 'map[[:space:]]\\+isSpace'"]]
  , gtTest libdir "MyType"
      "type MyType a = MyOtherType a"
      []
      [TypeForward "Test.MyType"]
      [["MyType"]]
      [GrepCommands [] ["grep -R --include=\"*.hs\" -l 'MyType' '~/si_sigma'"]]
  , gtTest libdir "isSpace with file"
      ""
      ["Test.hs", "Test2.hs"]
      [Adhoc "forall xs. or (map isSpace xs) = any isSpace xs"]
      [["or", "map isSpace"]]
      [GrepCommands ["Test.hs", "Test2.hs"] ["grep -l 'or'", "grep -l 'map[[:space:]]\\+isSpace'"]]
  ]

gtTest
  :: LibDir
  -> String
  -> Text
  -> [FilePath]
  -> [RewriteSpec]
  -> [[String]]
  -> [GrepCommands]
  -> Test
gtTest libdir lbl contents targFiles specs expected expectedCmds =
  TestLabel ("groundTerms: " ++ lbl) $ TestCase $ do
    -- since we 'zip' below
    assertEqual "length of specs and expected ground terms"
      (length specs)
      (length expected)
    assertEqual "length of expected ground terms and expected commands"
      (length expected)
      (length expectedCmds)

    rrs <-
      parseRewriteSpecs libdir
        (\_ -> parseCPP (parseContent libdir defaultFixityEnv "Test") contents)
        defaultFixityEnv
        specs
    let gtss = map groundTerms rrs

    assertEqual "groundTerms does not give expected term set"
      (HashSet.fromList $ map HashSet.fromList expected)
      (HashSet.fromList gtss) -- compare hashsets to avoid ordering issues

    forM_ (zip gtss expectedCmds) $ \(gts, expectedCmd) ->
          assertEqual "buildGrepChain did not give expected command"
            expectedCmd
            (buildGrepChain "~/si_sigma" gts targFiles)

getFocusTests :: LibDir -> IO [Test]
getFocusTests libdir = do
  rrs1 <- parseAdhocs libdir defaultFixityEnv ["forall xs. or (map isSpace xs) = any isSpace xs"]
  rrs2 <- parseAdhocs libdir defaultFixityEnv ["forall f g xs. map f (map g xs) = map (f . g) xs"]
  let
    -- compare hashsets to avoid ordering issues
    terms = HashSet.fromList $ map groundTerms rrs1

  return
    [ TestLabel caseName $ TestCase $
        assertEqual caseName expected $
          HashSet.fromList $ getGroundTerms retrie
    | (caseName, retrie, expected) <-
      [ ("apply", apply rrs1, terms)
      , ("apply twice", apply rrs1 >> apply rrs2, terms)
      , ("query", () <$ query rrs1, terms)
      , ("focus", focus rrs1, terms)
      , ("focus empty", focus ([] :: [Rewrite Universe]), HashSet.empty)
      , ("focus empty next", focus ([] :: [Rewrite Universe]) >> apply rrs1, terms)
        -- We should generate no ground terms if no iteration happens
      , ("iterateR 0", iterateR 0 (apply rrs1), HashSet.empty)
      , ("iterateR 0 then apply", iterateR 0 (apply rrs2) >> apply rrs1, terms)
      , ("iterateR 5", iterateR 5 (apply rrs1), terms)
        -- test that adding imports first (calling 'tell') doesn't block us
        -- from finding ground terms
      , ("addImports", addImports mempty >> apply rrs1, terms)
      , ("ifChanged normal", ifChanged (apply rrs1) (apply rrs2), terms)
      -- the pathological case: changed but no ground terms
      , ("ifChanged weird", ifChanged (addImports mempty) (apply rrs1), terms)
      , ("liftIO", liftIO (return ()) >> apply rrs1, HashSet.empty)
      , ("liftIO after focus", focus rrs1 >> liftIO (return ()) >> apply rrs2, terms)
      ]
    ]
