-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
module CPP (cppTest) where

import Control.Monad
import Data.List (intersperse, sort)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import qualified GHC.Paths as GHC.Paths
import Retrie.CPP
import Retrie.ExactPrint
import Retrie.Util
import Test.HUnit

data CPPTest = CPPTest
  { name :: String
  , code :: Text
  , results :: [[Text]]
  }

cppTest :: Test
cppTest = TestLabel "cpp" $ TestList $
  map cppForkTest testList ++
  map roundTripTest testList

testList :: [CPPTest]
testList =
  [ CPPTest "no cpp" noCPPCode [Text.lines noCPPCode]
  , CPPTest "define" defineCode
      [ ["a","","b"]
      ]
  , CPPTest "one if" oneIfCode
      [ ["a","","b","","c"]
      , ["a","","","","c"]
      ]
  , CPPTest "if else" ifElseCode
      [ ["a","b","","","","","e","f","","g","h"]
      , ["a","b","","c","d","","","","","g","h"]
      ]
  , CPPTest "if elif else" elIfCode
      [ ["a","b","","c","d","","","","","","","","i","j"]
      , ["a","b","","","","","e","f","","","","","i","j"]
      , ["a","b","","","","","","","","g","h","","i","j"]
      ]
  , CPPTest "if elif elif else" twoElIfCode
      [ ["a","b","","c","d","","","","","","","","","","","k","l"]
      , ["a","b","","","","","e","f","","","","","","","","k","l"]
      , ["a","b","","","","","","","","g","h","","","","","k","l"]
      , ["a","b","","","","","","","","","","","i","j","","k","l"]
      ]
  , CPPTest "if elif" elIfNoElseCode
      [ ["a","b","","c","d","","","","","i","j"]
      , ["a","b","","","","","e","f","","i","j"]
      , ["a","b","","","","","","","","i","j"]
      ]
  , CPPTest "nested if" nestedIfCode
      [ ["a","","b","","","","","e","","f","g","","h"]
      , ["a","","b","","c","d","","","","f","g","","h"]
      , ["a","","","","","","","","","","","","h"]
      ]
  , CPPTest "imports" importCode
      [ importExpected1, importExpected2 ]
  ]

noCPPCode :: Text
noCPPCode = Text.unlines
  [ "a"
  , "b"
  , "c"
  ]

defineCode :: Text
defineCode = Text.unlines
  [ "a"
  , "#define FOO 1"
  , "b"
  ]

oneIfCode :: Text
oneIfCode = Text.unlines
  [ "a"
  , "#if FOO"
  , "b"
  , "#endif"
  , "c"
  ]

ifElseCode :: Text
ifElseCode = Text.unlines
  [ "a"
  , "b"
  , "#if FOO"
  , "c"
  , "d"
  , "#else"
  , "e"
  , "f"
  , "#endif"
  , "g"
  , "h"
  ]

elIfCode :: Text
elIfCode = Text.unlines
  [ "a"
  , "b"
  , "#if FOO"
  , "c"
  , "d"
  , "#elif BAR"
  , "e"
  , "f"
  , "#else"
  , "g"
  , "h"
  , "#endif"
  , "i"
  , "j"
  ]

twoElIfCode :: Text
twoElIfCode = Text.unlines
  [ "a"
  , "b"
  , "#if FOO"
  , "c"
  , "d"
  , "#elif BAR"
  , "e"
  , "f"
  , "#elif BAZ"
  , "g"
  , "h"
  , "#else"
  , "i"
  , "j"
  , "#endif"
  , "k"
  , "l"
  ]

elIfNoElseCode :: Text
elIfNoElseCode = Text.unlines
  [ "a"
  , "b"
  , "#if FOO"
  , "c"
  , "d"
  , "#elif BAR"
  , "e"
  , "f"
  , "#endif"
  , "i"
  , "j"
  ]

nestedIfCode :: Text
nestedIfCode = Text.unlines
  [ "a"
  , "#if FOO"
  , "b"
  , "#if BAR"
  , "c"
  , "d"
  , "#else"
  , "e"
  , "#endif"
  , "f"
  , "g"
  , "#endif"
  , "h"
  ]

importCode :: Text
importCode = Text.unlines
  [ "module Foo where"
  , ""
  , "import Bar"
  , "#if BAZ"
  , "import Baz"
  , "#endif"
  , "import Quux"
  , "#if QUUX"
  , "import Something"
  , ""
  , "myDecl :: Int"
  , "myDecl = 54"
  , "#else"
  , "import Something.Else"
  , "#endif"
  , ""
  , "thats all = folks"
  ]

importExpected2 :: [Text]
importExpected2 =
  [ "module Foo where"
  , ""
  , "import Bar"
  , ""
  , "import Baz"
  , ""
  , "import Quux"
  , ""
  , "import Something"
  , ""
  , "myDecl :: Int"
  , "myDecl = 54"
  , ""
  , ""
  , ""
  , ""
  , "thats all = folks"
  ]

importExpected1 :: [Text]
importExpected1 =
  [ "module Foo where"
  , ""
  , "import Bar"
  , ""
  , "import Baz"
  , ""
  , "import Quux"
  , ""
  , ""
  , ""
  , ""
  , ""
  , ""
  , "import Something.Else"
  , ""
  , ""
  , "thats all = folks"
  ]

cppForkTest :: CPPTest -> Test
cppForkTest CPPTest{..} = TestLabel ("cpp fork: " ++ name) $ TestCase $ do
  let
    sorted = sort $ map Text.unlines results
    fork = sort $ cppFork code
  unless (sorted == fork) $ do
    putStrLn "Expected:"
    mapM_ Text.putStrLn (intersperse "===" sorted)
    putStrLn "But Got:"
    mapM_ Text.putStrLn (intersperse "===" fork)
    assertFailure "cppFork does not give expected result"

roundTripTest :: CPPTest -> Test
roundTripTest CPPTest{..} = TestLabel ("roundtrip: " ++ name) $ TestCase $ do
  r <- trySync $ parseCPP (parseContentNoFixity GHC.Paths.libdir "roundTripTest") code
  case r of
    Left msg -> assertFailure (show msg)
    Right cpp -> assertEqual "cpp did not roundtrip correctly"
      (Text.unpack code)
      (printCPP [] cpp)
