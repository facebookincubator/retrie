-- Copyright (c) Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
module Util where

import Control.Monad
import System.Directory (createDirectoryIfMissing)
import System.Exit
import System.FilePath
import System.IO.Temp
import System.Process
import Test.HUnit

withFakeRepo :: (FilePath -> IO ()) -> (FilePath -> IO ()) -> IO ()
withFakeRepo f initialise =
  withSystemTempDirectory "retrieTmpRepo" $ \dir -> do
    initialise dir
    f dir

withFakeRepoCmds
  :: String
  -> String
  -> [FilePath]
  -> [FilePath]
  -> (FilePath -> IO ())
  -> IO ()
withFakeRepoCmds initCmd ignoreFile ignoredFiles allFiles f =
  withFakeRepo f $ \dir -> do
  doOrDie dir initCmd
  createAllFiles dir allFiles
  writeFile (dir </> ignoreFile) $ unlines ignoredFiles
  where
    createAllFiles dir files = forM_ files $ \fp -> do
      let filePath = dir </> fp
      createDirectoryIfMissing True (takeDirectory filePath)
      -- Every file has its own name as the contents.
      writeFile filePath fp

withFakeHgRepo :: [FilePath] -> [FilePath] -> (FilePath -> IO ()) -> IO ()
withFakeHgRepo ignoredFiles allFiles f =
  withFakeRepoCmds "hg init" ".hgignore" ignoredFiles allFiles $ \dir -> do
    -- Tell 'hg' which ignore file to use for the repo, because Facebook's
    -- 'hg' looks at .gitignore by default.
    writeFile (dir </> ".hg" </> "hgrc") $ unlines
      [ "[ui]"
      , "ignore = .hgignore"
      ]
    f dir

withFakeGitRepo :: [FilePath] -> [FilePath] -> (FilePath -> IO ()) -> IO ()
withFakeGitRepo = withFakeRepoCmds "git init" ".gitignore"

doOrDie :: FilePath -> String -> IO ()
doOrDie dir cmd = do
  let shellCmd = (shell cmd) { cwd = Just dir }
  (ec, _, _) <- readCreateProcessWithExitCode shellCmd ""
  case ec of
    ExitSuccess -> return ()
    ExitFailure err ->
      assertFailure $ cmd ++ " failed with: " ++ show err
