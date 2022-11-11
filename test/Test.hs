
module Main where

import Control.Exception
import Control.Monad
import Data.List
import System.Directory.Recursive
import System.FilePath
import System.Exit

import Paths_sett

import Common
import MainInteraction

-- NOTE: stack test --coverage

dropPrefix :: Eq a => [a] -> [a] -> [a]
dropPrefix (x:xs) (y:ys) | x == y = dropPrefix xs ys
dropPrefix _      ys              = ys

main :: IO ()
main = do
  dir <- getDataDir
  let dropDir = dropPrefix dir
  succeedFiles <- getFilesRecursive (dir </> "succeed")
  failFiles    <- getFilesRecursive (dir </> "fail")

  disableDebug

  succeedFails <- flip filterM succeedFiles \path -> do
    catch
      (do {testElab path; putStrLn (dropDir path ++ " PASS"); pure False})
      (\(e :: SomeException) -> do {putStrLn (dropDir path ++ " FAIL"); pure True})

  failFails <- flip filterM failFiles \path -> do
    catch
      (do {testElab path; putStrLn (dropDir path ++ " FAIL"); pure True})
      (\(e :: SomeException) -> do {putStrLn (dropDir path ++" PASS"); pure False})

  case (succeedFails, failFails) of
    ([], []) -> pure ()
    _        -> exitFailure
