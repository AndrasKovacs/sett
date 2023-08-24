
module Main where

import Control.Exception
import Control.Monad
import Data.List
import System.Console.ANSI (setSGRCode)
import System.Directory.Recursive
import System.Exit
import System.FilePath
import System.IO
import qualified System.Console.ANSI.Codes as ANSI

import Paths_sett

import Common
import MainInteraction


-- NOTE: stack test --coverage

dropPrefix :: Eq a => [a] -> [a] -> [a]
dropPrefix (x:xs) (y:ys) | x == y = dropPrefix xs ys
dropPrefix _      ys              = ys

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering

  inTerminal <- hIsTerminalDevice stdout
  let withColor color str
        = if inTerminal
          then ANSI.setSGRCode [ANSI.SetColor ANSI.Foreground ANSI.Dull color] ++ str ++ ANSI.setSGRCode [ANSI.Reset]
          else str
  let passStr = withColor ANSI.Green "PASS"
  let failStr = withColor ANSI.Red "FAIL"

  dir <- getDataDir
  let dropDir = dropPrefix dir
  succeedFiles <- getFilesRecursive (dir </> "succeed")
  failFiles    <- getFilesRecursive (dir </> "fail")

  modifyDebugToggle \_ -> False

  succeedFails <- flip filterM succeedFiles \path -> do
    let path' = dropDir path
    putStr (path' ++ " ")
    catch
      (do {testElab path; putStrLn passStr; pure False})
      (\(e :: SomeException) -> do {putStrLn failStr; pure True})

  failFails <- flip filterM failFiles \path -> do
    let path' = dropDir path
    putStr (path' ++ " ")
    catch
      (do {testElab path; putStrLn failStr; pure True})
      (\(e :: SomeException) -> do {putStrLn passStr; pure False})

  case (succeedFails, failFails) of
    ([], []) -> pure ()
    _        -> exitFailure
