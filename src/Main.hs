
module Main where

import System.Environment

import Parser

main :: IO ()
main = do
  getArgs >>= \case
    [file] -> do
      putStrLn (replicate 50 '-')
      parseFile file >>= print
    _ -> putStrLn "Please enter exactly one argument, a file to parse!"
