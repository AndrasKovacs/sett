

module MainInteraction (main, loadFile, justElab, testElab) where

import System.IO
import qualified Control.Exception    as Ex
import qualified Data.Array.Dynamic.L as ADL
import qualified Data.ByteString      as B
import qualified Data.Ref.L           as RL
import qualified FlatParse.Stateful   as FP


import Common
import ElabState
import Elaboration
import Errors
import Evaluation
import Lexer
import Parser
import Pretty
import Values
import qualified NameTable as NT
import qualified Syntax as S

--------------------------------------------------------------------------------

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  putStrLn "sett 0.1.0.0"
  putStrLn "enter :? for help"
  loop

loadFile :: FilePath -> IO ()
loadFile path = do
  reset
  (_, time) <- timed $
    Ex.try (B.readFile path) >>= \case
      Left (e :: Ex.SomeException) -> do
        putStrLn (Ex.displayException e)
      Right bstr -> do
        let src = File path bstr
        writeElabSource (Just src)
        timedPure (runParser parse src) >>= \case
          (FP.Err e, _) -> do
            putStrLn (path ++ ":")
            putStrLn (prettyError src e)
          (FP.Fail, _) -> do
            putStrLn "unknown parse error"
          (FP.OK top _ _, time) -> do
            putStrLn (path ++ " parsed in " ++ show time)
            timed (Ex.try (elab top)) >>= \case
              (Left (e :: ErrorInCxt), time) -> do
                print e
              (Right ntbl, time) -> do
                RL.write topNameTable ntbl
                metas   <- nextMeta
                topsize <- topSize
                putStrLn (path ++ " elaborated in " ++ show time)
                putStrLn ("created " ++ show metas ++ " metavariables")
                putStrLn ("loaded " ++ show topsize ++ " definitions")
                RL.write loadedFile (Just path)
  putStrLn ("total load time: " ++ show time)

------------------------------------------------------------

-- | Elaborate a file, don't print anything, throw exception on error.
testElab :: FilePath -> IO ()
testElab path = do
  reset
  bstr <- B.readFile path
  (src, top) <- parseBS path bstr
  writeElabSource (Just src)
  _ <- elab top
  pure ()

-- | Elaborate a string, render output.
justElab :: String -> IO ()
justElab src = do
  reset
  (src, top) <- parseString src
  writeElabSource (Just src)
  ntbl <- elab top
  renderElab

renderElab :: IO ()
renderElab = do
 size <- topSize
 putStr "\n"

 let goMetaBlock frz m | m == frz = pure ()
     goMetaBlock frz m = do
       readMeta m >>= \case
         MEUnsolved a     -> putStrLn $ show m ++ " : "
                              ++ showTm0 (quote0 (g1 a)) ++ " unsolved"
         MESolved _ t _ a -> putStrLn $ show m ++ " : "
                              ++ showTm0 (quote0 (g1 a)) ++ " := " ++ showTm0 t
       goMetaBlock frz (m + 1)

 let goTop :: MetaVar -> Lvl -> IO ()
     goTop m i | i == size = pure ()
     goTop m i = readTopInfo i >>= \case
         TEDef x a t frz ->  do
           goMetaBlock frz m
           when (m /= frz) (putStrLn "")
           putStrLn $ show x ++ " : " ++ showTm0 a
           putStrLn $ "  := " ++ showTm0 t
           putStrLn ""
           goTop frz (i + 1)
         TEPostulate x a _ frz -> do
           goMetaBlock frz m
           when (m /= frz) (putStrLn "")
           putStrLn $ show x ++ " : " ++ showTm0 a
           putStrLn ""
           goTop frz (i + 1)
 goTop 0 0

renderBrowse :: IO ()
renderBrowse = do
  ADL.for topInfo \case
    TEDef x a _ _       -> putStrLn $ show x ++ " : " ++ showTm0 a
    TEPostulate x a _ _ -> putStrLn $ show x ++ " : " ++ showTm0 a

whenLoaded :: (FilePath -> IO ()) -> IO ()
whenLoaded action = RL.read loadedFile >>= \case
  Nothing   -> putStrLn "no file loaded" >> loop
  Just path -> action path

loadTopEntry :: String -> (Lvl -> S.Ty -> GTy -> Val -> IO ()) -> IO ()
loadTopEntry x act = whenLoaded \_ -> do
  ntbl <- RL.read topNameTable
  case NT.lookupBS (FP.packUTF8 x) ntbl of
    Just (NT.Top l a va v) -> act l a va v
    _ -> putStrLn "name not in scope" >> loop

loop :: IO ()
loop = do

  let dropSp = dropWhile (==' ')

  RL.read loadedFile >>= \case
    Nothing   -> putStr "> "
    Just path -> putStr $ path ++ "> "

  l <- getLine
  case l of
    ':':'l':' ':(dropSp -> rest) ->
      loadFile rest >> loop
    ':':'r':_ ->
      whenLoaded \path -> loadFile path >> loop
    ':':'t':' ':(dropSp -> rest) ->
      loadTopEntry rest \_ a _ _ -> do
        putStrLn $ showTm0 a
        loop
    ':':'n':'t':' ':(dropSp -> rest) ->
      loadTopEntry rest \_ a _ _ -> do
        putStrLn $ showTm0 $ nf0 UnfoldEverything a
        loop
    ':':'n':' ':(dropSp -> rest) ->
      loadTopEntry rest \_ _ _ v -> do
        putStrLn $ showTm0 $ quote0WithOpt UnfoldEverything v
        loop
    ':':'o':'u':'t':_ ->
      whenLoaded \_ -> renderElab >> loop
    ':':'b':'r':'o':_ ->
      whenLoaded \_ -> renderBrowse >> loop

    ':':'?':_ -> do
      putStrLn ":l <file>    load file"
      putStrLn ":r           reload file"
      putStrLn ":n  <name>   show normal form of top-level definition"
      putStrLn ":t  <name>   show elaborated type of top-level definition"
      putStrLn ":nt <name>   show normal type of top-level definition"
      putStrLn ":out         show whole elaboration output"
      putStrLn ":bro         show defined top-level names and their types"
      putStrLn ":q           quit"
      putStrLn ":?           show this message"
      loop
    ':':'q':_ -> do
      pure ()
    _ -> do
      putStrLn "unknown command"
      putStrLn "use :? for help"
      loop
