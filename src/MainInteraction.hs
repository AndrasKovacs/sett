

module MainInteraction (main, loadFile, justElab, testElab) where

import System.IO
import System.Exit
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

-- State of interaction
--------------------------------------------------------------------------------

data State
  = Empty
  | Focused FilePath  -- ^ We intend to load a path but haven't yet.
  | Loaded FilePath   -- ^ We have loaded a path. We are only allowed to
                      --   access ElabState in this state.
  deriving Show

--------------------------------------------------------------------------------

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  putStrLn "sett 0.1.0.0"
  putStrLn "enter :? for help"
  disableDebug
  loop Empty

loadFile :: FilePath -> IO State
loadFile path = do
  reset
  (state, time) <- timed $
    Ex.try (B.readFile path) >>= \case
      Left (e :: Ex.SomeException) -> do
        putStrLn (Ex.displayException e)
        pure $ Focused path
      Right bstr -> do
        let src = File path bstr
        writeElabSource (Just src)
        timedPure (runParser parse src) >>= \case
          (FP.Err e, _) -> do
            putStrLn (path ++ ":")
            putStrLn (prettyError src e)
            pure $ Focused path
          (FP.Fail, _) -> do
            putStrLn "unknown parse error"
            pure $ Focused path
          (FP.OK top _ _, time) -> do
            putStrLn (path ++ " parsed in " ++ show time)
            timed (Ex.try (elab top)) >>= \case
              (Left (e :: ErrorInCxt), time) -> do
                print e
                pure $ Focused path
              (Right ntbl, time) -> do
                RL.write topNameTable ntbl
                metas   <- nextMeta
                topsize <- topSize
                putStrLn (path ++ " elaborated in " ++ show time)
                putStrLn ("created " ++ show (coerce metas :: Int) ++ " metavariables")
                putStrLn ("loaded " ++ show topsize ++ " definitions")
                pure $ Loaded path
  putStrLn ("total load time: " ++ show time)
  pure state

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

loop :: State -> IO a
loop state = do

  let whenLoaded :: (FilePath -> IO a) -> IO a
      whenLoaded action = case state of
        Loaded path -> action path
        _           -> putStrLn "no file loaded" >> loop state

      whenFocused :: (FilePath -> IO a) -> IO a
      whenFocused action = case state of
        Focused path -> action path
        Loaded path  -> action path
        _            -> putStrLn "no file loaded" >> loop state

      loadTopEntry :: String -> (Lvl -> S.Ty -> GTy -> Val -> IO a) -> IO a
      loadTopEntry x act = whenLoaded \_ -> do
        ntbl <- RL.read topNameTable
        case NT.lookupBS (FP.packUTF8 x) ntbl of
          Just (NT.Top l a va v) -> act l a va v
          _ -> putStrLn "name not in scope" >> loop state

      renderPrompt :: IO ()
      renderPrompt = case state of
        Empty        -> putStr "> "
        Focused path -> putStr $ path ++ "> "
        Loaded path  -> putStr $ path ++ "> "

      renderBrowse :: IO ()
      renderBrowse = whenLoaded \_ -> do
        ADL.for topInfo \case
          TEDef x a _ _       -> putStrLn $ show x ++ " : " ++ showTm0 a
          TEPostulate x a _ _ -> putStrLn $ show x ++ " : " ++ showTm0 a

      dropSp :: String -> String
      dropSp = dropWhile (==' ')

  renderPrompt

  l <- getLine
  case l of
    ':':'l':' ':(dropSp -> rest) ->
      loop =<< loadFile rest
    ':':'r':_ ->
      whenFocused \path -> loop =<< loadFile path
    ':':'t':' ':(dropSp -> rest) ->
      loadTopEntry rest \_ a _ _ -> do
        putStrLn $ showTm0 a
        loop state
    ':':'n':'t':' ':(dropSp -> rest) ->
      loadTopEntry rest \_ a _ _ -> do
        putStrLn $ showTm0 $ nf0 UnfoldEverything a
        loop state
    ':':'n':' ':(dropSp -> rest) ->
      loadTopEntry rest \_ _ _ v -> do
        putStrLn $ showTm0 $ quote0WithOpt UnfoldEverything v
        loop state
    ':':'o':'u':'t':_ ->
      whenLoaded \_ -> renderElab >> loop state
    ':':'b':'r':'o':_ ->
      whenLoaded \_ -> renderBrowse >> loop state
    ':':'n':'o':'d':'e':'b':'u':'g':_ -> do
      putStrLn "debug printing disabled"
      disableDebug
      loop state
    ':':'d':'e':'b':'u':'g':_ -> do
      putStrLn "debug printing enabled"
      enableDebug
      loop state
    ':':'?':_ -> do
      putStrLn ":l <file>    load file"
      putStrLn ":r           reload file"
      putStrLn ":n  <name>   show normal form of top-level definition"
      putStrLn ":t  <name>   show elaborated type of top-level definition"
      putStrLn ":nt <name>   show normal type of top-level definition"
      putStrLn ":out         show whole elaboration output"
      putStrLn ":bro         show defined top-level names and their types"
      putStrLn ":q           quit"
      putStrLn ":debug       enable printing debugging information"
      putStrLn ":nodebug     disable printing debugging information"
      putStrLn ":?           show this message"
      loop state
    ':':'q':_ -> do
      exitSuccess
    _ -> do
      putStrLn "unknown command"
      putStrLn "use :? for help"
      loop state
