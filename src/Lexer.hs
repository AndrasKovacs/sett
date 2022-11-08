
module Lexer where

import Data.String

import FlatParse.Stateful
  hiding (Parser, runParser, string, char, cut, err,
          Pos, getPos, Span, spanOf, branch, withSpan)

import qualified FlatParse.Stateful as FP

import qualified Data.Set as S
import Data.Char
import Language.Haskell.TH

import Common
import Presyntax

import qualified Data.ByteString.Char8 as B

--------------------------------------------------------------------------------

data Expected
  = Lit String -- ^ Expected a concrete `String`.
  | Msg String -- ^ An arbitrary error message.
  deriving (Eq, Show, Ord)

instance IsString Expected where fromString = Lit

data Error'
  = Precise Expected     -- ^ Expected exactly something.
  | ExactIndent Int      -- ^ Expected exact indentation level.
  | IndentMore  Int      -- ^ Expected more than some indentation level.
  | Imprecise [String]   -- ^ Expected one of multiple things.
  deriving Show

data Error
  = Error {-# unpack #-} Pos Error'
  | DontUnboxError
  deriving Show

merge :: Error -> Error -> Error
merge ~err@(Error p e) ~err'@(Error p' e')
  | p == p', Imprecise ss <- e, Imprecise ss' <- e' = err'
  | otherwise = err
{-# noinline merge #-}

data Env = Env {envSrc :: Src, envLvl :: Int}
type Parser = FP.Parser Env Error

prettyError :: Src -> Error -> String
prettyError src DontUnboxError = impossible
prettyError src (Error pos e)  =

  let bstr   = srcToBs src
      ls     = FP.lines bstr
      (l, c) = head $ posLineCols bstr [rawPos pos]
      line   = if 0 <= l && l < length ls then ls !! l else ""
      linum  = show l
      lpad   = map (const ' ') linum

      expected (Lit s) = "expected " ++ s
      expected (Msg s) = s

      err (Precise exp)     = expected exp
      err (Imprecise exps)  = imprec $ S.toList $ S.fromList exps
      err (IndentMore col)  = "expected a token indented to column " ++ show (col + 1) ++ " or more."
      err (ExactIndent col) = "expected a token indented to column " ++ show (col + 1)

      imprec :: [String] -> String
      imprec [] = impossible
      imprec [s] = "expected " ++ s
      imprec ss = "expected one of the following:\n" ++ unlines (map ("  - "++) ss)

      showsrc (File path _) = path
      showsrc (Interactive _) = "interactive"

  in "parse error:\n"++
     showsrc src ++ ":" ++ show l ++ ":" ++ show c ++ ":\n" ++
     lpad   ++ "|\n" ++
     linum  ++ "| " ++ line ++ "\n" ++
     lpad   ++ "| " ++ replicate c ' ' ++ "^\n" ++
     err e

getPos :: Parser Pos
getPos = Pos <$!> (envSrc <$!> ask) <*!> FP.getPos
{-# inline getPos #-}

-- | Throw an error.
err :: Error' -> Parser a
err err = do
  pos <- getPos
  FP.err $ Error pos err

-- | Imprecise cut: we slap a list of expected things on inner errors.
cut :: Parser a -> [String] -> Parser a
cut p exps = do
  pos <- getPos
  cutting p (Error pos (Imprecise exps)) merge

-- | Precise cut: we propagate at most a single expected thing.
pcut :: Parser a -> Expected -> Parser a
pcut p exp = do
  pos <- getPos
  cutting p (Error pos (Precise exp)) merge

runParser :: Parser a -> Src -> Result Error a
runParser p src = FP.runParser p (Env src 0) 0 (srcToBs src)

-- | Run parser, print pretty error on failure.
testParser :: Show a => Parser a -> String -> IO ()
testParser p str = case Interactive (packUTF8 str) of
  b -> case runParser p b of
    Err e    -> putStrLn $ prettyError b e
    OK a _ _ -> print a
    Fail     -> putStrLn "parse error"

-- | Consume whitespace. We track the number of whitespace characters read since the start of the
--   current line. We don't need to track column numbers precisely! Relevant indentation consists of
--   only whitespace at the start of a line. For simplicity, whitespace parsing counts characters
--   all the time, although it would be a possible optimization to only count characters after the
--   start of a newline.
ws :: Parser ()
ws = $(switch [| case _ of
  " "  -> modify (+1) >> ws
  "\n" -> put 0 >> ws
  "\t" -> err $ Precise $ Msg "tabs are not allowed"
  "\r" -> modify (+1) >> ws
  "--" -> lineComment
  "{-" -> modify (+2) >> multilineComment
  _    -> pure () |])

-- | Parse a line comment.
lineComment :: Parser ()
lineComment =
  withOption anyWord8
    (\case 10 -> put 0 >> ws
           _  -> modify (+1) >> lineComment)
    (pure ())

-- | Parse a potentially nested multiline comment.
multilineComment :: Parser ()
multilineComment = go (1 :: Int) where
  go 0 = ws
  go n = $(switch [| case _ of
    "\n" -> put 0       >> go n
    "-}" -> modify (+2) >> go (n - 1)
    "{-" -> modify (+2) >> go (n + 1)
    _    -> FP.branch anyChar (modify (+1) >> go n) (pure ()) |])

-- | Query the current indentation level, fail if it's smaller than the current expected level.
lvl :: Parser Int
lvl = do
  Env _ lvl <- ask
  currentLvl <- get
  if currentLvl < lvl
    then empty
    else pure currentLvl
{-# inline lvl #-}

-- | Same as `lvl` except we throw an error on mismatch.
lvl' :: Parser Int
lvl' = do
  Env _ lvl <- ask
  currentLvl <- get
  if currentLvl < lvl
    then err $ IndentMore lvl
    else pure currentLvl
{-# inline lvl' #-}

-- | Fail if the current level is not the expected one.
exactLvl :: Int -> Parser ()
exactLvl l = do
  l' <- get
  if l == l' then pure () else empty
{-# inline exactLvl #-}

-- | Throw error if the current level is not the expected one.
exactLvl' :: Int -> Parser ()
exactLvl' l = do
  l' <- get
  if l == l' then pure () else err (ExactIndent l)
{-# inline exactLvl' #-}

-- | We check indentation first, then read the token, then read trailing whitespace.
token :: Parser a -> Parser a
token p = lvl *> p <* ws
{-# inline token #-}

-- | `token`, but indentation failure is an error.
token' :: Parser a -> Parser a
token' p = lvl' *> p <* ws
{-# inline token' #-}

spanOfToken :: Parser a -> Parser Span
spanOfToken p = do
  Env src _ <- ask
  FP.Span x y <- lvl *> FP.spanOf p <* ws
  pure $ Span# src x y
{-# inline spanOfToken #-}

spanOfToken' :: Parser a -> Parser Span
spanOfToken' p = do
  Env src _ <- ask
  FP.Span x y <- lvl' *> FP.spanOf p <* ws
  pure $ Span# src x y
{-# inline spanOfToken' #-}

moreIndented :: Parser a -> (a -> Parser b) -> Parser b
moreIndented pa k = do
  lvl <- get
  a <- pa
  local (\(Env src _) -> Env src (lvl + 1)) (k a)
{-# inline moreIndented #-}

-- | Run a parser with expected indentation level.
localIndentation :: Int -> Parser a -> Parser a
localIndentation n p = local (\(Env src _) -> Env src n) p
{-# inline localIndentation #-}

-- | Read a starting character of an identifier.
identStartChar :: Parser Char
identStartChar = fusedSatisfy
  isLatinLetter
  (\c -> isGreekLetter c || isLetter c)
  isLetter
  isLetter

-- | Read a non-starting character of an identifier.
identChar :: Parser Char
identChar = fusedSatisfy
  (\c -> isLatinLetter c || FP.isDigit c || c == '\'')
  (\c -> isGreekLetter c || isLetter c)
  isLetter
  isLetter

inlineIdentChar :: Parser Char
inlineIdentChar = fusedSatisfy
  (\c -> isLatinLetter c || FP.isDigit c || c == '\'')
  (\c -> isGreekLetter c || isLetter c)
  isLetter
  isLetter
{-# inline inlineIdentChar #-}

-- | Parse a non-keyword string, return the `Span` of the symbol.
sym :: String -> Q Exp
sym str = [| spanOfToken $(FP.string str) |]

-- | Parse a non-keyword string, throw precise error on failure, return the `Span` of the symbol
sym' :: String -> Q Exp
sym' str =
  [| spanOfToken' ($(FP.string str) `pcut` Lit str) |]

-- | Parse a keyword string, return the `Span`.
kw :: String -> Q Exp
kw str =
  [| spanOfToken ($(FP.string str) `notFollowedBy` identChar) |]

-- | Parse a keyword string, throw precise error on failure, return the `Span`.
kw' :: String -> Q Exp
kw' str =
  [| spanOfToken' (($(FP.string str) `notFollowedBy` identChar) `pcut` Lit str) |]

-- | Parse a keyword string, return the `Span`, don't check indentation and that it's not
--   a keyword. Used in atom parsing as an easy optimization.
rawKw :: String -> Q Exp
rawKw str = [| do
  Env src _ <- ask
  FP.Span x y <- FP.spanOf $(FP.string str) <* ws
  pure $ Span# src x y  |]

-- | Raw non-token parser that reads any keyword.
anyKw :: Parser ()
anyKw = $(switch [| case _ of
  "let"     -> eof
  "λ"       -> eof
  "Set"     -> eof
  "Prop"    -> eof
  "refl"    -> eof
  "coe"     -> eof
  "Top"     -> eof
  "Bot"     -> eof
  "tt"      -> eof
  "ap"      -> eof
  "sym"     -> eof
  "trans"   -> eof
  "El"      -> eof
  "exfalso" -> eof |])

scanIdent :: Parser ()
scanIdent = identStartChar >> many_ inlineIdentChar

withSpan :: Parser a -> Parser (a, Span)
withSpan a = FP.withSpan a \a (FP.Span x y) -> do
  Env src _ <- ask
  pure (a, Span# src x y)

identBase :: Parser Presyntax.Name
identBase = FP.withSpan scanIdent \_ span@(FP.Span x y) -> do
  fails $ inSpan span anyKw
  ws
  Env src _ <- ask
  pure $ Span# src x y

-- | Parse an identifier.
ident :: Parser Presyntax.Name
ident = lvl >> identBase
{-# inline ident #-}

-- | Parse an identifier.
ident' :: Parser Presyntax.Name
ident' = lvl' >> identBase `pcut` Lit "identifier"
{-# inline ident' #-}

branch :: Parser a -> (a -> Parser b) -> Parser b -> Parser b
branch p success fail = FP.Parser \fp !r eob s n -> case FP.runParser# p fp r eob s n of
  FP.OK# a s n -> FP.runParser# (success a) fp r eob s n
  FP.Fail#     -> FP.runParser# fail fp r eob s n
  FP.Err# e    -> FP.Err# e
{-# inline branch #-}

test = FP.runParser traceRest () 0 (B.pack "")
