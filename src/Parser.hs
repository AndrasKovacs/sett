
module Parser (parse, parseFile, parseString, parseBS) where

import FlatParse.Stateful
  hiding (Parser, runParser, string, char, cut, err,
          Pos, getPos, Span, spanOf, branch, withSpan)

import qualified FlatParse.Stateful as FP

import Prelude hiding (pi)
import Data.Foldable
import qualified Data.ByteString as B

-- import qualified Debug.Trace as Trace

import Lexer
import Presyntax
import Common hiding (assign)

--------------------------------------------------------------------------------

-- trace :: String -> Parser ()
-- trace str = do
--   rest <- traceRest
--   Trace.traceM (str ++ " | " ++ rest)

--------------------------------------------------------------------------------

-- TODO: grammar below is outdated

{-

Precedence summary from strongest to weakest:
  - atoms
  - projections            (postfix)
  - function application   (left assoc)
  - equality type          (infix, no assoc)
  - sigma                  (right assoc)
  - pi                     (right assoc)
  - lam/let                (right assoc)
  - pairs                  (right assoc)

Context-free grammar (disregarding indentation!)

  builtin     = "Set" | "Prop" | "refl" | "coe" | "ap" | "sym" | "trans" | "⊤" | "Top" | "Bot" | "tt" | "⊥" | "exfalso" | "Tagged"

  identifier  = <non-empty string of alphanumeric characters or "'", starting with a letter>
  binder      = identifier | "_"
  typedbinder = binder | binder ":" term
  arrow       = "->" | "→"
  pibinder    = "{" binder+ : term "}" | "(" binder+ : term ")" | "{" binder+ "}"
  lambda      = "λ" | "\"
  times       = "×" | "*"
  lambinder   = binder | "(" binder ":" term ")" | "{" typedbinder "}" | "{" typedbinder ":=" binder "}"

  atom        = builtin | identifier | "_" | "(" term ")" |
  projection  = atom | projection ".₁" | projection ".₂" | projection ".1" | projection ".2" | projection "." identifier
  application = projection | application projection | application "{" term "}" | application "{" identifier ":=" term "}"
                | "El" projection
  equality    = application | application "=" application
  sigma       = equality | equality "×" sigma | "(" binder : term ")" "×" sigma
  pi          = sigma | sigma arrow pi | pibinder+ arrow pi
  lamLet      = pi | lambda (lambinder)+ "." lamLet | "let" identifier ":=" pair "in" lamLet
                | "let" identifier ":" pair ":=" pair in lamLet
  pair        = lamLet | lamLet "," pair
  term        = pair

  topDef      = identifier ":" term ":=" term | identifier ":=" term
  postulate   = identifier ":" term
  program     = "" | topDef program | postulate program

Indentation:
  - every topDef or postulate identifier must be non-indented
  - every topDef or postulate type/definition must be indented (cannot have a lexeme at column 0)
  - top-level entries are delimited by indentation in implementation
-}

--------------------------------------------------------------------------------

atomErr   = ["an identifier", "a parenthesized expression", "a hole"]
projErr   = "a projection expression" : atomErr
appErr    = "an application expression" : projErr
eqErr     = "an equality type" : appErr
sigmaErr  = "a sigma type" : eqErr
piErr     = "a function type" : sigmaErr
lamLetErr = "a let-definition" : "a lambda expression" : piErr
tmErr     = ["a term"]

--------------------------------------------------------------------------------

-- TODO: get rid of ' parsers, instead write custom cut messages in situ

assign  = $(sym  ":=")
colon   = token  ($(FP.string ":") `notFollowedBy` $(FP.string "="))
colon'  = token' ($(FP.string ":") `notFollowedBy` $(FP.string "="))
semi    = $(sym  ";")
braceL  = $(sym  "{")
parL    = $(sym  "(")
parR'   = $(sym' ")")
parR    = $(sym  ")")
dot     = $(sym  ".")
arrow   = token  $(switch [| case _ of "->" -> pure (); "→" -> pure () |])
times   = token  $(switch [| case _ of "*"  -> pure (); "×" -> pure () |])
lambda  = token  $(switch [| case _ of "λ"  -> pure (); "\\" -> pure () |])

braceR  = $(sym  "}")
braceR' = $(sym' "}")

--------------------------------------------------------------------------------

-- TODO: optimize for performance
atom :: Parser Tm
atom =
  FP.withOption ident           (pure . Var)          $
  FP.withOption parL            parens                $
  FP.withOption $(sym "_")      (pure . Hole)         $
  FP.withOption $(kw "refl")    (pure . Refl)         $
  FP.withOption $(kw "Set")     (pure . Set)          $
  FP.withOption $(kw "Prop")    (pure . Prop)         $
  FP.withOption $(sym "⊤")      (pure . Top)          $
  FP.withOption $(kw "Top")     (pure . Top)          $
  FP.withOption $(sym "⊥")      (pure . Bot)          $
  FP.withOption $(kw "Bot")     (pure . Bot)          $
  FP.withOption $(kw "tt")      (pure . Tt)           $
  FP.withOption $(kw "exfalso") (pure . Exfalso)      $
  FP.withOption $(kw "ap")      (pure . Ap)           $
  FP.withOption $(kw "coe")     (pure . Coe)          $
  FP.withOption $(kw "trans")   (pure . Trans)        $
  FP.withOption $(kw "sym")     (pure . Sym)          $
  FP.withOption $(kw "El")      (pure . El)           $
  FP.withOption $(kw "Newtype") (pure . Newtype)      $
  empty

parens :: Span -> Parser Tm
parens l = Parens (leftPos l) <$> tm' <*> (rightPos <$> parR')

atom' :: Parser Tm
atom' = atom `cut` atomErr

bind :: Parser Bind
bind = (Bind     <$> ident)
   <|> (DontBind <$ ($(sym "_") >> ws))

bind' :: Parser Bind
bind' = bind `pcut` Lit "a binder"

goProj :: Tm -> Parser Tm
goProj t =
  FP.branch $(sym ".")
    (
       FP.withOption $(sym "₁")      (\(Span _ p) -> goProj (Proj1 t p)) $
       FP.withOption $(sym "1")      (\(Span _ p) -> goProj (Proj1 t p)) $
       FP.withOption $(sym "₂")      (\(Span _ p) -> goProj (Proj2 t p)) $
       FP.withOption $(sym "2")      (\(Span _ p) -> goProj (Proj2 t p)) $
       FP.withOption $(kw  "unpack") (\(Span _ p) -> goProj (Unpack t p)) $
       (ident `pcut`
          Lit "a field projection: \".₁\", \".1\", \".₂\", \".2\" or field name projection")
          >>= \x -> goProj (ProjField t x))
    (pure t)

proj' :: Parser Tm
proj' = (do
  a <- atom'
  goProj a)
  `cut` projErr

goApp :: Tm -> Parser Tm
goApp t = FP.branch braceL

  (FP.withOption (ident <* assign)
    (\x -> do
      u <- tm'
      p <- rightPos <$> (braceR `pcut` Lit "\"}\" in implicit application")
      goApp (App t u (AINamedImpl x p)))
    (do
      u <- tm'
      p <- getPos
      p <- rightPos <$> (braceR `pcut` Lit "\"}\" in implicit application")
      goApp (App t u (AIImpl p))))

  (FP.withOption atom
     (\u -> do
         u <- goProj u
         goApp (App t u AIExpl))
     (pure t))

app' :: Parser Tm
app' =
  (FP.withOption $(kw "pack") (\x -> Pack x <$> proj')
           (goApp =<< proj'))
  `cut` appErr

eq' :: Parser Tm
eq' = (do
  t <- app'
  FP.branch $(sym "=")
    (Eq t <$> optional (braceL *> tm <* braceR') <*> app')
    (pure t))
  `cut` eqErr

sigma' :: Parser Tm
sigma' = (do
  p <- getPos
  FP.withOption (parL *> bind <* colon)
    (\x -> do
      a <- tm'
      parR   `pcut` Lit "\")\" in sigma binder"
      times  `pcut` Lit "\"×\" or \"*\" after binder in sigma type expression"
      b <- sigma'
      pure $ Sg p x a b)
    (do
      t <- eq'
      FP.branch times
        (Sg p DontBind t <$> sigma')
        (pure t)))
  `cut` sigmaErr

-- TODO: allow parens in non-dependent domain, e.g. "(f x y) -> B"
explPiBinder :: Parser ([Bind], Tm, Icit)
explPiBinder = do
  binders <- some bind
  colon `pcut` Lit "\":\" in typed function argument binding"
  a <- tyAnnot
  parR `pcut` Lit "\")\" in typed function argument binding"
  pure (binders, a, Expl)

implPiBinder :: Parser ([Bind], Tm, Icit)
implPiBinder = do
  (binders, sp) <- withSpan (some bind)
  let braceClose = braceR  `pcut` Lit "\"}\" in implicit argument binder"
  FP.branch colon
    ((binders,,Impl) <$> (tm' <* braceClose))

    -- if there's no type annotation, we use the span of all binders for the hole
    ((binders, Hole sp, Impl) <$ braceClose)

piBinder :: Parser ([Bind], Tm, Icit)
piBinder =
  FP.branch parL   (explPiBinder) $
  FP.branch braceL (implPiBinder) $
  empty

pi' :: Parser Tm
pi' = (do
  pos <- getPos
  FP.withOption (try (some piBinder)) -- TODO: lookahead instead of try

    (\case
        -- pi/sigma ambiguity resolution
        [([x], a, Expl)] ->
          FP.branch arrow
            (Pi pos x Expl a <$> pi') $
            FP.branch times
              (do
                  dom <- Sg pos x a <$> sigma'
                  FP.branch arrow
                    (Pi pos DontBind Expl dom <$> pi')
                    (pure dom))
              (err $ Precise $ Msg "expected \"->\", \"→\", \"×\" or \"*\" after binder" )

        binders -> do
          arrow `pcut` Lit "\"->\" or \"→\" in function type"
          b <- pi'
          pure $!
            foldr' (\(xs, a, i) t -> foldr' (\x b -> Pi pos x i a b) t xs)
                   b binders)

    (do
      t <- sigma'
      FP.branch arrow
        (Pi pos DontBind Expl t <$> pi')
        (pure t)))

  `cut` piErr

-- TODO: unify binder syntax in lambda and pi
implLamBinder :: Parser (Bind, ArgInfo, Maybe Tm)
implLamBinder = do
  x <- bind'
  case x of
    DontBind -> do
      ma <- optional (colon *> tyAnnot)
      p <- rightPos <$> braceR'
      pure (DontBind, AIImpl p, ma)
    Bind x   -> do
      ma <- optional (colon *> tyAnnot)
      FP.branch assign
        (do
            y <- bind'
            p <- rightPos <$> braceR'
            pure (y, AINamedImpl x p, ma))
        (do p <- rightPos <$> braceR'
            pure (Bind x, AIImpl p, ma))

lamBinder :: Parser (Bind, ArgInfo, Maybe Tm)
lamBinder =
  FP.branch parL ((,AIExpl,) <$> bind' <*> (Just <$> (colon' *> tyAnnot <* parR'))) $
  FP.branch braceL (implLamBinder) $
  ((,AIExpl,Nothing) <$> bind)

lamLet' :: Parser Tm
lamLet' = (do
  pos <- getPos
  FP.branch lambda

    -- lambda
    (do
        binders <- some lamBinder
        dot `pcut` Lit "\".\" after lambda binders"
        body <- lamLet'
        pure $! foldr' (\(x, inf, a) -> Lam pos x inf a) body binders)

    -- let
    (FP.branch $(kw "let")
      (do
          x <- ident'
          FP.branch assign
            (do
                t <- tm'
                semi `pcut` Lit "\";\" in let-definition"
                u <- lamLet'
                pure $ Let pos x Nothing t u)
            (FP.branch colon
              (do
                  a <- tm'
                  assign `pcut` Lit "\":=\" in let-definition"
                  t <- tm'
                  semi `pcut` Lit "\";\" in let-definition"
                  u <- lamLet'
                  pure $ Let pos x (Just a) t u)
              (err $
                 Precise $
                 Lit "\":\" or \":=\" in let-expression")))

      -- otherwise
      pi'))

  `cut` lamLetErr


tm :: Parser Tm
tm = do
  t <- lamLet'
  FP.branch $(sym ",")
    (Pair t <$> tm')
    (pure t)

tm' :: Parser Tm
tm' = tm `cut` tmErr

tyAnnot :: Parser Tm
tyAnnot = tm `cut` ["a type annotation"]

topLevel :: Parser TopLevel
topLevel = FP.branch eof (pure Nil) do
  exactLvl' 0
  x <- ident `cut` ["top-level definition"]
  FP.modify (+1) -- TODO: remove this hack
  localIndentation 1 do
    ma <- optional (colon *> tyAnnot)
    rest <- FP.traceRest
    assign `pcut` Lit "\":=\" in top-level definition"
    rhs <- tm `cut` ["a top-level definition"]
    top <- localIndentation 0 topLevel
    pure $ Define x ma rhs top

parse :: Parser TopLevel
parse = ws *> topLevel

-- Testing helpers
--------------------------------------------------------------------------------

parseFile :: FilePath -> IO (Src, TopLevel)
parseFile path = do
  src <- File path <$!> B.readFile path
  case runParser parse src of
    OK a _ _ -> pure (src, a)
    Fail     -> impossible
    Err e    -> error $ prettyError src e

parseBS :: FilePath -> B.ByteString -> IO (Src, TopLevel)
parseBS path bs = do
  let src = File path bs
  case runParser parse src of
    OK a _ _ -> pure (src, a)
    Fail     -> impossible
    Err e    -> error $ prettyError src e

parseString :: String -> IO (Src, TopLevel)
parseString str = do
  let src = Interactive (strToUtf8 str)
  case runParser parse src of
    OK a _ _ -> pure (src, a)
    Fail     -> impossible
    Err e    -> error $ prettyError src e
