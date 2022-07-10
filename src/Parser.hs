
module Parser (parseFile, parseString) where

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
import Common

--------------------------------------------------------------------------------

-- trace :: String -> Parser ()
-- trace str = do
--   rest <- traceRest
--   Trace.traceM (str ++ " | " ++ rest)

--------------------------------------------------------------------------------


{-

Precedences from strongest to weakest:
  - atoms
  - projections            (postfix)
  - function application   (left assoc)
  - equality type          (infix, no assoc)
  - sigma                  (right assoc)
  - lam/let                (right assoc)
  - pairs                  (right assoc)

Context-free grammar (disregarding indentation!)

  builtin     = "Set" | "Prop" | "refl" | "coe" | "ap" | "sym" | "trans" | "⊤" | "tt" | "⊥" | "exfalso"

  identifier  = <non-empty string of alphanumeric characters or "'", starting with a letter>
  binder      = identifier | "_"
  typedbinder = binder | binder ":" term
  arrow       = "->" | "→"
  pibinder    = "{" (binder)+ : term "}" | "(" (binder)+ : term ")" | "{" (binder)+ "}"
  lambda      = "λ" | "\"
  times       = "×" | "*"
  lambinder   = binder | "(" binder ":" term ")" | "{" typedbinder "}" | "{" typedbinder "=" binder "}"

  atom        = builtin | identifier | "_" | "(" term ")" |
  projection  = atom | projection ".₁" | projection ".₂" | projection "." identifier
  application = projection | application projection | application "{" term "}" | application "{" identifier "=" term "}"
  equality    = application | application "=" application
  sigma       = equality | equality "×" sigma | "(" binder : term ")" "×" sigma
  pi          = sigma | sigma arrow pi | (pibinder)+ arrow pi
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

colon   = token  ($(FP.string ":") `notFollowedBy` $(FP.string "="))
colon'  = token  ($(FP.string ":") `notFollowedBy` $(FP.string "="))
semi    = $(sym  ";")
braceL  = $(sym  "{")
braceR  = $(sym  "}")
braceR' = $(sym' "}")
parL    = $(sym  "(")
parR'   = $(sym' ")")
parR    = $(sym  ")")
dot     = $(sym  ".")
assign  = $(sym  ":=")
assign' = $(sym' ":=")
arrow   = token  $(switch [| case _ of "->" -> pure (); "→" -> pure () |])
times   = token  $(switch [| case _ of "*"  -> pure (); "×" -> pure () |])
lambda  = token' $(switch [| case _ of "λ"  -> pure (); "\\" -> pure () |])

--------------------------------------------------------------------------------

atom :: Parser Tm
atom =
  branch ident              (pure . Var)          $
  branch parL               (\_  -> tm' <* parR') $
  branch $(sym "_")         (pure . Hole)         $
  branch $(rawKw "refl")    (pure . Refl)         $
  branch $(rawKw "Set")     (pure . Set)          $
  branch $(rawKw "Prop")    (pure . Prop)         $
  branch $(sym "⊤")         (pure . Top)          $
  branch $(rawKw "Top")     (pure . Top)          $
  branch $(sym "⊥")         (pure . Bot)          $
  branch $(rawKw "Bot")     (pure . Bot)          $
  branch $(rawKw "tt")      (pure . Tt)           $
  branch $(rawKw "exfalso") (pure . Exfalso)      $
  branch $(rawKw "ap")      (pure . Ap)           $
  branch $(rawKw "coe")     (pure . Coe)          $
  branch $(rawKw "trans")   (pure . Trans)        $
  branch $(rawKw "sym")     (pure . Sym)          $
  empty

atom' :: Parser Tm
atom' =
  atom
  `cut` atomErr

bind :: Parser Bind
bind = (Bind     <$> ident)
   <|> (DontBind <$ ($(sym "_") >> ws))

bind' :: Parser Bind
bind' = bind `pcut` Lit "a binder"

goProj :: Tm -> Parser Tm
goProj t =
  branch $(sym ".")
    (\_ ->
       branch $(sym "₁") (\(Span _ p) -> goProj (Proj1 t p)) $
       branch $(sym "1") (\(Span _ p) -> goProj (Proj1 t p)) $
       branch $(sym "₂") (\(Span _ p) -> goProj (Proj2 t p)) $
       branch $(sym "2") (\(Span _ p) -> goProj (Proj2 t p)) $
       (ident `pcut` Lit "a field projection: \".₁\", \".1\", \".₂\", \".2\" or field name projection")
       >>= \x -> goProj (ProjField t x))
    (pure t)

proj' :: Parser Tm
proj' = (do
  a <- atom'
  goProj a)
  `cut` projErr

goApp :: Tm -> Parser Tm
goApp t = branch braceL

  (\_ -> branch (ident <* assign)
    (\x -> do
      u <- tm'
      braceR `pcut` Lit "\"}\" in implicit application"
      goApp (App t u (Named x)))
    (do
      u <- tm'
      braceR `pcut` Lit "\"}\" in implicit application"
      goApp (App t u (NoName Impl))))

  (branch atom
     (\u -> do
         u <- goProj u
         goApp (App t u (NoName Expl)))
     (pure t))

app' :: Parser Tm
app' = (goApp =<< proj')
  `cut` appErr

eq' :: Parser Tm
eq' = (do
  t <- app'
  branch $(sym "=")
    (\_ -> Eq t <$> app')
    (pure t))
  `cut` eqErr

sigma' :: Parser Tm
sigma' = (do
  p <- getPos
  branch (parL *> bind <* colon)
    (\x -> do
      a <- tm'
      parR   `pcut` Lit "\")\" in sigma binder"
      times  `pcut` Lit "\"×\" or \"*\" after binder in sigma type expression"
      b <- sigma'
      pure $ Sg p x a b)
    (do
      t <- eq'
      branch times
        (\_ -> Sg p DontBind t <$> sigma')
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
  branch colon
    (\_ -> (binders,,Impl) <$> (tm' <* braceClose))

    -- if there's no type annotation, we use the span of all binders for the hole
    ((binders, Hole sp, Impl) <$ braceClose)

piBinder :: Parser ([Bind], Tm, Icit)
piBinder =
  branch parL   (\_ -> explPiBinder) $
  branch braceL (\_ -> implPiBinder) $
  empty

pi' :: Parser Tm
pi' = (do
  pos <- getPos
  branch (some piBinder)

    (\case
        -- pi/sigma ambiguity resolution
        [([x], a, Expl)] ->
          branch arrow
            (\_ -> Pi pos x Expl a <$> pi') $
            branch times
              (\_ -> do
                  dom <- Sg pos x a <$> sigma'
                  branch arrow
                    (\_ -> Pi pos DontBind Expl dom <$> pi')
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
      branch arrow
        (\_ -> Pi pos DontBind Expl t <$> pi')
        (pure t)))

  `cut` piErr

-- TODO: unify binder syntax in lambda and pi
implLamBinder :: Parser (Bind, ArgInfo, Maybe Tm)
implLamBinder = do
  x <- bind'
  case x of
    DontBind -> do
      ma <- optional (colon *> tyAnnot)
      pure (DontBind, NoName Impl, ma)
    Bind x   -> do
      ma <- optional (colon *> tyAnnot)
      branch assign
        (\_ -> do
            y <- bind' <* braceR'
            pure (y, Named x, ma))
        (do braceR'
            pure (Bind x, NoName Impl, ma))

lamBinder :: Parser (Bind, ArgInfo, Maybe Tm)
lamBinder =
  branch parL   (\_ -> (,NoName Expl,) <$> bind' <*> (Just <$> (colon' *> tyAnnot <* parR'))) $
  branch braceL (\_ -> implLamBinder) $
  ((,NoName Expl,Nothing) <$> bind)

lamLet' :: Parser Tm
lamLet' = (do
  pos <- getPos
  branch lambda

    -- lambda
    (\_ -> do
        binders <- some lamBinder
        dot `pcut` Lit "\".\" after lambda binders"
        body <- lamLet'
        pure $! foldr' (\(x, inf, a) -> Lam pos x inf a) body binders)

    -- let
    (branch $(kw "let")
      (\_ -> do
          x <- ident'
          branch assign
            (\_ -> do
                t <- tm'
                semi `pcut` Lit "\";\" in let-definition"
                u <- lamLet'
                pure $ Let pos x Nothing t u)
            (branch colon
              (\_ -> do
                  a <- tm'
                  assign'
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
  branch $(sym ",")
    (\_ -> Pair t <$> tm')
    (pure t)

tm' :: Parser Tm
tm' = tm `cut` tmErr

tyAnnot :: Parser Tm
tyAnnot = tm `cut` ["a type annotation"]

topLevel :: Parser TopLevel
topLevel = branch (exactLvl 0)

  (\_ -> do
      x <- ident'
      localIndentation 1 do
        ma <- optional (colon *> tyAnnot)
        assign'
        rhs <- tm `cut` ["a top-level definition"]
        top <- localIndentation 0 topLevel
        pure $ Define x ma rhs top
  )

  (do eof `cut` ["end of file", "new non-indented top-level definition"]
      pure Nil
  )

--------------------------------------------------------------------------------

parseFile :: FilePath -> IO (Src, TopLevel)
parseFile path = do
  src <- File path <$!> B.readFile path
  case runParser topLevel src of
    OK a _ _ -> pure (src, a)
    Fail     -> impossible
    Err e    -> putStrLn (prettyError src e) >> error "parse error"

parseString :: String -> IO (Src, TopLevel)
parseString str = do
  let src = Interactive (packUTF8 str)
  case runParser topLevel src of
    OK a _ _ -> pure (src, a)
    Fail     -> impossible
    Err e    -> putStrLn (prettyError src e) >> error "parse error"
