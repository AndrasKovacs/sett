
{-# options_ghc -Wno-unused-top-binds #-}

module Pretty (showTm, showTm', showTm0) where

import IO

import Common
import Syntax
import ElabState

-- import Debug.Trace

--------------------------------------------------------------------------------

-- printing precedences
-- atomp  = 7  :: Int
projp  = 6  :: Int
appp   = 5  :: Int
eqp    = 4  :: Int
sigmap = 3  :: Int
pip    = 2  :: Int
letp   = 1  :: Int
pairp  = 0  :: Int

-- Wrap in parens if expression precedence is lower than
-- enclosing expression precedence.
par :: Int -> Int -> ShowS -> ShowS
par p p' = showParen (p' < p)

braces :: ShowS -> ShowS
braces s = ('{':).s.('}':)

ws = (' ':)

goTm :: Int -> [String] -> Tm -> ShowS
goTm prec ns t = go prec ns t where

  -- TODO: more efficient printing & freshening
  --       or just overhaul printing
  count :: [String] -> String -> Int
  count ns n = go ns 0 where
    go []      acc = acc
    go (n':ns) acc | n == n' = go ns (acc + 1)
                   | True    = go ns acc

  counted :: String -> Int -> String
  counted x 0 = x
  counted x n = x ++ show n

  fresh :: [String] -> Name -> (String, String)
  fresh ns NUnused   = ("_", "_")
  fresh ns (NLit n)  = (,) $$! n $$! counted n (count ns n)
  fresh ns (NSpan x) =
    let n = spanToString x in
    (,) $$! n $$! counted n (count ns n)

  piBind ns x Expl a = ('(':) . (x++) . (" : "++) . go letp ns a .(')':)
  piBind ns x Impl a = braces  ((x++) . (" : "++) . go letp ns a)

  lamBind x Impl = braces (x++)
  lamBind x Expl = (x++)

  sgBind ns "_" a = go eqp ns a
  sgBind ns x   a = ('(':).(x++).(" : "++).go pairp ns a.(')':)

  splitSpine :: Tm -> (Tm, [(Tm, Icit)])
  splitSpine t = go t [] where
    go (App t u i) acc = go t ((u,i):acc)
    go t           acc = (t, acc)

  isIdSp ns sp =
    let go l [] = l == 0
        go l ((LocalVar x, _):sp) | x == l - 1 = go (l-1) sp
        go _ _ = False

    in go (Ix (length ns)) sp

  goMetaSp :: [String] -> [(Tm,Icit)] -> ShowS
  goMetaSp ns sp | isIdSp ns sp = ("(..)"++)
                 | True         = goSpine ns sp

  goSpine ns [] = id
  goSpine ns ((t, Expl):sp) = ws . go projp ns t . goSpine ns sp
  goSpine ns ((t, Impl):sp) = ws . braces (go pairp ns t) . goSpine ns sp

  goApp :: Int -> [String] -> Tm -> ShowS
  goApp p ns t = case splitSpine t of
    (Meta x, sp) -> par p appp $ (show x++) . goMetaSp ns sp
    (h, sp)      -> par p appp $ go appp ns h . goSpine ns sp

  local :: [String] -> Ix -> String
  local ns topIx = go ns topIx where
    go (n:ns) 0 = case n of "_" -> '@':show topIx
                            n   -> snd (fresh ns (NLit n))
    go (n:ns) x = go ns (x - 1)
    go _      _ = "@" ++ show topIx
    go _      _ = impossible

  go :: Int -> [String] -> Tm -> ShowS
  go p ns = \case

    LocalVar x ->
      (local ns x++)

    TopDef x _ _ -> runIO do
      str <- readTopInfo x >>= \case
        TEDef x _ _ _       -> pure $! spanToString x
        _                   -> impossible
      pure $! (str++)

    Lam (fresh ns -> (n,x)) i a t -> par p letp $ ("λ "++) . lamBind x i . goLam (n:ns) t where
      goLam ns (Lam (fresh ns -> (n,x)) i a t) = ws . lamBind x i . goLam (n:ns) t
      goLam ns t                               = (". "++) . go letp ns t

    EqSym `AppI` a `AppE` t `AppE` u ->
      par p eqp $ go appp ns t . (" ={"++) . go pairp ns a . ("} "++). go appp ns u

    -- Coe a b _ t -> par p appp $ ("coe "++) . go appp ns a . ws . go appp ns b . (" _ "++) . go projp ns t

    t@App{} -> goApp p ns t

    -- App t u Expl -> par p appp $ go appp ns t . ws . go projp ns u
    -- App t u Impl -> par p appp $ go appp ns t . ws . braces (go pairp ns u)

    Pair t u -> par p pairp $ go letp ns t . (", "++) . go pairp ns u

    ProjField t x _ -> par p projp $ go projp ns t . ('.':) . (show x++)

    Proj1 t -> par p projp $ go projp ns t . (".1"++)
    Proj2 t -> par p projp $ go projp ns t . (".2"++)

    Pi NUnused Expl a b  -> par p pip $ go sigmap ns a . (" → "++) . go pip ("_":ns) b
    Pi (fresh ns -> (n,x)) i a b ->
      par p pip $ piBind ns x i a . goPi (n:ns) b where
        goPi ns (Pi (fresh ns -> (n,x)) i a b)
          | x /= "_"  = piBind ns x i a . goPi (n:ns) b
        goPi ns b = (" → "++) . go pip ns b

    Sg _ NUnused a b ->
      par p sigmap $ go eqp ns a . (" × "++) . go sigmap ("_":ns) b
    Sg _ (fresh ns -> (n,x)) a b ->
      par p sigmap $ sgBind ns x a . (" × "++) . go sigmap (n:ns) b

    Postulate x _ -> runIO do
      str <- readTopInfo x >>= \case
        TEPostulate x _ _ _ -> pure $! spanToString x
        _                   -> impossible
      pure $! (str++)

    InsertedMeta x LEmpty -> (show x++)
    InsertedMeta x ls     -> (show x++).("(..)"++)

    Meta x -> (show x++)

    Let (fresh ns -> (n,x)) a t u ->
      par p letp $ ("let "++) . (x++) . (" : "++) . go letp ns a
      . (" := "++) . go letp ns t . ("; "++) . go letp (n:ns) u

    TaggedSym  -> ("Tagged"++)
    Tag t      -> par p projp $ go projp ns t . (".tag"++)
    Untag t    -> par p projp $ go projp ns t . (".untag"++)

    Set        -> ("Set"++)
    Prop       -> ("Prop"++)
    Top        -> ("⊤"++)
    Tt         -> ("tt"++)
    Bot        -> ("⊥"++)
    CoeSym     -> ("coe"++)
    EqSym      -> ("(=)"++)
    ReflSym    -> ("refl"++)
    SymSym     -> ("sym"++)
    TransSym   -> ("trans"++)
    ApSym      -> ("ap"++)
    ExfalsoSym -> ("exfalso"++)
    ElSym      -> ("El"++)

    Magic m -> case m of
      Undefined  -> ("undefined"++)
      Nonlinear  -> ("nonlinear"++)
      MetaOccurs -> ("metaoccurs"++)

showTm :: LocalsArg => Tm -> String
showTm t = goTm pairp localNames t []

showTm0 :: Tm -> String
showTm0 t = let ?locals = LEmpty in showTm t

-- showTm :: LocalsArg => Tm -> String
-- showTm t = show t

-- showTm0 :: Tm -> String
-- showTm0 t = show t

showTm' :: NamesArg => Tm -> String
showTm' t = goTm pairp ?names t []
