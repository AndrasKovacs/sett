
{-# options_ghc -Wno-unused-top-binds #-}

module Pretty (showTm, showTm', showTm0) where

import IO

import Common
import Syntax
import ElabState

-- TODO: shadowing is not handled at all now!
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

  piBind ns x Expl a = ('(':) . (x++) . (" : "++) . go letp ns a .(')':)
  piBind ns x Impl a = braces  ((x++) . (" : "++) . go letp ns a)

  lamBind x Impl = braces (x++)
  lamBind x Expl = (x++)

  sgBind ns "_" a = go eqp ns a
  sgBind ns x   a = ('(':).(x++).(" : "++).go pairp ns a.(')':)

  go :: Int -> [String] -> Tm -> ShowS
  go p ns = \case

    -- LocalVar (Ix x) -> case ns !! x of
    --   "_" -> (('@':show x)++)
    --   x   -> (x++)

    LocalVar (Ix x) | x < length ns ->
      case ns !! x of
        "_" -> (('@':show x)++)
        x   -> (x++)
    LocalVar (Ix x) -> (('@':show x)++)

    TopDef x _ _ -> runIO do
      str <- readTopInfo x >>= \case
        TEDef x _ _ _       -> pure $! spanToString x
        _                   -> impossible
      pure $! (str++)

    Lam (show -> x) i a t -> par p letp $ ("λ "++) . lamBind x i . goLam (x:ns) t where
      goLam ns (Lam (show -> x) i a t) = ws . lamBind x i . goLam (x:ns) t
      goLam ns t                       = (". "++) . go letp ns t

    EqSym `AppI` a `AppE` t `AppE` u ->
      par p eqp $ go appp ns t . (" ={"++) . go pairp ns a . ("} "++). go appp ns u

    -- Coe a b _ t -> par p appp $ ("coe "++) . go appp ns a . ws . go appp ns b . (" _ "++) . go projp ns t

    App t u Expl -> par p appp $ go appp ns t . ws . go projp ns u
    App t u Impl -> par p appp $ go appp ns t . ws . braces (go pairp ns u)

    Pair t u -> par p pairp $ go letp ns t . (", "++) . go pairp ns u

    ProjField t x _ -> par p projp $ go projp ns t . ('.':) . (show x++)

    Proj1 t -> par p projp $ go projp ns t . (".1"++)
    Proj2 t -> par p projp $ go projp ns t . (".2"++)

    Pi NUnused Expl a b  -> par p pip $ go sigmap ns a . (" → "++) . go pip ("_":ns) b
    Pi (show -> x) i a b ->
      par p pip $ piBind ns x i a . goPi (x:ns) b where
        goPi ns (Pi (show -> x) i a b)
          | x /= "_"  = piBind ns x i a . goPi (x:ns) b
        goPi ns b = (" → "++) . go pip ns b

    Sg _ NUnused a b ->
      par p sigmap $ go eqp ns a . (" × "++) . go sigmap ("_":ns) b
    Sg _ (show -> x) a b ->
      par p sigmap $ sgBind ns x a . (" × "++) . go sigmap (x:ns) b

    Postulate x _ -> runIO do
      str <- readTopInfo x >>= \case
        TEPostulate x _ _ _ -> pure $! spanToString x
        _                   -> impossible
      pure $! (str++)

    InsertedMeta x LEmpty -> (show x++)
    InsertedMeta x ls     -> (show x++).("(..)"++)

    Meta x -> (show x++)

    Let (show -> x) a t u ->
      par p letp $ ("let "++) . (x++) . (" : "++) . go letp ns a
      . (" := "++) . go letp ns t . ("; "++) . go letp (x:ns) u

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
