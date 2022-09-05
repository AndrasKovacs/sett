
module Pretty where

import IO
import qualified Data.Array.LI as LI

import Common
import Syntax
import ElabState

-- TODO: shadowing
--------------------------------------------------------------------------------

-- printing precedences
atomp  = 7  :: Int
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

goTm :: Int -> LI.Array String -> [String] -> Tm -> ShowS
goTm prec topns ns t = go prec ns t where

  piBind ns x Expl a = ('(':) . (x++) . (" : "++) . go letp ns a .(')':)
  piBind ns x Impl a = braces  ((x++) . (" : "++) . go letp ns a)

  lamBind x Impl = braces (x++)
  lamBind x Expl = (x++)

  sgBind ns "_" a = go eqp ns a
  sgBind ns x   a = ('(':).(x++).(" : "++).go pairp ns a.(')':)

  go :: Int -> [String] -> Tm -> ShowS
  go p ns = \case

    LocalVar (Ix x) -> case ns !! x of
      "_" -> (('@':show x)++)
      x   -> (x++)

    TopDef (Lvl x) _ _ -> (topns LI.! x++)

    Lam _ (show -> x) i a t -> par p letp $ ("λ "++) . lamBind x i . goLam (x:ns) t where
      goLam ns (Lam _ (show -> x) i a t) = ws . lamBind x i . goLam (x:ns) t
      goLam ns t                         = (". "++) . go letp ns t

    EqSym `AppI` a `AppE` t `AppE` u ->
      par p eqp $ go appp ns t . (" = "++) . go appp ns u

    App t u Expl -> par p appp $ go appp ns t . ws . go projp ns u
    App t u Impl -> par p appp $ go appp ns t . ws . braces (go pairp ns u)

    Pair _ t u -> par p pairp $ go letp ns t . (", "++) . go pairp ns u

    ProjField t x _ -> par p projp $ go projp ns t . ('.':) . (show x++)

    Proj1 t -> par p projp $ go projp ns t . (".1"++)
    Proj2 t -> par p projp $ go projp ns t . (".2"++)

    Pi NUnused Expl a b  -> par p pip $ go appp ns a . (" → "++) . go pip ("_":ns) b
    Pi (show -> x) i a b ->
      par p pip $ piBind ns x i a . goPi (x:ns) b where
        goPi ns (Pi (show -> x) i a b)
          | x /= "_"  = piBind ns x i a . goPi (x:ns) b
        goPi ns b = (" → "++) . go pip ns b

    Sg (show -> x) a b ->
      par p sigmap $ sgBind ns x a . (" × "++) . go sigmap (x:ns) b

    Postulate (Lvl x) _ -> (topns LI.! x++)

    InsertedMeta x ls -> ("?"++).(show x++).("(..)"++)

    Meta x -> ("?"++).(show x++)

    Let (show -> x) a t u ->
      par p letp $ ("let "++) . (x++) . (" : "++) . go letp ns a
      . (" := "++) . go letp ns t . ("; "++) . go letp (x:ns) u

    Set        -> ("Set"++)
    Prop       -> ("Prop"++)
    Top        -> ("⊤"++)
    Tt         -> ("tt"++)
    Bot        -> ("⊥"++)
    ElSym      -> ("El"++)
    CoeSym     -> ("coe"++)
    EqSym      -> ("(=)"++)
    ReflSym    -> ("refl"++)
    SymSym     -> ("sym"++)
    TransSym   -> ("trans"++)
    ApSym      -> ("ap"++)
    ExfalsoSym -> ("exfalso"++)

    Magic m -> case m of
      Undefined  -> ("undefined"++)
      Nonlinear  -> ("nonlinear"++)
      MetaOccurs -> ("metaoccurs"++)

showTm :: LocalsArg => Tm -> String
showTm t = runIO do
  topns <- topNames
  pure $! goTm pairp topns localNames t []
