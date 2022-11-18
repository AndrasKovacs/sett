
module Syntax where

import Common
import Values (Val)
import qualified Values as V

-- Pruning
--------------------------------------------------------------------------------

-- | A `Pruning` represents a spine of variables, which contains a subsequence
--   of all variables in scope. A `Just` represents application to a var, a `Nothing`
--   skips over a var.
type Pruning = [Maybe Icit]

type PruningArg = (?pruning :: Pruning)

-- | A reversed pruning. Used for pruning Pi domains, where we have to iterate
--   inside-out.
newtype RevPruning = RevPruning# Pruning

revPruning :: Pruning -> RevPruning
revPruning = RevPruning# . reverse

--------------------------------------------------------------------------------

-- | Description of the local scope.
data Locals
  = LEmpty
  | LDefine Locals Name Tm Ty
  | LBind Locals Name Ty
  deriving Show

type LocalsArg = (?locals :: Locals)

locals :: (LocalsArg => a) -> (LocalsArg => a)
locals a = seq ?locals a
{-# inline locals #-}

--
localNames :: LocalsArg => [String]
localNames = go ?locals where
  go LEmpty = []
  go (LDefine ls x _ _) = show x : go ls
  go (LBind ls x _)     = show x : go ls

type NamesArg = (?names :: [String])

closeTy :: LocalsArg => Ty -> Ty
closeTy b = go ?locals b where
  go ls b = case ls of
    LEmpty           -> b
    LBind ls x a     -> go ls (Pi x Expl a b)
    LDefine ls x t a -> go ls (Let x a t b)

--------------------------------------------------------------------------------

type Ty = Tm

data Tm
  = LocalVar Ix
  | HideTopDef Lvl ~(Hide Val) ~(Hide V.Ty)

  | Lam Name Icit Ty Tm
  | App Tm Tm Icit

  | Pair Tm Tm
  | ProjField Tm Name Int
  | Proj1 Tm
  | Proj2 Tm

  | Pi Name Icit Ty Ty
  | Sg SP Name Ty Ty

  | NewtypeSym
  | Pack Ty Tm  -- annotation: type of the result (some Newtype A B x)
  | Unpack Tm

  | HidePostulate Lvl ~(Hide V.Ty)
  | InsertedMeta MetaVar Locals
  | Meta MetaVar
  | Let Name Ty Tm Tm

  | Set
  | Prop
  | Top
  | Tt
  | Bot

  | EqSym
  | CoeSym
  | ReflSym
  | SymSym
  | TransSym
  | ApSym
  | ExfalsoSym
  | ElSym

  | Magic Magic
  deriving Show

pattern TopDef :: Lvl -> Val -> V.Ty -> Tm
pattern TopDef x t a <- HideTopDef x (coerce -> t) (coerce -> a) where
  TopDef x ~t ~a = HideTopDef x (coerce t) (coerce a)

pattern Postulate :: Lvl -> V.Ty -> Tm
pattern Postulate x a <- HidePostulate x (coerce -> a) where
  Postulate x ~a = HidePostulate x (coerce a)

{-# complete
  LocalVar, TopDef, Lam, App, Pair, ProjField, Proj1, Proj2, Pi, Sg, Postulate,
  InsertedMeta, Meta, Let, Set, Prop, Top, Tt, Bot, EqSym, CoeSym, ReflSym,
  SymSym, TransSym, ApSym, ExfalsoSym, Magic, ElSym, NewtypeSym, Pack, Unpack
  #-}

pattern AppE t u = App t u Expl
pattern AppI t u = App t u Impl

pattern Exfalso a t       = ExfalsoSym `AppI` a `AppE` t
pattern Eq a t u          = EqSym  `AppI`  a `AppE`  t `AppE`  u
pattern Refl a t          = ReflSym `AppI`  a `AppI`  t
pattern Coe a b p t       = CoeSym `AppI`  a `AppI`  b `AppE`  p `AppE` t
pattern Sym a x y p       = SymSym `AppI`  a `AppI`  x `AppI`  y `AppE`  p
pattern Trans a x y z p q = TransSym `AppI`  a `AppI`  x `AppI`  y `AppI` z  `AppE` p `AppE` q
pattern Ap a b f x y p    = ApSym  `AppI` a `AppI`  b `AppE`  f `AppI`  x `AppI`  y `AppE`  p
pattern El a              = ElSym `AppE` a
pattern Newtype a b x     = NewtypeSym `AppI` a `AppE` b `AppE` x
