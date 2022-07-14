
module Syntax where

import Common
import Values (Val)

type Ty = Tm

-- | Description of the local scope.
data Locals
  = LEmpty
  | LDefine Locals Name Tm Ty
  | LBind Locals Name Ty
  deriving Show

data Tm
  = LocalVar Ix
  | TopDef ~(Hide Val) Lvl

  | Lam SP Name Icit Ty Tm
  | App Tm Tm Icit

  | Pair SP Tm Tm
  | ProjField Tm Name Int
  | Proj1 Tm
  | Proj2 Tm

  | Pi SP Name Icit Ty Ty
  | Sg SP Name Ty Ty

  | Postulate Lvl
  | InsertedMeta MetaVar Locals
  | Meta MetaVar
  | Let Name Ty Tm Tm

  | Set
  | Prop
  | Top
  | Tt
  | Bot

  | ElSym
  | EqSym
  | CoeSym
  | ReflSym
  | SymSym
  | TransSym
  | ApSym
  | ExfalsoSym

  | Irrelevant
  deriving Show

pattern AppE t u = App t u Expl
pattern AppI t u = App t u Impl

pattern El a              = ElSym `AppE` a
pattern Exfalso a t       = ExfalsoSym `AppI` a `AppE` t
pattern Eq a t u          = EqSym  `AppI`  a `AppE`  t `AppE`  u
pattern Refl a t          = ReflSym `AppI`  a `AppI`  t
pattern Coe a b p t       = CoeSym `AppI`  a `AppI`  b `AppE`  p `AppE` t
pattern Sym a x y p       = SymSym `AppI`  a `AppI`  x `AppI`  y `AppE`  p
pattern Trans a x y z p q = TransSym `AppI`  a `AppI`  x `AppI`  y `AppI` z  `AppE` p `AppE` q
pattern Ap a b f x y p    = ApSym  `AppI`  a `AppI`  b `AppE`  f `AppI`  x `AppI`  y `AppE`  p
