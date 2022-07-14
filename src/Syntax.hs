
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
  | El
  | Top
  | Tt
  | Bot
  -- | Eq
  | Coe
  | Refl
  | Sym
  | Trans
  | Ap
  | Exfalso

  | Irrelevant
  deriving Show
