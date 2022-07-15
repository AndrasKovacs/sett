
module Values where

import Common

--------------------------------------------------------------------------------

data RigidHead
  = RHLocalVar Lvl ~Ty
  | RHPostulate Lvl
  | RHCoe Val Val Val Val  -- rigid neutral coe (including canonical mismatch)
  | RHExfalso Val Val

pattern Exfalso a t = Rigid (RHExfalso a t) SId

data FlexHead
  = FHMeta MetaVar                -- blocking on meta
  | FHCoe MetaVar Val Val Val Val -- coe rigidly blocked on a meta

headMeta :: FlexHead -> MetaVar
headMeta = \case
  FHMeta x        -> x
  FHCoe x _ _ _ _ -> x

data UnfoldHead
  = UHSolvedMeta MetaVar
  | UHTopDef Lvl

data Spine
  = SId
  | SApp Spine Val Icit

  | SProj1 Spine
  | SProj2 Spine
  | SProjField Spine Name Int   -- t : (foo : A) * (bar : B) * Top
                                -- t.bar

  -- ISSUE: printed field names can't be re-checked (after reductions)
  --   solution 1: just recompute type, print field name corresponding to
  --               Int projection (or maybe the Int itself, if there's no name)

  -- f : Rec → Rec
  -- f = λ (u : (foo' : A) * (bar' : B) * Top). u

  -- (f t).foo'           --
  -- (f t).foo'
  -- t.n  (doesn't check)

--------------------------------------------------------------------------------

newtype Closure = Cl {unCl :: Val -> Val}

instance Show Closure where showsPrec _ _ acc = "<closure>" ++ acc

-- | Strict application.
($$) :: Closure -> Val -> Val
Cl f $$ t = f t
{-# inline ($$) #-}
infixl 0 $$

-- | Lazy application
($$~) :: Closure -> Val -> Val
Cl f $$~ ~t = f t
{-# inline ($$~) #-}
infixl 0 $$~

--------------------------------------------------------------------------------

type Ty = Val

data Val
  -- Rigidly stuck values
  = Rigid RigidHead Spine

  -- Flexibly stuck values
  | Flex FlexHead Spine

  -- Traced reductions
  | Unfold UnfoldHead Spine ~Val  -- unfolding choice (top/meta)
  -- | Eq Val Val Val Val            -- Eq computation to non-Eq type

  -- Canonical values
  | Pi SP Name Icit Ty Closure
  | Lam SP Name Icit Ty Closure

  | Sg SP Name Ty Closure
  | Pair SP Val Val

  | Prop
  | El Val
  | Top
  | Tt
  | Bot

  | Set

  | Refl Val Val
  | Sym Val Val Val Val
  | Trans Val Val Val Val Val Val
  | Ap Val Val Val Val Val Val

  | Irrelevant

markEq :: Val -> Val -> Val -> Val -> Val
markEq ~a ~t ~u ~v = v
{-# inline markEq #-}

pattern Var x ga = Rigid (RHLocalVar x ga) SId

pattern LamP x i a t = Lam P x i a (Cl t)
pattern LamS x i a t = Lam S x i a (Cl t)
pattern LamPE x a t = Lam P x Expl a (Cl t)
pattern LamPI x a t = Lam P x Impl a (Cl t)
pattern LamSE x a t = Lam S x Expl a (Cl t)
pattern LamSI x a t = Lam S x Impl a (Cl t)

pattern PiS x i a b = Pi S x i a (Cl b)
pattern PiSE x a b = Pi S x Expl a (Cl b)
pattern PiSI x a b = Pi S x Impl a (Cl b)

pattern PiP x i a b = Pi P x i a (Cl b)
pattern PiPE x a b = Pi P x Expl a (Cl b)
pattern PiPI x a b = Pi P x Impl a (Cl b)

pattern SgS x a b   = Sg S x a (Cl b)
pattern SgP x a b   = Sg P x a (Cl b)

funP :: Val -> Val -> Val
funP a b = PiPE NUnused a \_ -> b

funS :: Val -> Val -> Val
funS a b = PiSE NUnused a \_ -> b

andP :: Val -> Val -> Val
andP a b = SgP NUnused a \_ -> b

gSet = gjoin Set
gProp = gjoin Prop
gEl (G a fa) = G (El a) (El fa); {-# inline gEl #-}

--------------------------------------------------------------------------------

data G    = G {g1 :: Val, g2 :: ~Val}
type GTy  = G

gjoin :: Val -> G
gjoin ~v = G v v
{-# inline gjoin #-}

--------------------------------------------------------------------------------

data Env = ENil | EDef Env ~Val
