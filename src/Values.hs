
module Values where

import Common

--------------------------------------------------------------------------------

data RigidHead
  = RHLocalVar Lvl Ty
  | RHPostulate Lvl
  | RHCoe Val Val Val Val
  | RHRefl Val Val
  | RHSym Val Val Val Val
  | RHTrans Val Val Val Val Val Val
  | RHAp Val Val Val Val Val Val
  | RHExfalso Val Val

pattern Refl a t          = Rigid (RHRefl a t) SId
pattern Sym a t u p       = Rigid (RHSym a t u p) SId
pattern Trans a t u v p q = Rigid (RHTrans a t u v p q) SId
pattern Ap a b f t u p    = Rigid (RHAp a b f t u p) SId
pattern Exfalso a t       = Rigid (RHExfalso a t) SId

data FlexHead
  = FHMeta MetaVar                    -- blocking on meta
  | FHCoeRefl MetaVar Val Val Val Val -- coe-refl rule blocked by a meta

headMeta :: FlexHead -> MetaVar
headMeta = \case
  FHMeta x            -> x
  FHCoeRefl x _ _ _ _ -> x

data UnfoldHead
  = UHSolvedMeta MetaVar
  | UHTopDef Lvl

-- TODO: Coe/Id blocking is perhaps too fine-grained!
data Spine
  = SId
  | SApp Spine Val Icit

  | SProj1 Spine
  | SProj2 Spine
  | SProjField Spine Name Int

  | SCoeSrc Spine Val Val Val    -- netural source type
  | SCoeTgt Val Spine Val Val    -- neutral target type
  | SCoeTrans Val Val Val Spine  -- composition blocking on neutral coerced value

  | SEqSet Spine Val Val  -- neutral eq type
  | SEqLhs Val Spine Val  -- neutral eq lhs
  | SEqRhs Val Val Spine  -- neutral eq rhs

--------------------------------------------------------------------------------

newtype Closure = Cl {unCl :: Val -> Val}

instance Show Closure where showsPrec _ _ acc = "<closure>" ++ acc

-- | Strict application.
($$) :: Closure -> Val -> Val
Cl f $$ t = f t
{-# inline ($$) #-}
infixl 0 $$

-- | Lazy application
($$$) :: Closure -> Val -> Val
Cl f $$$ ~t = f t
{-# inline ($$$) #-}
infixl 0 $$$

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
  | Pair SP Val Val
  | Lam SP Name Icit Ty Closure
  | Sg SP Name Ty Closure
  | Pi SP Name Icit Ty Closure
  | Set
  | Prop
  | El Val
  | Top
  | Tt
  | Bot
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

--------------------------------------------------------------------------------

data GVal = G {g1, g2 :: ~Val}
type GTy  = GVal

gjoin :: Val -> GVal
gjoin ~v = G v v
{-# inline gjoin #-}

--------------------------------------------------------------------------------

data Env = ENil | EDef Env ~Val
