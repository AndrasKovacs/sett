
module Values where

import Common
import GHC.Exts

--------------------------------------------------------------------------------

data RigidHead
  = RHLocalVar Lvl ~Ty
  | RHPostulate Lvl
  | RHExfalso Val Val
  | RHCoe Val Val Val Val  -- rigid neutral coe

pattern Exfalso a t = Rigid (RHExfalso a t) SId
pattern Coe a b p t = Rigid (RHCoe a b p t) SId

data FlexHead
  = FHMeta MetaVar                 -- blocking on meta
  | FHCoe MetaVar Val Val Val Val  -- coe rigidly blocked on a meta

flexHeadMeta :: FlexHead -> MetaVar
flexHeadMeta = \case
  FHMeta x        -> x
  FHCoe x _ _ _ _ -> x

data UnfoldHead
  = UHSolvedMeta MetaVar
  | UHTopDef Lvl
  | UHCoe Val Val Val Val  -- at least 1 Unfold

data Spine
  = SId
  | SApp Spine Val Icit
  | SProj1 Spine
  | SProj2 Spine
  | SProjField Spine ~Ty Int  -- we display field projections based on computed types

--------------------------------------------------------------------------------

-- | A closure abstract over the `Int#` which marks the next fresh variable.
--   Since it is impossible for GHC to unbox this argument, and we want to make
--   the argument implicit, and only lifted types can be implicit, we unbox it
--   by hand, and define `Cl` as a pattern synonym with the more convenient
--   type.
newtype Closure = Cl# {unCl# :: Int# -> Val -> Val}
newtype Wrap# = Wrap# (LvlArg => Val -> Val)

pattern Cl :: (LvlArg => Val -> Val) -> Closure
pattern Cl f <- ((\(Cl# f) -> Wrap# \v -> case ?lvl of Lvl (I# l) -> f l v) -> Wrap# f) where
  Cl f = Cl# \l v -> let ?lvl = Lvl (I# l) in f v
{-# complete Cl #-}

unCl :: Closure -> LvlArg => Val -> Val
unCl (Cl f) = f
{-# inline unCl #-}

instance Show Closure where showsPrec _ _ acc = "<closure>" ++ acc

-- | Strict application.
($$) :: LvlArg => Closure -> Val -> Val
Cl f $$ t = f t
{-# inline ($$) #-}
infixl 0 $$

-- | Lazy application
($$~) :: LvlArg => Closure -> Val -> Val
Cl f $$~ ~t = f t
{-# inline ($$~) #-}
infixl 0 $$~

--------------------------------------------------------------------------------

type Ty = Val

data Val
  -- Rigidly stuck values
  = Rigid RigidHead Spine
  | RigidEq Val Val Val           -- at least 1 Val is rigid

  -- Flexibly stuck values
  | Flex FlexHead Spine
  | FlexEq MetaVar Val Val Val    -- at least 1 Val is flex

  -- Traced reductions
  | Unfold UnfoldHead Spine ~Val  -- unfolding choice (top/meta)
  | TraceEq Val Val Val ~Val      -- trace Eq reduction to non-Eq proposition
  | UnfoldEq Val Val Val ~Val     -- at least 1 Val is Unfold

  -- Canonical values
  | Set
  | El Val

  | Pi Name Icit Ty Closure
  | Lam SP Name Icit Ty Closure

  | Sg Name Ty Closure
  | Pair SP Val Val

  | Prop
  | Top
  | Tt
  | Bot

  | Refl Val Val
  | Sym Val Val Val Val
  | Trans Val Val Val Val Val Val
  | Ap Val Val Val Val Val Val

  | Irrelevant

markEq :: Val -> Val -> Val -> Val -> Val
markEq ~a ~t ~u ~v = TraceEq a t u v
{-# inline markEq #-}

pattern Var x ga = Rigid (RHLocalVar x ga) SId

pattern LamP x i a t = Lam P x i a (Cl t)
pattern LamS x i a t = Lam S x i a (Cl t)
pattern LamPE x a t = Lam P x Expl a (Cl t)
pattern LamPI x a t = Lam P x Impl a (Cl t)
pattern LamSE x a t = Lam S x Expl a (Cl t)
pattern LamSI x a t = Lam S x Impl a (Cl t)

pattern PiS x i a b = Pi x i a (Cl b)
pattern PiSE x a b = Pi x Expl a (Cl b)
pattern PiSI x a b = Pi x Impl a (Cl b)

pattern PiP x i a b = Pi x i a (Cl b)
pattern PiPE x a b = Pi x Expl a (Cl b)
pattern PiPI x a b = Pi x Impl a (Cl b)

pattern SgS x a b   = Sg x a (Cl b)
pattern SgP x a b   = Sg x a (Cl b)

funP :: Val -> Val -> Val
funP a b = PiPE NUnused a \_ -> b

funS :: Val -> Val -> Val
funS a b = PiSE NUnused a \_ -> b

andP :: Val -> Val -> Val
andP a b = SgP NUnused a \_ -> b

gU :: SP -> GTy
gU S = gjoin Set
gU P = gjoin Prop

gSet         = gjoin Set
gProp        = gjoin Prop
gEl (G a fa) = G (El a) (El fa); {-# inline gEl #-}

--------------------------------------------------------------------------------

-- | @g1@ is minimally computed and @g2@ is maximally computed.
--   The two values are definitionally equal.
data G    = G {g1 :: ~Val, g2 :: ~Val}
type GTy  = G

gjoin :: Val -> G
gjoin ~v = G v v
{-# inline gjoin #-}

--------------------------------------------------------------------------------

data Env = ENil | EDef Env ~Val
type EnvArg = (?env :: Env)
