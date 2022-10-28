
module Values where

import Common
import GHC.Exts

--------------------------------------------------------------------------------

-- | Annotation on bound variables which is only used during partial
--   substitution. If a variable is in the domain of a partial substitution,
--   that means that it has been already substituted.
type InPSubDomain = Bool

data RigidHead
  = RHLocalVar Lvl ~Ty InPSubDomain
  | RHPostulate Lvl ~Ty
  | RHExfalso Val Val
  | RHCoe Val Val Val Val  -- rigid neutral coe

pattern Exfalso a t <- Rigid (RHExfalso a t) SId _ where
  Exfalso a t = Rigid (RHExfalso a t) SId a

pattern Coe a b p t <- Rigid (RHCoe a b p t) SId _ where
  Coe a b p t = Rigid (RHCoe a b p t) SId b

data FlexHead
  = FHMeta MetaVar                 -- blocking on meta
  | FHCoe MetaVar Val Val Val Val  -- coe rigidly blocked on a meta

flexHeadMeta :: FlexHead -> MetaVar
flexHeadMeta = \case
  FHMeta x        -> x
  FHCoe x _ _ _ _ -> x

data UnfoldHead
  = UHSolvedMeta MetaVar
  | UHTopDef Lvl ~Val ~Ty
  | UHCoe Val Val Val Val  -- at least 1 Unfold

data Spine
  = SId
  | SApp Spine Val Icit
  | SProj1 Spine
  | SProj2 Spine
  | SProjField Spine Val ~Ty Int -- projected value, its type, field index

-- | Reversed spine.
data RevSpine
  = RSId
  | RSApp Val Icit RevSpine
  | RSProj1 RevSpine
  | RSProj2 RevSpine
  | RSProjField Val ~Ty Int RevSpine

reverseSpine :: Spine -> RevSpine
reverseSpine = go RSId where
  go acc = \case
    SId                 -> acc
    SApp t u i          -> go (RSApp u i acc) t
    SProj1 t            -> go (RSProj1 acc) t
    SProj2 t            -> go (RSProj2 acc) t
    SProjField t tv a n -> go (RSProjField tv a n acc) t

hasProjection :: Spine -> Bool
hasProjection = \case
  SId          -> False
  SApp t _ _   -> hasProjection t
  SProj1{}     -> True
  SProj2{}     -> True
  SProjField{} -> True


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

appClIn :: Lvl -> Closure -> Val -> Val
appClIn l = let ?lvl = l in ($$)
{-# inline appClIn #-}

appClInLazy :: Lvl -> Closure -> Val -> Val
appClInLazy l = let ?lvl = l in ($$~)
{-# inline appClInLazy #-}

--------------------------------------------------------------------------------

type Ty = Val

data Val
  -- Rigidly stuck values
  = Rigid RigidHead Spine ~Ty
  | RigidEq Ty Val Val                -- at least 1 Val is rigid

  -- Flexibly stuck values
  | Flex FlexHead Spine ~Ty
  | FlexEq MetaVar Val Val Val        -- at least 1 Val is flex

  -- Traced reductions
  | Unfold UnfoldHead Spine ~Val ~Ty  -- unfolding choice (top/meta)
  | TraceEq Val Val Val ~Val          -- trace Eq reduction to non-Eq proposition
  | UnfoldEq Ty Val Val ~Val          -- at least 1 Val is Unfold

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

  | Magic Magic

markEq :: Val -> Val -> Val -> Val -> Val
markEq ~a ~t ~u ~v = TraceEq a t u v
{-# inline markEq #-}

pattern Var' x a b <- Rigid (RHLocalVar x _ b) SId a where
  Var' x ~a b = Rigid (RHLocalVar x a b) SId a

pattern Var x a = Var' x a False

-- | Bump the `Lvl` and get a fresh variable.
newVar :: Ty -> (LvlArg => Val -> a) -> LvlArg => a
newVar a cont =
  let v = Var ?lvl a in
  let ?lvl = ?lvl + 1 in
  seq ?lvl (cont v)
{-# inline newVar #-}

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

pattern VUndefined  = Magic Undefined
pattern VNonlinear  = Magic Nonlinear
pattern VMetaOccurs = Magic MetaOccurs

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

envLength :: Env -> Lvl
envLength e = Lvl (go 0 e) where
  go n ENil = n
  go n (EDef e _) = go (n + 1) e

type Vars = Env

--------------------------------------------------------------------------------

showVal :: Val -> String
showVal = \case
  Rigid (RHLocalVar x _ _) _ _ -> "(LocalVar "++ show x ++ ")"
  Set -> "Set"
  _ -> error "showVal"
