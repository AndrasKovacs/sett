
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

  -- axioms
  | RHRefl Val Val
  | RHSym Val Val Val Val
  | RHTrans Val Val Val Val Val Val
  | RHAp Val Val Val Val Val Val
  deriving Show

data FlexHead
  = FHMeta MetaVar                 -- blocking on meta
  | FHCoe MetaVar Val Val Val Val  -- coe rigidly blocked on a meta
  deriving Show

flexHeadMeta :: FlexHead -> MetaVar
flexHeadMeta = \case
  FHMeta x        -> x
  FHCoe x _ _ _ _ -> x

data UnfoldHead
  = UHSolvedMeta MetaVar
  | UHTopDef Lvl ~Val ~Ty
  | UHCoe Val Val Val Val  -- at least 1 Unfold
  deriving Show

data Spine
  = SId
  | SApp Spine Val Icit
  | SProj1 Spine
  | SProj2 Spine
  | SProjField Spine Val ~Ty Int -- projected value, its type, field index
  | SUntag Spine
  deriving Show

-- | Reversed spine.
data RevSpine
  = RSId
  | RSApp Val Icit RevSpine
  | RSProj1 RevSpine
  | RSProj2 RevSpine
  | RSProjField Val ~Ty Int RevSpine
  | RSUntag RevSpine

reverseSpine :: Spine -> RevSpine
reverseSpine = go RSId where
  go acc = \case
    SId                 -> acc
    SApp t u i          -> go (RSApp u i acc) t
    SProj1 t            -> go (RSProj1 acc) t
    SProj2 t            -> go (RSProj2 acc) t
    SProjField t tv a n -> go (RSProjField tv a n acc) t
    SUntag t            -> go (RSUntag acc) t

hasProjection :: Spine -> Bool
hasProjection = \case
  SId          -> False
  SApp t _ _   -> hasProjection t
  SProj1{}     -> True
  SProj2{}     -> True
  SProjField{} -> True
  SUntag{}     -> True

computeProjField :: Spine -> Int -> Spine
computeProjField t n
  | n > 0  = SProj1 (computeProjField t (n-1))
  | n == 0 = SProj2 t
  | otherwise = impossible

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
  | Lam Name Icit Ty Closure

  | Sg SP Name Ty Closure
  | Pair Val Val

  | Tagged Val Val Val
  | Tag Val

  | Prop
  | Top
  | Tt
  | Bot

  | Magic Magic
  deriving Show

markEq :: Val -> Val -> Val -> Val -> Val
markEq ~a ~t ~u ~v = TraceEq a t u v
{-# inline markEq #-}

pattern Var' x a b <- Rigid (RHLocalVar x _ b) SId a where
  Var' x ~a b = Rigid (RHLocalVar x a b) SId a

pattern Var x a = Var' x a False

pattern LamE x a t = Lam x Expl a (Cl t)
pattern LamI x a t = Lam x Impl a (Cl t)

pattern PiE  x a b = Pi x Expl a (Cl b)
pattern PiI  x a b = Pi x Impl a (Cl b)
pattern SgP  x a b = Sg P x a (Cl b)
pattern SpS  x a b = Sg S x a (Cl b)

pattern VUndefined  = Magic Undefined
pattern VNonlinear  = Magic Nonlinear
pattern VMetaOccurs = Magic MetaOccurs

infixr 1 ==>
(==>) :: Val -> Val -> Val
(==>) a b = PiE NUnused a \_ -> b

andP :: Val -> Val -> Val
andP a b = SgP NUnused a \_ -> b

gSet  = gjoin Set
gProp = gjoin Prop

gU S = gSet
gU P = gProp

gEl (G a fa) = G (El a) (El fa)
{-# inline gEl #-}

elSP :: SP -> Val -> Val
elSP S a = a
elSP P a = El a
{-# inline elSP #-}

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
