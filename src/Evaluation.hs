
module Evaluation where

import Control.Exception hiding (force)
import IO

import Common
import ElabState
import Values

import qualified Presyntax as P
import qualified Syntax as S

--------------------------------------------------------------------------------

localVar :: Env -> Ix -> Val
localVar (EDef _ v) 0 = v
localVar (EDef e _) x = localVar e (x - 1)
localVar _          _ = impossible

meta :: MetaVar -> Val
meta x = runIO do
  readMeta x >>= \case
    MEUnsolved{}   -> pure (Flex (FHMeta x) SId)
    MESolved _ v _ -> pure (Unfold (UHSolvedMeta x) SId v)
{-# inline meta #-}

app :: Val -> Val -> Icit -> Val
app t u i = case t of
  Lam hl x i a t -> t $$ u
  Rigid h sp     -> Rigid h (SApp sp u i)
  Flex h sp      -> Flex h (SApp sp u i)
  Unfold h sp t  -> Unfold h (SApp sp u i) (app t u i)
  Irrelevant     -> Irrelevant
  _              -> impossible

appE :: Val -> Val -> Val
appE t u = app t u Expl

appI :: Val -> Val -> Val
appI t u = app t u Impl

proj1 :: Val -> Val
proj1 t = case t of
  Pair _ t u    -> t
  Rigid h sp    -> Rigid  h (SProj1 sp)
  Flex h sp     -> Flex   h (SProj1 sp)
  Unfold h sp t -> Unfold h (SProj1 sp) (proj1 t)
  Irrelevant    -> Irrelevant
  _             -> impossible

proj2 :: Val -> Val
proj2 t = case t of
  Pair _ t u    -> u
  Rigid h sp    -> Rigid  h (SProj2 sp)
  Flex h sp     -> Flex   h (SProj2 sp)
  Unfold h sp t -> Unfold h (SProj2 sp) (proj2 t)
  Irrelevant    -> Irrelevant
  _             -> impossible

projField :: Val -> P.Name -> Int -> Val
projField t x n = case t of
  Pair _ t u     -> case n of 0 -> t
                              n -> projField u x (n - 1)
  Rigid h sp     -> Rigid  h (SProjField sp x n)
  Flex h sp      -> Flex   h (SProjField sp x n)
  Unfold h sp t  -> Unfold h (SProjField sp x n) (projField t x n)
  Irrelevant     -> Irrelevant
  _              -> impossible

coe :: Lvl -> Val -> Val -> Val -> Val -> Val
coe l a b p t = case a // b of

  -- canonical
  ------------------------------------------------------------

  (El a, El b) -> proj1 p `appE` t

  (Pi _ x i a b, topB@(Pi _ x' i' a' b'))
    | i /= i' -> Exfalso topB p
    | True    -> LamS (pick x x') i a' \x' ->
        let p1 = proj1 p
            p2 = proj2 p
            x  = coe l a' a (Sym Set a a' p1) x'
        in coe l (b $$ x) (b' $$ x') (p2 `appE` x) (app t x i)

  (Sg _ x a b, Sg _ x' a' b') ->
    let t1  = proj1 t
        t2  = proj2 t
        t1' = coe l a a' (proj1 p) t1
        t2' = coe l (b $$ t1) (b' $$ t1') (proj2 p) t2
    in Pair S t1' t2'

  (Set, Set) -> t
  (Prop, Prop) -> t

  -- non-canonical
  ------------------------------------------------------------

  (Irrelevant, _) -> Irrelevant
  (_, Irrelevant) -> Irrelevant

  (Unfold h sp a, b) -> Unfold h (SCoeSrc sp b p t) (coe l a b p t)
  (a, Unfold h sp b) -> Unfold h (SCoeTgt a sp p t) (coe l a b p t)

  (Flex h sp, b) -> Flex h (SCoeSrc sp b p t)
  (a, Flex h sp) -> Flex h (SCoeTgt a sp p t)

  (a@Rigid{}, b) -> coeTrans l a b p t
  (a, b@Rigid{}) -> coeTrans l a b p t

  -- canonical mismatch
  ------------------------------------------------------------
  (a, b) -> Exfalso b p


coeTrans :: Lvl -> Val -> Val -> Val -> Val -> Val
coeTrans l a b p t = case t of
  Flex h sp                    -> Flex h (SCoeTrans a b p sp)
  Unfold h sp t                -> Unfold h (SCoeTrans a b p sp) (coeTrans l a b p t)
  Rigid (RHCoe a' _ p' t') SId -> coe l a' b (Trans Set a' a b p' p) t'
  Irrelevant                   -> Irrelevant
  t                            -> coeRefl l a b p t

coeRefl :: Lvl -> Val -> Val -> Val -> Val -> Val
coeRefl l a b p t = case conv l a b of
  Same      -> t
  Diff      -> Rigid (RHCoe a b p t) SId
  BlockOn x -> Flex (FHCoeRefl x a b p t) SId


-- Equality type
--------------------------------------------------------------------------------

eq :: Lvl -> Val -> Val -> Val -> Val
eq l a t u = case a of
  Set  -> eqSet l t u
  Prop -> eqProp t u
  El a -> Eq (El a) t u Top

  topA@(Pi _ x i a b) -> Eq topA t u $
    PiSE x a \x -> eq l (b $$ x) (app t x i) (app u x i)

  topA@(Sg _ x a b) ->
    let t1 = proj1 t
        u1 = proj1 u
        t2 = proj2 t
        u2 = proj2 u
    in Eq topA t u $
       SgP NP (eq l a t1 u2) \p ->
         eq l (b $$ u1)
              (coe l (b $$ t1) (b $$ u1)
                     (Ap a Set (LamSE x a (unCl b)) t1 u1 p)
                     t2)
              u2

  Rigid h sp    -> Rigid h (SEqSet sp t u)
  Flex h sp     -> Flex h (SEqSet sp t u)
  Unfold h sp a -> Unfold h (SEqSet sp t u) (eq l a t u)
  Irrelevant    -> Irrelevant
  _             -> impossible

eqSet :: Lvl -> Val -> Val -> Val
eqSet l a b = case a // b of

  -- canonical
  ------------------------------------------------------------
  (Set , Set)  -> Eq Set Set Set Top
  (Prop, Prop) -> Eq Set Prop Prop Top
  (El a, El b) -> eqProp a b

  (topA@(Pi _ x i a b), topB@(Pi _ x' i' a' b'))
    | i /= i' -> Eq Set topA topB Bot
    | True    -> Eq Set topA topB $
      SgP NP (eqSet l a a') \p ->
      PiPE (pick x x') a \x -> eqSet l (b $$ x) (b' $$ coe l a a' p x)

  (topA@(Sg _ x a b), topB@(Sg _ x' a' b')) -> Eq Set topA topB $
      SgP NP (eqSet l a a') \p ->
      PiPE (pick x x') a \x -> eqSet l (b $$ x) (b' $$ coe l a a' p x)

  -- non-canonical
  ------------------------------------------------------------
  (Irrelevant, _) -> Irrelevant
  (_, Irrelevant) -> Irrelevant

  (Unfold h sp a, b) -> Unfold h (SEqLhs Set sp b) (eqSet l a b)
  (a, Unfold h sp b) -> Unfold h (SEqRhs Set a sp) (eqSet l a b)

  (Flex h sp, b) -> Flex h (SEqLhs Set sp b)
  (a, Flex h sp) -> Flex h (SEqRhs Set a sp)

  (Rigid h sp, b) -> Rigid h (SEqLhs Set sp b)
  (a, Rigid h sp) -> Rigid h (SEqRhs Set a sp)

  -- canonical mismatch
  ------------------------------------------------------------
  (a, b) -> Eq Set a b Bot

eqProp :: Val -> Val -> Val
eqProp a b = Eq Prop a b (andP (funP a b) (funP b a))

--------------------------------------------------------------------------------

spine :: Lvl -> Val -> Spine -> Val
spine l v sp =
  let go = spine l v; {-# inline go #-}
  in case sp of
    SId               -> v
    SApp t u i        -> app (go t) u i
    SProj1 t          -> proj1 (go t)
    SProj2 t          -> proj2 (go t)
    SProjField t x n  -> projField (go t) x n
    SCoeSrc a b p t   -> coe l (go a) b p t
    SCoeTgt a b p t   -> coe l a (go b) p t
    SCoeTrans a b p t -> coeTrans l a b p (go t)
    SEqSet a t u      -> eq l (go a) t u
    SEqLhs a t u      -> eq l a (go t) u
    SEqRhs a t u      -> eq l a t (go u)

maskEnv :: Env -> S.Locals -> Spine
maskEnv e ls = case e // ls of
  (ENil,     S.LEmpty          ) -> SId
  (EDef e _, S.LDefine ls _ _ _) -> maskEnv e ls
  (EDef e v, S.LBind ls x _    ) -> SApp (maskEnv e ls) v Expl
  _                              -> impossible

insertedMeta :: Lvl -> Env -> MetaVar -> S.Locals -> Val
insertedMeta l e x ls = runIO do
  let sp = maskEnv e ls
  readMeta x >>= \case
    MEUnsolved{}   -> pure (Flex (FHMeta x) sp)
    MESolved _ v _ -> pure (Unfold (UHSolvedMeta x) sp (spine l v sp))

eqCl, coeCl, symCl, apCl, transCl :: Lvl -> Val
eqCl  l   = LamSI NA Set \a -> LamSE NX a \x -> LamSE NY a \y -> eq l a x y
coeCl l   = LamSI NA Set \a -> LamSI NB Set \b -> LamSE NP (El (eqSet l a b)) \p -> LamSE NX a \x ->
            coe l a b p x
symCl l   = LamPI NA Set \a -> LamPI NY a \x -> LamPI NY a \y -> LamPE NP (El (eq l a x y)) \p -> Sym a x y p
apCl  l   = LamPI NA Set \a -> LamPI NB Set \b -> LamPE NF (funS a b) \f -> LamPI NX a \x -> LamPI NY a \y ->
            LamPE NP(eq l a x y) \p -> Ap a b f x y p
transCl l = LamPI NA Set \a -> LamPI NX a \x -> LamPI NY a \y -> LamPI NZ a \z -> LamPE NP (eq l a x y) \p ->
            LamPE NQ (eq l a y z) \q -> Trans a x y z p q

elCl, reflCl, exfalsoCl :: Val
elCl      = LamSE NA Prop El
reflCl    = LamPI NA Set \a -> LamPI NX a \x -> Refl a x
exfalsoCl = LamSI NA Set \a -> LamSE NP (El Bot) \p -> Exfalso a p


eval :: Lvl -> Env -> S.Tm -> Val
eval l e t =

  let go t     = eval l e t;                   {-# inline go #-}
      goBind t = Cl \u -> eval l (EDef e u) t; {-# inline goBind #-}

  in case t of
    S.LocalVar x        -> localVar e x
    S.TopDef v x        -> Unfold (UHTopDef x) SId (coerce v)
    S.Lam hl x i a t    -> Lam hl x i (go a) (goBind t)
    S.App t u i         -> app (go t) (go u) i
    S.Pair hl t u       -> Pair hl (go t) (go u)
    S.ProjField t x n   -> projField (go t) x n
    S.Proj1 t           -> proj1 (go t)
    S.Proj2 t           -> proj2 (go t)
    S.Pi hl x i a b     -> Pi hl x i (go a) (goBind b)
    S.Sg hl x a b       -> Sg hl x (go a) (goBind b)
    S.Postulate x       -> Rigid (RHPostulate x) SId
    S.InsertedMeta x ls -> insertedMeta l e x ls
    S.Meta x            -> meta x
    S.Let x a t u       -> eval l (EDef e (eval l e t)) u
    S.Set               -> Set
    S.Prop              -> Prop
    S.El                -> elCl
    S.Top               -> Top
    S.Tt                -> Tt
    S.Bot               -> Bot
    S.Eq                -> eqCl l
    S.Coe               -> coeCl l
    S.Refl              -> reflCl
    S.Sym               -> symCl l
    S.Trans             -> transCl l
    S.Ap                -> apCl l
    S.Exfalso           -> exfalsoCl
    S.Irrelevant        -> Irrelevant

-- Forcing
--------------------------------------------------------------------------------

-- Forcing
--------------------------------------------------------------------------------

unblock :: MetaVar -> a -> (Val -> IO a) -> IO a
unblock x def k = readMeta x >>= \case
  MEUnsolved{}   -> pure def
  MESolved _ v _ -> k v
{-# inline unblock #-}

-- | Eliminate newly solved VFlex-es from the head.
force :: Lvl -> Val -> IO Val
force l = \case
  hsp@(Flex h sp) -> force' l hsp h sp
  v               -> pure v
{-# inline force #-}

force' :: Lvl -> Val -> FlexHead -> Spine -> IO Val
force' l hsp h sp = case h of
  FHMeta x            -> unblock x hsp \v -> force l $! spine l v sp
  FHCoeRefl x a b p t -> unblock x hsp \_ -> force l $! coeRefl l a b p t
{-# noinline force' #-}

-- | Force + eliminate all unfoldings from the head.
forceAll :: Val -> IO Val
forceAll = \case
  hsp@(Flex h sp) -> uf
  Unfold _ _ v    -> uf
  t               -> pure t
{-# inline forceAll #-}

-- forceAll :: MetaCxt -> Val -> U.IO Val
-- forceAll ms = \case
--   xsp@(VFlex x sp)-> forceAllFlex ms x sp xsp
--   VUnfold _ sp v  -> forceAll' ms v
--   t               -> U.pure t
-- {-# inline forceAll #-}

-- forceAll' :: MetaCxt -> Val -> U.IO Val
-- forceAll' ms = \case
--   xsp@(VFlex x sp) -> forceAllFlex ms x sp xsp
--   VUnfold _ sp v   -> forceAll' ms v
--   t                -> U.pure t

-- forceAllFlex :: MetaCxt -> MetaVar -> Spine -> Val -> U.IO Val
-- forceAllFlex ms x sp ~xsp =
--   MC.read ms x U.>>= \case
--     Unsolved _     -> U.pure xsp
--     Solved _ _ _ v -> forceAll' ms $! appSp ms v sp
-- {-# noinline forceAllFlex #-}

-- -- | Force + eliminate all top def unfolding from the head.
-- forceMetas :: MetaCxt -> Val -> U.IO Val
-- forceMetas ms = \case
--   xsp@(VFlex x sp)        -> forceMetasFlex ms x sp xsp
--   VUnfold UHSolved{} sp v -> forceMetas' ms v
--   t                       -> U.pure t
-- {-# inline forceMetas #-}

-- forceMetas' :: MetaCxt -> Val -> U.IO Val
-- forceMetas' ms = \case
--   xsp@(VFlex x sp)       -> forceMetasFlex ms x sp xsp
--   VUnfold UHSolved{} _ v -> forceMetas' ms v
--   t                      -> U.pure t

-- forceMetasFlex :: MetaCxt -> MetaVar -> Spine -> Val -> U.IO Val
-- forceMetasFlex ms x sp ~xsp =
--   MC.read ms x U.>>= \case
--     Unsolved _     -> U.pure xsp
--     Solved _ _ _ v -> forceMetas' ms $! appSp ms v sp
-- {-# noinline forceMetasFlex #-}


-- Conversion
--------------------------------------------------------------------------------

data ConvRes = Same | Diff | BlockOn MetaVar
  deriving Show
instance Exception ConvRes

data ConvState = CSRigid | CSFlex | CSFull | CSIrrelevant
  deriving (Eq, Show)

conv :: Lvl -> Val -> Val -> ConvRes
conv l t u = runIO ((Same <$ convIO l t u) `catch` pure)

convIO :: Lvl -> Val -> Val -> IO ()
convIO l t u = uf
