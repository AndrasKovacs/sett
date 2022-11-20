
module Evaluation (
    app, appE, appI, proj1, proj2, gproj1, gproj2, projField, unpack, gunpack
  , eval, quote, eval0, quote0, nf, nf0, spine, spine0, spineIn, coe, eq
  , force, forceAll, forceMetas, eqSet, forceSet, unblock
  , projFieldName, setRelevance, Relevance(..), appTy, proj1Ty, proj2Ty, unpackTy
  , evalIn, forceAllIn, closeVal, quoteIn, quoteWithOpt, appIn, quote0WithOpt
  , quoteNf, quoteSpWithOpt, localVar, eqProp, quoteInWithOpt, maskEnv'
  , pattern Exfalso
  , pattern Coe
  , pattern Refl
  , pattern Sym
  , pattern Ap
  , pattern Trans
  ) where

import Control.Exception
import IO

import Common
import ElabState
import Values
import qualified Syntax as S

--------------------------------------------------------------------------------
{-
NOTE
 - We immediately block on metas. E.g. we don't try to conversion check
   flex-flex. The reason is the following. Assume flex-flex conversion. If
   we block on a meta when we have different flex-flex heads, that meta is not a
   rigid blocker, because the other meta could be solved to it, which makes the
   sides convertible.

 - TODO (alternative design): we block on a disjunction of multiple metas. In
   this case we can just grab all offending metas, and during forcing retry
   computation if either is solved.


TODO
 - use approximate unfoldings in conversion


 - unfolding preservation in semantic eq/coe
   - right now eq preserves unfoldings except when we return a flex case
   TODO: store G instead of Val in FlexEq
         use G-s in semantic coe as well, store G-s in FHCoe

-}

--------------------------------------------------------------------------------

-- | Bump the `Lvl` and get a fresh variable.
newVar :: Ty -> (LvlArg => Val -> a) -> LvlArg => a
newVar a cont =
  let v = Var ?lvl a in
  let ?lvl = ?lvl + 1 in
  seq ?lvl (cont v)
{-# inline newVar #-}

-- pattern synonyms
--------------------------------------------------------------------------------

pattern Exfalso a t <- Rigid (RHExfalso a t) SId _ where
  Exfalso a t = Rigid (RHExfalso a t) SId a

pattern Coe a b p t <- Rigid (RHCoe a b p t) SId _ where
  Coe a b p t = Rigid (RHCoe a b p t) SId b

pattern Refl :: LvlArg => Val -> Val -> Val
pattern Refl a t <- Rigid (RHRefl a t) SId _ where
  Refl a t = Rigid (RHRefl a t) SId (El (eq a t t))

pattern Sym :: LvlArg => Val -> Val -> Val -> Val -> Val
pattern Sym a x y p <- Rigid (RHSym a x y p) SId _ where
  Sym a x y p = Rigid (RHSym a x y p) SId (El (eq a y x))

pattern Ap :: LvlArg => Val -> Val -> Val -> Val -> Val -> Val -> Val
pattern Ap a b f x y p <- Rigid (RHAp a b f x y p) SId _ where
  Ap a b f x y p = Rigid (RHAp a b f x y p) SId (El (eq b (appE f x) (appE f y)))

pattern Trans :: LvlArg => Val -> Val -> Val -> Val -> Val -> Val -> Val
pattern Trans a x y z p q <- Rigid (RHTrans a x y z p q) SId _ where
  Trans a x y z p q = Rigid (RHTrans a x y z p q) SId (El (eq a x z))

--------------------------------------------------------------------------------

localVar :: EnvArg => Ix -> Val
localVar topx = go ?env topx where
  go (EDef _ v) 0 = v
  go (EDef e _) x = go e (x - 1)
  go _          _ = impossible

meta :: MetaVar -> Val
meta x = runIO $ readMeta x >>= \case
  MEUnsolved a  _        -> pure (Flex (FHMeta x) SId a)
  MESolved _ _ v a True  -> pure v
  MESolved _ _ v a False -> pure (Unfold (UHSolvedMeta x) SId v a)

appTy :: LvlArg => Ty -> Val -> Ty
appTy a t = runIO $ forceSet a >>= \case
  Pi _ _ _ b      -> pure $! (b $$ t)
  El (Pi _ _ _ b) -> pure $! El (b $$ t)
  _               -> impossible

app :: LvlArg => Val -> Val -> Icit -> Val
app t u i = case t of
  Lam x i a t      -> t $$ u
  Rigid h sp a     -> Rigid h (SApp sp u i) (appTy a u)
  Flex h sp a      -> Flex h (SApp sp u i) (appTy a u)
  Unfold h sp t a  -> Unfold h (SApp sp u i) (app t u i) (appTy a u)
  Magic m          -> Magic m
  v                -> impossible

lazyApp :: LvlArg => Val -> Val -> Icit -> Val
lazyApp t ~u i = case t of
  Lam x i a t      -> t $$~ u
  Rigid h sp a     -> Rigid h (SApp sp u i) (appTy a u)
  Flex h sp a      -> Flex h (SApp sp u i) (appTy a u)
  Unfold h sp t a  -> Unfold h (SApp sp u i) (app t u i) (appTy a u)
  Magic m          -> Magic m
  _                -> impossible

appIn :: Lvl -> Val -> Val -> Icit -> Val
appIn l = let ?lvl = l in app

appE :: LvlArg => Val -> Val -> Val
appE t u = app t u Expl

appI :: LvlArg => Val -> Val -> Val
appI t u = app t u Impl

proj1Ty :: LvlArg => Ty -> Ty
proj1Ty a = runIO $ forceSet a >>= \case
  Sg _ _ a _      -> pure a
  El (Sg _ _ a _) -> pure (El a)
  a               -> impossible

proj1 :: LvlArg => Val -> Val
proj1 t = case t of
  Pair t u        -> t
  Rigid h sp a    -> Rigid  h (SProj1 sp) (proj1Ty a)
  Flex h sp a     -> Flex   h (SProj1 sp) (proj1Ty a)
  Unfold h sp t a -> Unfold h (SProj1 sp) (proj1 t) (proj1Ty a)
  Magic m         -> Magic m
  _               -> impossible

gproj1 :: LvlArg => G -> G
gproj1 (G t ft) = G (proj1 t) (proj1 ft)
{-# inline gproj1 #-}

gproj2 :: LvlArg => G -> G
gproj2 (G t ft) = G (proj2 t) (proj2 ft)
{-# inline gproj2 #-}

-- | Args: type which is a sigma, value for the first projection, returns type of the
--   second projection.
proj2Ty :: LvlArg => Ty -> Val -> Ty
proj2Ty a proj1 = runIO $ forceSet a >>= \case
  Sg _ _ _ b      -> pure $! (b $$ proj1)
  El (Sg _ _ _ b) -> pure $! El (b $$ proj1)
  _               -> impossible

proj2 :: LvlArg => Val -> Val
proj2 topt = case topt of
  Pair t u        -> u
  Rigid h sp a    -> Rigid  h (SProj2 sp) (proj2Ty a (proj1 topt))
  Flex h sp a     -> Flex   h (SProj2 sp) (proj2Ty a (proj1 topt))
  Unfold h sp t a -> Unfold h (SProj2 sp) (proj2 t) (proj2Ty a (proj1 topt))
  Magic m         -> Magic m
  _               -> impossible

-- TODO: ghc 9.4 will unbox the result
projFieldInfo :: LvlArg => Val -> Ty -> Int -> IO (Name, Ty)
projFieldInfo val topa topn = do

  let go :: Ty -> Int -> IO (Name, Ty)
      go a ix = do
        a <- forceSet a
        if ix == topn then
          case a of
            Sg _ x a b      -> pure (x, a)
            El (Sg _ x a b) -> pure (x, El a)
            _               -> impossible
        else
          case a of
            Sg _ _ a b      -> go (b $$ projField val ix) (ix + 1)
            El (Sg _ _ a b) -> go (El (b $$ projField val ix)) (ix + 1)
            _               -> impossible

  go topa 0

projFieldName :: LvlArg => Val -> Ty -> Int -> Name
projFieldName val a n = runIO (fst <$!> projFieldInfo val a n)

projFieldTy :: LvlArg => Val -> Ty -> Int -> Ty
projFieldTy val a n = runIO (snd <$!> projFieldInfo val a n)

projField :: LvlArg => Val -> Int -> Val
projField topt n = case topt of
  Pair t u      -> case n of 0 -> t
                             n -> projField u (n - 1)
  Rigid h sp a    -> Rigid  h (SProjField sp topt a n) (projFieldTy topt a n)
  Flex h sp a     -> Flex   h (SProjField sp topt a n) (projFieldTy topt a n)
  Unfold h sp t a -> Unfold h (SProjField sp topt a n) (projField t n) (projFieldTy topt a n)
  Magic m         -> Magic m
  _               -> impossible

-- Newtype
--------------------------------------------------------------------------------

newtypeSym :: Val
newtypeSym =
  LamI na Set \a ->
  LamE nb (a ==> Set) \b ->
  LamE nx a \x ->
  Newtype a b x (b `appE` x)

unpackTy :: LvlArg => Ty -> Ty
unpackTy a = runIO $ forceSet a >>= \case
  Newtype _ _ _ bx -> pure $! bx
  _                -> impossible

unpack :: LvlArg => Val -> Val
unpack = \case
  Pack t          -> t
  Rigid h sp a    -> Rigid  h (SUnpack sp) (unpackTy a)
  Flex h sp a     -> Flex   h (SUnpack sp) (unpackTy a)
  Unfold h sp t a -> Unfold h (SUnpack sp) (unpack t) (unpackTy a)
  Magic m         -> Magic m
  _               -> impossible

-- pack :: Val -> Val -> Val
-- pack ~a = \case
--   Rigid  h (SUnpack sp) _   -> Rigid h sp a
--   Flex   h (SUnpack sp) _   -> Flex h sp a
--   Unfold h (SUnpack sp) t _ -> Unfold h sp (pack a t) a
--   Magic m                   -> Magic m
--   v                         -> Pack a v

gunpack :: LvlArg => G -> G
gunpack (G t ft) = G (unpack t) (unpack ft)
{-# inline gunpack #-}

-- Coercion
--------------------------------------------------------------------------------

coe :: LvlArg => Val -> Val -> Val -> Val -> Val
coe a b p t = case (a, b) of

  -- canonical
  ------------------------------------------------------------

  (El _, El _) -> proj1 p `appE` t

  (topA@(Pi x i a b), topB@(Pi x' i' a' b'))
    | i /= i' -> Coe topA topB p t
    | True    ->
        let p1   = proj1 p
            p2   = proj2 p
            name = pick x x'
        in Lam name i a' $ Cl \x' ->
            let x = coe a' a (Sym Set a a' p1) x'
            in coe (b $$ x) (b' $$ x') (p2 `appE` x) (app t x i)

  (Sg _ x a b, Sg _ x' a' b') ->
    let t1  = proj1 t
        t2  = proj2 t
        t1' = coe a a' (proj1 p) t1
        t2' = coe (b $$ t1) (b' $$ t1') (proj2 p `appE` t1) t2
    in Pair t1' t2'

  (Set,  Set )   -> t
  (Prop, Prop)   -> t

  (topa@(Newtype a b x bx), topb@(Newtype a' b' x' b'x')) ->
    let aeq    = proj1 p
        p2     = proj2 p
        beq    = proj1 p2
        xeq    = proj2 p2
        coex   = coe a a' aeq x
        b'coex = appE b' coex in
    Pack $!
      coe bx b'x'
          (Trans Set bx b'coex b'x'
             (appE beq x)
             (Ap a' Set b' coex x' xeq))
          (unpack t)

  -- aeq : a = a'
  -- beq : ∀ x. b x = b' (coe aeq x)
  -- xeq : coe aeq x = x'
  -- goal : b x = b' x'

  -- beq x     : b x = b' (coe aeq x)
  -- ap b' xeq : b' (coe aeq x) = b' x'
  -- trans (beq x) (ap b' xeq) : b x = b' x'

  -- non-canonical
  ------------------------------------------------------------

  (Magic m, _) -> Magic m
  (_, Magic m) -> Magic m

  (ua@(Unfold h sp a _), b) -> Unfold (UHCoe ua b p t) SId (coe a b p t) b
  (a, ub@(Unfold h sp b _)) -> Unfold (UHCoe a ub p t) SId (coe a b p t) b

  (a@(Flex h sp _), b) -> Flex (FHCoe (flexHeadMeta h) a b p t) SId b
  (a, b@(Flex h sp _)) -> Flex (FHCoe (flexHeadMeta h) a b p t) SId b

  (a@Rigid{}, b) -> coeTrans a b p t
  (a, b@Rigid{}) -> coeTrans a b p t

  -- Canonical mismatch
  -- NOTE: Canonical mismatch can't compute to Exfalso!
  --       That + coe-trans causes conversion to be undecidable.

  (a, b) -> Coe a b p t

coeTrans :: LvlArg => Val -> Val -> Val -> Val -> Val
coeTrans a b p t = case t of
  Flex (FHCoe x a' _ p' t') SId _ -> coe a' b (Trans Set a' a b p' p) t'
  Rigid (RHCoe a' _ p' t') SId _  -> coe a' b (Trans Set a' a b p' p) t'
  t@(Unfold h sp ft _)            -> Unfold (UHCoe a b p t) SId (coeTrans a b p ft) b
  Magic m                         -> Magic m
  t                               -> coeRefl a b p t

coeRefl :: LvlArg => Val -> Val -> Val -> Val -> Val
coeRefl a b p t = case runConv (conv a b) of
  Same      -> t
  Diff      -> Rigid (RHCoe a b p t) SId b
  BlockOn x -> Flex (FHCoe x a b p t) SId b
  CRMagic m -> Magic m


-- Equality type
--------------------------------------------------------------------------------

geq :: LvlArg => G -> G -> G -> Val
geq (G topa ftopa) (G t ft) (G u fu) = case ftopa of
  Set  -> geqSet (G t ft) (G u fu)
  Prop -> eqProp t u
  El a -> markEq topa t u Top

  Pi x i a b -> markEq topa t u $!
    PiE x a \x -> eq (b $$ x) (app t x i) (app u x i)

  Sg _ x a b ->
    let t1  = proj1 t
        u1  = proj1 u
        t2  = proj2 t
        u2  = proj2 u
        bu1 = b $$ u1
        bt1 = b $$ t1

    in markEq topa t u $!
       SgP np (eq a t1 u1) \p ->
          eq bu1
            (coe bt1 bu1
                 (Ap a Set (LamE x a (unCl b)) t1 u1 p)
                 t2)
              u2

  Newtype a b x bx -> geq (gjoin bx) (gunpack (G t ft)) (gunpack (G u fu))

  Rigid{}          -> RigidEq topa t u
                   -- NOTE: FlexEq must have at least 1 Flex component
  Flex h _ _       -> FlexEq (flexHeadMeta h) ftopa t u
  Unfold h sp fa _ -> UnfoldEq topa t u (geq (G topa fa) (G t ft) (G u fu))
  Magic m          -> Magic m
  a                -> impossible

geqSet :: LvlArg => G -> G -> Val
geqSet (G topa ftopa) (G topb ftopb) = case (ftopa, ftopb) of

  -- canonical
  ------------------------------------------------------------
  (Set , Set)  -> markEq Set  Set  Set  Top
  (Prop, Prop) -> markEq Set  Prop Prop Top
  (El a, El b) -> eqProp a b

  (Pi x i a b, Pi x' i' a' b')
    | i /= i' -> markEq Set topa topb Bot
    | True    ->
      let name = pick x x'
      in markEq Set topa topb $!
        SgP np (eqSet a a') \p ->
        PiE name a \x -> eqSet (b $$ x) (b' $$~ coe a a' p x)

  (Sg _ x a b, Sg _ x' a' b') ->
      let name = pick x x'
      in markEq Set topa topb $!
        SgP np (eqSet a a') \p ->
        PiE name a \x -> eqSet (b $$ x) (b' $$~ coe a a' p x)

  (Newtype a b x bx, Newtype a' b' x' _) ->
    markEq Set topa topb $!
      SgP np (eqSet a a') \p ->
      SgP nq (PiE nx a \x -> eqSet bx (lazyApp b' (coe a a' p x) Expl)) \q ->
      eq a' (coe a a' p x) x'

  -- non-canonical
  ------------------------------------------------------------
  (Magic m, _) -> Magic m
  (_, Magic m) -> Magic m

  (Rigid{}, _)   -> RigidEq Set topa topb
  (_, Rigid{})   -> RigidEq Set topa topb

  -- NOTE: FlexEq must have at least 1 flex component.
  (Flex h _ _, b) -> FlexEq (flexHeadMeta h) Set ftopa topb
  (a, Flex h _ _) -> FlexEq (flexHeadMeta h) Set topa ftopb

  (Unfold _ _ fa _, _) -> UnfoldEq Set topa topb (geqSet (G topa fa) (G topb ftopb))
  (_, Unfold _ _ fb _) -> UnfoldEq Set topa topb (geqSet (G topa ftopa) (G topb fb))

  -- canonical mismatch
  ------------------------------------------------------------
  (_, _) -> markEq Set topa topb Bot

eqProp :: Val -> Val -> Val
eqProp a b = markEq Prop a b $! andP (El a ==> b) (El b ==> a)
{-# inline eqProp #-}

eq :: LvlArg => Val -> Val -> Val -> Val
eq a t u = geq (gjoin a) (gjoin t) (gjoin u)
{-# inline eq #-}

eqSet :: LvlArg => Val -> Val -> Val
eqSet a b = geqSet (gjoin a) (gjoin b)
{-# inline eqSet #-}


--------------------------------------------------------------------------------

spine :: LvlArg => Val -> Spine -> Val
spine v sp =
  let go = spine v; {-# inline go #-}
  in case sp of
    SId                -> v
    SApp t u i         -> app (go t) u i
    SProj1 t           -> proj1 (go t)
    SProj2 t           -> proj2 (go t)
    SProjField t _ _ n -> projField (go t) n
    SUnpack t          -> unpack (go t)

spineIn :: Lvl -> Val -> Spine -> Val
spineIn l v sp = let ?lvl = l in spine v sp

spine0 :: Val -> Spine -> Val
spine0 = spineIn 0

-- Compute the spine which applies a meta to all bound vars,
-- return the resulting type of the neutral application as well.
maskEnv :: LvlArg => Env -> S.Locals -> Ty -> (Spine, Ty)
maskEnv e ls ty = case (e, ls) of
  (ENil,     S.LEmpty          ) -> (SId, ty)
  (EDef e _, S.LDefine ls _ _ _) -> maskEnv e ls ty
  (EDef e v, S.LBind ls _ _    ) -> case maskEnv e ls ty of
                                      (sp, ty) -> (SApp sp v Expl, appTy ty v)
  _                              -> impossible

maskEnv' :: LvlArg => Env -> S.Locals -> Ty -> Spine
maskEnv' e ls ty = case (e, ls) of
  (ENil,     S.LEmpty          ) -> SId
  (EDef e _, S.LDefine ls _ _ _) -> maskEnv' e ls ty
  (EDef e v, S.LBind ls _ _    ) -> case maskEnv' e ls ty of
                                      sp -> SApp sp v Expl
  _                              -> impossible

insertedMeta :: LvlArg => EnvArg => MetaVar -> S.Locals -> Val
insertedMeta x locals = runIO do
  readMeta x >>= \case
    MEUnsolved a _ -> do
      let (sp, ty) = maskEnv ?env locals a
      pure (Flex (FHMeta x) sp ty)
    MESolved _ _ v a True -> do
      pure $! spine v $! maskEnv' ?env locals a
    MESolved _ _ v a False -> do
      let (sp, ty) = maskEnv ?env locals a
      pure (Unfold (UHSolvedMeta x) sp (spine v sp) ty)


eqSym, coeSym, symSym, apSym, transSym, reflSym, exfalsoSym :: Val
eqSym      = LamI na Set \a -> LamE nx a \x -> LamE ny a \y -> eq a x y

coeSym     = LamI na Set \a -> LamI nb Set \b -> LamE np (El (eqSet a b)) \p -> LamE nx a \x ->
             coe a b p x

symSym     = LamI na Set \a -> LamI ny a \x -> LamI ny a \y -> LamE np (El (eq a x y)) \p ->
             Sym a x y p

apSym      = LamI na Set \a -> LamI nb Set \b -> LamE nf (a ==> b) \f -> LamI nx a \x ->
             LamI ny a \y -> LamE np (El (eq a x y)) \p ->
             Ap a b f x y p

transSym   = LamI na Set \a -> LamI nx a \x -> LamI ny a \y -> LamI nz a \z ->
             LamE np (El (eq a x y)) \p -> LamE nq (El (eq a y z)) \q ->
             Trans a x y z p q

reflSym    = LamI na Set \a -> LamI nx a \x -> Refl a x
exfalsoSym = LamI na Set \a -> LamE np (El Bot) \p -> Exfalso a p
elSym      = LamE na Prop El

eval :: LvlArg => EnvArg => S.Tm -> Val
eval t =
  let go t     = eval t; {-# inline go #-}
      goBind t = Cl \u -> let ?env = EDef ?env u in eval t; {-# inline goBind #-}

  in case t of
    S.LocalVar x        -> localVar x
    S.TopDef x v a      -> Unfold (UHTopDef x v a) SId v a
    S.Lam x i a t       -> Lam x i (go a) (goBind t)
    S.App t u i         -> app (go t) (go u) i
    S.Pair t u          -> Pair (go t) (go u)
    S.ProjField t _ n   -> projField (go t) n
    S.Proj1 t           -> proj1 (go t)
    S.Proj2 t           -> proj2 (go t)
    S.Pi x i a b        -> Pi x i (go a) (goBind b)
    S.Sg sp x a b       -> Sg sp x (go a) (goBind b)
    S.Postulate x a     -> Rigid (RHPostulate x a) SId a
    S.InsertedMeta m ls -> insertedMeta m ls
    S.Meta x            -> meta x
    S.Let x a t u       -> let ?env = EDef ?env (eval t) in eval u
    S.NewtypeSym        -> newtypeSym
    S.Pack t            -> Pack (go t)
    S.Unpack t          -> unpack (go t)
    S.Set               -> Set
    S.Prop              -> Prop
    S.Top               -> Top
    S.Tt                -> Tt
    S.Bot               -> Bot
    S.EqSym             -> eqSym
    S.CoeSym            -> coeSym
    S.ReflSym           -> reflSym
    S.SymSym            -> symSym
    S.TransSym          -> transSym
    S.ApSym             -> apSym
    S.ExfalsoSym        -> exfalsoSym
    S.ElSym             -> elSym
    S.Magic m           -> Magic m

evalIn :: Lvl -> Env -> S.Tm -> Val
evalIn l e t = let ?lvl = l; ?env = e in eval t


-- Forcing
--------------------------------------------------------------------------------

unblock :: MetaVar -> a -> (Val -> Ty -> Bool -> IO a) -> IO a
unblock x deflt k = readMeta x >>= \case
  MEUnsolved{}         -> pure deflt
  MESolved _ _ v a inl -> k v a inl
{-# inline unblock #-}

------------------------------------------------------------

-- | Eliminate solved flex heads & inlinable solved metas
force :: LvlArg => Val -> IO Val
force v = case v of
  topv@(Flex h sp _)     -> forceFlex topv h sp
  topv@(FlexEq x a t u)  -> forceFlexEq topv x a t u
  v                      -> pure v
{-# inline force #-}

forceFlexEq :: LvlArg => Val -> MetaVar -> Val -> Val -> Val -> IO Val
forceFlexEq topv x a t u = unblock x topv \_ _ _ -> do
  a <- force a
  t <- force t
  u <- force u
  force $! eq a t u
{-# noinline forceFlexEq #-}

forceFlex :: LvlArg => Val -> FlexHead -> Spine -> IO Val
forceFlex hsp h sp = case h of
  FHMeta x -> unblock x hsp \v a -> \case
      True  -> force $! spine v sp
      False -> pure $ Unfold (UHSolvedMeta x) sp (spine v sp) a
  FHCoe x a b p t -> unblock x hsp \_ _ _ -> do
    a <- force a
    b <- force b
    t <- force t
    force $! spine (coe a b p t) sp
{-# noinline forceFlex #-}

------------------------------------------------------------

-- TODO: this loses unfoldings in the flex coe cases!!!


-- | Eliminate all unfoldings from the head.
forceAll :: LvlArg => Val -> IO Val
forceAll v = case v of
  topv@(Flex h sp _)    -> forceAllFlex topv h sp
  topv@(FlexEq x a t u) -> forceAllFlexEq topv x a t u
  Unfold _ _ v _        -> forceAll' v
  TraceEq _ _ _ v       -> forceAll' v
  UnfoldEq _ _ _ v      -> forceAll' v
  t                     -> pure t
{-# inline forceAll #-}

forceAllIn :: Lvl -> Val -> IO Val
forceAllIn l t = let ?lvl = l in forceAll t
{-# inline forceAllIn #-}

forceAllFlex :: LvlArg => Val -> FlexHead -> Spine -> IO Val
forceAllFlex topv h sp = case h of
  FHMeta x -> unblock x topv \v _ _ ->
    forceAll' $! spine v sp
  FHCoe x a b p t -> unblock x topv \_ _ _ -> do
    a <- forceSet' a
    b <- forceSet' b
    t <- forceAll' t
    forceAll' $! coe a b p t      -- loses unfolding!
{-# noinline forceAllFlex #-}

forceAllFlexEq :: LvlArg => Val -> MetaVar -> Val -> Val -> Val -> IO Val
forceAllFlexEq topv x a t u = unblock x topv \_ _ _ -> do
  fa <- forceSet' a
  ft <- forceAll' t
  fu <- forceAll' u
  forceAll' $! geq (G a fa) (G t ft) (G u fu)
{-# noinline forceAllFlexEq #-}

forceAll' :: LvlArg => Val -> IO Val
forceAll' v = case v of
  topv@(Flex h sp _)    -> forceAllFlex topv h sp
  topv@(FlexEq x a t u) -> forceAllFlexEq topv x a t u
  Unfold _ _ v _        -> forceAll' v
  TraceEq _ _ _ v       -> forceAll' v
  UnfoldEq _ _ _ v      -> forceAll' v
  t                     -> pure t

------------------------------------------------------------

-- | Eliminate all unfoldings from the head of a type. NOTE: we force *under*
--   `El` as well, because in many cases we want to match on the `El` of some
--   canonical `Prop`.
forceSet :: LvlArg => Val -> IO Val
forceSet v = case v of
  topv@(Flex h sp _)    -> forceSetFlex topv h sp
  Unfold _ _ v _        -> forceSet' v
  El a                  -> El <$!> forceAll' a
  t                     -> pure t
{-# inline forceSet #-}

forceSetFlex :: LvlArg => Val -> FlexHead -> Spine -> IO Val
forceSetFlex topv h sp = case h of
  FHMeta x -> unblock x topv \v _ _ ->
    forceSet' $! spine v sp
  FHCoe x a b p t -> unblock x topv \_ _ _ -> do
    a <- forceSet' a
    b <- forceSet' b
    t <- forceAll' t
    forceSet' $! spine (coe a b p t) sp -- loses unfolding!
{-# noinline forceSetFlex #-}

forceSet' :: LvlArg => Val -> IO Val
forceSet' v = case v of
  topv@(Flex h sp _) -> forceSetFlex topv h sp
  Unfold _ _ v _     -> forceSet' v
  El a               -> El <$!> forceAll' a
  t                  -> pure t

------------------------------------------------------------

-- | Only eliminate meta unfoldings from the head.
forceMetas :: LvlArg => Val -> IO Val
forceMetas v = case v of
  topv@(Flex h sp _)          -> forceMetasFlex topv h sp
  topv@(FlexEq x a t u)       -> forceMetasFlexEq topv x a t u
  Unfold UHSolvedMeta{} _ v _ -> forceMetas' v
  t                           -> pure t
{-# inline forceMetas #-}

forceMetasFlexEq :: LvlArg => Val -> MetaVar -> Val -> Val -> Val -> IO Val
forceMetasFlexEq topv x a t u = unblock x topv \_ _ _ -> do
  a <- forceMetas' a
  t <- forceMetas' t
  u <- forceMetas' u
  forceMetas' $! eq a t u
{-# noinline forceMetasFlexEq #-}

forceMetasFlex :: LvlArg => Val -> FlexHead -> Spine -> IO Val
forceMetasFlex hsp h sp = case h of
  FHMeta x -> unblock x hsp \v _ _ ->
    forceMetas' $! spine v sp
  FHCoe x a b p t -> unblock x hsp \_ _ _ -> do
    a <- forceMetas' a
    b <- forceMetas' b
    t <- forceMetas' t
    forceMetas' $! spine (coe a b p t) sp
{-# noinline forceMetasFlex #-}

forceMetas' :: LvlArg => Val -> IO Val
forceMetas' v = case v of
  topv@(Flex h sp _)          -> forceMetasFlex topv h sp
  topv@(FlexEq x a t u)       -> forceMetasFlexEq topv x a t u
  Unfold UHSolvedMeta{} _ v _ -> forceMetas' v
  t                           -> pure t

-- Relevance
--------------------------------------------------------------------------------

data Relevance = RRel | RIrr | RBlockOn MetaVar | RMagic Magic

mergeMagic :: Magic -> Magic -> Magic
mergeMagic m1 m2 = case (m1, m2) of
  (Undefined , m         ) -> m
  (m         , Undefined ) -> m
  (Nonlinear , _         ) -> Nonlinear
  (_         , Nonlinear ) -> Nonlinear
  (m         , _         ) -> m
{-# inline mergeMagic #-}

sgRelevance :: Relevance -> Relevance -> Relevance
sgRelevance p ~q = case (p, q) of
  (RRel       , _          ) -> RRel
  (RBlockOn x , _          ) -> RBlockOn x
  (_          , RRel       ) -> RRel
  (_          , RBlockOn x ) -> RBlockOn x
  (RIrr       , RIrr       ) -> RIrr
  (RMagic m1  , RMagic m2  ) -> RMagic (mergeMagic m1 m2)
  (RMagic m1  , _          ) -> RMagic m1
  (_          , RMagic m2  ) -> RMagic m2
{-# inline sgRelevance #-}

setRelevance :: LvlArg => Ty -> Relevance
setRelevance a = do
  let go         = setRelevance; {-# inline go #-}
      goBind a b = newVar a \v -> setRelevance (b $$ v); {-# inline goBind #-}
  case runIO (forceSet a) of
    Set              -> RRel
    Prop             -> RRel
    El _             -> RIrr
    Pi _ _ a b       -> goBind a b
    Sg _ _ a b       -> sgRelevance (go a) (goBind a b)
    Rigid{}          -> RRel
    Flex h sp _      -> RBlockOn (flexHeadMeta h)
    Magic m          -> RMagic m
    Newtype _ _ _ bx -> go bx
    _                -> impossible


-- Conversion
--------------------------------------------------------------------------------

data ConvRes = Same | Diff | BlockOn MetaVar | CRMagic Magic
  deriving Show
instance Exception ConvRes

runConv :: IO () -> ConvRes
runConv act = runIO ((Same <$ act) `catch` pure)
{-# inline runConv #-}

convEq :: Eq a => a -> a -> IO ()
convEq x y = when (x /= y) $ throwIO Diff
{-# inline convEq #-}

ensureNProj2 :: Int -> Spine -> IO Spine
ensureNProj2 n sp
  | n == 0 = pure sp
  | n > 0 = case sp of
      SProj2 t -> ensureNProj2 (n-1) t
      _ -> throwIO Diff
  | otherwise = impossible

convSp :: LvlArg => Spine -> Spine -> IO ()
convSp sp sp' = do
  let go   = conv; {-# inline go #-}
      goSp = convSp; {-# inline goSp #-}
  case (sp, sp') of
    (SId                , SId                 ) -> pure ()
    (SApp t u i         , SApp t' u' i'       ) -> goSp t t' >> go u u'
    (SProj1 t           , SProj1 t'           ) -> goSp t t'
    (SProj2 t           , SProj2 t'           ) -> goSp t t'
    (SProjField t _ _ n , SProjField t' _ _ n') -> goSp t t' >> convEq n n'
    (SProjField t _ _ n , SProj1 t'           ) -> do {t' <- ensureNProj2 n t'; convSp t t'}
    (SProj1 t           , SProjField t' _ _ n ) -> do {t <- ensureNProj2 n t; convSp t t'}
    (SUnpack t          , SUnpack t'          ) -> goSp t t'
    _                                           -> throwIO Diff

-- | Magical rigid coe conversion.
convCoeCoe :: LvlArg => Val -> Val -> Val -> Val -> Spine -> Val -> Val -> Val -> Val -> Spine -> IO ()
convCoeCoe a b p t sp a' b' p' t' sp' = do

  -- if spines are empty, then by assumption we know that target types are the same
  case (sp, sp') of (SId, SId) -> pure ()
                    _          -> conv b b'

  conv (coe a a' (Trans Set a b a' p (Sym Set a' b p')) t) t'
  convSp sp sp'

convExfalso :: LvlArg => Ty -> Ty -> Spine -> Spine -> IO ()
convExfalso a a' sp sp' = case (sp, sp') of
  (SId, SId) -> pure ()
  _          -> conv a a' >> convSp sp sp'

-- | Compare rigid-s which are known to be relevant.
convRigidRel :: LvlArg => RigidHead -> Spine -> RigidHead -> Spine -> IO ()
convRigidRel h sp h' sp' = case (h, h') of
  (RHLocalVar x _ _, RHLocalVar x' _ _ ) -> convEq x x' >> convSp sp sp'
  (RHPostulate x _ , RHPostulate x' _  ) -> convEq x x' >> convSp sp sp'
  (RHCoe a b p t   , RHCoe a' b' p' t' ) -> convCoeCoe a b p t sp a' b' p' t' sp'
  (RHExfalso a p   , RHExfalso a' p'   ) -> convExfalso a a' sp sp'
  _                                      -> throwIO Diff

-- TODO: approx unfolding
conv :: LvlArg => Val -> Val -> IO ()
conv t u = do
  let go = conv
      {-# inline go #-}

      goBind a t u = newVar a \v -> conv (t $$ v) (u $$ v)
      {-# inline goBind #-}

  t <- forceAll t
  u <- forceAll u
  case (t, u) of

    -- canonical & rigid match
    ------------------------------------------------------------
    (Pi x i a b, Pi x' i' a' b') -> do
      convEq i i'
      go a a'
      goBind a b b'

    (Sg sp x a b, Sg _ x' a' b') -> do
      go a a'
      goBind (elSP sp a) b b'

    (Newtype a b x _, Newtype a' b' x' _) -> do
      go a a'
      go b b'
      go x x'

    (El a, El a' ) -> go a a'
    (Set , Set   ) -> pure ()
    (Prop, Prop  ) -> pure ()
    (Top , Top   ) -> pure ()
    (Bot , Bot   ) -> pure ()
    (Tt  , Tt    ) -> pure ()

    (Rigid h sp a, Rigid h' sp' _) -> case setRelevance a of
      RIrr       -> pure ()
      RBlockOn x -> throwIO $ BlockOn x
      RRel       -> convRigidRel h sp h' sp'
      RMagic m   -> throwIO $ CRMagic m

    (RigidEq a t u , RigidEq a' t' u') -> go a a' >> go t t' >> go u u'
    (Lam _ _ _ t   , Lam _ _ a t'    ) -> goBind a t t'
    (Pair t u      , Pair t' u'      ) -> go t t' >> go u u'
    (Pack t        , Pack t'         ) -> go t t'

    -- syntax-directed eta
    --------------------------------------------------------------------------------

    (Lam _ i a t , t'           ) -> goBind a t (Cl \u -> app t' u i)
    (t           , Lam _ i a t' ) -> goBind a (Cl \u -> app t u i) t'
    (Pair t u    , t'           ) -> go t (proj1 t') >> go u (proj2 t')
    (t           , Pair t' u'   ) -> go (proj1 t) t' >> go (proj2 t) u'
    (Pack t      , t'           ) -> go t (unpack t')
    (t           , Pack t'      ) -> go (unpack t) t'

    ------------------------------------------------------------

    (Magic m, _) -> throwIO $ CRMagic m
    (_, Magic m) -> throwIO $ CRMagic m

    (Flex h sp a, _) -> case setRelevance a of
      RIrr       -> pure ()
      RMagic m   -> throwIO $ CRMagic m
      RRel       -> throwIO $! BlockOn (flexHeadMeta h)
      RBlockOn{} -> throwIO $! BlockOn (flexHeadMeta h)

    (_, Flex h sp a) -> case setRelevance a of
      RIrr       -> pure ()
      RMagic m   -> throwIO $ CRMagic m
      RRel       -> throwIO $! BlockOn (flexHeadMeta h)
      RBlockOn{} -> throwIO $! BlockOn (flexHeadMeta h)

    (FlexEq x _ _ _, _) -> throwIO $ BlockOn x
    (_, FlexEq x _ _ _) -> throwIO $ BlockOn x

    (Rigid h sp a, _) -> case setRelevance a of
      RIrr       -> pure ()
      RRel       -> throwIO Diff
      RBlockOn x -> throwIO $ BlockOn x
      RMagic m   -> throwIO $ CRMagic m

    (_, Rigid h' sp' a) -> case setRelevance a of
      RIrr       -> pure ()
      RRel       -> throwIO Diff
      RBlockOn x -> throwIO $ BlockOn x
      RMagic m   -> throwIO $ CRMagic m

    -- canonical mismatch is always a failure, because we don't yet
    -- have inductive data in Prop, so mismatch is only possible in Set.
    --------------------------------------------------------------------------------

    (a, b) -> throwIO Diff


-- Quoting
--------------------------------------------------------------------------------

quoteSpWithOpt :: LvlArg => UnfoldOpt -> S.Tm -> Spine -> S.Tm
quoteSpWithOpt opt hd sp = let
  go   = quoteWithOpt opt; {-# inline go #-}
  goSp = quoteSpWithOpt opt hd; {-# inline goSp #-}
  in case sp of
    SId                 -> hd
    SApp t u i          -> S.App (goSp t) (go u) i
    SProj1 t            -> S.Proj1 (goSp t)
    SProj2 t            -> S.Proj2 (goSp t)
    SProjField t tv x n -> S.ProjField (goSp t) (projFieldName tv x n) n
    SUnpack t           -> S.Unpack (goSp t)

quoteWithOpt :: LvlArg => UnfoldOpt -> Val -> S.Tm
quoteWithOpt opt t = let
  go         = quoteWithOpt opt; {-# inline go #-}
  goSp       = quoteSpWithOpt opt; {-# inline goSp #-}
  goBind a t = newVar a \v -> quoteWithOpt opt (t $$ v); {-# inline goBind #-}

  goFlexHead = \case
    FHMeta x        -> S.Meta x
    FHCoe x a b p t -> S.Coe (go a) (go b) (go p) (go t)

  goRigidHead = \case
    RHLocalVar x _ _    -> S.LocalVar (lvlToIx x)
    RHPostulate x a     -> S.Postulate x a
    RHCoe a b p t       -> S.Coe (go a) (go b) (go p) (go t)
    RHExfalso a t       -> S.Exfalso (go a) (go t)
    RHRefl a t          -> S.Refl (go a) (go t)
    RHSym a x y p       -> S.Sym (go a) (go x) (go y) (go p)
    RHTrans a x y z p q -> S.Trans (go a) (go x) (go y) (go z) (go p) (go q)
    RHAp a b f x y p    -> S.Ap (go a) (go b) (go f) (go x) (go y) (go p)

  goUnfoldHead ~v = \case
    UHSolvedMeta x -> S.Meta x
    UHTopDef x v a -> S.TopDef x v a
    UHCoe a b p t  -> S.Coe (go a) (go b) (go p) (go t)

  cont :: Val -> S.Tm
  cont = \case
    Flex h sp _        -> goSp (goFlexHead h) sp
    FlexEq x a t u     -> S.Eq (go a) (go t) (go u)
    Rigid h sp _       -> goSp (goRigidHead h) sp
    RigidEq a t u      -> S.Eq (go a) (go t) (go u)
    Unfold h sp v _    -> goSp (goUnfoldHead v h) sp
    UnfoldEq a t u v   -> S.Eq (go a) (go t) (go u)
    TraceEq a t u v    -> S.Eq (go a) (go t) (go u)
    Pair t u           -> S.Pair (go t) (go u)
    Lam x i a t        -> S.Lam x i (go a) (goBind a t)
    Sg sp x a b        -> S.Sg sp x (go a) (goBind (elSP sp a) b)
    Pi x i a b         -> S.Pi x i (go a) (goBind a b)
    Set                -> S.Set
    El a               -> S.El (go a)
    Prop               -> S.Prop
    Newtype a b x _    -> S.Newtype (go a) (go b) (go x)
    Pack t             -> S.Pack (go t)
    Top                -> S.Top
    Tt                 -> S.Tt
    Bot                -> S.Bot
    Magic m            -> S.Magic m

  in case opt of
    UnfoldEverything -> cont (runIO (forceAll t))
    UnfoldMetas      -> cont (runIO (forceMetas t))
    UnfoldNothing    -> cont (runIO (force t))

-- | Quote with `UnfoldNone` as default option.
quote :: LvlArg => Val -> S.Tm
quote = quoteWithOpt UnfoldNothing

-- | Quote with `UnfoldNone` as default option.
quoteNf :: LvlArg => Val -> S.Tm
quoteNf = quoteWithOpt UnfoldEverything

quoteIn :: Lvl -> Val -> S.Tm
quoteIn l t = let ?lvl = l in quote t

quoteInWithOpt :: Lvl -> UnfoldOpt -> Val -> S.Tm
quoteInWithOpt l opt t = let ?lvl = l in quoteWithOpt opt t

eval0 :: S.Tm -> Val
eval0 t = let ?env = ENil; ?lvl = 0 in eval t

quote0 :: Val -> S.Tm
quote0 t = let ?lvl = 0 in quote t

quote0WithOpt :: UnfoldOpt -> Val -> S.Tm
quote0WithOpt opt t = let ?lvl = 0 in quoteWithOpt opt t

nf0 :: UnfoldOpt -> S.Tm -> S.Tm
nf0 opt t = quote0WithOpt opt (eval0 t)

-- | Create a closure from a value.
closeVal :: LvlArg => EnvArg => Val -> Closure
closeVal v = let
  v' = quoteIn (?lvl + 1) v
  in Cl \x -> evalIn ?lvl (EDef ?env x) v'
{-# inline closeVal #-}
