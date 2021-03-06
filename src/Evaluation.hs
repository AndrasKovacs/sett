
module Evaluation (
    app, appE, appI, proj1, proj2, projField
  , eval, quote, eval0, quote0, nf, nf0, spine, coe, eq
  , force, forceAll, forceMetas, eqSet
  ) where

import Control.Exception
import IO
import GHC.Exts

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
 - use approximate unfoldings including TraceEq, use ConvState
 - handle conversion between field proj and iterated primitive proj
-}

--------------------------------------------------------------------------------

localVar :: EnvArg => Ix -> Val
localVar x = go ?env x where
  go (EDef _ v) 0 = v
  go (EDef e _) x = go e (x - 1)
  go _          _ = impossible

meta :: MetaVar -> Val
meta x = runIO do
  readMeta x >>= \case
    MEUnsolved{}   -> pure (Flex (FHMeta x) SId)
    MESolved _ v _ -> pure (Unfold (UHSolvedMeta x) SId v)
{-# inline meta #-}

app :: LvlArg => Val -> Val -> Icit -> Val
app t u i = case t of
  Lam hl x i a t -> t $$ u
  Rigid h sp     -> Rigid h (SApp sp u i)
  Flex h sp      -> Flex h (SApp sp u i)
  Unfold h sp t  -> Unfold h (SApp sp u i) (app t u i)
  Irrelevant     -> Irrelevant
  _              -> impossible

appE :: LvlArg => Val -> Val -> Val
appE t u = app t u Expl

appI :: LvlArg => Val -> Val -> Val
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

projField :: Val -> Int -> Val
projField t n = case t of
  Pair _ t u     -> case n of 0 -> t
                              n -> projField u (n - 1)
  Rigid h sp     -> Rigid  h (SProjField sp n)
  Flex h sp      -> Flex   h (SProjField sp n)
  Unfold h sp t  -> Unfold h (SProjField sp n) (projField t n)
  Irrelevant     -> Irrelevant
  _              -> impossible

coe :: LvlArg => Val -> Val -> Val -> Val -> Val
coe a b p t = case (a, b) of

  -- canonical
  ------------------------------------------------------------

  (El a, El b) -> proj1 p `appE` t

  (topA@(Pi _ x i a b), topB@(Pi _ x' i' a' b'))
    | i /= i' -> Rigid (RHCoe topA topB p t) SId

    | True    ->
        let p1 = proj1 p
            p2 = proj2 p
        in LamS (pick x x') i a' \x' ->
            let x = coe a' a (Sym Set a a' p1) x'
            in coe (b $$ x) (b' $$ x') (p2 `appE` x) (app t x i)

  (Sg _ x a b, Sg _ x' a' b') ->
    let t1  = proj1 t
        t2  = proj2 t
        t1' = coe a a' (proj1 p) t1
        t2' = coe (b $$ t1) (b' $$ t1') (proj2 p) t2
    in Pair S t1' t2'

  (Set,  Set ) -> t
  (Prop, Prop) -> t

  -- non-canonical
  ------------------------------------------------------------

  (Irrelevant, _) -> Irrelevant
  (_, Irrelevant) -> Irrelevant

  (ua@(Unfold h sp a), b) -> Unfold (UHCoe ua b p t) SId (coe a b p t)
  (a, ub@(Unfold h sp b)) -> Unfold (UHCoe a ub p t) SId (coe a b p t)

  (a@(Flex h sp), b) -> Flex (FHCoe (flexHeadMeta h) a b p t) SId
  (a, b@(Flex h sp)) -> Flex (FHCoe (flexHeadMeta h) a b p t) SId

  (a@Rigid{}, b) -> coeTrans a b p t
  (a, b@Rigid{}) -> coeTrans a b p t

  -- Canonical mismatch
  -- NOTE: Canonical mismatch can't compute to Exfalso!
  --       That + coe-trans causes conversion to be undecidable.
  --       If Bot is provable, then every canonical type is irrelevant.
  --       E.g.    True
  --             = coe Bool Bool _ True
  --             = coe Nat Bool _ (coe Bool Nat _ True)
  --             = Exfalso Bool _
  --             = ...
  --             = False

  (a, b) -> Rigid (RHCoe a b p t) SId


coeTrans :: LvlArg => Val -> Val -> Val -> Val -> Val
coeTrans a b p t = case t of
  t@(Flex h sp)                -> Flex (FHCoe (flexHeadMeta h) a b p t) SId
  t@(Unfold h sp ft)           -> Unfold (UHCoe a b p t) SId (coeTrans a b p ft)
  Rigid (RHCoe a' _ p' t') SId -> coe a' b (Trans Set a' a b p' p) t'
  Irrelevant                   -> Irrelevant
  t                            -> coeRefl a b p t

coeRefl :: LvlArg => Val -> Val -> Val -> Val -> Val
coeRefl a b p t = case runConv (conv a b) of
  Same      -> t
  Diff      -> Rigid (RHCoe a b p t) SId
  BlockOn x -> Flex (FHCoe x a b p t) SId


-- Equality type
--------------------------------------------------------------------------------

eq :: LvlArg => Val -> Val -> Val -> Val
eq a t u = case a of
  Set  -> eqSet t u
  Prop -> eqProp t u
  El a -> markEq (El a) t u Top

  topA@(Pi _ x i a b) -> markEq topA t u $!
    PiSE x a \x -> eq (b $$ x) (app t x i) (app u x i)

  topA@(Sg _ x a b) ->
    let t1  = proj1 t
        u1  = proj1 u
        t2  = proj2 t
        u2  = proj2 u
        bu1 = b $$ u1
        bt1 = b $$ t1

    in markEq topA t u $!
       SgP np (eq a t1 u2) \p ->
         eq bu1
            (coe bt1 bu1
                 (Ap a Set (LamSE x a (unCl b)) t1 u1 p)
                 t2)
              u2

  a@Rigid{}          -> RigidEq a t u
  a@(FlexEq x _ _ _) -> FlexEq x a t u
  a@(Unfold h sp fa) -> UnfoldEq a t u (eq fa t u)
  Irrelevant         -> Irrelevant
  _                  -> impossible

eqSet :: LvlArg => Val -> Val -> Val
eqSet a b = case (a, b) of

  -- canonical
  ------------------------------------------------------------
  (Set , Set)  -> markEq Set Set Set Top
  (Prop, Prop) -> markEq Set Prop Prop Top
  (El a, El b) -> eqProp a b

  (topA@(Pi _ x i a b), topB@(Pi _ x' i' a' b'))
    | i /= i' -> markEq Set topA topB Bot
    | True    ->
      let name = pick x x'
      in markEq Set topA topB $!
        SgP np (eqSet a a') \p ->
        PiPE name a \x -> eqSet (b $$ x) (b' $$ coe a a' p x)

  (topA@(Sg _ x a b), topB@(Sg _ x' a' b')) ->
      let name = pick x x'
      in markEq Set topA topB $!
        SgP np (eqSet a a') \p ->
        PiPE name a \x -> eqSet (b $$ x) (b' $$ coe a a' p x)

  -- non-canonical
  ------------------------------------------------------------
  (Irrelevant, _) -> Irrelevant
  (_, Irrelevant) -> Irrelevant

  (a@(Unfold h sp fa), b) -> UnfoldEq Set a b (eqSet fa b)
  (a, b@(Unfold h sp fb)) -> UnfoldEq Set a b (eqSet a fb)

  (a@(Flex h _), b) -> FlexEq (flexHeadMeta h) Set a b
  (a, b@(Flex h _)) -> FlexEq (flexHeadMeta h) Set a b
  (a@Rigid{}, b)    -> RigidEq Set a b
  (a, b@Rigid{})    -> RigidEq Set a b

  -- canonical mismatch
  ------------------------------------------------------------
  (a, b) -> markEq Set a b Bot

eqProp :: Val -> Val -> Val
eqProp a b = markEq Prop a b (andP (funP a b) (funP b a))

--------------------------------------------------------------------------------

spine :: LvlArg => Val -> Spine -> Val
spine v sp =
  let go = spine v; {-# inline go #-}
  in case sp of
    SId            -> v
    SApp t u i     -> app (go t) u i
    SProj1 t       -> proj1 (go t)
    SProj2 t       -> proj2 (go t)
    SProjField t n -> projField (go t) n

maskEnv :: Env -> S.Locals -> Spine
maskEnv e ls = case (e, ls) of
  (ENil,     S.LEmpty          ) -> SId
  (EDef e _, S.LDefine ls _ _ _) -> maskEnv e ls
  (EDef e v, S.LBind ls x _    ) -> SApp (maskEnv e ls) v Expl
  _                              -> impossible

insertedMeta :: LvlArg => EnvArg => MetaVar -> S.Locals -> Val
insertedMeta x ls = runIO do
  let sp = maskEnv ?env ls
  readMeta x >>= \case
    MEUnsolved{}   -> pure (Flex (FHMeta x) sp)
    MESolved _ v _ -> pure (Unfold (UHSolvedMeta x) sp (spine v sp))


eqSym, coeSym, symSym, apSym, transSym, elSym, reflSym, exfalsoSym :: Val
eqSym      = LamSI na Set \a -> LamSE nx a \x -> LamSE ny a \y -> eq a x y

coeSym     = LamSI na Set \a -> LamSI nb Set \b -> LamSE np (El (eqSet a b)) \p -> LamSE nx a \x ->
             coe a b p x

symSym     = LamPI na Set \a -> LamPI ny a \x -> LamPI ny a \y -> LamPE np (El (eq a x y)) \p ->
             Sym a x y p

apSym      = LamPI na Set \a -> LamPI nb Set \b -> LamPE nf (funS a b) \f -> LamPI nx a \x ->
             LamPI ny a \y -> LamPE np (eq a x y) \p ->
             Ap a b f x y p

transSym   = LamPI na Set \a -> LamPI nx a \x -> LamPI ny a \y -> LamPI nz a \z ->
             LamPE np (eq a x y) \p -> LamPE nq (eq a y z) \q ->
             Trans a x y z p q

elSym      = LamSE na Prop El
reflSym    = LamPI na Set \a -> LamPI nx a \x -> Refl a x
exfalsoSym = LamSI na Set \a -> LamSE np (El Bot) \p -> Exfalso a p

eval :: LvlArg => EnvArg => S.Tm -> Val
eval t =
  let go t     = eval t; {-# inline go #-}
      goBind t = Cl \u -> let ?env = EDef ?env u in eval t; {-# inline goBind #-}

  in case t of
    S.LocalVar x        -> localVar x
    S.TopDef v x        -> Unfold (UHTopDef x) SId (coerce v)
    S.Lam hl x i a t    -> Lam hl x i (go a) (goBind t)
    S.App t u i         -> app (go t) (go u) i
    S.Pair hl t u       -> Pair hl (go t) (go u)
    S.ProjField t n     -> projField (go t) n
    S.Proj1 t           -> proj1 (go t)
    S.Proj2 t           -> proj2 (go t)
    S.Pi hl x i a b     -> Pi hl x i (go a) (goBind b)
    S.Sg hl x a b       -> Sg hl x (go a) (goBind b)
    S.Postulate x       -> Rigid (RHPostulate x) SId
    S.InsertedMeta x ls -> insertedMeta x ls
    S.Meta x            -> meta x
    S.Let x a t u       -> let ?env = EDef ?env (eval t) in eval u
    S.Set               -> Set
    S.Prop              -> Prop
    S.Top               -> Top
    S.Tt                -> Tt
    S.Bot               -> Bot
    S.ElSym             -> elSym
    S.EqSym             -> eqSym
    S.CoeSym            -> coeSym
    S.ReflSym           -> reflSym
    S.SymSym            -> symSym
    S.TransSym          -> transSym
    S.ApSym             -> apSym
    S.ExfalsoSym        -> exfalsoSym
    S.Irrelevant        -> Irrelevant

-- Forcing
--------------------------------------------------------------------------------

unblock :: MetaVar -> a -> (Val -> IO a) -> IO a
unblock x def k = readMeta x >>= \case
  MEUnsolved{}   -> pure def
  MESolved _ v _ -> k v
{-# inline unblock #-}

-- | Eliminate solved flex head metas.
force :: LvlArg => Val -> IO Val
force v = case v of
  hsp@(Flex h sp) -> forceFlex hsp h sp
  v               -> pure v
{-# inline force #-}

forceFlex :: LvlArg => Val -> FlexHead -> Spine -> IO Val
forceFlex hsp h sp = case h of
  FHMeta x        -> unblock x hsp \v -> pure $ Unfold (UHSolvedMeta x) sp v
  FHCoe x a b p t -> unblock x hsp \_ -> force $! coeRefl a b p t
{-# noinline forceFlex #-}

-- | Eliminate all unfoldings from the head.
forceAll :: LvlArg => Val -> IO Val
forceAll v = case v of
  hsp@(Flex h sp) -> forceAllFlex hsp h sp
  Unfold _ _ v    -> forceAllUnfold v
  TraceEq _ _ _ v -> forceAllUnfold v
  t               -> pure t
{-# inline forceAll #-}

forceAllFlex :: LvlArg => Val -> FlexHead -> Spine -> IO Val
forceAllFlex hsp h sp = case h of
  FHMeta x        -> unblock x hsp \v -> forceAll $! spine v sp
  FHCoe x a b p t -> unblock x hsp \_ -> forceAll $! coeRefl a b p t
{-# noinline forceAllFlex #-}

forceAllUnfold :: LvlArg => Val -> IO Val
forceAllUnfold v = case v of
  hsp@(Flex h sp) -> forceAllFlex hsp h sp
  Unfold _ _ v    -> forceAllUnfold v
  TraceEq _ _ _ v -> forceAllUnfold v
  t               -> pure t

-- | Eliminate all meta unfoldings from the head.
forceMetas :: LvlArg => Val -> IO Val
forceMetas v = case v of
  hsp@(Flex h sp)           -> forceMetasFlex hsp h sp
  Unfold UHSolvedMeta{} _ v -> forceMetasUnfold v
  t                         -> pure t
{-# inline forceMetas #-}

forceMetasFlex :: LvlArg => Val -> FlexHead -> Spine -> IO Val
forceMetasFlex hsp h sp = case h of
  FHMeta x        -> unblock x hsp \v -> forceMetas $! spine v sp
  FHCoe x a b p t -> unblock x hsp \_ -> forceMetas $! coeRefl a b p t
{-# noinline forceMetasFlex #-}

forceMetasUnfold :: LvlArg => Val -> IO Val
forceMetasUnfold v = case v of
  hsp@(Flex h sp)           -> forceMetasFlex hsp h sp
  Unfold UHSolvedMeta{} _ v -> forceMetasUnfold v
  t                         -> pure t

-- Computing types & relevance
--------------------------------------------------------------------------------

postulateType :: Lvl -> IO GTy
postulateType x = readTopInfo x >>= \case
  TEDef{}           -> impossible
  TEPostulate _ a _ -> pure a

metaType :: MetaVar -> IO GTy
metaType x = readMeta x >>= \case
  MEUnsolved a -> pure a
  _            -> impossible

rigidHeadType :: RigidHead -> IO Ty
rigidHeadType = \case
  RHLocalVar _ a      -> pure a
  RHPostulate x       -> g2 <$!> postulateType x
  RHCoe a b p t       -> pure $! b
  RHExfalso a p       -> pure $! a

projFieldType :: LvlArg => Spine -> (Spine -> Val) -> Ty -> Int -> IO Ty
projFieldType sp mkval a n = do
  let go = projFieldType sp mkval; {-# inline go #-}
  a <- forceAll a
  case (a, n) of
    (Sg _ x a b     , 0) -> pure a
    (Sg _ x a b     , n) -> go (b $$ mkval (SProjField sp n)) (n + 1)
    (El (Sg _ _ a b), 0) -> pure $ El a
    (El (Sg _ x a b), n) -> go (El (b $$ mkval (SProjField sp n))) (n + 1)
    _                    -> impossible

spineType :: LvlArg => (Spine -> Val) -> Ty -> Spine -> IO Ty
spineType mkval a sp =
  let go = spineType mkval a; {-# inline go #-}
  in case sp of
    SId             -> pure a
    SApp t u i      -> (go t >>= forceAll) >>= \case
                         Pi _ _ _ _ b      -> pure $! (b $$ u)
                         El (Pi _ _ _ _ b) -> pure $! El (b $$ u)
                         _                 -> impossible
    SProj1 t        -> (go t >>= forceAll) >>= \case
                         Sg _ _ a _      -> pure a
                         El (Sg _ _ a _) -> pure (El a)
                         _               -> impossible
    SProj2 t        -> (go t >>= forceAll) >>= \case
                         Sg _ _ _ b      -> pure $! (b $$ mkval (SProj1 t))
                         El (Sg _ _ _ b) -> pure $! El (b $$ mkval (SProj1 t))
                         _               -> impossible
    SProjField t n  -> do {a <- go t; projFieldType t mkval a n}


flexHeadType :: LvlArg => FlexHead -> IO Ty
flexHeadType h = case h of
  FHMeta x        -> g2 <$!> metaType x
  FHCoe x a b p t -> pure b

rigidType :: LvlArg => RigidHead -> Spine -> IO Ty
rigidType h sp = do
  hty <- rigidHeadType h
  spineType (Rigid h) hty sp

flexType :: LvlArg => FlexHead -> Spine -> IO Ty
flexType h sp = do
  hty <- flexHeadType h
  spineType (Flex h) hty sp

data Relevance = RRel | RIrr | RBlockOn MetaVar

instance Semigroup Relevance where
  (<>) (RBlockOn x) _ = RBlockOn x
  (<>) _ (RBlockOn x) = RBlockOn x
  (<>) RRel RRel      = RRel
  (<>) _ _            = RIrr
  {-# inline (<>) #-}

typeRelevance :: LvlArg => Ty -> IO Relevance
typeRelevance a = do
  let go         = typeRelevance; {-# inline go #-}
      goBind a b = newVar a \v -> typeRelevance (b $$ v); {-# inline goBind #-}
  forceAll a >>= \case
    El _         -> pure RIrr
    Set          -> pure RRel
    Prop         -> pure RRel
    Irrelevant   -> pure RIrr
    Pi _ _ _ a b -> goBind a b
    Sg _ _ a b   -> go a <> goBind a b
    Rigid h sp   -> pure RRel
    Flex h sp    -> pure $! RBlockOn (flexHeadMeta h)
    _            -> impossible

flexRelevance :: LvlArg => FlexHead -> Spine -> IO Relevance
flexRelevance h sp = typeRelevance =<< flexType h sp

rigidRelevance :: LvlArg => RigidHead -> Spine -> IO Relevance
rigidRelevance h sp = typeRelevance =<< rigidType h sp


-- Conversion
--------------------------------------------------------------------------------

-- | Bump the `Lvl` and get a fresh variable.
newVar :: Ty -> (LvlArg => Val -> a) -> LvlArg => a
newVar a cont =
  let v = Var ?lvl a in
  let ?lvl = ?lvl + 1 in
  seq ?lvl (cont v)
{-# inline newVar #-}

data ConvRes = Same | Diff | BlockOn MetaVar
  deriving Show
instance Exception ConvRes

runConv :: IO () -> ConvRes
runConv act = runIO ((Same <$ act) `catch` pure)
{-# inline runConv #-}

convEq :: Eq a => a -> a -> IO ()
convEq x y = when (x /= y) $ throwIO Diff
{-# inline convEq #-}

convSp :: LvlArg => Spine -> Spine -> IO ()
convSp sp sp' = do
  let go   = conv; {-# inline go #-}
      goSp = convSp; {-# inline goSp #-}
  case (sp, sp') of
    (SId            , SId             ) -> pure ()
    (SApp t u i     , SApp t' u' i'   ) -> goSp t t' >> go u u'
    (SProj1 t       , SProj1 t'       ) -> goSp t t'
    (SProj2 t       , SProj2 t'       ) -> goSp t t'
    (SProjField t n , SProjField t' n') -> goSp t t' >> convEq n n'
    _                                   -> throwIO Diff

-- | Magical rigid coe conversion.
convCoe :: LvlArg => Val -> Val -> Val -> Val -> Spine -> Val -> Val -> Val -> Val -> Spine -> IO ()
convCoe a b p t sp a' b' p' t' sp' = do

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
  (RHLocalVar x _, RHLocalVar x' _   ) -> convEq x x' >> convSp sp sp'
  (RHPostulate x , RHPostulate x'    ) -> convEq x x' >> convSp sp sp'
  (RHCoe a b p t , RHCoe a' b' p' t' ) -> convCoe a b p t sp a' b' p' t' sp'
  (RHExfalso a p , RHExfalso a' p'   ) -> convExfalso a a' sp sp'
  _                                    -> throwIO Diff

conv :: LvlArg => Val -> Val -> IO ()
conv t u = do
  let go = conv
      {-# inline go #-}

      goBind a t u = do
        let v = Var ?lvl a
        let ?lvl = ?lvl + 1
        conv (t $$ v) (u $$ v)
      {-# inline goBind #-}

      guardP hl (cont :: IO ()) = case hl of
        P -> pure ()
        _ -> cont
      {-# inline guardP #-}

  t <- forceAll t
  u <- forceAll u
  case (t, u) of

    -- canonical
    ------------------------------------------------------------
    (Pi _ x i a b, Pi _ x' i' a' b') -> do
      unless (i == i') $ throwIO Diff
      go a a'
      goBind a b b'

    (Sg _ x a b, Sg _ x' a' b') -> do
      go a a'
      goBind a b b

    (Set  , Set  ) -> pure ()
    (Prop , Prop ) -> pure ()
    (Top  , Top  ) -> pure ()
    (Bot  , Bot  ) -> pure ()
    (El a , El b ) -> go a b
    (Tt   , Tt   ) -> pure ()

    (RigidEq a t u  , RigidEq a' t' u') -> go a a' >> go t t' >> go u u'
    (Lam hl _ _ _ t , Lam _ _ _ a t'  ) -> guardP hl $ goBind a t t'
    (Pair hl t u    , Pair _ t' u'    ) -> guardP hl $ go t t' >> go u u'

    -- eta
    --------------------------------------------------------------------------------

    (Lam hl _ i a t , t'              ) -> guardP hl $ goBind a t (Cl \u -> app t' u i)
    (t              , Lam hl _ i a t' ) -> guardP hl $ goBind a (Cl \u -> app t u i) t'
    (Pair hl t u    , t'              ) -> guardP hl $ go t (proj1 t') >> go u (proj2 t')
    (t              , Pair hl t' u'   ) -> guardP hl $ go (proj1 t) t' >> go (proj2 t) u'

    -- non-canonical
    ------------------------------------------------------------

    (Irrelevant , _         ) -> pure ()
    (_          , Irrelevant) -> pure ()

    (Flex h sp, _) -> flexRelevance h sp >>= \case
      RIrr       -> pure ()
      _          -> throwIO $ BlockOn (flexHeadMeta h)

    (_, Flex h sp) -> flexRelevance h sp >>= \case
      RIrr       -> pure ()
      _          -> throwIO $ BlockOn (flexHeadMeta h)

    (FlexEq x _ _ _, _) -> throwIO $ BlockOn x
    (_, FlexEq x _ _ _) -> throwIO $ BlockOn x

    (Rigid h sp, Rigid h' sp') -> rigidRelevance h sp >>= \case
      RIrr       -> pure ()
      RBlockOn x -> throwIO $ BlockOn x
      RRel       -> convRigidRel h sp h' sp'

    (Rigid h sp, _) -> rigidRelevance h sp >>= \case
      RIrr       -> pure ()
      RBlockOn x -> throwIO $ BlockOn x
      RRel       -> throwIO Diff

    (_, Rigid h' sp') -> rigidRelevance h' sp' >>= \case
      RIrr       -> pure ()
      RBlockOn x -> throwIO $ BlockOn x
      RRel       -> throwIO Diff

    -- canonical mismatch is always a failure, because we don't yet
    -- have inductive data in Prop, so mismatch is only possible in Set.
    --------------------------------------------------------------------------------

    (a, b) -> throwIO Diff


-- Quoting
--------------------------------------------------------------------------------

quoteSp :: LvlArg => UnfoldOpt -> S.Tm -> Spine -> S.Tm
quoteSp opt hd sp = let
  go         = quote opt; {-# inline go #-}
  goSp       = quoteSp opt hd; {-# inline goSp #-}
  in case sp of
    SId            -> hd
    SApp t u i     -> S.App (goSp t) (go u) i
    SProj1 t       -> S.Proj1 (goSp t)
    SProj2 t       -> S.Proj2 (goSp t)
    SProjField t n -> S.ProjField (goSp t) n

quote :: LvlArg => UnfoldOpt -> Val -> S.Tm
quote opt t = let
  go         = quote opt; {-# inline go #-}
  goSp       = quoteSp opt; {-# inline goSp #-}
  goBind a t = newVar a \v -> quote opt (t $$ v); {-# inline goBind #-}

  goFlexHead = \case
    FHMeta x        -> S.Meta x
    FHCoe x a b p t -> S.Coe (go a) (go b) (go p) (go t)

  goRigidHead = \case
    RHLocalVar x _ -> S.LocalVar (lvlToIx x)
    RHPostulate x  -> S.Postulate x
    RHCoe a b p t  -> S.Coe (go a) (go b) (go p) (go t)
    RHExfalso a t  -> S.Exfalso (go a) (go t)

  goUnfoldHead ~v = \case
    UHSolvedMeta x -> S.Meta x
    UHTopDef x     -> S.TopDef (coerce v) x
    UHCoe a b p t  -> S.Coe (go a) (go b) (go p) (go t)

  cont :: Val -> S.Tm
  cont = \case
    Flex h sp         -> goSp (goFlexHead h) sp
    FlexEq x a t u    -> S.Eq (go a) (go t) (go u)
    Rigid h sp        -> goSp (goRigidHead h) sp
    RigidEq a t u     -> S.Eq (go a) (go t) (go u)
    Unfold h sp v     -> goSp (goUnfoldHead v h) sp
    UnfoldEq a t u v  -> S.Eq (go a) (go t) (go u)
    TraceEq a t u v   -> go v
    Pair hl t u       -> S.Pair hl (go t) (go u)
    Lam hl x i a t    -> S.Lam hl x i (go a) (goBind a t)
    Sg hl x a b       -> S.Sg hl x (go a) (goBind a b)
    Pi hl x i a b     -> S.Pi hl x i (go a) (goBind a b)
    Set               -> S.Set
    Prop              -> S.Prop
    El a              -> S.El (go a)
    Top               -> S.Top
    Tt                -> S.Tt
    Bot               -> S.Bot
    Refl a t          -> S.Refl (go a) (go t)
    Sym a x y p       -> S.Sym (go a) (go x) (go y) (go p)
    Trans a x y z p q -> S.Trans (go a) (go x) (go y) (go z) (go p) (go q)
    Ap a b f x y p    -> S.Ap (go a) (go b) (go f) (go x) (go y) (go p)
    Irrelevant        -> S.Irrelevant

  in case opt of
    UnfoldAll   -> cont (runIO (forceAll t))
    UnfoldMetas -> cont (runIO (forceMetas t))
    UnfoldNone  -> cont (runIO (force t))

eval0 :: S.Tm -> Val
eval0 t = let ?env = ENil; ?lvl = 0 in eval t
{-# inline eval0 #-}

quote0 :: UnfoldOpt -> Val -> S.Tm
quote0 opt t = let ?lvl = 0 in quote opt t
{-# inline quote0 #-}

nf0 :: UnfoldOpt -> S.Tm -> S.Tm
nf0 opt t = quote0 opt (eval0 t)
{-# inline nf0 #-}
