
module Evaluation where

import Control.Exception
import IO

import Common
import ElabState
import Values
import qualified Syntax as S

--------------------------------------------------------------------------------

-- TODO
--  - approximate unfoldings, use ConvState
--  - conversion between field proj and iterated primitive proj

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

projField :: Val -> Name -> Int -> Val
projField t x n = case t of
  Pair _ t u     -> case n of 0 -> t
                              n -> projField u x (n - 1)
  Rigid h sp     -> Rigid  h (SProjField sp x n)
  Flex h sp      -> Flex   h (SProjField sp x n)
  Unfold h sp t  -> Unfold h (SProjField sp x n) (projField t x n)
  Irrelevant     -> Irrelevant
  _              -> impossible

coe :: Lvl -> Val -> Val -> Val -> Val -> Val
coe l a b p t = case (a, b) of

  -- canonical
  ------------------------------------------------------------

  (El a, El b) -> proj1 p `appE` t

  (topA@(Pi _ x i a b), topB@(Pi _ x' i' a' b'))
    | i /= i' -> Rigid (RHCoe topA topB p t) SId

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

  (Set,  Set ) -> t
  (Prop, Prop) -> t

  -- non-canonical
  ------------------------------------------------------------

  (Irrelevant, _) -> Irrelevant
  (_, Irrelevant) -> Irrelevant

  (Unfold h sp a, b) -> Unfold h (SCoeSrc sp b p t) (coe l a b p t)
  (a, Unfold h sp b) -> Unfold h (SCoeTgt a sp p t) (coe l a b p t)

  -- "early coe-refl" if sides are convertible
  (Flex h sp, Flex h' sp') -> case runConv (convFlexRel l h sp h' sp') of
    Same      -> t
    Diff      -> impossible
    BlockOn _ -> Flex h (SCoeSrc sp b p t)

  -- Rafael: only put in heads, not in spines
  -- TODO: think about Spine + Head repr

  (Flex h sp, b) -> Flex h (SCoeSrc sp b p t)
  (a, Flex h sp) -> Flex h (SCoeTgt a sp p t)

  (a@Rigid{}, b) -> coeTrans l a b p t
  (a, b@Rigid{}) -> coeTrans l a b p t

  -- Canonical mismatch
  -- NOTE: Canonical mismatch can't compute to Exfalso!
  --       That + coe-trans causes conversion to be undecidable.
  --       If Bot is provable, then every canonical type is irrelevant.
  --       E.g.    true
  --             = coe Bool Bool _ true
  --             = coe Nat Bool _ (coe Bool Nat _ true)
  --             = Exfalso Bool _

  (a, b) -> Rigid (RHCoe a b p t) SId


coeTrans :: Lvl -> Val -> Val -> Val -> Val -> Val
coeTrans l a b p t = case t of
  Flex h sp                    -> Flex h (SCoeTrans a b p sp)
  Unfold h sp t                -> Unfold h (SCoeTrans a b p sp) (coeTrans l a b p t)
  Rigid (RHCoe a' _ p' t') SId -> coe l a' b (Trans Set a' a b p' p) t'
  Irrelevant                   -> Irrelevant
  t                            -> coeRefl l a b p t

coeRefl :: Lvl -> Val -> Val -> Val -> Val -> Val
coeRefl l a b p t = case runConv (conv l a b) of
  Same      -> t
  Diff      -> Rigid (RHCoe a b p t) SId
  BlockOn x -> Flex (FHCoeRefl x a b p t) SId


-- Equality type
--------------------------------------------------------------------------------

eq :: Lvl -> Val -> Val -> Val -> Val
eq l a t u = case a of
  Set  -> eqSet l t u
  Prop -> eqProp t u
  El a -> markEq (El a) t u Top

  topA@(Pi _ x i a b) -> markEq topA t u $
    PiSE x a \x -> eq l (b $$ x) (app t x i) (app u x i)

  topA@(Sg _ x a b) ->
    let t1 = proj1 t
        u1 = proj1 u
        t2 = proj2 t
        u2 = proj2 u
    in markEq topA t u $
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
eqSet l a b = case (a, b) of

  -- canonical
  ------------------------------------------------------------
  (Set , Set)  -> markEq Set Set Set Top
  (Prop, Prop) -> markEq Set Prop Prop Top
  (El a, El b) -> eqProp a b

  (topA@(Pi _ x i a b), topB@(Pi _ x' i' a' b'))
    | i /= i' -> markEq Set topA topB Bot
    | True    -> markEq Set topA topB $
      SgP NP (eqSet l a a') \p ->
      PiPE (pick x x') a \x -> eqSet l (b $$ x) (b' $$ coe l a a' p x)

  (topA@(Sg _ x a b), topB@(Sg _ x' a' b')) -> markEq Set topA topB $
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
  (a, b) -> markEq Set a b Bot

eqProp :: Val -> Val -> Val
eqProp a b = markEq Prop a b (andP (funP a b) (funP b a))

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
    -- SCoeSrc a b p t   -> coe l (go a) b p t
    -- SCoeTgt a b p t   -> coe l a (go b) p t
    -- SCoeTrans a b p t -> coeTrans l a b p (go t)
    -- SEqSet a t u      -> eq l (go a) t u
    -- SEqLhs a t u      -> eq l a (go t) u
    -- SEqRhs a t u      -> eq l a t (go u)

maskEnv :: Env -> S.Locals -> Spine
maskEnv e ls = case (e, ls) of
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


eqSym, coeSym, symSym, apSym, transSym :: Lvl -> Val
eqSym  l   = LamSI NA Set \a -> LamSE NX a \x -> LamSE NY a \y -> eq l a x y
coeSym l   = LamSI NA Set \a -> LamSI NB Set \b -> LamSE NP (El (eqSet l a b)) \p -> LamSE NX a \x ->
             coe l a b p x
symSym l   = LamPI NA Set \a -> LamPI NY a \x -> LamPI NY a \y -> LamPE NP (El (eq l a x y)) \p -> Sym a x y p
apSym  l   = LamPI NA Set \a -> LamPI NB Set \b -> LamPE NF (funS a b) \f -> LamPI NX a \x -> LamPI NY a \y ->
             LamPE NP (eq l a x y) \p -> Ap a b f x y p
transSym l = LamPI NA Set \a -> LamPI NX a \x -> LamPI NY a \y -> LamPI NZ a \z -> LamPE NP (eq l a x y) \p ->
             LamPE NQ (eq l a y z) \q -> Trans a x y z p q

elSym, reflSym, exfalsoSym :: Val
elSym      = LamSE NA Prop El
reflSym    = LamPI NA Set \a -> LamPI NX a \x -> Refl a x

exfalsoSym = LamSI NA Set \l a -> LamSE NP (El Bot) \l' p -> Exfalso a p
-- only the last level matters in a chain of lambdas!


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
    S.Top               -> Top
    S.Tt                -> Tt
    S.Bot               -> Bot
    S.ElSym             -> elSym
    S.EqSym             -> eqSym l
    S.CoeSym            -> coeSym l
    S.ReflSym           -> reflSym
    S.SymSym            -> symSym l
    S.TransSym          -> transSym l
    S.ApSym             -> apSym l
    S.ExfalsoSym        -> exfalsoSym
    S.Irrelevant        -> Irrelevant

-- Forcing
--------------------------------------------------------------------------------

-- 3 different forcings (from smalltt)
--

unblock :: MetaVar -> a -> (Val -> IO a) -> IO a
unblock x def k = readMeta x >>= \case
  MEUnsolved{}   -> pure def
  MESolved _ v _ -> k v
{-# inline unblock #-}

-- | Eliminate solved flex head metas.
force :: Lvl -> Val -> IO Val
force l = \case
  hsp@(Flex h sp) -> forceFlex l hsp h sp
  v               -> pure v
{-# inline force #-}

forceFlex :: Lvl -> Val -> FlexHead -> Spine -> IO Val
forceFlex l hsp h sp = case h of
  FHMeta x            -> unblock x hsp \v -> pure $ Unfold (UHSolvedMeta x) sp v
  FHCoeRefl x a b p t -> unblock x hsp \_ -> force l $! coeRefl l a b p t
{-# noinline forceFlex #-}
-- TODO: ensure that we pick a rigidly blocking meta for CoeRefl!

-- | Eliminate all unfoldings from the head.
forceAll :: Lvl -> Val -> IO Val
forceAll l = \case
  hsp@(Flex h sp) -> forceAllFlex l hsp h sp
  Unfold _ _ v    -> forceAllUnfold l v
  t               -> pure t
{-# inline forceAll #-}

forceAllFlex :: Lvl -> Val -> FlexHead -> Spine -> IO Val
forceAllFlex l hsp h sp = case h of
  FHMeta x            -> unblock x hsp \v -> forceAll l $! spine l v sp
  FHCoeRefl x a b p t -> unblock x hsp \_ -> forceAll l $! coeRefl l a b p t
{-# noinline forceAllFlex #-}

forceAllUnfold :: Lvl -> Val -> IO Val
forceAllUnfold l = \case
  hsp@(Flex h sp) -> forceAllFlex l hsp h sp
  Unfold _ _ v    -> forceAllUnfold l v
  t               -> pure t

-- | Eliminate all meta unfoldings from the head.
forceMetas :: Lvl -> Val -> IO Val
forceMetas l = \case
  hsp@(Flex h sp)           -> forceMetasFlex l hsp h sp
  Unfold UHSolvedMeta{} _ v -> forceMetasUnfold l v
  t                         -> pure t
{-# inline forceMetas #-}

forceMetasFlex :: Lvl -> Val -> FlexHead -> Spine -> IO Val
forceMetasFlex l hsp h sp = case h of
  FHMeta x            -> unblock x hsp \v -> forceMetas l $! spine l v sp
  FHCoeRefl x a b p t -> unblock x hsp \_ -> forceMetas l $! coeRefl l a b p t
{-# noinline forceMetasFlex #-}

forceMetasUnfold :: Lvl -> Val -> IO Val
forceMetasUnfold l = \case
  hsp@(Flex h sp)           -> forceMetasFlex l hsp h sp
  Unfold UHSolvedMeta{} _ v -> forceMetasUnfold l v
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

rigidHeadType :: Lvl -> RigidHead -> IO Ty
rigidHeadType l = \case
  RHLocalVar _ a      -> pure a
  RHPostulate x       -> g2 <$!> postulateType x
  RHCoe a b p t       -> pure $! b
  RHExfalso a p       -> pure $! a

projFieldType :: Lvl -> Spine -> (Spine -> Val) -> Ty -> Int -> IO Ty
projFieldType l sp mkval a n = do
  let go = projFieldType l sp mkval; {-# inline go #-}
  a <- forceAll l a
  case (a, n) of
    (Sg _ x a b     , 0) -> pure a
    (Sg _ x a b     , n) -> go (b $$ mkval (SProjField sp x n)) (n + 1)
    (El (Sg _ _ a b), 0) -> pure $ El a
    (El (Sg _ x a b), n) -> go (El (b $$ mkval (SProjField sp x n))) (n + 1)
    _                    -> impossible

spineType :: Lvl -> (Spine -> Val) -> Ty -> Spine -> IO Ty
spineType l mkval a sp =
  let go = spineType l mkval a; {-# inline go #-}
  in case sp of
    SId          -> pure a
    SApp t u i   -> (go t >>= forceAll l) >>= \case
                      Pi _ _ _ _ b      -> pure $! (b $$ u)
                      El (Pi _ _ _ _ b) -> pure $! El (b $$ u)
                      _                 -> impossible
    SProj1 t     -> (go t >>= forceAll l) >>= \case
                      Sg _ _ a _      -> pure a
                      El (Sg _ _ a _) -> pure (El a)
                      _               -> impossible
    SProj2 t     -> (go t >>= forceAll l) >>= \case
                      Sg _ _ _ b      -> pure $! (b $$ mkval (SProj1 t))
                      El (Sg _ _ _ b) -> pure $! El (b $$ mkval (SProj1 t))
                      _               -> impossible
    SProjField t x n  -> do {a <- go t; projFieldType l t mkval a n}
    -- SCoeSrc a b p t   -> pure b
    -- SCoeTgt a b p t   -> go b
    -- SCoeTrans a b p t -> pure b
    -- SEqSet a t u      -> pure Prop
    -- SEqLhs a t u      -> pure Prop
    -- SEqRhs a t u      -> pure Prop

flexHeadType :: Lvl -> FlexHead -> IO Ty
flexHeadType l = \case
  FHMeta x            -> g2 <$!> metaType x
  FHCoeRefl x a b p t -> pure b

rigidType :: Lvl -> RigidHead -> Spine -> IO Ty
rigidType l h sp = do
  hty <- rigidHeadType l h
  spineType l (Rigid h) hty sp

flexType :: Lvl -> FlexHead -> Spine -> IO Ty
flexType l h sp = do
  hty <- flexHeadType l h
  spineType l (Flex h) hty sp

data Relevance = RRel | RIrr | RBlockOn MetaVar

instance Semigroup Relevance where
  (<>) (RBlockOn x) _ = RBlockOn x
  (<>) _ (RBlockOn x) = RBlockOn x
  (<>) RRel RRel      = RRel
  (<>) _ _            = RIrr
  {-# inline (<>) #-}

typeRelevance :: Lvl -> Ty -> IO Relevance
typeRelevance l a = do
  let go = typeRelevance; {-# inline go #-}
  forceAll l a >>= \case
    El _         -> pure RIrr
    Set          -> pure RRel
    Prop         -> pure RRel
    Irrelevant   -> pure RIrr
    Pi _ _ _ a b -> go (l + 1) (b $$ Var l a)
    Sg _ _ a b   -> go l a <> go (l + 1) (b $$ Var l a)
    Rigid h sp   -> pure RRel
    Flex h sp    -> pure $! RBlockOn (headMeta h)
    _            -> impossible

flexRelevance :: Lvl -> FlexHead -> Spine -> IO Relevance
flexRelevance l h sp = do
  ty <- flexType l h sp
  typeRelevance l ty

rigidRelevance :: Lvl -> RigidHead -> Spine -> IO Relevance
rigidRelevance l h sp = do
  ty <- rigidType l h sp
  typeRelevance l ty


-- Conversion
--------------------------------------------------------------------------------

data ConvRes = Same | Diff | BlockOn MetaVar
  deriving Show
instance Exception ConvRes

runConv :: IO () -> ConvRes
runConv act = runIO ((Same <$ act) `catch` pure)
{-# inline runConv #-}

convEq :: Eq a => a -> a -> IO ()
convEq x y = when (x /= y) $ throwIO Diff
{-# inline convEq #-}

convSp :: Lvl -> Spine -> Spine -> IO ()
convSp l sp sp' = do
  let go   = conv l; {-# inline go #-}
      goSp = convSp l; {-# inline goSp #-}
  case (sp, sp') of
    (SId               , SId                   ) -> pure ()
    (SApp t u i        , SApp t' u' i'         ) -> goSp t t' >> go u u'
    (SProj1 t          , SProj1 t'             ) -> goSp t t'
    (SProj2 t          , SProj2 t'             ) -> goSp t t'
    (SProjField t _ n  , SProjField t' _ n'    ) -> goSp t t' >> convEq n n'
    -- (SCoeSrc a b p t   , SCoeSrc a' b' p' t'   ) -> goSp a a' >> go b b' >> go t t'
    -- (SCoeTgt a b p t   , SCoeTgt a' b' p' t'   ) -> go a a' >> goSp b b' >> go t t'
    -- (SCoeTrans a b p t , SCoeTrans a' b' p' t' ) -> go a a' >> go b b' >> goSp t t'
    -- (SEqSet a t u      , SEqSet a' t' u'       ) -> goSp a a' >> go t t' >> go u u'
    -- (SEqLhs a t u      , SEqLhs a' t' u'       ) -> go a a' >> goSp t t' >> go u u'
    -- (SEqRhs a t u      , SEqRhs a' t' u'       ) -> go a a' >> go t t' >> goSp u u'
    _                                            -> throwIO Diff

-- | Compare flex heads which are known to be relevant.
convFlexHeadRel :: Lvl -> FlexHead -> FlexHead -> IO MetaVar
convFlexHeadRel l h h' = case (h, h') of
 (FHMeta x, FHMeta x') -> x <$ (when (x /= x') $ throwIO $ BlockOn x)
 (FHMeta x, _        ) -> throwIO $ BlockOn x
 (_       , FHMeta x ) -> throwIO $ BlockOn x

 (FHCoeRefl x a b p t, FHCoeRefl x' a' b' p' t') -> do
   when (x /= x') $ throwIO $ BlockOn x
   conv l a a' >> conv l b b' >> conv l t t'
   pure x

-- | Compare flex-es which are known to be relevant.
convFlexRel :: Lvl -> FlexHead -> Spine -> FlexHead -> Spine -> IO ()
convFlexRel l h sp h' sp' = do
  x <- convFlexHeadRel l h h'
  convSp l sp sp' `catch` \case
    Diff      -> throwIO $ BlockOn x
    BlockOn _ -> throwIO $ BlockOn x
    _         -> impossible

-- | Magical rigid coe conversion.
convCoe :: Lvl -> Val -> Val -> Val -> Val -> Spine -> Val -> Val -> Val -> Val -> Spine -> IO ()
convCoe l a b p t sp a' b' p' t' sp' = do

  case (sp, sp') of (SId, SId) -> pure ()
                    _          -> conv l b b'

  conv l (coe l a a' (Trans Set a b a' p (Sym Set a' b p')) t) t'
  convSp l sp sp'

convExfalso :: Lvl -> Ty -> Ty -> Spine -> Spine -> IO ()
convExfalso l a a' sp sp' = case (sp, sp') of
  (SId, SId) -> pure ()
  _          -> conv l a a' >> convSp l sp sp'

-- | Compare rigid-s which are known to be relevant.
convRigidRel :: Lvl -> RigidHead -> Spine -> RigidHead -> Spine -> IO ()
convRigidRel l h sp h' sp' = case (h, h') of
  (RHLocalVar x _, RHLocalVar x' _   ) -> convEq x x' >> convSp l sp sp'
  (RHPostulate x , RHPostulate x'    ) -> convEq x x' >> convSp l sp sp'
  (RHCoe a b p t , RHCoe a' b' p' t' ) -> convCoe l a b p t sp a' b' p' t' sp'
  (RHExfalso a p , RHExfalso a' p'   ) -> convExfalso l a a' sp sp'
  _                                    -> throwIO Diff

conv :: Lvl -> Val -> Val -> IO ()
conv l t u = do
  let go = conv l
      {-# inline go #-}

      goBind a t u = do
        let v = Var l a
        conv (l + 1) (t $$ v) (u $$ v)
      {-# inline goBind #-}

      guardP hl (cont :: IO ()) = case hl of
        P -> pure ()
        _ -> cont
      {-# inline guardP #-}

  t <- forceAll l t
  u <- forceAll l u
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

    (Lam hl _ _ _ t , Lam _ _ _ a t'  ) -> guardP hl $ goBind a t t'
    (Pair hl t u    , Pair _ t' u'    ) -> guardP hl do {go t t'; go u u'}
    (Lam hl _ i a t , t'              ) -> guardP hl $ goBind a t (Cl \u -> app t' u i)
    (t              , Lam hl _ i a t' ) -> guardP hl $ goBind a (Cl \u -> app t u i) t'
    (Pair hl t u    , t'              ) -> guardP hl do {go t (proj1 t'); go u (proj2 t')}
    (t              , Pair hl t' u'   ) -> guardP hl do {go (proj1 t) t'; go (proj2 t) u'}

    -- non-canonical
    ------------------------------------------------------------

    (Irrelevant , _         ) -> pure ()
    (_          , Irrelevant) -> pure ()

    (Flex h sp, Flex h' sp') -> flexRelevance l h sp >>= \case
      RIrr       -> pure ()
      RBlockOn x -> throwIO $ BlockOn x
      RRel       -> convFlexRel l h sp h' sp'

    (Flex h sp, _) -> flexRelevance l h sp >>= \case
      RIrr       -> pure ()
      RBlockOn x -> throwIO $  BlockOn x
      RRel       -> throwIO $! BlockOn (headMeta h)

    (_ , Flex h sp) -> flexRelevance l h sp >>= \case
      RIrr       -> pure ()
      RBlockOn x -> throwIO $  BlockOn x
      RRel       -> throwIO $! BlockOn (headMeta h)

    (Rigid h sp, Rigid h' sp') -> rigidRelevance l h sp >>= \case
      RIrr       -> pure ()
      RBlockOn x -> throwIO $ BlockOn x
      RRel       -> convRigidRel l h sp h' sp'

    (Rigid h sp, _) -> rigidRelevance l h sp >>= \case
      RIrr       -> pure ()
      RBlockOn x -> throwIO $ BlockOn x
      RRel       -> throwIO Diff

    (_, Rigid h' sp') -> rigidRelevance l h' sp' >>= \case
      RIrr       -> pure ()
      RBlockOn x -> throwIO $ BlockOn x
      RRel       -> throwIO Diff

    -- canonical mismatch is always a failure, because we don't yet
    -- have inductive data in Prop, so mismatch is only possible in Set.
    --------------------------------------------------------------------------------

    (a, b) -> throwIO Diff


-- Quoting
--------------------------------------------------------------------------------

quoteSp :: Lvl -> UnfoldOpt -> S.Tm -> Spine -> S.Tm
quoteSp l opt hd sp = let
  go         = quote l opt; {-# inline go #-}
  goSp       = quoteSp l opt hd; {-# inline goSp #-}
  in case sp of
    SId               -> hd
    SApp t u i        -> S.App (goSp t) (go u) i
    SProj1 t          -> S.Proj1 (goSp t)
    SProj2 t          -> S.Proj2 (goSp t)
    SProjField t x n  -> S.ProjField (goSp t) x n
    -- SCoeSrc a b p t   -> S.Coe (goSp a) (go b) (go p) (go t)
    -- SCoeTgt a b p t   -> S.Coe (go a) (goSp b) (go p) (go t)
    -- SCoeTrans a b p t -> S.Coe (go a) (go b) (go p) (goSp t)
    -- SEqSet a t u      -> S.Eq (goSp a) (go t) (go u)
    -- SEqLhs a t u      -> S.Eq (go a) (goSp t) (go u)
    -- SEqRhs a t u      -> S.Eq (go a) (go t) (goSp u)

quote :: Lvl -> UnfoldOpt -> Val -> S.Tm
quote l opt t = let
  go         = quote l opt; {-# inline go #-}
  goSp       = quoteSp l opt; {-# inline goSp #-}
  goBind a t = quote (l + 1) opt (t $$ Var l a); {-# inline goBind #-}

  goFlexHead = \case
    FHMeta x            -> S.Meta x
    -- FHCoeRefl x a b p t -> S.Coe (go a) (go b) (go p) (go t)

  goRigidHead = \case
    RHLocalVar x _ -> S.LocalVar (lvlToIx l x)
    RHPostulate x  -> S.Postulate x
    RHCoe a b p t  -> S.Coe (go a) (go b) (go p) (go t)
    RHExfalso a t  -> S.Exfalso (go a) (go t)

  goUnfoldHead ~v = \case
    UHSolvedMeta x -> S.Meta x
    UHTopDef x     -> S.TopDef (coerce v) x

  cont :: Val -> S.Tm
  cont = \case
    Flex h sp         -> goSp (goFlexHead h) sp
    Rigid h sp        -> goSp (goRigidHead h) sp
    Unfold h sp v     -> goSp (goUnfoldHead v h) sp
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
    UnfoldAll   -> cont (runIO (forceAll l t))
    UnfoldMetas -> cont (runIO (forceMetas l t))
    UnfoldNone  -> cont (runIO (force l t))

eval0 :: S.Tm -> Val
eval0 = eval 0 ENil
{-# inline eval0 #-}

quote0 :: UnfoldOpt -> Val -> S.Tm
quote0 opt = quote 0 opt
{-# inline quote0 #-}

nf0 :: UnfoldOpt -> S.Tm -> S.Tm
nf0 opt t = quote0 opt (eval0 t)
{-# inline nf0 #-}
