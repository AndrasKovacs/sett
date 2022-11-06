
module Unification where

import Common

import IO
import Control.Exception

import qualified Data.IntMap as IM
import qualified Data.Ref.F as RF
import Lens.Micro.Platform

import Values
import Evaluation
import qualified ElabState as ES
-- import Errors
import qualified Syntax as S
import Pretty

----------------------------------------------------------------------------------------------------

-- | Bump the `Lvl` and get a fresh variable.
newVar :: Ty -> Name -> (LvlArg => S.NamesArg => Val -> a) -> LvlArg => S.NamesArg => a
newVar a x cont =
  let v = Var ?lvl a in
  let ?lvl = ?lvl + 1 in
  let ?names = show x : ?names in
  seq ?lvl (cont v)
{-# inline newVar #-}

----------------------------------------------------------------------------------------------------

-- TODO: optimize
freshMeta :: LvlArg => S.LocalsArg => GTy -> IO S.Tm
freshMeta (G a fa) = do
  let closed   = eval0 $ S.closeTy $ quote a
  let ~fclosed = eval0 $ S.closeTy $ quote fa
  m <- ES.newMeta (G closed fclosed)
  pure $ S.InsertedMeta m ?locals

freshMeta0 :: GTy -> IO S.Tm
freshMeta0 a = do
  m <- ES.newMeta a
  pure $ S.InsertedMeta m S.LEmpty

catchUE :: IO a -> IO a -> IO a
catchUE act handle = act `catch` \(_ :: UnifyEx) -> handle
{-# inline catchUE #-}

----------------------------------------------------------------------------------------------------
-- Partial substitution
----------------------------------------------------------------------------------------------------

type AllowPruning = Bool
type AllowPruningArg = (?allowPruning :: AllowPruning)

-- TODO: use mutable array instead
data PartialSub = PSub {
    partialSubDomVars      :: Vars           -- Identity env from Γ to Γ, serves as the list of Γ types.
                                             -- We need this when we want to evaluate the result term of
                                             -- partial substitution.
  , partialSubOcc          :: Maybe MetaVar  -- optional occurs check
  , partialSubDom          :: Lvl            -- size of Γ
  , partialSubCod          :: Lvl            -- size of Δ
  , partialSubSub          :: IM.IntMap Val  -- Map from Δ vars to Γ values. A var which is not
                                             -- in the map is mapped to VUndefined.
  , partialSubAllowPruning :: AllowPruning   -- Is pruning allowed during partial substitution.
  }
makeFields ''PartialSub


-- showPSub :: PartialSub -> String
-- showPSub (PSub domvars occ dom cod sub allowpruning) = _


-- | Evaluate something in the domain of the `PartialSub`.
evalInDom :: PartialSub -> S.Tm -> Val
evalInDom psub t = let ?env = psub^.domVars; ?lvl = psub^.dom in eval t

-- | lift : (σ : PSub Γ Δ) → PSub (Γ, x : A[σ]) (Δ, x : A)
--   Note: gets A[σ] as Ty input, not A!
lift :: PartialSub -> Ty -> PartialSub
lift (PSub idenv occ dom cod sub allowpr) ~asub =
  let var = Var' dom asub True
  in PSub (EDef idenv var) occ (dom + 1) (cod + 1)
          (IM.insert (coerce cod) var sub) allowpr

-- | Compute a value under a partial subsitution to head form, leave unfoldings
--   in place.
forceWithPSub :: PartialSub -> Val -> IO Val
forceWithPSub psub topt = do
  let ?lvl = psub^.cod
  let go = forceWithPSub psub; {-# inline go #-}
  case topt of

    Flex h sp _  -> case h of

      FHMeta m ->
        if Just m == psub^.occ then
          pure $ Magic MetaOccurs
        else unblock m topt \v _ ->
          go $! spine v sp

      FHCoe x a b p t -> unblock x topt \_ _ -> do
        a <- go a
        b <- go b
        t <- go t
        go $! coe a b p t

    FlexEq x a t u -> unblock x topt \_ _ -> do
      a <- go a
      t <- go t
      u <- go u
      go $! eq a t u

    Rigid (RHLocalVar (Lvl x) _ inDom) sp _ -> do
      if inDom then
        pure topt
      else case IM.lookup x (psub^.sub) of
        Nothing -> pure $ Magic Undefined
        Just v  -> go $! spine v sp
    t ->
      pure t

-- | Compute a value under a partial substitution to head form while
--   also computing all unfoldings.
forceAllWithPSub :: PartialSub -> Val -> IO Val
forceAllWithPSub psub topt = do
  let ?lvl = psub^.cod
  let go = forceAllWithPSub psub; {-# inline go #-}
  case topt of

    Flex h sp _  -> case h of

      FHMeta m ->
        if Just m == psub^.occ then
          pure $ Magic MetaOccurs
        else unblock m topt \v _ ->
          go $! spine v sp

      FHCoe x a b p t -> unblock x topt \_ _ -> do
        a <- go a
        b <- go b
        t <- go t
        go $! coe a b p t

    FlexEq x a t u -> unblock x topt \_ _ -> do
      a <- go a
      t <- go t
      u <- go u
      go $! eq a t u

    Rigid (RHLocalVar (Lvl x) _ inDom) sp _ ->
      if inDom then
        pure topt
      else case IM.lookup x (psub^.sub) of
        Nothing -> pure $ Magic Undefined
        Just v  -> go $! spine v sp

    Unfold _ _ v _   -> go v
    TraceEq _ _ _ v  -> go v
    UnfoldEq _ _ _ v -> go v
    t                -> pure t

data ApproxOccursEx = ApproxOccursEx
  deriving Show
instance Exception ApproxOccursEx

approxOccursInMeta' :: MetaVar -> MetaVar -> IO ()
approxOccursInMeta' occ m = ES.isFrozen m >>= \case
  True -> pure ()
  _    -> ES.readMeta m >>= \case
    ES.MEUnsolved{} -> do
      when (occ == m) (throwIO ApproxOccursEx)
    ES.MESolved cache t tv a -> do
      cached <- RF.read cache
      when (cached /= occ) do
        approxOccurs occ t
        RF.write cache occ

approxOccursInMeta :: MetaVar -> MetaVar -> IO Bool
approxOccursInMeta occ m =
  (False <$ approxOccursInMeta' occ m)
  `catch` \(_ :: ApproxOccursEx) -> pure True

approxOccurs :: MetaVar -> S.Tm -> IO ()
approxOccurs occ t = do
  let go = approxOccurs occ; {-# inline go #-}
      goMeta = approxOccursInMeta' occ; {-# inline goMeta #-}

  case t of
    S.LocalVar{}       -> pure ()
    S.HideTopDef{}     -> pure ()
    S.Lam _ _ a t      -> go a >> go t
    S.App t u i        -> go t >> go u
    S.Pair t u         -> go t >> go u
    S.ProjField t _ _  -> go t
    S.Proj1 t          -> go t
    S.Proj2 t          -> go t
    S.Pi x i a b       -> go a >>  go b
    S.Sg x a b         -> go a >>  go b
    S.HidePostulate{}  -> pure ()
    S.InsertedMeta m _ -> goMeta m
    S.Meta m           -> goMeta m
    S.Let x a t u      -> go a >> go t >> go u
    S.Set{}            -> pure ()
    S.Prop{}           -> pure ()
    S.Top{}            -> pure ()
    S.Tt{}             -> pure ()
    S.Bot{}            -> pure ()
    S.EqSym{}          -> pure ()
    S.CoeSym{}         -> pure ()
    S.ReflSym{}        -> pure ()
    S.SymSym{}         -> pure ()
    S.TransSym{}       -> pure ()
    S.ApSym{}          -> pure ()
    S.ExfalsoSym{}     -> pure ()
    S.PropextSym{}     -> pure ()
    S.Magic{}          -> pure ()

psubstSp :: PartialSub -> S.Tm -> Spine -> IO S.Tm
psubstSp psub hd sp = do
  let ?lvl = psub^.cod
  let goSp = psubstSp psub hd; {-# inline goSp #-}
      go   = psubst psub;      {-# inline go #-}
  case sp of
    SId                 -> pure hd
    SApp t u i          -> S.App <$!> goSp t <*!> go u <*!> pure i
    SProj1 t            -> S.Proj1 <$!> goSp t
    SProj2 t            -> S.Proj2 <$!> goSp t
    SProjField t tv a n -> S.ProjField <$!> goSp t <*!> pure (projFieldName tv a n) <*!> pure n

psubst :: PartialSub -> Val -> IO S.Tm
psubst psub topt = do

  let ?lvl = psub^.cod

  let goSp     = psubstSp psub; {-# inline goSp #-}
      goSpFlex = psubstSp (psub & allowPruning .~ False); {-# inline goSpFlex #-}
      go       = psubst psub; {-# inline go #-}
      goFlex   = psubst (psub & allowPruning .~ False); {-# inline goFlex #-}

      goBind :: Val -> Closure -> (S.Tm -> S.Tm -> S.Tm) -> IO S.Tm
      goBind a t k = do
        (!a, ~va) <- psubst' psub a
        t <- psubst (lift psub va) (appClIn (?lvl + 1) t (Var ?lvl va))
        pure $! k a t
      {-# inline goBind #-}

      goUnfolding unf act =
        catch @UnifyEx act (\_ -> go unf)

      goRigid h sp = do
        h <- case h of
          RHLocalVar x a True  -> let ?lvl = psub^.dom in pure (S.LocalVar (lvlToIx x))
          RHLocalVar x a False -> impossible
          RHPostulate x a      -> pure (S.Postulate x a)
          RHExfalso a p        -> S.Exfalso <$!> go a <*!> go p
          RHCoe a b p t        -> S.Coe <$!> go a <*!> go b <*!> go p <*!> go t
          RHRefl a t           -> S.Refl <$!> go a <*!> go t
          RHSym a x y p        -> S.Sym <$!> go a <*!> go x <*!> go y <*!> go p
          RHTrans a x y z p q  -> S.Trans <$!> go a <*!> go x <*!> go y <*!> go z <*!> go p <*!> go q
          RHAp a b f x y p     -> S.Ap <$!> go a <*!> go b <*!> go f <*!> go x <*!> go y <*!> go p
          RHPropext p q f g    -> S.Propext <$!> go p <*!> go q <*!> go f <*!> go g
        goSp h sp

      goUnfold h sp = do
        h <- case h of
          UHSolvedMeta m   -> case psub^.occ of
                                Nothing  -> pure (S.Meta m)
                                Just occ -> do approxOccursInMeta occ m
                                               pure (S.Meta m)
          UHTopDef x t tty -> pure (S.TopDef x t tty)
          UHCoe a b p t    -> S.Coe <$!> goFlex a <*!> goFlex b <*!> goFlex p <*!> goFlex t
        goSpFlex h sp

      goFlex' h sp = case h of
        FHMeta m -> do
          goSpFlex (S.Meta m) sp `catch` \(_ :: UnifyEx) -> do

            debug ["PRUNE", showTm0 $ quoteIn (psub^.cod) (Flex (FHMeta m) sp Set)]
            a <- ES.metaType m
            debug ["ORIG TY", showTm0 $ quote0WithOpt UnfoldEverything a]

            (m, sp) <- prune psub m sp

            debug ["PRUNED", showTm0 $ quoteIn (psub^.cod) (Flex (FHMeta m) sp Set)]
            a <- ES.metaType m
            debug ["PRUNED TY", showTm0 $ quote0WithOpt UnfoldEverything a]

            goSp (S.Meta m) sp
        FHCoe x a b p t -> do
          h <- S.Coe <$!> goFlex a <*!> goFlex b <*!> goFlex p <*!> goFlex t
          goSpFlex h sp


  ftopt <- forceWithPSub psub topt
  debug ["PSUBST", showTm0 $ quoteIn (psub^.cod) topt, showTm0 $ quoteIn (psub^.cod) ftopt ]
  case ftopt of
    Rigid h sp _       -> goRigid h sp
    RigidEq a t u      -> S.Eq <$!> go a <*!> go t <*!> go u
    Flex h sp _        -> goFlex' h sp
    FlexEq x a t u     -> S.Eq <$!> go a <*!> go t <*!> go u
    Unfold uh sp unf _ -> goUnfolding unf $ goUnfold uh sp
    TraceEq a t u unf  -> goUnfolding unf $ S.Eq <$!> goFlex a <*!> goFlex t <*!> goFlex u
    UnfoldEq a t u unf -> goUnfolding unf $ S.Eq <$!> goFlex a <*!> goFlex t <*!> goFlex u
    Set                -> pure S.Set
    Pi x i a b         -> goBind a b (S.Pi x i)
    Lam x i a t        -> goBind a t (S.Lam x i)
    SgPrim x a b       -> goBind a b (S.Sg x)
    Pair t u           -> S.Pair <$!> go t <*!> go u
    Prop               -> pure S.Prop
    Top                -> pure S.Top
    Tt                 -> pure S.Tt
    Bot                -> pure S.Bot
    Magic m            -> throwIO CantPartialSubst

psubst' :: PartialSub -> Val -> IO (S.Tm, Val)
psubst' psub t = do
  t <- psubst psub t
  let ~vt = evalInDom psub t
  pure (t, vt)
{-# inline psubst' #-}

----------------------------------------------------------------------------------------------------
-- Eta-expansion
----------------------------------------------------------------------------------------------------

metaExpansion' :: LvlArg => EnvArg => S.LocalsArg => Ty -> RevSpine -> IO S.Tm
metaExpansion' a sp = do
  let go = metaExpansion'; {-# inline go #-}

      bind x a qa k = do
        let var     = Var ?lvl a
        let ?lvl    = ?lvl + 1
        let ?env    = EDef ?env
        let ?locals = S.LBind ?locals x qa
        k var
      {-# inline bind #-}

  a <- forceSet a
  case (a, sp) of
    (a, RSId) ->
      freshMeta (gjoin a)
    (Pi x i a b, RSApp t _ sp) -> do
      let qa = quote a
      bind x a qa \var -> S.Lam x i qa <$!> go (b $$ var) sp
    (Sg x a b, RSProj1 sp) -> do
      fst <- go a sp
      S.Pair fst <$!> freshMeta (gjoin (b (eval fst)))
    (Sg x a b, RSProj2 sp) -> do
      fst <- freshMeta (gjoin a)
      S.Pair fst <$!> go (b (eval fst)) sp
    (a, RSProjField _  _  0 sp) ->
      go a (RSProj1 sp)
    (a, RSProjField tv ta n sp) ->
      go a (RSProj2 (RSProjField VUndefined VUndefined (n - 1) sp))
    _ ->
      impossible

metaExpansion :: Ty -> RevSpine -> IO S.Tm
metaExpansion a sp = do
  let ?lvl = 0; ?env = ENil; ?locals = S.LEmpty
  metaExpansion' a sp

-- | Eta-expand a meta enough so that all projections disappear from the given spine.
--   Does nothing if the spine doesn't contain projections.
etaExpandMeta :: MetaVar -> Spine -> IO (MetaVar, Spine)
etaExpandMeta m sp | not (hasProjection sp) =
  pure (m, sp)
etaExpandMeta m sp = do
  a <- ES.unsolvedMetaType m
  sol <- metaExpansion a (reverseSpine sp)
  let vsol = eval0 sol
  ES.solve m sol vsol
  case spineIn 0 vsol sp of
    Flex (FHMeta m) sp _ -> pure (m, sp)
    _                    -> impossible


----------------------------------------------------------------------------------------------------
-- Pruning
----------------------------------------------------------------------------------------------------

{-
1. Eta-expand meta to get rid of projections.

2. Create a `PruneSp` from the spine. This only contains the "shape" of parts to
   prune, nothing else. We can fail at this point if the spine contains some
   non-prunable things. Only pairs, lambdas and rigid neutrals are prunable.

3. Compute the pruned type by direct recursion on the meta type and the
   `PruneSp`. This can produce a type which contains `Undefined`-s. At the same
   time we define back-and forth maps to the pruned type. We propagate
   `Undefined`-s in these maps.

4. Create a fresh meta with the pruned type, transport to original type,then
   solve the original meta with it. We need to check here that the solution is
   fully defined. For this, we use `psubst` to quote the solution
   value. Unfortunately we can't use vanilla `quote` here because it preserves
   Undefined without throwing any error. So we mostly just copy code from
   `quote` to `partialQuote` which does ensure that the output is fully defined.

TODO (long term): handle pruning contractible types! In that case we should insert
  the unique value instead of Undefined.

-}

-- | Structure pointing to parts to prune.
data PruneVal = PLam PruneVal | PPair PruneVal PruneVal | PKeep | PDrop

-- | Structure pointing to parts to prune.
data PruneSp = PId | PApp PruneVal PruneSp

mkPPair :: PruneVal -> PruneVal -> PruneVal
mkPPair PKeep PKeep = PKeep
mkPPair PDrop PDrop = PDrop
mkPPair p1    p2    = PPair p1 p2

mkPLam :: PruneVal -> PruneVal
mkPLam PKeep = PKeep
mkPLam PDrop = PDrop
mkPLam p     = PLam p

mkPruneVal :: PartialSub -> Val -> IO PruneVal
mkPruneVal psub t = forceAllWithPSub psub t >>= \case
  Pair t u        -> mkPPair <$!> mkPruneVal psub t <*!> mkPruneVal psub u
  Lam _ _ a t     -> do (_, ~a') <- psubst' psub a
                        let ?lvl = psub^.cod
                        mkPLam <$!> mkPruneVal (lift psub a') (appClIn (?lvl + 1) t (Var ?lvl a))
  Rigid{}         -> pure PKeep
  Magic Undefined -> pure PDrop
  _               -> throwIO CantPruneSpine

mkPruneSp :: PartialSub -> RevSpine -> IO PruneSp
mkPruneSp psub = \case
  RSId         -> pure PId
  RSApp t i sp -> PApp <$!> mkPruneVal psub t <*!> mkPruneSp psub sp
  _            -> impossible

prArgTy :: LvlArg => PruneVal -> Ty -> Ty
prArgTy p a = case (p, runIO (forceSet a)) of
  (PKeep      , a              ) -> a
  (PDrop      , a              ) -> Top
  (PLam p     , Pi x i a b     ) -> Pi x i a $ Cl \x -> prArgTy p (b $$ x)
  (PPair p1 p2, Sg x a b       ) -> Sg x (prArgTy p1 a) \x ->
                                    prArgTy p2 (b (fromPrArg p1 a x))
  (_          , VUndefined     ) -> VUndefined
  _                              -> impossible


toPrArg :: LvlArg => PruneVal -> Ty -> Val -> Val
toPrArg p a t = case (p, runIO (forceSet a)) of
  (PKeep      , a              ) -> t
  (PDrop      , a              ) -> Tt
  (PLam p     , Pi x i a b     ) -> Lam x i a $ Cl \x -> toPrArg p (b $$ x) (app t x i)
  (PPair p1 p2, Sg x a b       ) -> let t1 = proj1 t; t2 = proj2 t in
                                    Pair (toPrArg p1 a t1) (toPrArg p2 (b t1) t2)
  (_          , VUndefined     ) -> VUndefined
  _                              -> impossible

fromPrArg :: LvlArg => PruneVal -> Ty -> Val -> Val
fromPrArg p a t = case (p, runIO (forceSet a)) of
  (PKeep      , a              ) -> t
  (PDrop      , a              ) -> VUndefined
  (PLam p     , Pi x i a b     ) -> Lam x i a $ Cl \x -> fromPrArg p (b $$ x) (app t x i)
  (PPair p1 p2, Sg x a b       ) -> let t1 = proj1 t; t2 = proj2 t; fst = fromPrArg p1 a t1 in
                                    Pair fst (fromPrArg p2 (b fst) t2)
  (_          , VUndefined     ) -> VUndefined
  _                              -> impossible

prTy :: LvlArg => PruneSp -> Ty -> Ty
prTy p a = case (p, runIO (forceSet a)) of
  (PId, a) ->
    a
  (PApp p sp, Pi x i a b) ->
    Pi x i (prArgTy p a) $ Cl \x -> prTy sp (b $$ fromPrArg p a x)
  (_, VUndefined) ->
    VUndefined
  _ ->
    impossible

fromPrTy :: LvlArg => PruneSp -> Ty -> Val -> Val
fromPrTy p a t = case (p, runIO (forceSet a)) of
  (PId, a) ->
    t
  (PApp p sp, Pi x i a b) ->
    Lam x i a $ Cl \x -> fromPrTy sp (b $$ x) (app t (toPrArg p a x) i)
  (_, VUndefined) ->
    VUndefined
  _ ->
    impossible

prTy0     = let ?lvl = 0 in prTy
fromPrTy0 = let ?lvl = 0 in fromPrTy

-- | Prune dependencies from a metavar, solve it with pruned solution,
--   return new meta and spine. TODO: review.
prune :: PartialSub -> MetaVar -> Spine -> IO (MetaVar, Spine)
prune psub m sp = do
  unless (psub^.allowPruning) (throwIO PruningNotAllowed)
  (m, sp) <- etaExpandMeta m sp
  psp     <- mkPruneSp psub (reverseSpine sp)
  a       <- ES.unsolvedMetaType m
  pra     <- pure $! prTy0 psp a
  qpra    <- partialQuote0 pra
  sol     <- fromPrTy0 psp a . eval0 <$!> freshMeta0 (gjoin pra)
  qsol    <- partialQuote0 sol
  ES.solve m qsol sol
  case spine0 sol sp of
    Flex (FHMeta m) sp _ -> pure (m, sp)
    _                    -> impossible


partialQuoteSp :: LvlArg => S.NamesArg => S.Tm -> Spine -> IO S.Tm
partialQuoteSp hd sp = let
  go   = partialQuote;      {-# inline go #-}
  goSp = partialQuoteSp hd; {-# inline goSp #-}
  in case sp of
    SId                 -> pure hd
    SApp t u i          -> S.App <$!> goSp t <*!> go u <*!> pure i
    SProj1 t            -> S.Proj1 <$!> goSp t
    SProj2 t            -> S.Proj2 <$!> goSp t
    SProjField t tv x n -> S.ProjField <$!> goSp t <*!> (pure $! projFieldName tv x n) <*!> pure n

-- | Quote a value but ensure that the output contains no `Magic`.
partialQuote :: LvlArg => S.NamesArg => Val -> IO S.Tm
partialQuote t = do
  let
    go         = partialQuote;   {-# inline go #-}
    goSp       = partialQuoteSp; {-# inline goSp #-}

    goBind a x t = newVar a x \v -> partialQuote (t $$ v); {-# inline goBind #-}

    goFlexHead = \case
      FHMeta x        -> pure (S.Meta x)
      FHCoe x a b p t -> S.Coe <$!> go a <*!> go b <*!> go p <*!> go t

    goRigidHead = \case
      RHLocalVar x _ _    -> pure $! S.LocalVar (lvlToIx x)
      RHPostulate x a     -> pure $ S.Postulate x a
      RHCoe a b p t       -> S.Coe <$!> go a <*!> go b <*!> go p <*!> go t
      RHExfalso a t       -> S.Exfalso <$!> go a <*!> go t
      RHPropext p q f g   -> S.Propext <$!> go p <*!> go q <*!> go f <*!> go g
      RHRefl a t          -> S.Refl <$!> go a <*!> go t
      RHSym a x y p       -> S.Sym <$!> go a <*!> go x <*!> go y <*!> go p
      RHTrans a x y z p q -> S.Trans <$!> go a <*!> go x <*!> go y <*!> go z <*!> go p <*!> go q
      RHAp a b f x y p    -> S.Ap <$!> go a <*!> go b <*!> go f <*!> go x <*!> go y <*!> go p

    goUnfoldHead ~v = \case
      UHSolvedMeta x -> pure $ S.Meta x
      UHTopDef x v a -> pure $ S.TopDef x v a
      UHCoe a b p t  -> S.Coe <$!> go a <*!> go b <*!> go p <*!> go t

  force t >>= \case
    Flex h sp a        -> do {h <- goFlexHead h; goSp h sp}
    FlexEq x a t u     -> S.Eq <$!> go a <*!> go t <*!> go u
    Rigid h sp a       -> do {h <- goRigidHead h; goSp h sp}
    RigidEq a t u      -> S.Eq <$!> go a <*!> go t <*!> go u
    Unfold h sp v a    -> do {h <- goUnfoldHead v h; goSp h sp}
    UnfoldEq a t u v   -> S.Eq <$!> go a <*!> go t <*!> go u
    TraceEq a t u v    -> go v
    Pair t u           -> S.Pair <$!> go t <*!> go u
    Lam x i a t        -> S.Lam x i <$!> go a <*!> goBind a x t
    SgPrim x a b       -> S.Sg x <$!> go a <*!> goBind a x b
    Pi x i a b         -> S.Pi x i <$!> go a <*!> goBind a x b
    Set                -> pure S.Set
    Prop               -> pure S.Prop
    Top                -> pure S.Top
    Tt                 -> pure S.Tt
    Bot                -> pure S.Bot
    Magic m            -> throwIO CantPartialQuote

partialQuote0 :: Val -> IO S.Tm
partialQuote0 t = let ?lvl = 0; ?names = [] in partialQuote t

----------------------------------------------------------------------------------------------------
-- Spine solving
----------------------------------------------------------------------------------------------------

mergeSp :: LvlArg => S.Tm -> Spine -> Spine -> IO S.Tm
mergeSp hd sp sp' = case (sp, sp') of
  (SId          , SId          ) -> pure hd
  (SApp t u i   , SApp t' u' _ ) -> S.App <$!> mergeSp hd t t' <*!> merge u u' <*!> pure i
  (SProj1 t     , SProj1 t'    ) -> S.Proj1 <$!> mergeSp hd t t'
  (SProj2 t     , SProj2 t'    ) -> S.Proj2 <$!> mergeSp hd t t'
  (SProjField{} , _            ) -> impossible
  (_            , SProjField{} ) -> impossible
  _                              -> pure $ S.Magic Nonlinear

-- | Take the least upper bound of values where Undefined is bottom and Nonlinear is top.
merge :: LvlArg => Val -> Val -> IO S.Tm
merge topt topu = do

  let guardIrr a act = act >>= \case
        S.Magic Nonlinear -> typeIsProp a >>= \case
          ItsNotProp  -> pure $ S.Magic Nonlinear
          ItsProp     -> pure $! quote topt -- TODO: choose the more defined side?
          IPBlockOn{} -> pure $ S.Magic Nonlinear
          IPMagic{}   -> impossible
        t -> pure t

  case (topt, topu) of

    (Rigid (RHLocalVar x xty _) sp a, Rigid (RHLocalVar x' _ _) sp' _) -> guardIrr a do
      if x == x' then do
        mergeSp (S.LocalVar (lvlToIx x)) sp sp'
      else
        pure $ S.Magic Nonlinear

    (Pair t u, Pair t' u') -> do
      S.Pair <$!> merge t t' <*!> merge u u'

    (Lam x i a t, Lam _ _ _ t') -> do
      let var = Var ?lvl a
      let ?lvl = ?lvl + 1
      S.Lam x i (quote a) <$!> merge (t $$ var) (t' $$ var)

    (Magic m, t) -> case m of
      Nonlinear -> pure $ S.Magic Nonlinear
      Undefined -> pure $! quote t
      _         -> impossible

    (t, Magic m) -> case m of
      Nonlinear -> pure $ S.Magic Nonlinear
      Undefined -> pure $! quote t
      _         -> impossible

    (Lam x i a t, t') -> do
      let var = Var ?lvl a
      let ?lvl = ?lvl + 1
      S.Lam x i (quote a) <$!> merge (t $$ var) (app t' var i)

    (t, Lam x i a t') -> do
      let var = Var ?lvl a
      let ?lvl = ?lvl + 1
      S.Lam x i (quote a) <$!> merge (app t var i) (t' $$ var)

    (Pair t u, t') ->
      S.Pair <$!> merge t (proj1 t') <*!> merge u (proj2 t')

    (t, Pair t' u') ->
      S.Pair <$!> merge (proj1 t) t' <*!> merge (proj2 t) u'

    _ -> impossible

updatePSub :: Lvl -> Val -> PartialSub -> IO PartialSub
updatePSub (Lvl x) t psub = case IM.lookup x (psub^.sub) of
  Nothing -> do
    pure $! (psub & sub %~ IM.insert x t)
  Just t' -> do
    let ?lvl = psub^.dom
    merged <- evalInDom psub <$!> merge t t'
    pure $! (psub & sub %~ IM.insert x merged)

debugRhsSp :: Spine -> String
debugRhsSp sp = go sp [] where
  go SId = id
  go (SApp sp (Var' x _ _) _) = go sp . (' ':) . (show x++)
  go (SProj1 sp) = go sp . (" .1"++)
  go (SProj2 sp) = go sp . (" .2"++)
  go _ = id

invertVal :: Lvl -> PartialSub -> Lvl -> Val -> Spine -> IO PartialSub
invertVal solvable psub param t rhsSp = do

  t <- let ?lvl = param in forceAll t
  case t of

    Tt ->
      pure psub

    Pair t u -> do
      psub <- invertVal solvable psub param t (SProj1 rhsSp)
      invertVal solvable psub param u (SProj2 rhsSp)

    Lam x i a t -> do
      let var  = Var param a
      let ?lvl = param + 1
      invertVal solvable psub ?lvl (t $$ var) (SApp rhsSp var i)

    -- Rigid h (SProj1 sp) rhsty -> do
    --   uf
    --   psub <- invertVal solvable psub param (Rigid h sp _) _
    --   _

    -- TODO: consider passing an *un-psubsted* variable type to solveNestedSp!!!

    Rigid (RHLocalVar x xty _) sp rhsTy -> do
      unless (solvable <= x && x < psub^.cod) (throw CantInvertSpine)

      case (sp, rhsSp) of

        -- optimized shortcut for vanilla variable inversion
        (SId, SId) -> do

          let var = case psub^.domVars of
                EDef _ var -> var
                _          -> impossible

          updatePSub x var psub

        -- general case
        _ -> do
          debug ["PRE", showTm0 $ quoteInWithOpt (psub^.dom) UnfoldNothing xty]
          debug ["PRE", showTm0 $ quoteInWithOpt (psub^.dom) UnfoldEverything xty]
          (_, ~xty) <- psubst' psub xty
          debug ["POST"]
          let psub' = PSub (psub^.domVars) Nothing (psub^.dom) param mempty True
          sol <- solveNestedSp (psub^.cod) psub' xty (reverseSpine sp) (psub^.dom - 1, rhsSp) rhsTy
          res <- updatePSub x (evalInDom psub sol) psub
          pure res

    _ ->
      throwIO CantInvertSpine

-- TODO OPTIMIZE: get domain var types in term form, instead of extracting from meta types
-- by quoting Pi domains.
solveTopSp :: PartialSub -> S.Locals -> Ty -> RevSpine -> Val -> Ty -> IO S.Tm
solveTopSp psub ls a sp rhs rhsty = do

  let go psub ls a sp = solveTopSp psub ls a sp rhs rhsty
      {-# inline go #-}

  let ?lvl    = psub^.dom
      ?env    = psub^.domVars
      ?locals = ls

  a <- forceSet a

  case (a, sp) of

    (a, RSId) -> do
      _ <- psubst psub rhsty -- TODO optimize: somehow check for nonlinearity
      psubst psub rhs

    (Pi x i a b, RSApp u _ t) -> do
      debug ["FOO"]
      let var   = Var' ?lvl a True
      let qa    = quote a
      let ?lvl  = ?lvl + 1
      psub  <- pure (psub & domVars %~ (`EDef` var) & dom .~ ?lvl)
      ls    <- pure (S.LBind ls x qa)
      psub  <- invertVal 0 psub (psub^.cod) u SId
      debug ["BAR"]
      S.Lam x i qa <$!> go psub ls (b $$ var) t

    (Sg x a b, RSProj1 t) -> do
      fst <- go psub ls a t
      let ~vfst = eval fst
      snd <- freshMeta (gjoin (b vfst))
      pure $ S.Pair fst snd

    (Sg x a b, RSProj2 t) -> do
      fst <- freshMeta (gjoin a)
      let ~vfst = eval fst
      snd <- go psub ls (b vfst) t
      pure $ S.Pair fst snd

    -- TODO: do it properly
    (a, RSProjField _ _ n t) ->
      case n of
        0 -> go psub ls a (RSProj1 t)
        n -> go psub ls a (RSProj2 (RSProjField VUndefined VUndefined (n - 1) t))

    _ -> impossible

solveNestedSp :: Lvl -> PartialSub -> Ty -> RevSpine -> (Lvl, Spine) -> Ty -> IO S.Tm
solveNestedSp solvable psub a sp (!rhsVar, !rhsSp) rhsty = do

  let go psub a sp = solveNestedSp solvable psub a sp (rhsVar, rhsSp) rhsty
      {-# inline go #-}

  let ?lvl = psub^.dom
      ?env = psub^.domVars

  a <- forceSet a
  case (a, sp) of

    (a, RSId) -> do
      _ <- psubst psub rhsty -- TODO optiimze: check nonlinearity
      psubstSp psub (S.LocalVar (lvlToIx rhsVar)) rhsSp

    (Pi x i a b, RSApp u _ t) -> do
      let var   = Var' ?lvl a True
      let qa    = quote a
      let ?lvl  = ?lvl + 1
      psub  <- pure (psub & domVars %~ (`EDef` var) & dom .~ ?lvl)
      psub  <- invertVal solvable psub (psub^.cod) u SId
      S.Lam x i qa <$!> go psub (b $$ var) t

    (Sg x a b, RSProj1 t) ->
      S.Pair <$!> go psub a t <*!> pure (S.Magic Undefined)

    (Sg x a b, RSProj2 t) ->
      S.Pair (S.Magic Undefined) <$!> go psub (b (Magic Undefined)) t

    (a, RSProjField tv tty n t) ->
      case n of
        0 -> go psub a (RSProj1 t)
        n -> go psub a (RSProj2 (RSProjField tv tty (n - 1) t))

    _ -> impossible

-- | Solve (?x sp ?= rhs : A).
solve :: LvlArg => UnifyStateArg => S.NamesArg => MetaVar -> Spine -> Val -> Ty -> IO ()
solve x sp rhs rhsty = do

  debug ["SOLVE", showTm' (quote (Flex (FHMeta x) sp rhsty)), showTm' (quote rhs)]

  ES.isFrozen x >>= \case
    True  -> throwIO $ CantSolveFrozenMeta x
    False -> pure ()

  let goRelevant = do

        case ?unifyState of
          USRigid{} -> pure ()
          USFull    -> pure ()
          _         -> throwIO CantSolveMetaInNonRigidState

        a <- ES.unsolvedMetaType x
        -- debug ["solve", showTm' (quote (Flex (FHMeta x) sp rhsty)), showTm' (quote rhs)]
        sol <- solveTopSp (PSub ENil (Just x) 0 ?lvl mempty True)
                          S.LEmpty a (reverseSpine sp) rhs rhsty
        ES.solve x sol (eval0 sol)

      goIrrelevant = do
        metaCxtSize <- ES.nextMeta

        catchUE
          (do a <- ES.unsolvedMetaType x
              sol <- solveTopSp (PSub ENil (Just x) 0 ?lvl mempty False)
                                S.LEmpty a (reverseSpine sp) rhs rhsty
              ES.solve x sol (eval0 sol))

          -- clean up unnecessary eta-expansion metas
          (do ES.resetMetaCxt metaCxtSize)


  typeIsProp rhsty >>= \case
    ItsNotProp  -> goRelevant
    IPBlockOn{} -> goRelevant -- TODO: postpone
    ItsProp     -> goIrrelevant
    IPMagic{}   -> impossible

solveEtaShort :: LvlArg => UnifyStateArg => S.NamesArg => MetaVar -> Spine -> Val -> Ty -> IO ()
solveEtaShort m sp rhs rhsty =
  catchUE (solve m sp rhs rhsty)
          (unifyEtaLong m sp rhs rhsty)

intersect :: LvlArg => UnifyStateArg => MetaVar -> Spine -> MetaVar -> Spine -> Ty -> IO ()
intersect = uf -- TODO

unifyEtaLong :: LvlArg => UnifyStateArg => S.NamesArg => MetaVar -> Spine -> Val -> Ty -> IO ()
unifyEtaLong m sp rhs rhsty = forceAll rhs >>= \case
  Lam x i a t -> do
    newVar a x \v -> unifyEtaLong m (SApp sp v i) (t $$ v) (appTy rhsty v)
  Pair t u -> do
    unifyEtaLong m (SProj1 sp) t (proj1Ty rhsty)
    unifyEtaLong m (SProj2 sp) u (proj2Ty rhsty t)
  Flex (FHMeta m') sp' _ ->
    if m == m' then unifySp sp sp' -- TODO: intersect
               else unifyMetaMeta m sp m' sp' rhsty
  rhs ->
    solve m sp rhs rhsty

-- | Try to unify when the sides are headed by different metas. We only retry in case of inversion
--   failure because we can't backtrack from destructive updates.
unifyMetaMeta :: LvlArg => UnifyStateArg => S.NamesArg => MetaVar -> Spine -> MetaVar -> Spine -> Ty -> IO ()
unifyMetaMeta m sp m' sp' ty =
  catch
    (solve m sp (Flex (FHMeta m') sp' ty) ty)
    (\case
        CantInvertSpine -> solve m' sp' (Flex (FHMeta m) sp ty) ty
        e               -> throwIO e)

----------------------------------------------------------------------------------------------------
-- Unification
----------------------------------------------------------------------------------------------------

unifyEq :: Eq a => a -> a -> IO ()
unifyEq x y = when (x /= y) $ throwIO CantUnify
{-# inline unifyEq #-}

-- TODO: handle FieldProj vs Proj1/2
unifySp :: LvlArg => UnifyStateArg => S.NamesArg => Spine -> Spine -> IO ()
unifySp sp sp' = case (sp, sp') of
  (SId                , SId                 ) -> pure ()
  (SApp t u i         , SApp t' u' i'       ) -> unifySp t t' >> unify (gjoin u) (gjoin u')
  (SProj1 t           , SProj1 t'           ) -> unifySp t t'
  (SProj2 t           , SProj2 t'           ) -> unifySp t t'
  (SProjField t _ _ n , SProjField t' _ _ n') -> unifySp t t' >> unifyEq n n'
  _                                           -> throwIO CantUnify


unify :: LvlArg => UnifyStateArg => S.NamesArg => G -> G -> IO ()
unify (G topt ftopt) (G topt' ftopt') = do

  let go :: LvlArg => UnifyStateArg => S.NamesArg => G -> G -> IO ()
      go = unify
      {-# inline go #-}

      goJoin :: LvlArg => UnifyStateArg => S.NamesArg => Val -> Val -> IO ()
      goJoin t t' = go (gjoin t) (gjoin t')
      {-# inline goJoin #-}

      goSp :: LvlArg => UnifyStateArg => S.NamesArg => Spine -> Spine -> IO ()
      goSp = unifySp
      {-# inline goSp #-}

      rigid :: Int -> (UnifyStateArg => IO ()) -> IO ()
      rigid n act = let ?unifyState = USRigid n in act
      {-# inline rigid #-}

      flex :: (UnifyStateArg => IO ()) -> IO ()
      flex act = let ?unifyState = USFlex in act
      {-# inline flex #-}

      irr :: (UnifyStateArg => IO ()) -> (UnifyStateArg => IO ())
      irr act = case ?unifyState of
        USIrrelevant -> act
        _            -> catchUE (let ?unifyState = USIrrelevant in act) (pure ())
      {-# inline irr #-}

      full :: (UnifyStateArg => IO ()) -> IO ()
      full act = let ?unifyState = USFull in act
      {-# inline full #-}

      goBind :: UnifyStateArg => Ty -> Name -> Closure -> Closure -> IO ()
      goBind a x t t' =
        newVar a x \v -> unify (gjoin $! (t $$ v)) (gjoin $! (t' $$ v))
      {-# inline goBind #-}

      withRelevance :: Ty -> (UnifyStateArg => IO ()) -> IO ()
      withRelevance a act = typeIsProp a >>= \case
        ItsNotProp   -> act
        IPBlockOn{}  -> act -- TODO: postpone
        IPMagic{}    -> impossible
        ItsProp      -> irr act
      {-# inline withRelevance #-}

      goRH :: UnifyStateArg => RigidHead -> RigidHead -> IO ()
      goRH h h' = case (h, h') of
        (RHLocalVar x _ _ , RHLocalVar x' _ _ ) -> unifyEq x x'
        (RHPostulate x _  , RHPostulate x' _  ) -> unifyEq x x'
        (RHExfalso a p    , RHExfalso a' p'   ) -> goJoin a a' >> irr (goJoin p p')
        (RHCoe a b p t    , RHCoe a' b' p' t' ) -> goJoin a a' >> goJoin b b' >>
                                                   irr (goJoin p p') >> goJoin t t'

        (RHRefl a t    , RHRefl a' t'      ) -> goJoin a a' >> goJoin t t'
        (RHSym a x y p , RHSym a' x' y' p' ) -> goJoin a a' >> goJoin x x' >>
                                                goJoin y y' >> irr (goJoin p p')

        (RHTrans a x y z p q, RHTrans a' x' y' z' p' q') ->
          goJoin a a' >> goJoin x x' >> goJoin y y' >> goJoin z z' >>
          irr (goJoin p p' >> goJoin q q')

        (RHAp a b f x y p, RHAp a' b' f' x' y' p') ->
          goJoin a a' >> goJoin b b' >> goJoin f f' >> goJoin x x' >>
          goJoin y y' >> irr (goJoin p p')

        (RHPropext p q f g, RHPropext p' q' f' g') ->
          goJoin p p' >> goJoin q q' >> irr (goJoin f f' >> goJoin g g')

        _ -> throwIO CantUnify

      goFH :: UnifyStateArg => FlexHead -> Spine -> FlexHead -> Spine -> Ty -> IO ()
      goFH h sp h' sp' a = case (h, h') of
        (FHCoe _ a b p t, FHCoe _ a' b' p' t') ->
          goJoin a a' >> goJoin b b' >> irr (goJoin p p') >> goJoin t t'
        (FHMeta m, FHMeta m') ->
          if m == m' then unifySp sp sp' -- TODO: intersect
                     else unifyMetaMeta m sp m' sp' a
        (FHMeta m, h') -> solve m sp (Flex h' sp' a) a
        (h, FHMeta m') -> solve m' sp' (Flex h sp a) a

      goUnfoldEqs :: Ty -> Val -> Val -> Val -> Ty -> Val -> Val -> Val -> IO ()
      goUnfoldEqs a t u ~v a' t' u' ~v' = do
        let unfold :: UnifyStateArg => IO ()
            unfold = go (G topt v) (G topt' v')

            dontunfold :: UnifyStateArg => IO ()
            dontunfold = goJoin a a' >> goJoin t t' >> goJoin u u'

            retry :: Int -> IO ()
            retry n = case n of 0 -> full unfold
                                n -> rigid (n - 1) unfold

        case ?unifyState of
          USRigid n    -> catchUE (flex dontunfold) (retry n)
          USFlex       -> dontunfold
          USIrrelevant -> dontunfold
          USFull       -> impossible

      lopsidedUnfold :: G -> G -> IO ()
      lopsidedUnfold g g' = case ?unifyState of
        USRigid _    -> go g g'
        USFlex       -> throwIO CantUnify
        USIrrelevant -> throwIO CantUnify
        USFull       -> impossible
      {-# inline lopsidedUnfold #-}

      forceUS :: Val -> IO Val
      forceUS t = case ?unifyState of
        USRigid{} -> forceAllButEq t
        USFull    -> forceAll t
        _         -> force t
      {-# inline forceUS #-}

  ftopt  <- forceUS ftopt
  ftopt' <- forceUS ftopt'

  debug ["unify", showTm' (quote ftopt), showTm' (quote ftopt')]
  -- debug ["unifyV ", show ftopt, show ftopt']
  -- debug ["unifyF", showTm' (quote ftopt), showTm' (quote ftopt'), show ?unifyState]

  case (ftopt, ftopt') of

    -- matching sides
    ------------------------------------------------------------

    (Pi x i a b , Pi x' i' a' b' ) -> unifyEq i i' >> goJoin a a' >> goBind a x b b'
    (Sg x a b   , Sg x' a' b'    ) -> goJoin a a' >> goBind a x (Cl b) (Cl b')
    (Set        , Set            ) -> pure ()
    (Prop       , Prop           ) -> pure ()
    (Top        , Top            ) -> pure ()
    (Bot        , Bot            ) -> pure ()
    (Tt         , Tt             ) -> pure ()

    (Rigid h sp a   , Rigid h' sp' _   ) -> withRelevance a (goRH h h' >> goSp sp sp')
    (Lam x i a t    , Lam _ _ _ t'     ) -> goBind a x t t'
    (Pair t u       , Pair t' u'       ) -> goJoin t t' >> goJoin u u'
    (RigidEq a t u  , RigidEq a' t' u' ) -> goJoin a a' >> goJoin t t' >> goJoin u u'

    (FlexEq _ a t u, FlexEq _ a' t' u') -> do
      goJoin a a' >> goJoin t t' >> goJoin u u' -- approx

    (TraceEq  a t u v, TraceEq  a' t' u' v') -> goUnfoldEqs a t u v a' t' u' v'
    (UnfoldEq a t u v, UnfoldEq a' t' u' v') -> goUnfoldEqs a t u v a' t' u' v'

    (Unfold h sp t a, Unfold h' sp' t' _) -> do

      let dontunfold = case (h, h') of
           (UHSolvedMeta m, UHSolvedMeta m'  ) -> unifyEq m m' >> goSp sp sp'
           (UHTopDef x _ _, UHTopDef x' _ _  ) -> unifyEq x x' >> goSp sp sp'
           (UHCoe a b p t , UHCoe a' b' p' t') -> goJoin a a' >> goJoin b b'
                                                  >> irr (goJoin p p') >> goJoin t t'
                                                  >> goSp sp sp'
           _                                   -> throwIO CantUnify

      let unfold :: UnifyStateArg => IO ()
          unfold = go (G topt t) (G topt' t')

      case ?unifyState of

        USRigid n -> do

          let retry = case n of
                0 -> full unfold
                n -> rigid (n - 1) unfold

          let speculateSp = catchUE (flex (goSp sp sp')) retry

          let speculateCoe a b p t a' b' p' t' =
                catchUE (flex (goJoin a a' >> goJoin b b' >> irr (goJoin p p') >> goJoin t t'
                               >> goSp sp sp'))
                        retry

          case (h, h') of
            (UHSolvedMeta m, UHSolvedMeta m'  ) -> if m == m' then speculateSp else unfold
            (UHTopDef x _ _, UHTopDef x' _ _  ) -> if x == x' then speculateSp else unfold
            (UHCoe a b p t , UHCoe a' b' p' t') -> speculateCoe a b p t a' b' p' t'
            _                                   -> unfold

        USFlex       -> dontunfold
        USIrrelevant -> dontunfold
        USFull       -> impossible


    -- eta-short meta solutions
    ------------------------------------------------------------

    (Flex h sp a, Flex h' sp' _) -> goFH h sp h' sp' a
    (Flex (FHMeta m) sp a, rhs)  -> solveEtaShort m sp rhs a
    (lhs, Flex (FHMeta m) sp a)  -> solveEtaShort m sp lhs a

    -- approximate Eq
    ------------------------------------------------------------

    (FlexEq _ a t u, RigidEq a' t' u')   -> goJoin a a' >> goJoin t t' >> goJoin u u'
    (FlexEq _ a t u, TraceEq a' t' u' _) -> do
      goJoin a a' >> goJoin t t' >> goJoin u u' -- approx

    (RigidEq a t u  , FlexEq _ a' t' u') -> goJoin a a' >> goJoin t t' >> goJoin u u'
    (TraceEq a t u _, FlexEq _ a' t' u') -> do
      goJoin a a' >> goJoin t t' >> goJoin u u' -- approx

    -- lopsided unfold
    ------------------------------------------------------------

    (Unfold _ _ t _, t'  ) -> lopsidedUnfold (G topt t) (G topt' t')
    (t, Unfold _ _ t' _  ) -> lopsidedUnfold (G topt t) (G topt' t')
    (UnfoldEq _ _ _ t, t') -> lopsidedUnfold (G topt t) (G topt' t')
    (t, UnfoldEq _ _ _ t') -> lopsidedUnfold (G topt t) (G topt' t')
    (TraceEq _ _ _ t, t' ) -> lopsidedUnfold (G topt t) (G topt' t')
    (t, TraceEq _ _ _ t' ) -> lopsidedUnfold (G topt t) (G topt' t')

    -- syntax-directed eta
    ------------------------------------------------------------
    (Lam x i a t, t') -> goBind a x t (Cl \u -> app t' u i)
    (t, Lam x' i' a' t') -> goBind a' x' (Cl \u -> app t u i') t'

    (Pair t u, t')  -> go (gjoin t) (gproj1 (G topt' t')) >> go (gjoin u) (gproj2 (G topt' t'))
    (t, Pair t' u') -> go (gproj1 (G topt t)) (gjoin t') >> go (gproj2 (G topt t)) (gjoin u')

    (Tt, _) -> pure ()
    (_, Tt) -> pure ()

    ------------------------------------------------------------

    (Magic m, _) -> impossible
    (_, Magic m) -> impossible
    _            -> throwIO CantUnify
