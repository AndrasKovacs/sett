
module Unification where

import Common

-- import IO
import Control.Exception

import qualified Data.IntMap as IM
-- import qualified Data.IntSet as IS
import qualified Data.Ref.F as RF
import Lens.Micro.Platform

import Values
import Evaluation
import qualified ElabState as ES
-- import Errors
import qualified Syntax as S

import ErrWriter (ErrWriter)
import qualified ErrWriter as EW

----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

data UnifyEx = CantUnify | CantSolveFrozenMeta | CantSolveFlexMeta
  deriving (Eq, Show)
instance Exception UnifyEx

-- | Forcing depending on conversion state.
forceCS :: LvlArg => ConvState -> Val -> IO Val
forceCS cs v = case cs of
  CSFull -> forceAll v
  _      -> force    v
{-# inline forceCS #-}

-- TODO: optimize
freshMeta :: LvlArg => S.LocalsArg => GTy -> IO S.Tm
freshMeta (G a fa) = do
  let closed   = eval0 $ S.closeTy $ quote UnfoldNone a
  let ~fclosed = eval0 $ S.closeTy $ quote UnfoldNone fa
  m <- ES.newMeta (G closed fclosed)
  pure $ S.InsertedMeta m ?locals


----------------------------------------------------------------------------------------------------
-- Partial substitution
----------------------------------------------------------------------------------------------------

type AllowPruning = Bool
type AllowPruningArg = (?allowPruning :: Bool)

data PartialSub = PSub {
    partialSubDomVars      :: Vars           -- Identity env from Γ to Γ, serves as the list of Γ types.
                                             -- We need this when we want to evaluate the result term of
                                             -- partial substitution.
  , partialSubOcc          :: Maybe MetaVar  -- optional occurs check
  , partialSubDom          :: Lvl            -- size of Γ
  , partialSubCod          :: Lvl            -- size of Δ
  , partialSubSub          :: IM.IntMap Val  -- Partial map from Δ vars to Γ values. A var which is not
                                             -- in the map is mapped to a scope error, but note that
                                             -- PSVal-s can contain scope errors as well.
  , partialSubIsLinear     :: Bool           -- Does the sub contain PSNonlinearEntry.
  , partialSubAllowPruning :: Bool           -- Is pruning allowed during partial substitution.
  }
makeFields ''PartialSub

-- | Evaluate something in the domain of the `PartialSub`.
evalInDom :: PartialSub -> S.Tm -> Val
evalInDom psub t = let ?env = psub^.domVars; ?lvl = psub^.dom in eval t

emptyPSub :: Maybe MetaVar -> AllowPruning -> PartialSub
emptyPSub occ allowpr = PSub ENil occ 0 0 mempty True allowpr

-- | lift : (σ : PSub Γ Δ) → PSub (Γ, x : A[σ]) (Δ, x : A)
--   Note: gets A[σ] as Ty input, not A!
lift :: PartialSub -> Ty -> PartialSub
lift (PSub idenv occ dom cod sub linear allowpr) ~asub =
  let var = Var dom asub
  in PSub (EDef idenv var) occ (dom + 1) (cod + 1)
          (IM.insert (coerce cod) var sub) linear allowpr

unlift :: PartialSub -> PartialSub
unlift (PSub (EDef idenv _) occ dom cod sub linear allowpr) =
  PSub idenv occ (dom - 1) (cod - 1)
       (IM.delete (unLvl (cod - 1)) sub) linear allowpr

-- | skip : PSub Γ Δ → PSub Γ (Δ, x : A)
skip :: PartialSub -> PartialSub
skip psub = psub & cod +~ 1

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

    Rigid (RHLocalVar (Lvl x) _ inDom) sp _ ->
      if inDom then
        pure topt
      else case IM.lookup x (psub^.sub) of
        Nothing -> pure $ Magic Undefined
        Just v  -> go $! spine v sp
    t ->
      pure t

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
    S.Lam _ _ _ a t    -> go a >> go t
    S.App t u i        -> go t >> go u
    S.Pair _ t u       -> go t >> go u
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
    S.ElSym{}          -> pure ()
    S.EqSym{}          -> pure ()
    S.CoeSym{}         -> pure ()
    S.ReflSym{}        -> pure ()
    S.SymSym{}         -> pure ()
    S.TransSym{}       -> pure ()
    S.ApSym{}          -> pure ()
    S.ExfalsoSym{}     -> pure ()
    S.Magic{}          -> pure ()

flexPSubstSp :: PartialSub -> S.Tm -> Spine -> ErrWriter S.Tm
flexPSubstSp psub hd sp = do
  let ?lvl = psub^.cod
  let go   = flexPSubst psub; {-# inline go #-}
      goSp = flexPSubstSp psub hd; {-# inline goSp #-}
  case sp of
    SId                 -> pure hd
    SApp t u i          -> S.App <$> goSp t <*> go u <*> pure i
    SProj1 t            -> S.Proj1 <$> goSp t
    SProj2 t            -> S.Proj2 <$> goSp t
    SProjField t tv a n -> S.ProjField <$> goSp t <*> pure (projFieldName tv a n) <*> pure n

flexPSubst :: PartialSub -> Val -> ErrWriter S.Tm
flexPSubst psub t = do

  let ?lvl = psub^.cod

  let go   = flexPSubst psub; {-# inline go #-}
      goSp = flexPSubstSp psub; {-# inline goSp #-}

      goBind a t = do
        (_, a) <- EW.liftIO (psubst' psub a)
        flexPSubst (lift psub a) (t $$ Var ?lvl a)
      {-# inline goBind #-}

      goRigid h sp = do
        h <- case h of
          RHLocalVar x _ True  -> pure (S.LocalVar (lvlToIx x))
          RHLocalVar x _ False -> impossible
          RHPostulate x a      -> pure (S.Postulate x a)
          RHExfalso a p        -> S.Exfalso <$> go a <*> go p
          RHCoe a b p t        -> S.Coe <$> go a <*> go b <*> go p <*> go t
        goSp h sp

      goFlex h sp = do
        h <- case h of
          FHMeta x        -> pure $ S.Meta x
          FHCoe x a b p t -> S.Coe <$> go a <*> go b <*> go p <*> go t
        goSp h sp

      goUnfold h sp = do
        h <- case h of
          UHTopDef x v a ->
            pure $ S.TopDef x v a
          UHSolvedMeta m -> do
            case psub^.occ of
              Nothing  -> pure ()
              Just occ -> EW.liftIOBool (approxOccursInMeta occ m)
            pure $ S.Meta m
          UHCoe a b p t ->
            S.Coe <$> go a <*> go b <*> go p <*> go t
        goSp h sp

      goMagic = \case
        ComputesAway -> pure $ S.Magic ComputesAway
        Undefined    -> S.Magic ComputesAway <$ EW.writeErr
        Nonlinear    -> S.Magic ComputesAway <$ EW.writeErr
        MetaOccurs   -> S.Magic ComputesAway <$ EW.writeErr

  EW.liftIO (forceWithPSub psub t) >>= \case

    Rigid h sp _      -> goRigid h sp
    RigidEq a t u     -> S.Eq <$> go a <*> go t <*> go u
    Flex h sp _       -> goFlex h sp
    FlexEq x a t u    -> S.Eq <$> go a <*> go t <*> go u
    Unfold h sp _ _   -> goUnfold h sp
    TraceEq a t u _   -> S.Eq <$> go a <*> go t <*> go u
    UnfoldEq a t u _  -> S.Eq <$> go a <*> go t <*> go u
    Set               -> pure S.Set
    El a              -> S.El <$> go a
    Pi x i a b        -> S.Pi x i <$> go a <*> goBind a b
    Lam sp x i a t    -> S.Lam sp x i <$> go a <*> goBind a t
    Sg x a b          -> S.Sg x <$> go a <*> goBind a b
    Pair sp t u       -> S.Pair sp <$> go t <*> go u
    Prop              -> pure S.Prop
    Top               -> pure S.Top
    Tt                -> pure S.Tt
    Bot               -> pure S.Bot
    Refl a t          -> S.Refl <$> go a <*> go t
    Sym a x y p       -> S.Sym <$> go a <*> go x <*> go y <*> go p
    Trans a x y z p q -> S.Trans <$> go a <*> go x <*> go y <*> go z <*> go p <*> go q
    Ap a b f x y p    -> S.Ap <$> go a <*> go b <*> go f <*> go x <*> go y <*> go p
    Magic m           -> goMagic m


rigidPSubstSp :: PartialSub -> S.Tm -> Spine -> IO S.Tm
rigidPSubstSp psub hd sp = do
  let ?lvl = psub^.cod
  let goSp = rigidPSubstSp psub hd; {-# inline goSp #-}
      go   = rigidPSubst psub;      {-# inline go #-}
  case sp of
    SId                 -> pure hd
    SApp t u i          -> S.App <$!> goSp t <*!> go u <*!> pure i
    SProj1 t            -> S.Proj1 <$!> goSp t
    SProj2 t            -> S.Proj2 <$!> goSp t
    SProjField t tv a n -> S.ProjField <$!> goSp t <*!> pure (projFieldName tv a n) <*!> pure n

rigidPSubst :: PartialSub -> Val -> IO S.Tm
rigidPSubst psub topt = do

  let ?lvl = psub^.cod

  let goSp = rigidPSubstSp psub; {-# inline goSp #-}
      go   = rigidPSubst psub;   {-# inline go #-}

      goBind a t = do
        (_, ~a) <- psubst' psub a
        rigidPSubst (lift psub a) (t $$ Var ?lvl a)
      {-# inline goBind #-}

      goUnfolding unf t = do
        (!t, !tv) <- EW.run (flexPSubst psub t)
        unless tv $ fullPSubstCheck psub unf
        pure t
      {-# inline goUnfolding #-}

      goRigid h sp = do
        h <- case h of
          RHLocalVar x a True  -> pure (S.LocalVar (lvlToIx x))
          RHLocalVar x a False -> impossible
          RHPostulate x a      -> pure (S.Postulate x a)
          RHExfalso a p        -> S.Exfalso <$!> go a <*!> go p
          RHCoe a b p t        -> S.Coe <$!> go a <*!> go b <*!> go p <*!> go t
        goSp h sp

      goFlex h sp = case h of
        FHMeta m        -> goSp (S.Meta m) sp `catch` \(_ :: UnifyEx) -> go =<< prune psub m sp
        FHCoe x a b p t -> do h <- S.Coe <$!> go a <*!> go b <*!> go p <*!> go t
                              goSp h sp

      goMagic = \case
        ComputesAway -> impossible
        Undefined    -> throwIO CantUnify
        Nonlinear    -> throwIO CantUnify
        MetaOccurs   -> throwIO CantUnify

  topt <- forceWithPSub psub topt
  case topt of
    Rigid h sp _       -> goRigid h sp
    RigidEq a t u      -> S.Eq <$!> go a <*!> go t <*!> go u
    Flex h sp _        -> goFlex h sp
    FlexEq x a t u     -> S.Eq <$!> go a <*!> go t <*!> go u
    Unfold _ _ unf _   -> goUnfolding unf topt
    TraceEq _ _ _ unf  -> goUnfolding unf topt
    UnfoldEq _ _ _ unf -> goUnfolding unf topt
    Set                -> pure S.Set
    El a               -> S.El <$!> go a
    Pi x i a b         -> S.Pi x i <$!> go a <*!> goBind a b -- TODO: share "go a" and "psubst' a" work!
    Lam sp x i a t     -> S.Lam sp x i <$!> go a <*!> goBind a t
    Sg x a b           -> S.Sg x <$!> go a <*!> goBind a b
    Pair sp t u        -> S.Pair sp <$!> go t <*!> go u
    Prop               -> pure S.Prop
    Top                -> pure S.Top
    Tt                 -> pure S.Tt
    Bot                -> pure S.Bot
    Refl a t           -> S.Refl <$!> go a <*!> go t
    Sym a x y p        -> S.Sym <$!> go a <*!> go x <*!> go y <*!> go p
    Trans a x y z p q  -> S.Trans <$!> go a <*!> go x <*!> go y <*!> go z <*!> go p <*!> go q
    Ap a b f x y p     -> S.Ap <$!> go a <*!> go b <*!> go f <*!> go x <*!> go y <*!> go p
    Magic m            -> goMagic m

fullPSubstCheckSp :: PartialSub -> Spine -> IO ()
fullPSubstCheckSp psub = \case
    SId                -> pure ()
    SApp t u _         -> fullPSubstCheckSp psub t >> fullPSubstCheck psub u
    SProj1 t           -> fullPSubstCheckSp psub t
    SProj2 t           -> fullPSubstCheckSp psub t
    SProjField t _ _ _ -> fullPSubstCheckSp psub t

fullPSubstCheck :: PartialSub -> Val -> IO ()
fullPSubstCheck psub topt = do
  let ?lvl = psub^.cod

  let go   = fullPSubstCheck psub; {-# inline go #-}
      goSp = fullPSubstCheckSp psub; {-# inline goSp #-}

      goBind a t = do
        (_, a) <- psubst' psub a
        fullPSubstCheck (lift psub a) (t $$ Var ?lvl a)
      {-# inline goBind #-}

      goRH = \case
        RHLocalVar x a True  -> pure ()
        RHLocalVar x a False -> impossible
        RHPostulate x a      -> pure ()
        RHExfalso a p        -> go a >> go p
        RHCoe a b p t        -> go a >> go b >> go p >> go t

      goFlex h sp = case h of
        FHMeta m        -> goSp sp `catch` \(_ :: UnifyEx) -> go =<< prune psub m sp
        FHCoe _ a b p t -> go a >> go b >> go p >> go t >> goSp sp

      goMagic = \case
        ComputesAway -> impossible
        Undefined    -> throwIO CantUnify
        Nonlinear    -> throwIO CantUnify
        MetaOccurs   -> throwIO CantUnify

  forceAllWithPSub psub topt >>= \case
    Rigid h sp _      -> goRH h >> goSp sp
    RigidEq a t u     -> go a >> go t >> go u
    Flex h sp a       -> goFlex h sp
    FlexEq x a t u    -> go a >> go t >> go u
    Unfold{}          -> impossible
    TraceEq{}         -> impossible
    UnfoldEq{}        -> impossible
    Set               -> pure ()
    El a              -> go a
    Pi x i a b        -> go a >> goBind a b
    Lam sp x i a t    -> go a >> goBind a t
    Sg x a b          -> go a >> goBind a b
    Pair sp t u       -> go t >> go u
    Prop              -> pure ()
    Top               -> pure ()
    Tt                -> pure ()
    Bot               -> pure ()
    Refl a t          -> go a >> go t
    Sym a x y p       -> go a >> go x >> go y >> go p
    Trans a x y z p q -> go a >> go x >> go y >> go z >> go p >> go q
    Ap a b f x y p    -> go a >> go b >> go f >> go x >> go y >> go p
    Magic m           -> goMagic m


psubst :: PartialSub -> Val -> IO S.Tm
psubst = rigidPSubst

psubst' :: PartialSub -> Val -> IO (S.Tm, Val)
psubst' psub t = do
  t <- psubst psub t
  let ~vt = evalInDom psub t
  pure (t, vt)


----------------------------------------------------------------------------------------------------
-- Pruning
----------------------------------------------------------------------------------------------------

prune :: PartialSub -> MetaVar -> Spine -> IO Val
prune psub m sp = do
  unless (psub^.allowPruning) (throwIO CantUnify)
  uf


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

-- TODO: can we gain anything from trying to merge irrelevant values?
-- Recall how we dig for irrelevant solutions in unification.
merge :: LvlArg => Val -> Val -> IO S.Tm
merge topt topu = do

  let guardIrr a act = act >>= \case
        S.Magic Nonlinear -> typeRelevance a >>= \case
          RRel       -> pure $ S.Magic Nonlinear
          RIrr       -> pure $! quote UnfoldNone topt -- TODO: choose the more defined side?
          RBlockOn{} -> pure $ S.Magic Nonlinear
          RMagic{}   -> impossible -- TODO: is ComputedAway possible?
        t -> pure t

  -- TODO: think about where ComputedAway is possible in general!!!

  case (topt, topu) of

    (Rigid (RHLocalVar x xty dom) sp a, Rigid (RHLocalVar x' _ _) sp' _) -> guardIrr a do
      if not dom then
        impossible
      else if x == x' then do
        mergeSp (S.LocalVar (lvlToIx x)) sp sp'
      else
        pure $ S.Magic Nonlinear

    (Pair sp t u, Pair _ t' u') -> do
      S.Pair sp <$!> merge t t' <*!> merge u u'

    (Lam sp x i a t, Lam _ _ _ _ t') -> do
      let var = Var' ?lvl a True
      let ?lvl = ?lvl + 1
      S.Lam sp x i (quote UnfoldNone a) <$!> merge (t $$ var) (t' $$ var)

    (Magic m, t) -> case m of
      Nonlinear -> pure $ S.Magic Nonlinear
      Undefined -> pure $! quote UnfoldNone t
      _         -> impossible

    (t, Magic m) -> case m of
      Nonlinear -> pure $ S.Magic Nonlinear
      Undefined -> pure $! quote UnfoldNone t
      _         -> impossible

    (Lam sp x i a t, t') -> do
      let var = Var' ?lvl a True
      let ?lvl = ?lvl + 1
      S.Lam sp x i (quote UnfoldNone a) <$!> merge (t $$ var) (app t' var i)

    (t, Lam sp x i a t') -> do
      let var = Var' ?lvl a True
      let ?lvl = ?lvl + 1
      S.Lam sp x i (quote UnfoldNone a) <$!> merge (app t var i) (t' $$ var)

    (Pair sp t u, t') ->
      S.Pair S <$!> merge t (proj1 t') <*!> merge u (proj2 t')

    (t, Pair sp t' u') ->
      S.Pair S <$!> merge (proj1 t) t' <*!> merge (proj2 t) u'

    _ -> impossible

solveTopSp :: PartialSub -> S.Locals -> Ty -> Spine -> Val -> Ty -> IO S.Tm
solveTopSp psub ls a sp rhs rhsty = do

  let go psub a sp = solveTopSp psub ls a sp rhs rhsty
      {-# inline go #-}

      goBind x xty qxty psub a sp =
        solveTopSp (lift psub xty) (S.LBind ls x qxty) a sp rhs rhsty
      {-# inline goBind #-}

  let ?lvl    = psub^.dom
      ?env    = psub^.domVars
      ?locals = ls

  a <- forceSet a
  case (a, sp) of

    (a, SId) -> do
      unless (psub^.isLinear) (() <$ psubst psub rhsty)
      psubst psub rhs

    (Pi x i a b, SApp t u _) -> do
      let var = Var' ?lvl a True
      let qa = quote UnfoldNone a
      psub <- invertVal 0 (psub^.cod) psub u var a
      sol  <- goBind x a qa psub (b $$ var) t
      pure $ S.Lam S x i qa sol

    (El (Pi x i a b), SApp t u _) -> do
      let var = Var' ?lvl a True
      let qa = quote UnfoldNone a
      psub <- invertVal 0 (psub^.cod) psub u var a
      sol  <- goBind x a qa psub (b $$ var) t
      pure $ S.Lam P x i qa sol

    (Sg x a b, SProj1 t) -> do
      fst <- go psub a t
      let ~vfst = eval fst
      snd <- freshMeta (gjoin (b $$ vfst))
      pure $ S.Pair S fst snd

    (Sg x a b, SProj2 t) -> do
      fst <- freshMeta (gjoin a)
      let ~vfst = eval fst
      snd <- go psub (b $$ vfst) t
      pure $ S.Pair S fst snd

    (El (Sg x a b), SProj1 t) -> do
      fst <- go psub (El a) t
      let ~vfst = eval fst
      snd <- freshMeta (gjoin (El (b $$ vfst)))
      pure $ S.Pair P fst snd

    (El (Sg x a b), SProj2 t) -> do
      fst <- freshMeta (gjoin (El a))
      let ~vfst = eval fst
      snd <- go psub (El (b $$ vfst)) t
      pure $ S.Pair P fst snd

    (a, SProjField t tv tty n) ->
      case n of
        0 -> go psub a (SProj1 t)
        n -> go psub a (SProj2 (SProjField t tv tty (n - 1)))

    _ -> impossible

solveNestedSp :: Lvl -> PartialSub -> Ty -> Spine -> Val -> Ty -> IO S.Tm
solveNestedSp solvable psub a sp rhs rhsty = do

  let go psub a sp = solveNestedSp solvable psub a sp rhs rhsty
      {-# inline go #-}

      goBind x xty qxty psub a sp =
        solveNestedSp solvable (lift psub xty) a sp rhs rhsty
      {-# inline goBind #-}

  let ?lvl = psub^.dom
      ?env = psub^.domVars

  a <- forceSet a
  case (a, sp) of
    (a, SId) -> do
      unless (psub^.isLinear) (() <$ psubst psub rhsty)
      psubst psub rhs

    (Pi x i a b, SApp t u _) -> do
      let var = Var' ?lvl a True
      let qa = quote UnfoldNone a
      psub <- invertVal solvable (psub^.cod) psub u var a
      sol  <- goBind x a qa psub (b $$ var) t
      pure $ S.Lam S x i qa sol

    (El (Pi x i a b), SApp t u _) -> do
      let var = Var' ?lvl a True
      let qa = quote UnfoldNone a
      psub <- invertVal solvable (psub^.cod) psub u var a
      sol  <- goBind x a qa psub (b $$ var) t
      pure $ S.Lam P x i qa sol

    (Sg x a b, SProj1 t) ->
      S.Pair S <$!> go psub a t <*!> pure (S.Magic Undefined)

    (Sg x a b, SProj2 t) -> do
      let fst  = S.Magic Undefined
          vfst = Magic Undefined
      S.Pair S fst <$!> go psub (b $$ vfst) t

    (El (Sg x a b), SProj1 t) ->
      S.Pair P <$!> go psub (El a) t <*!> pure (S.Magic Undefined)

    (El (Sg x a b), SProj2 t) -> do
      let fst  = S.Magic Undefined
          vfst = Magic Undefined
      S.Pair P fst <$!> go psub (El (b $$ vfst)) t

    (a, SProjField t tv tty n) ->
      case n of
        0 -> go psub a (SProj1 t)
        n -> go psub a (SProj2 (SProjField t tv tty (n - 1)))

    _ -> impossible


invertVal :: Lvl -> Lvl -> PartialSub -> Val -> Val -> Ty -> IO PartialSub
invertVal solvable param psub t rhs rhsty = do

  let ?lvl = psub^.dom
      ?env = psub^.domVars

  (let ?lvl = psub^.cod in forceAll t) >>= \case

    Lam sp x i a t -> do
      (_, ~a) <- psubst' psub a
      let var = Var' ?lvl a True
      psub <- invertVal solvable param (lift psub a) (t $$ var) (app rhs var i) (appTy rhsty var)
      pure $! unlift psub

    Pair sp t u -> do
      psub <- invertVal solvable param psub t (proj1 rhs) (proj1Ty rhsty)
      invertVal solvable param psub u (proj2 rhs) (proj2Ty rhsty (proj1 rhs))

    Rigid (RHLocalVar x xty dom) sp a -> do
      _

-- | Solve (?x sp ?= rhs : A).
solve :: LvlArg => AllowPruningArg => MetaVar -> Spine -> Val -> Ty -> IO ()
solve x sp rhs rhsty = do
  a <- ES.unsolvedMetaType x

  let goRelevant = do
        sol <- solveTopSp (emptyPSub (Just x) ?allowPruning)
                          S.LEmpty a (reverseSpine sp) rhs rhsty
        ES.solve x sol (eval0 sol)

      goIrrelevant =
        (do sol <- solveTopSp (emptyPSub (Just x) False)
                          S.LEmpty a (reverseSpine sp) rhs rhsty
            ES.solve x sol (eval0 sol))
        `catch`
        \(_ :: UnifyEx) -> pure () -- TODO: clean up unused expansion metas in this branch!

  typeRelevance rhsty >>= \case
    RRel       -> goRelevant
    RBlockOn{} -> goRelevant
    RIrr       -> goIrrelevant
    RMagic{}   -> impossible

----------------------------------------------------------------------------------------------------
-- Unification
----------------------------------------------------------------------------------------------------


unify :: LvlArg => UnifyState -> G -> G -> IO ()
unify st t t' = uf
