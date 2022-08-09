
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

--------------------------------------------------------------------------------

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


-- Partial substitutions
--------------------------------------------------------------------------------


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

-- | lift : (σ : PSub Γ Δ) → PSub (Γ, x : A[σ]) (Δ, x : A)
--   Note: gets A[σ] as Ty input, not A!
lift :: PartialSub -> Ty -> PartialSub
lift (PSub idenv occ dom cod sub linear allowpr) ~asub =
  let var = Var dom asub
  in PSub (EDef idenv var) occ (dom + 1) (cod + 1)
          (IM.insert (coerce cod) var sub) linear allowpr

-- | skip : PSub Γ Δ → PSub Γ (Δ, x : A)
skip :: PartialSub -> PartialSub
skip psub = psub & cod +~ 1

forceAllWithPSub :: PartialSub -> Val -> IO Val
forceAllWithPSub psub t = uf

forceWithPSub :: PartialSub -> Val -> IO Val
forceWithPSub = uf


-- Partial substitution
--------------------------------------------------------------------------------

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
    S.ComputesAway{}   -> pure ()

flexPSubstSp :: PartialSub -> S.Tm -> Spine -> ErrWriter S.Tm
flexPSubstSp psub hd sp = do
  let go   = flexPSubst psub; {-# inline go #-}
      goSp = flexPSubstSp psub hd; {-# inline goSp #-}
  case sp of
    SId              -> pure hd
    SApp t u i       -> S.App <$> goSp t <*> go u <*> pure i
    SProj1 t         -> S.Proj1 <$> goSp t
    SProj2 t         -> S.Proj2 <$> goSp t
    SProjField t x n -> S.ProjField <$> goSp t <*> pure x <*> pure n

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
        ComputesAway -> pure S.ComputesAway
        Undefined    -> S.ComputesAway <$ EW.writeErr
        Nonlinear    -> S.ComputesAway <$ EW.writeErr
        MetaOccurs   -> S.ComputesAway <$ EW.writeErr

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
  let goSp = rigidPSubstSp psub hd; {-# inline goSp #-}
      go   = rigidPSubst psub;      {-# inline go #-}
  case sp of
    SId              -> pure hd
    SApp t u i       -> S.App <$!> goSp t <*!> go u <*!> pure i
    SProj1 t         -> S.Proj1 <$!> goSp t
    SProj2 t         -> S.Proj2 <$!> goSp t
    SProjField t x n -> S.ProjField <$!> goSp t <*!> pure x <*!> pure n

rigidPSubst :: PartialSub -> Val -> IO S.Tm
rigidPSubst psub topt = do

  let ?lvl = psub^.cod

  let goSp     = rigidPSubstSp psub; {-# inline goSp #-}
      go       = rigidPSubst psub;   {-# inline go #-}

      goBind a t = do
        (_, ~a) <- psubst' psub a
        rigidPSubst (lift psub a) (t $$ Var ?lvl a)
      {-# inline goBind #-}

      goUnfolding :: Val -> Val -> IO S.Tm
      goUnfolding fullval t = do
        (!t, !tv) <- EW.run (flexPSubst psub t)
        unless tv $ fullPSubstCheck psub fullval
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
    Pi x i a b         -> S.Pi x i <$!> go a <*!> goBind a b
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
    SId              -> pure ()
    SApp t u _       -> fullPSubstCheckSp psub t >> fullPSubstCheck psub u
    SProj1 t         -> fullPSubstCheckSp psub t
    SProj2 t         -> fullPSubstCheckSp psub t
    SProjField t _ _ -> fullPSubstCheckSp psub t

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
  let ?env = psub^.domVars; ?lvl = psub^.dom
  let ~vt = eval t
  pure (t, vt)

-- Pruning
--------------------------------------------------------------------------------

prune :: PartialSub -> MetaVar -> Spine -> IO Val
prune psub m sp = uf

--------------------------------------------------------------------------------

-- | Solve (?x sp ?= rhs : A).
solve :: LvlArg => MetaVar -> Spine -> Val -> Ty -> IO ()
solve x sp rhs rhsty = do
  uf


-- | Solve metavariable with an inverted spine.
solve' :: MetaVar -> PartialSub -> Val -> Ty -> IO ()
solve' m psub rhs rhsty = do
  uf


-- Unification
--------------------------------------------------------------------------------

unify :: LvlArg => UnifyState -> G -> G -> IO ()
unify st t t' = uf
