
module Unification where

import Common

-- import IO
import Control.Exception

import qualified Data.IntMap as IM
-- import qualified Data.IntSet as IS
-- import qualified Data.Ref.F as RF
import Lens.Micro.Platform

import Values
import Evaluation
import qualified ElabState as ES
-- import Errors
import qualified Syntax as S

import ErrWriter (ErrWriter)
import qualified ErrWriter as EW


--------------------------------------------------------------------------------

{-
DESIGN
  backtracking:
    - whenever we can backtrack, we want to disallow non-conservative
      destructive updates. Currently this is *meta solution* and
      *pruning*. Eta-expansion is always allowed!
    - we need an extra argument to partial sub for toggling pruning!

  unification:
    - 4 states, rigid, flex, irrelevant, full
    - irrelevant:
      - we can solve only irrelevant metas
      - pruning is not allowed, but eta-expansion is
    - eta-short solutions:
      - we try to solve, on any failure we retry with expansion
      - pruning is allowed in speculative eta-short solutions! That's because we
        would repeat the same prunings in the eta-long retries.
    - flex-flex:
      - we try to invert left spine *with pruning disabled*, else try the right spine
    - TraceEq: TODO
    - Setoid ops: TODO

  solving ?m spine = rhs
    1. check relevance
       - if irrelevant, disable pruning, catch any subsequent exception and then succeed
    2. eliminate projections
    3. eta-contract sides
    4. invert spine
         4.1. walk spine, invert values
           - when hitting a bound var, check relevance
             - if relevant, invert as usual
             - if irrelevant, disregard linearity
               - this means that we just keep the innermost non-linear binding
         4.2. check well-typing of spine pruning
           - Noe: this may involve pruning in types (which may be disabled here)
           - compute domain idEnv here
    5. substitute rhs
      - 3 states: rigid, flex, full
      - use smalltt optimizations
      - we don't have to care about irrelevance
      - note: pruning can be disallowed at this point

    TODO: fancy

  pruning flex spine
    - try to psub spine. If it fails, and pruning is allowed, we try pruning
      1. eliminate all projections and pairs from spine
      2. prune spine

WARNING:
  - eta-contraction for equations in smalltt is buggy!
    If we have   ?0 f x = f x x x, it gets contracted to ?0 f = f x x, which is ill-scoped!
    We have to check contracted var occurrence in rhs too!
    (Let's skip eta-contraction at first)


INVERSION & PRUNING DESIGN
  - partialsub maps to values made of pairing, projection, var, OUT-OF-SCOPE
    - there's a separate data type for these values

  - in psubst, we specially handle the rigid case, we explicitly recurse over
    the value

  - in pruning, we just do proj elimination and currying as in my other implementations
    - A rigid neutral with illegal head counts as a prunable value, not just a plain rigid
      illegal var as in my old stuff.

  - In summary, the current design can handle pairing and projections in spines
    in inversion & in pruning. It can't handle lambdas.

    We don't have to do "forcing" in partial sub, nor do we have to use
    fresh variable generation.


TODO: in solving, grab a precise bundle of info about the spine
      args (S/P, type, name), don't recompute the same things.

-}



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
freshMeta :: LvlArg => S.LocalsArg => S.PruningArg => GTy -> IO S.Tm
freshMeta (G a fa) = do
  let closed   = eval0 $ S.closeTy $ quote UnfoldNone a
  let ~fclosed = eval0 $ S.closeTy $ quote UnfoldNone fa
  m <- ES.newMeta (G closed fclosed)
  pure $ S.InsertedMeta m ?pruning


-- Partial substitutions
--------------------------------------------------------------------------------


data PartialPairings
  = PPId
  | PPPair1 PartialPairings     -- ^ Pairing whose second field is undefined.
  | PPPair2 PartialPairings     -- ^ Pairing whose first  field is undefined.
  | PPPairN PartialPairings Int -- ^ Pairing with only the given field defined.
  deriving Show

-- | Apply a spine to partial pairings. We succeed if all pairings are
--   cancelled by a projection, otherwise the result is undefined.
--   TODO: handle conversion between field proj and simple proj!
cancelPairings :: PartialPairings -> Spine -> Maybe Spine
cancelPairings pps sp = do
  let go :: Spine -> Maybe (Spine, PartialPairings)
      go = \case
        SId -> pure (SId, pps)
        SApp t u i -> do
          (t, PPId) <- go t
          pure (SApp t u i, PPId)
        SProj1 t -> do
          (t, PPPair1 pps) <- go t
          pure (t, pps)
        SProj2 t -> do
          (t, PPPair2 pps) <- go t
          pure (t, pps)
        SProjField t _ n -> do
          (t, PPPairN pps n') <- go t
          guard (n == n')
          pure (t, pps)
  (t, PPId) <- go sp
  pure t


data PSEntry = PSENonlinear | PSEVal Val PartialPairings

data PartialSub = PSub {
    partialSubDomVars      :: Vars              -- Identity env from Γ to Γ, serves as the list of Γ types.
                                                -- We need this when we want to evaluate the result term of
                                                -- partial substitution.
  , partialSubOcc          :: Maybe MetaVar     -- optional occurs check
  , partialSubDom          :: Lvl               -- size of Γ
  , partialSubCod          :: Lvl               -- size of Δ
  , partialSubSub          :: IM.IntMap PSEntry -- Partial map from Δ vars to Γ values. A var which is not
                                                -- in the map is mapped to a scope error, but note that
                                                -- PSVal-s can contain scope errors as well.
  , partialSubIsLinear     :: Bool              -- Does the sub contain PSNonlinearEntry.
  , partialSubAllowPruning :: Bool              -- Is pruning allowed during partial substitution.
  }
makeFields ''PartialSub

type CanPrune = (?canPrune :: Bool)

-- | lift : (σ : PSub Γ Δ) → PSub (Γ, x : A[σ]) (Δ, x : A)
--   Note: gets A[σ] as Ty input, not A!
lift :: PartialSub -> Ty -> PartialSub
lift (PSub idenv occ dom cod sub linear allowpr) ~asub =
  let var     = Var dom asub
      psentry = PSEVal var PPId
  in PSub (EDef idenv var) occ (dom + 1) (cod + 1)
          (IM.insert (coerce cod) psentry sub) linear allowpr

-- | skip : PSub Γ Δ → PSub Γ (Δ, x : A)
skip :: PartialSub -> PartialSub
skip psub = psub & cod +~ 1

--------------------------------------------------------------------------------

invertRigid :: LvlArg => RigidHead -> Spine -> Ty -> PartialSub -> Val -> PartialPairings -> IO PartialSub
invertRigid rh sp a psub psval pairings = do
  let go sp = invertRigid rh sp a psub; {-# inline go #-}
  case sp of
    SId -> case rh of
      RHLocalVar (Lvl x) -> do
        typeRelevance a >>= \case
          RIrr -> do
            pure $! psub & sub %~ IM.insert x (PSEVal psval pairings)
          _ ->
            pure $! psub & sub %~ IM.insertWithKey (\_ _ _ -> PSENonlinear) x (PSEVal psval pairings)
      _ ->
        throwIO CantUnify

    SProj1 sp         -> go sp psval (PPPair1 pairings)
    SProj2 sp         -> go sp psval (PPPair2 pairings)
    SProjField sp _ n -> go sp psval (PPPairN pairings n)
    _                 -> throwIO CantUnify


invertVal :: LvlArg => Val -> PartialSub -> Val -> IO PartialSub
invertVal v psub psval = forceAll v >>= \case
  Rigid rh sp a -> do
    invertRigid rh sp a psub psval PPId
  Pair _ t u -> do
    psub <- invertVal t psub (proj1 psval)
    invertVal u psub (proj2 psval)
  _ ->
    throwIO CantUnify

invertSpine :: LvlArg => CanPrune => Vars -> Spine -> IO PartialSub
invertSpine vars sp = do
  let go = invertSpine; {-# inline go #-}
  case (vars, sp) of
    (_, SId) ->
       pure $! PSub ENil Nothing 0 0 mempty True ?canPrune
    (EDef vars a, SApp sp t i) -> do
       psub <- go vars sp
       let psub' = psub & dom +~ 1 & domVars .~ EDef vars a
       invertVal t psub' (Var (psub^.dom) a)
    _ ->
      impossible

-- | Remove some arguments from a closed iterated (Set) Pi type. Return the pruned type
--   + the identity environment containing the variables with the binder types.
pruneTy :: CanPrune => S.RevPruning -> Ty -> IO S.Ty
pruneTy (S.RevPruning# pr) a = go pr (PSub ENil Nothing 0 0 mempty True ?canPrune) a where

  go :: S.Pruning -> PartialSub -> Ty -> IO S.Ty
  go pr psub a = do
    let ?lvl = psub^.cod
    a <- forceAll a
    case (pr, a) of

      ([], a) ->
        psubst psub a

      (Just{} : pr, Pi x i a b) -> do
        (a', va') <- psubst' psub a
        t <- go pr (lift psub va') (b $$ Var (psub^.cod) va')
        pure (S.Pi x i a' t)

      (Nothing : pr, Pi x i a b) -> do
        (_, va') <- psubst' psub a
        go pr (skip psub) (b $$ Var (psub^.cod) va')

      (Just{} : pr, El (Pi x i a b)) -> do
        (a', El -> va') <- psubst' psub a
        t <- go pr (lift psub va') (b $$ Var (psub^.cod) va')
        pure (S.Pi x i a' t)

      (Nothing : pr, El (Pi x i a b)) -> do
        (_, El -> va') <- psubst' psub a
        go pr (skip psub) (b $$ Var (psub^.cod) va')

      _ -> impossible


-- Eta expansion of metas
--------------------------------------------------------------------------------

-- | Helper synonym for the args that we need when eta-expanding metas.
type WithExpansion a = LvlArg => S.LocalsArg => S.PruningArg => EnvArg => a


-- | Create a fresh eta-expanded value with the same type as the given meta,
--   expanded along the given spine.
expansionOfMeta :: MetaVar -> Spine -> IO Val
expansionOfMeta meta sp = do
  a <- ES.unsolvedMetaType meta
  let ?lvl = 0; ?locals = S.LEmpty; ?pruning = []; ?env = ENil
  eval0 <$!> freshExpandedTm sp a

-- | Create a value a value containing possible multiple fresh metas, which is
--   eta-expanded along the given spine. For example,
--     - If the spine is a single function application, we eta-expand to a fresh
--       meta wrapped in a lambda.
--     - If the spine is a single projection, we eta-expand to a pair of fresh metas.
--   The point is
freshExpandedTm :: WithExpansion (Spine -> Ty -> IO S.Tm)
freshExpandedTm sp a = do
  let go = freshExpandedTm; {-# inline go #-}

  let bind :: WithExpansion (Name -> Ty -> WithExpansion (Val -> a) -> a)
      bind x a k =
        let qa  = quote UnfoldNone a in
        let var = Var ?lvl a in
        let ?lvl     = ?lvl + 1
            ?locals  = S.LBind ?locals x qa
            ?pruning = Just Expl : ?pruning
            ?env     = EDef ?env var
        in k var
      {-# inline bind #-}

  a <- forceAll a
  case (sp, a) of
    (SId, a) -> freshMeta (gjoin a)

    (SApp t u i          , Pi x _ a b) -> do t <- bind x a (\var -> go t (b $$ var))
                                             pure $! S.Lam S x i (quote UnfoldNone a) t
    (SProj1 t            , Sg x a b  ) -> do t <- go t a
                                             S.Pair S t <$!> freshMeta (gjoin (b $$~ eval t))
    (SProj2 sp           , Sg x a b  ) -> do t <- freshMeta (gjoin a)
                                             S.Pair S t <$!> go sp (b $$~ eval t)
    (SProjField t _ 0    , Sg x a b  ) -> do t <- go t a
                                             S.Pair S t <$!> freshMeta (gjoin (b $$~ eval t))
    (SProjField sp spty n, Sg x a b  ) -> do sp <- pure $! SProjField sp spty (n - 1)
                                             t <- freshMeta (gjoin a)
                                             S.Pair S t <$!> go sp (b $$~ eval t)

    (SApp t u i          , El (Pi x _ a b)) -> do t <- bind x (El a) (\var -> go t (b $$ var))
                                                  pure $! S.Lam S x i (quote UnfoldNone a) t
    (SProj1 t            , El (Sg x a b)  ) -> do t <- go t a
                                                  S.Pair S t <$!> freshMeta (gjoin (El (b $$~ eval t)))
    (SProj2 sp           , El (Sg x a b)  ) -> do t <- freshMeta (gjoin (El a))
                                                  S.Pair S t <$!> go sp (b $$~ eval t)
    (SProjField t _ 0    , El (Sg x a b)  ) -> do t <- go t a
                                                  S.Pair S t <$!> freshMeta (gjoin (El (b $$~ eval t)))
    (SProjField sp spty n, El (Sg x a b)  ) -> do sp <- pure $! SProjField sp spty (n - 1)
                                                  t <- freshMeta (gjoin (El a))
                                                  S.Pair S t <$!> go sp (El (b $$~ eval t))
    _ -> impossible


-- Partial substitution
--------------------------------------------------------------------------------

approxOccursInSolution :: MetaVar -> MetaVar -> IO Bool
approxOccursInSolution occ x = uf

approxOccurs :: MetaVar -> S.Tm -> IO Bool
approxOccurs x t = uf

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

      illegal = S.Irrelevant <$ EW.writeErr; {-# inline illegal #-}

      goBind a t = do
        (_, a) <- EW.liftIO (psubst' psub a)
        flexPSubst (lift psub a) (t $$ Var ?lvl a)
      {-# inline goBind #-}

      goLocalVar :: Lvl -> Spine -> ErrWriter S.Tm
      goLocalVar x sp = case IM.lookup (coerce x) (psub^.sub) of

        Nothing           -> illegal
        Just PSENonlinear -> illegal

        Just (PSEVal v pairings) ->
          case cancelPairings pairings sp of
            Just sp -> goSp (quote UnfoldNone v) sp
            _       -> illegal

  EW.liftIO (force t) >>= \case

    Rigid h sp a -> case h of
      RHLocalVar x    -> goLocalVar x sp
      RHPostulate x a -> goSp (S.Postulate x a) sp
      RHExfalso a p   -> do {a <- go a; p <- go p; goSp (S.Exfalso a p) sp}
      RHCoe a b p t   -> do {a <- go a; b <- go b; p <- go p; t <- go t; goSp (S.Coe a b p t) sp}

    RigidEq a t u -> do
      S.Eq <$> go a <*> go t <*> go u

    Flex h sp a -> case h of

      FHMeta x -> do
        if Just x == psub^.occ then
          illegal
        else
          goSp (S.Meta x) sp

      FHCoe x a b p t -> do
        hd <- S.Coe <$> go a <*> go b <*> go p <*> go t
        goSp hd sp

    FlexEq x a t u -> do
      S.Eq <$> go a <*> go t <*> go u

    Unfold h sp unf a -> do
      (t, tValid) <- EW.catch $ case h of
        UHTopDef x v a -> goSp (S.TopDef x v a) sp
        UHSolvedMeta x -> goSp (S.Meta x) sp
        UHCoe a b p t  -> do hd <- S.Coe <$> go a <*> go b <*> go p <*> go t
                             goSp hd sp
      uf




-- topt@(VUnfold h sp t) -> U.do
--       (t, tf) <- case h of    -- WARNING: Core was fine here, but should be checked on ghc change
--         UHTopVar x v -> U.do
--           goSp (TopVar x (coerce v) // UTrue) sp
--         UHSolved x -> U.do
--           xf <- approxOccursInSolution ms frz (occ pren) x
--           goSp (Meta x // xf) sp

--       U.when (tf == UFalse) $
--         fullCheckRhs ms frz pren topt

--       U.pure (t // UTrue)

    -- Unfold h sp unf a -> runFlexPS unf do
    --   hd <- case h of
    --     UHTopDef x v a ->
    --       pure (S.TopDef x v a)

    --     UHSolvedMeta x -> FlexPS do
    --       xValid <- case psub^.occ of
    --         Just occ -> approxOccursInSolution occ x
    --         Nothing  -> pure True
    --       pure (S.Meta x // xValid)

    --     UHCoe a b p t -> do
    --       S.Coe <$> goFlex a <*> goFlex b <*> goFlex p <*> goFlex t

    --   goSpFlex hd sp

    -- TraceEq a t u unf -> runFlexPS unf do
    --   S.Eq <$> goFlex a <*> goFlex t <*> goFlex u

    -- UnfoldEq a t u unf -> runFlexPS unf do
    --   S.Eq <$> goFlex a <*> goFlex t <*> goFlex u

    -- Set               -> pure S.Set
    -- El a              -> S.El <$!> go a
    -- Pi x i a b        -> S.Pi x i <$!> go a <*!> goBind a b
    -- Lam sp x i a t    -> S.Lam sp x i <$!> go a <*!> goBind a t
    -- Sg x a b          -> S.Sg x <$!> go a <*!> goBind a b
    -- Pair sp t u       -> S.Pair sp <$!> go t <*!> go u
    -- Prop              -> pure S.Prop
    -- Top               -> pure S.Top
    -- Tt                -> pure S.Tt
    -- Bot               -> pure S.Bot
    -- Refl a t          -> S.Refl <$!> go a <*!> go t
    -- Sym a x y p       -> S.Sym <$!> go a <*!> go x <*!> go y <*!> go p
    -- Trans a x y z p q -> S.Trans <$!> go a <*!> go x <*!> go y <*!> go z <*!> go p <*!> go q
    -- Ap a b f x y p    -> S.Ap <$!> go a <*!> go b <*!> go f <*!> go x <*!> go y <*!> go p
    -- Irrelevant        -> impossible

rigidPSubstSp :: PartialSub -> S.Tm -> Spine -> IO S.Tm
rigidPSubstSp psub hd sp = do
  let goSp = rigidPSubstSp psub hd; {-# inline goSp #-}
      go   = rigidPSubst psub; {-# inline go #-}
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
      goSpFlex = flexPSubstSp psub; {-# inline goSpFlex #-}
      goFlex   = flexPSubst psub; {-# inline goFlex #-}
      go       = rigidPSubst psub; {-# inline go #-}

      goBind a t = do
        (_, ~a) <- psubst' psub a
        rigidPSubst (lift psub a) (t $$ Var ?lvl a)
      {-# inline goBind #-}

      goLocalVar :: Lvl -> Spine -> IO S.Tm
      goLocalVar x sp = case IM.lookup (unLvl x) (psub^.sub) of

        Nothing           -> throwIO CantUnify
        Just PSENonlinear -> throwIO CantUnify

        Just (PSEVal v pairings) ->
          case cancelPairings pairings sp of
            Just sp -> goSp (quote UnfoldNone v) sp
            _       -> throwIO CantUnify

      goUnfolding :: Val -> ErrWriter S.Tm -> IO S.Tm
      goUnfolding fullval act = do
        (t, tv) <- EW.run act
        unless tv $ fullPSubstCheck psub fullval
        pure t
      {-# inline goUnfolding #-}

  topt <- force topt
  case topt of

    Rigid h sp a -> case h of
      RHLocalVar x    -> goLocalVar x sp
      RHPostulate x a -> goSp (S.Postulate x a) sp
      RHExfalso a p   -> do {a <- go a; p <- go p; goSp (S.Exfalso a p) sp}
      RHCoe a b p t   -> do {a <- go a; b <- go b; p <- go p; t <- go t; goSp (S.Coe a b p t) sp}

    RigidEq a t u ->
      S.Eq <$!> go a <*!> go t <*!> go u

    Flex h sp a -> case h of

      FHMeta x -> do
        if Just x == psub^.occ then
          throwIO CantUnify
        else
          uf -- pruning

      FHCoe x a b p t -> do
        hd <- S.Coe <$!> go a <*!> go b <*!> go p <*!> go t
        goSp hd sp

    FlexEq x a t u -> do
      S.Eq <$!> go a <*!> go t <*!> go u

    Unfold h sp unf a -> goUnfolding unf do
      hd <- case h of
        UHTopDef x v a ->
          pure (S.TopDef x v a)

        UHSolvedMeta x -> do
          case psub^.occ of
            Just occ -> EW.liftIOBool (approxOccursInSolution occ x)
            Nothing  -> pure ()
          pure (S.Meta x)

        UHCoe a b p t -> do
          S.Coe <$> goFlex a <*> goFlex b <*> goFlex p <*> goFlex t

      goSpFlex hd sp

    TraceEq a t u unf -> goUnfolding unf do
      S.Eq <$> goFlex a <*> goFlex t <*> goFlex u

    UnfoldEq a t u unf -> goUnfolding unf do
      S.Eq <$> goFlex a <*> goFlex t <*> goFlex u

    Set               -> pure S.Set
    El a              -> S.El <$!> go a
    Pi x i a b        -> S.Pi x i <$!> go a <*!> goBind a b
    Lam sp x i a t    -> S.Lam sp x i <$!> go a <*!> goBind a t
    Sg x a b          -> S.Sg x <$!> go a <*!> goBind a b
    Pair sp t u       -> S.Pair sp <$!> go t <*!> go u
    Prop              -> pure S.Prop
    Top               -> pure S.Top
    Tt                -> pure S.Tt
    Bot               -> pure S.Bot
    Refl a t          -> S.Refl <$!> go a <*!> go t
    Sym a x y p       -> S.Sym <$!> go a <*!> go x <*!> go y <*!> go p
    Trans a x y z p q -> S.Trans <$!> go a <*!> go x <*!> go y <*!> go z <*!> go p <*!> go q
    Ap a b f x y p    -> S.Ap <$!> go a <*!> go b <*!> go f <*!> go x <*!> go y <*!> go p
    Irrelevant        -> impossible

fullPSubstCheckSp :: PartialSub -> Spine -> IO ()
fullPSubstCheckSp psub sp = do
  let go   = fullPSubstCheck psub; {-# inline go #-}
      goSp = fullPSubstCheckSp psub; {-# inline goSp #-}
  case sp of
    SId              -> pure ()
    SApp t u _       -> goSp t >> go u
    SProj1 t         -> goSp t
    SProj2 t         -> goSp t
    SProjField t _ _ -> goSp t

fullPSubstCheck :: PartialSub -> Val -> IO ()
fullPSubstCheck psub topt = do
  let ?lvl = psub^.cod

  let go   = fullPSubstCheck psub; {-# inline go #-}
      goSp = fullPSubstCheckSp psub; {-# inline goSp #-}

      goBind a t = do
        (_, a) <- psubst' psub a
        fullPSubstCheck (lift psub a) (t $$ Var ?lvl a)
      {-# inline goBind #-}

      goLocalVar x sp = uf

  topt <- forceAll topt
  case topt of
    Rigid h sp a -> case h of
      RHLocalVar x    -> goLocalVar x sp
      RHPostulate x a -> goSp sp
      RHExfalso a p   -> go a >> go p >> goSp sp
      RHCoe a b p t   -> go a >> go b >> go p >> go t >> goSp sp

    RigidEq a t u -> go a >> go t >> go u

    Flex h sp a -> do
      case h of
        FHMeta x        -> when (Just x == psub^.occ) (throwIO CantUnify)
        FHCoe x a b p t -> go a >> go b >> go p >> go t
      goSp sp

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
    Irrelevant        -> impossible


psubst :: PartialSub -> Val -> IO S.Tm
psubst = rigidPSubst

psubst' :: PartialSub -> Val -> IO (S.Tm, Val)
psubst' psub t = do
  t <- psubst psub t
  let ?env = psub^.domVars; ?lvl = psub^.dom
  let ~vt = eval t
  pure (t, vt)


--------------------------------------------------------------------------------

hasProjection :: Spine -> Bool
hasProjection = \case
  SId          -> False
  SApp t _ _   -> hasProjection t
  SProj1{}     -> True
  SProj2{}     -> True
  SProjField{} -> True

removeProjections :: MetaVar -> Spine -> IO (MetaVar, Spine)
removeProjections x sp = do
  if hasProjection sp then do
    v <- expansionOfMeta x sp
    ES.solve x v
    let ?lvl = 0
    case spine v sp of
      Flex (FHMeta x) sp _ -> pure (x, sp)
      _                    -> impossible
  else pure (x, sp)

-- | Grab spine-many argument types for a meta.
metaArgs :: MetaVar -> Spine -> IO Vars
metaArgs x sp = do
  a <- ES.unsolvedMetaType x
  let ?lvl = 0
  metaArgs' a sp ENil

metaArgs' :: LvlArg => Ty -> Spine -> Vars -> IO Vars
metaArgs' a sp vars = do
  a <- forceAll a
  case (a, sp) of
    (Pi x i a b, SApp sp _ _) -> do
      let var = Var ?lvl a
      let ?lvl = ?lvl + 1
      metaArgs' (b $$ var) sp (EDef vars var)
    (El (Pi x i a b), SApp sp _ _) -> do
      let var = Var ?lvl a
      let ?lvl = ?lvl + 1
      metaArgs' (b $$ var) sp (EDef vars var)
    (_, SId) ->
      pure vars
    _ ->
      impossible

-- | Wrap a term in Lvl number of lambdas, pulling
--   binder information from the given Ty.
addLams :: Lvl -> Ty -> S.Tm -> IO S.Tm
addLams l a t = go a (0 :: Lvl) where
  go a l' | l' == l = pure t
  go a l' = do
    let ?lvl = l'
    forceAll a >>= \case
      Pi x i a b      -> S.Lam S x i (quote UnfoldNone a) <$!> go (b $$ Var l' a) (l' + 1)
      El (Pi x i a b) -> S.Lam P x i (quote UnfoldNone a) <$!> go (b $$ Var l' a) (l' + 1)
      _               -> impossible

-- | Solve (?x sp ?= rhs : A).
solve :: LvlArg => CanPrune => MetaVar -> Spine -> Val -> Ty -> IO ()
solve x sp rhs rhsty = do

  -- check freezing
  frz <- ES.isFrozen x
  when frz $ throwIO CantSolveFrozenMeta

  -- eliminate spine projections
  (x, sp) <- removeProjections x sp

  -- get meta arg types
  argTypes <- metaArgs x sp

  -- invert spine
  psub <- invertSpine argTypes sp

  solve' x psub rhs rhsty

-- | Solve metavariable with an inverted spine.
solve' :: MetaVar -> PartialSub -> Val -> Ty -> IO ()
solve' m psub rhs rhsty = do

  mty <- ES.unsolvedMetaType m

  -- if spine was non-linear, check rhsty well-formedness
  when (not (psub^.isLinear))
    (() <$ psubst psub rhsty)

  -- occurs check
  psub <- pure $! psub & occ .~ Just m

  -- get rhs
  rhs <- psubst psub rhs

  -- add lambdas
  rhs <- eval0 <$!> addLams (psub^.dom) mty rhs

  -- register solution
  ES.solve m rhs

-- Unification
--------------------------------------------------------------------------------

unify :: LvlArg => UnifyState -> G -> G -> IO ()
unify st t t' = uf
