
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
      destructive updates. Allowed updates:
      - solving irrelevant metas
      - eta-expanding metas

    - we need to pass backtracking/non-backtracking toggle arg to psub,
      or put it *in* psub

  unification:
    - 4 states, rigid, flex, irrelevant, full
    - see smalltt for rigid, flex, full
    - irrelevant:
      - backtracking mode, no unfolding, we solve only irrelevant metas, always succeeds
    - eta-short solutions:
      - we try to solve, on any failure we retry with expansion
      - pruning is allowed in speculative eta-short solutions! That's because we
        would repeat the same prunings in the eta-long retries.
    - flex-flex:
      - we try to invert left spine *with pruning disabled*, else try the right spine
    - TraceEq: TODO
    - Setoid ops: TODO

  solving ?m spine = rhs
    - NEW algorithm: solution is computed by single pass on reversed spine,
      handles all inversion & expansion. See notes below.
    - When we get down to the rhs substitution, we check relevance. If we're irrelevant,
      we catch rhs subst failure and instead return a fresh meta.

  psub:
    - We have *partial values*. Eliminators propagate error values in eval.
      Error values never appear in conversion checking or unification.
    - We have to tag bound vars with types in general, for nested spine inversions.
    - We have *forcing* with psub. We have to disambiguate dom/cod vars here,
      so we simply tag dom vars, and only substitute cod vars in forcing.
    - 3 modes, rigid, flex, full (see smalltt)

  pruning
    - NEW: see notes below.


PRUNING:
    Note: only UNDEF boundvars can be pruned, non-linear bound vars can't!
    assume σ : PSub Δ Γ, always force terms with it, extend it under binders.
    question: should prA, wkA be Val functions or terms? Probably yes.


    pruneSp : ((Γ Γ* : Con) × (wk : Sub Γ Γ*) × (pr : PSub Γ* Γ)) → (A : Ty Γ) → Spine Δ → Tm Γ A
    pruneTm : ((Γ Γ* : Con) × (wk : Sub Γ Γ*) × (pr : PSub Γ* Γ)) → (A : Ty Γ) → (t : Tm Δ A[σ])
              → ((A* : Ty Γ*) × (wkA : Tm (Γ,A) A*[wk]) × (prA : PTm (Γ*,A*) A[wk⁻¹]))

    pruneSp Γ Γ* wk pr ((a : A) → B a) ($t sp) =
      (A*, wkA, prA) <- pruneTm Γ Γ* wk pr A t
      sol <- pruneSp (Γ,A) (Γ*,A*) (wk, wkA) (pr, prA) sp
      return (λ (a:A).sol)

    pruneSp Γ Γ* wk pr A ∙ =
      m <- fresh meta : Tm Γ* A[pr]
      m[wk] : Tm Γ A[pr][wk]
            : Tm Γ A
      return m[wk]

    pruneSp Γ Γ* wk pr ((a : A) × B a) (.1 sp) =
      sol <- pruneSp Γ Γ* wk pr A
      m   <- freshMeta : Tm Γ (B sol)
      return (sol, m)

    pruneSp Γ Γ* wk pr ((a : A) × B a) (.2 sp) =
      m   <- freshMeta : Tm Γ A
      sol <- pruneSp Γ Γ* wk pr (B sol)
      return (m, sol)


    + force terms with σ everywhere below!

    pruneTm Γ Γ* wk pr A UNDEF =
      A*  := ⊤
      wkA := tt
      prA := UNDEF

    pruneTm Γ Γ* wk pr A (x sp) =
      A*  = A
      wkA = a.a
      prA = a*.a*

    pruneTm Γ Γ* wk pr A (?x sp) =
      throw error (can't prune metas from metas)

    pruneTm Γ Γ* wk pr (a : A, B a) (t, u) =
      A*, wkA, prA <- pruneTm Γ Γ* wk pr A t
      B*, wkB, prB <- pruneTm (Γ,A) (Γ*,A*) (wk, wkA) (pr, prA) (B t) u
      return
        (a* : A*, B* a*)
        (wkA, wkB)
        (prA, prB)

    pruneTm Γ Γ* wk pr ((a : A) → B a) (λ a. t) =

      B*, wkB, prB <- pruneTm (Γ, a:A) (Γ*, A[pr]) (B a) t

      wkB : Γ, a:A, b : B a ⊢ B*[wk] a
      prB : Γ*, a:A[pr], b* : B* ⊢ B[pr]

      return
        A*  := (a : A[pr]) → B*
        wkA := (f : (a : A) → B). λ a. wkB [f a]
        prA := (f : (a : A[pr]) → B*). λ a. prB [f a]

BASIC TOP SPINE INVERSION
  (no nested inversion, only projections and tuples allowed in spine)

  assume ?x metavar, rhs : Tm Δ A

  invSp : PSub Γ Δ → (A : Ty Γ) → Spine Δ → Tm Γ
  invTm : (σ : PSub Γ Δ) → Tm Δ A[_] → Tm Γ A → PSub Γ Δ     -- _ is previous spine entries

  invSp σ A ε = rhs[σ]

  invSp σ ((a : A) → B a) ($t sp) =
    σ' <- invTm {Γ,a:A}{Δ} σ t
    sol <- invSp σ' (B a) sp
    return λ (a : A). sol

  invSp σ (a : A, B a) (.1 sp) =
    sol <- invSp σ A sp
    m   <- freshMeta Γ (B sol)
    return (sol, m)

  invSp σ (a : A, B a) (.2 sp) =
    m   <- freshMeta Γ A
    sol <- invSp σ (B m) sp
    return (m, sol)

  invSp σ A (+elim sp) =
    ensure that rhs is of the form (rhs' +elim sp)
    return (rhs' +elim sp)[σ]

  invTm σ (t, u) rhs =
    σ <- invTm σ t (rhs.1)
    σ <- invTm σ u (rhs.2)
    return σ

  invTm σ ((x:A) projs) rhs | x solvable
    return (σ, x ↦ invProjs A projs rhs)

  invProjs A ε rhs = rhs
  invProjs (a : A, B a) (.1 projs) rhs = (invProjs A projs rhs, UNDEF)
  invProjs (a : A, B a) (.2 projs) rhs = (UNDEF, invProjs (B UNDEF) projs rhs)


EXTENSION of PSub with a mapping: we MERGE the existing value and the new value

  merge (x sp) (y sp') | x /= y, irrelevant (x sp) = x sp
                       | x /= y = NONLINEAR
                       | x == y = x (mergeSp sp sp')

  merge NONLINEAR u = NONLINEAR
  merge t NONLINEAR = NONLINEAR
  merge UNDEF u = u
  merge t UNDEF = t

  merge (t, u) (t', u') = (merge t t', merge u u')
  merge (t, u) t'       = (merge t t'.1, merge u t'.2)
  merge t      (t', u') = (merge t.1 t', merge t.2 u')

  merge (λ x. t) (λ x. t') = λ x. merge t t'
  merge (λ x. t) t'        = λ x. merge t (t' x)
  merge t (λ x. t')        = λ x. merge (t x) t'



NOW WE TRY NESTED INVERSION
--------------------------------------------------------------------------------

top-level invSp is the same
invTm is generalized + we have nested invSp
TODO: in implementation, can we write just one code for top+local invSp, by abstracting over stuff?

- Δ is consists of Δᵤ|Δₛ|Δₚ, where u is unsolvable, s is solvable and p is "parameters"
- at the top level, we have = ∙|Δ|∙

invTm : {Γ Δᵤ Δₛ Δₚ} → (σ : PSub Γ Δ) → Tm Δ A[_] → Tm Γ A → PSub Γ Δ  -- _ consists of prev spine entries
invSp : {Γ Δᵤ Δₛ} → PSub Γ Δᵤₛ → (A : Ty Γ) → Spine Δ → Tm Γ

invSp Γ (Δᵤ|Δₛ) σ A ε = rhs[σ]

invSp Γ (Δᵤ|Δₛ) σ ((a : A) → B a) ($t sp) =
  σ'  <- invTm (Γ, a : A) (Δᵤ|Δₛ|∙) σ t
  sol <- invSp (Γ, a: A) (Δᵤ|Δₛ) σ' (B a) sp
  return λ (a : A). sol

invSp σ (a : A, B a) (.1 sp) =
  sol <- invSp σ A sp
  m   <- if TOP then (freshMeta Γ (B sol)) else UNDEF
  return (sol, m)

invSp σ (a : A, B a) (.2 sp) =
  m   <- if TOP then (freshMeta Γ A) else UNDEF
  sol <- invSp σ (B m) sp
  return (m, sol)

invSp σ A (+elim sp) =
  if TOP then
    ensure that rhs is of the form (rhs' +elim sp)
    return (rhs' +elim sp)[σ]
  else
    FAIL

invTm Γ (Δᵤ|Δₛ|Δₚ) σ (t, u) rhs =
  σ <- invTm Γ (Δᵤ|Δₛ|Δₚ) σ t (rhs.1)
  σ <- invTm Γ (Δᵤ|Δₛ|Δₚ) σ u (rhs.2)
  return σ

invTm Γ (Δᵤ|Δₛ|Δₚ) σ (λ (a : A). t) rhs =
  σ <- invTm (Γ,a:A) (Δᵤ|Δₛ|Δₚ,x:A[σ]) (σ,x↦a) t (rhs a)
  return (delete {x↦_} from σ)

invTm Γ (Δᵤ|Δₛ|Δₚ) σ ((x:A) sp) rhs | x ∈ Δₛ =
  sol <- invSp Γ ΔᵤΔₛ|Δₚ A sp
  return (σ, x ↦ sol)

invTm Γ (Δᵤ|Δₛ|Δₚ) σ ((x:A) sp) rhs | x ∉ Δₛ =
  FAIL

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
