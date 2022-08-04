
module Unification where

import IO
import Control.Exception

import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
-- import qualified Data.Ref.F as RF
import Lens.Micro.Platform

import Common
import Values
import Evaluation
import ElabState
-- import Errors
import qualified Syntax as S

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

-}



--------------------------------------------------------------------------------

data UnifyEx = CantUnify | CantSolveFrozenMeta | CantSolveFlexMeta
  deriving (Eq, Show)
instance Exception UnifyEx

-- | Bump the `Lvl` and get a fresh variable.
newVar :: Ty -> (LvlArg => Val -> a) -> LvlArg => a
newVar a cont =
  let v = Var ?lvl a in
  let ?lvl = ?lvl + 1 in
  seq ?lvl (cont v)
{-# inline newVar #-}

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
  m <- newMeta (G closed fclosed)
  pure $ S.InsertedMeta m ?pruning


-- Partial substitutions
--------------------------------------------------------------------------------

-- | Values appearing in partial substitutions.
--   They can be bound vars, projections or pairings, where one field
--   of a pairing is always undefined (i.e. a "scope error" value).
data PSVal
  = PSVar Lvl ~Ty
  | PSProj1 PSVal
  | PSProj2 PSVal
  | PSProjField PSVal ~Ty Int
  | PSPair1 PSVal          -- pairing whose second field is undefined
  | PSPair2 PSVal          -- pairing whose first field is undefined
  | PSPairN PSVal Int      -- pairing whose N-th field projection is defined, and undefined elsewhere

data PartialSub = PSub {
    partialSubDomIdEnv :: Env             -- Identity env from Γ to Γ, serves as the list of Γ types.
                                          -- We need this when we want to evaluate the result term of
                                          -- partial substitution, which is in Γ.
  , partialSubOcc      :: Maybe MetaVar   -- optional occurs check
  , partialSubDom      :: Lvl             -- size of Γ
  , partialSubCod      :: Lvl             -- size of Δ
  , partialSubSub      :: IM.IntMap PSVal -- Partial map from Δ vars to Γ values. A var which is not
                                          -- in the map is mapped to a scope error, but note that
                                          -- PSVal-s can contain scope errors as well.
  }

makeFields ''PartialSub

-- | lift : (σ : PSub Γ Δ) → PSub (Γ, x : A[σ]) (Δ, x : A)
--   Note: gets A[σ] as Ty input, not A!
lift :: PartialSub -> Ty -> PartialSub
lift (PSub idenv occ dom cod sub) asub =
  let psvar = PSVar dom asub
      var   = Var dom asub
  in PSub (EDef idenv var) occ (dom + 1) (cod + 1) (IM.insert (coerce cod) psvar sub)

-- | skip : PSub Γ Δ → PSub Γ (Δ, x : A)
skip :: PartialSub -> PartialSub
skip (PSub idenv occ dom cod sub) = PSub idenv occ dom (cod + 1) sub

--------------------------------------------------------------------------------

solve :: LvlArg => MetaVar -> Spine -> Val -> IO ()
solve = uf

solve' :: MetaVar -> (PartialSub, Maybe S.Pruning) -> Val -> IO ()
solve' m (psub, pruneNonLinear) = do
  uf


-- | Spine inversion helper data type, to help unboxing and forcing. Contains:
--   spine length, set of domain vars, inverse substitution, pruning of
--   nonlinear entries, flag indicating linearity.
data Inversion = Invert {
    inversionSpineLen :: Lvl
  , inversionDomVars  :: IS.IntSet
  , inversionSub      :: IM.IntMap Val
  , inversionIsLinear :: Bool
  }

makeFields ''Inversion


invertRigid :: RigidHead -> Spine -> Ty -> Inversion -> PSVal -> IO Inversion
invertRigid rh sp a psub psval = do
  let go sp psval = invertRigid rh sp a psub psval; {-# inline go #-}
  case sp of

    -- if relevant, handle linearity, else just update psub
    SId -> case rh of
      RHLocalVar (Lvl x) -> _


    SProj1 sp         -> go sp (PSPair1 psval)
    SProj2 sp         -> go sp (PSPair2 psval)
    SProjField sp _ n -> go sp (PSPairN psval n)
    _                 -> throwIO CantUnify


invertVal :: LvlArg => Val -> Inversion -> PSVal -> IO Inversion
invertVal v psub psval = do

  forceAll v >>= \case

    Rigid rh sp a -> do
      invertRigid rh sp a psub psval

    Pair _ t u -> do
      psub <- invertVal t psub (PSProj1 psval)
      invertVal u psub (PSProj2 psval)

    _ ->
      throwIO CantUnify


-- | Input: a projection-free spine.
--   Inverts the spine and returns a pruning of non-linear entries. Does not yet
--   return a PartialSub! We still need the domain idEnv, and we compute that in
--   the next step, when pruning the meta type.
preInvertSpine :: LvlArg => Spine -> IO Inversion
preInvertSpine sp = do
  let go sp = preInvertSpine sp; {-# inline go #-}
  case sp of
    SId         -> pure (Invert 0 mempty mempty True)
    SApp sp t i -> do
      psub <- go sp
      invertVal t (psub & spineLen +~ 1) (PSVar (psub^.spineLen) _) -- Need meta arg types!


        -- let invertVal x invx = case IS.member x domvars of
        --       True  -> pure $! Invert (dom + 1) domvars
        --                                  (IM.delete x sub) (Nothing : pr) False

        --       False -> pure $! Invert (dom + 1) (IS.insert x domvars)
        --                                  (IM.insert x invx sub) (Just i : pr) isLinear



        -- let ?lvl = dom

        -- -- TODO: sigma inversions
        -- forceAll t >>= \case
        --   Var (Lvl x) a -> invertVal x (Var dom uf)
        --   _             -> throwIO CantUnify

    SProj1{}     -> impossible
    SProj2{}     -> impossible
    SProjField{} -> impossible


-- | Remove some arguments from a closed iterated (Set) Pi type. Return the pruned type
--   + the identity environment containing the variables with the binder types.
pruneTy :: S.RevPruning -> Ty -> IO (S.Ty, Env)
pruneTy (S.RevPruning# pr) a = go pr (PSub ENil Nothing 0 0 mempty) a where

  go :: S.Pruning -> PartialSub -> Ty -> IO (S.Ty, Env)
  go pr psub a = do
    let ?lvl = psub^.cod
    a <- forceAll a
    case (pr, a) of

      ([], a) -> do
        a <- psubst psub a
        pure $! (a // psub^.domIdEnv)

      (Just{} : pr, Pi x i a b) -> do
        (a', va') <- psubst' psub a
        (t, idenv) <- go pr (lift psub va') (b $$ Var (psub^.cod) va')
        pure (S.Pi x i a' t, idenv)

      (Nothing : pr, Pi x i a b) -> do
        (_, va') <- psubst' psub a
        go pr (skip psub) (b $$ Var (psub^.cod) va')

      (Just{} : pr, El (Pi x i a b)) -> do
        (a', El -> va') <- psubst' psub a
        (t, idenv) <- go pr (lift psub va') (b $$ Var (psub^.cod) va')
        pure (S.Pi x i a' t, idenv)

      (Nothing : pr, El (Pi x i a b)) -> do
        (_, El -> va') <- psubst' psub a
        go pr (skip psub) (b $$ Var (psub^.cod) va')

      _ -> impossible

-- | Invert a spine.
-- invertSpine :: LvlArg => MetaVar -> Spine -> IO PartialSub
-- invertSpine m sp = do
--   uf


-- Eta expansion of metas
--------------------------------------------------------------------------------

-- | Helper synonym for the args that we need when eta-expanding metas.
type WithExpansion a = LvlArg => S.LocalsArg => S.PruningArg => EnvArg => a


-- | Create a fresh eta-expanded value with the same type as the given meta,
--   expanded along the given spine.
expansionOfMeta :: MetaVar -> Spine -> IO Val
expansionOfMeta meta sp = do
  a <- unsolvedMetaType meta
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


-- partial substitution
--------------------------------------------------------------------------------

flexPSubst :: PartialSub -> Val -> IO S.Tm
flexPSubst = uf

rigidPSubst :: PartialSub -> Val -> IO S.Tm
rigidPSubst = uf

fullPSubst :: PartialSub -> Val -> IO ()
fullPSubst = uf


psubst :: PartialSub -> Val -> IO S.Tm
psubst = rigidPSubst

psubst' :: PartialSub -> Val -> IO (S.Tm, Val)
psubst' sigma@(PSub idenv occ dom cod sub) t = do
  t <- psubst sigma t
  let ?env = idenv; ?lvl = dom
  let vt = eval t
  pure (t, vt)


-- Unification
--------------------------------------------------------------------------------

unify :: LvlArg => UnifyState -> G -> G -> IO ()
unify st t t' = uf

-- unify :: LvlArg => Val -> Val -> IO ()
-- unify t u = do
--   let go = conv
--       {-# inline go #-}

--       goBind a t u = do
--         let v = Var ?lvl a
--         let ?lvl = ?lvl + 1
--         conv (t $$ v) (u $$ v)
--       {-# inline goBind #-}

--       guardP hl (cont :: IO ()) = case hl of
--         P -> pure ()
--         _ -> cont
--       {-# inline guardP #-}

--   t <- forceAll t
--   u <- forceAll u
--   case (t, u) of

--     -- canonical
--     ------------------------------------------------------------
--     (Pi _ x i a b, Pi _ x' i' a' b') -> do
--       unless (i == i') $ throwIO Diff
--       go a a'
--       goBind a b b'

--     (Sg _ x a b, Sg _ x' a' b') -> do
--       go a a'
--       goBind a b b

--     (Set  , Set  ) -> pure ()
--     (Prop , Prop ) -> pure ()
--     (Top  , Top  ) -> pure ()
--     (Bot  , Bot  ) -> pure ()
--     (El a , El b ) -> go a b
--     (Tt   , Tt   ) -> pure ()

--     (RigidEq a t u  , RigidEq a' t' u') -> go a a' >> go t t' >> go u u'
--     (Lam hl _ _ _ t , Lam _ _ _ a t'  ) -> guardP hl $ goBind a t t'
--     (Pair hl t u    , Pair _ t' u'    ) -> guardP hl $ go t t' >> go u u'

--     -- eta
--     --------------------------------------------------------------------------------

--     (Lam hl _ i a t , t'              ) -> guardP hl $ goBind a t (Cl \u -> app t' u i)
--     (t              , Lam hl _ i a t' ) -> guardP hl $ goBind a (Cl \u -> app t u i) t'
--     (Pair hl t u    , t'              ) -> guardP hl $ go t (proj1 t') >> go u (proj2 t')
--     (t              , Pair hl t' u'   ) -> guardP hl $ go (proj1 t) t' >> go (proj2 t) u'

--     -- non-canonical
--     ------------------------------------------------------------

--     (Irrelevant , _         ) -> pure ()
--     (_          , Irrelevant) -> pure ()

--     (Flex h sp, _) -> flexRelevance h sp >>= \case
--       RIrr       -> pure ()
--       _          -> throwIO $ BlockOn (flexHeadMeta h)

--     (_, Flex h sp) -> flexRelevance h sp >>= \case
--       RIrr       -> pure ()
--       _          -> throwIO $ BlockOn (flexHeadMeta h)

--     (FlexEq x _ _ _, _) -> throwIO $ BlockOn x
--     (_, FlexEq x _ _ _) -> throwIO $ BlockOn x

--     (Rigid h sp, Rigid h' sp') -> rigidRelevance h sp >>= \case
--       RIrr       -> pure ()
--       RBlockOn x -> throwIO $ BlockOn x
--       RRel       -> convRigidRel h sp h' sp'

--     (Rigid h sp, _) -> rigidRelevance h sp >>= \case
--       RIrr       -> pure ()
--       RBlockOn x -> throwIO $ BlockOn x
--       RRel       -> throwIO Diff

--     (_, Rigid h' sp') -> rigidRelevance h' sp' >>= \case
--       RIrr       -> pure ()
--       RBlockOn x -> throwIO $ BlockOn x
--       RRel       -> throwIO Diff

--     -- canonical mismatch is always a failure, because we don't yet
--     -- have inductive data in Prop, so mismatch is only possible in Set.
--     --------------------------------------------------------------------------------

--     (a, b) -> throwIO Diff
