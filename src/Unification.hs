
module Unification where

import IO
import Control.Exception

import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.Ref.F as RF

import Common
import Values
import Evaluation
import Errors
import qualified Syntax as S

-- first round:
--   basic unification (pattern unification)
--   sigma unification
--       ?0 (x, y, z) =? rhs
--       (?0 x y).field =? rhs
--         ?0 (\x y. f (x, y)) =? rhs (NOT SUPPORTED)
--
--   pruning:
--       ?0 =? ?1 y -> ?1 y      (y is bound var)
--          ?1 := \_. ?2         (?2 is fresh)
--       ?0 := ?2 -> ?2
--   unfolding control
--
--   freezing
--   postponing (for frecord field lookup, implicit labda insertion)

-- next round:
--   postpone unification by inserting coe
--      idea:  f t u =? f t' u'                 f t True =? f t' False
--          t =? t' is postponed
--          we get p : t = t'
--          coe _ _ p u =? u'
--
--
--   result of unif:
--      t =? t'      - Success  (t ≡ t')
--                   - Success with postponed constraints
--                   - Fail




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

--------------------------------------------------------------------------------

data PartialSub = PSub {
    occ :: Maybe MetaVar   -- optional occurs check
  , dom :: Lvl             -- size of Γ
  , cod :: Lvl             -- size of Δ
  , sub :: IM.IntMap Val}  -- mapping from Δ vars to Γ values

-- | lift : (σ : Psub Γ Δ) → Psub (Γ, x : A[σ]) (Δ, x : A)
lift :: PartialSub -> Ty -> PartialSub
lift (PSub occ dom cod sub) a =
  PSub occ (dom + 1) (cod + 1) (IM.insert (unLvl cod) (Var dom a) sub)

-- | skip : Psub Γ Δ → Psub Γ (Δ, x : A)
skip :: PartialSub -> PartialSub
skip (PSub occ dom cod sub) =
  PSub occ dom (cod + 1) sub

--------------------------------------------------------------------------------

-- | invert : (Γ : Cxt) → (spine : Sub Δ Γ) → Psub Γ Δ
--   Optionally returns a pruning of nonlinear spine entries, if there's any.
invert :: Lvl -> Spine -> IO (PartialSub, Maybe S.Pruning)
invert gamma sp = do

  let go :: Spine -> IO (Lvl, IS.IntSet, IM.IntMap Val, S.Pruning, Bool)
      go SId           = pure (0, mempty, mempty, [], True)
      go (SApp sp t i) = do
        (!dom, !domvars, !sub, !pr, !isLinear) <- go sp

        let invertVal x invx = case IS.member x domvars of
              True  -> pure (dom + 1, domvars,             IM.delete x sub     , Nothing : pr, False   )
              False -> pure (dom + 1, IS.insert x domvars, IM.insert x invx sub, Just i  : pr, isLinear)

        let ?lvl = dom
        forceAll t >>= \case
          Var (Lvl x) a -> invertVal x (Var dom uf)
          _             -> throwIO CantUnify

      go SProj1{}     = impossible
      go SProj2{}     = impossible
      go SProjField{} = impossible

  (dom, domvars, sub, pr, isLinear) <- go sp
  pure (PSub Nothing dom gamma sub, pr <$ guard isLinear)

-- -- | Remove some arguments from a closed iterated Pi type.
-- pruneTy :: S.RevPruning -> Ty -> IO S.Ty
-- pruneTy (S.RevPruning# pr) a = go pr (PSub Nothing 0 0 mempty) a where
--   go :: S.Pruning -> PartialSub -> Ty -> IO S.Ty
--   go pr psub a = do
--     let ?lvl = dom psub
--     fa <- forceAll a
--     case (pr, fa) of
--       ([]          , a           ) -> psubst psub a
--       (Just{}  : pr, Pi _ x i a b) -> S.Pi S x i <$!> psubst psub a
--                                                  <*!> go pr (lift psub a) (b $$ Var (cod psub) a)
--       (Nothing : pr, Pi _ x i a b) -> go pr (skip psub) (b $$ Var (cod psub) a)
--       _                            -> impossible

psubst :: PartialSub -> Val -> IO S.Tm
psubst = uf
--------------------------------------------------------------------------------

-- unify :: LvlArg => UnifyState -> G -> G -> IO ()
-- unify st t t' =

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
