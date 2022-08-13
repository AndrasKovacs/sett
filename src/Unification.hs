
module Unification where

import Common

import IO
import Control.Exception

import qualified Data.IntMap as IM
-- import qualified Data.IntSet as IS
import qualified Data.Ref.F as RF
import Lens.Micro.Platform hiding (to)

import Values
import Evaluation
import qualified ElabState as ES
-- import Errors
import qualified Syntax as S

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
  , partialSubAllowPruning :: AllowPruning   -- Is pruning allowed during partial substitution.
  }
makeFields ''PartialSub

-- | Evaluate something in the domain of the `PartialSub`.
evalInDom :: PartialSub -> S.Tm -> Val
evalInDom psub t = let ?env = psub^.domVars; ?lvl = psub^.dom in eval t

-- | lift : (σ : PSub Γ Δ) → PSub (Γ, x : A[σ]) (Δ, x : A)
--   Note: gets A[σ] as Ty input, not A!
lift :: PartialSub -> Ty -> PartialSub
lift (PSub idenv occ dom cod sub allowpr) ~asub =
  let var = Var dom asub
  in PSub (EDef idenv var) occ (dom + 1) (cod + 1)
          (IM.insert (coerce cod) var sub) allowpr

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
        t <- psubst (lift psub va) (t $$ Var ?lvl va)
        pure $! k a t
      {-# inline goBind #-}

      goUnfolding unf act =
        catch @UnifyEx act (\_ -> go unf)

      goRigid h sp = do
        h <- case h of
          RHLocalVar x a True  -> pure (S.LocalVar (lvlToIx x))
          RHLocalVar x a False -> impossible
          RHPostulate x a      -> pure (S.Postulate x a)
          RHExfalso a p        -> S.Exfalso <$!> go a <*!> go p
          RHCoe a b p t        -> S.Coe <$!> go a <*!> go b <*!> go p <*!> go t
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
            (m, sp) <- prune psub m sp
            goSp (S.Meta m) sp
        FHCoe x a b p t -> do
          h <- S.Coe <$!> goFlex a <*!> goFlex b <*!> goFlex p <*!> goFlex t
          goSpFlex h sp

  forceWithPSub psub topt >>= \case
    Rigid h sp _       -> goRigid h sp
    RigidEq a t u      -> S.Eq <$!> go a <*!> go t <*!> go u
    Flex h sp _        -> goFlex' h sp
    FlexEq x a t u     -> S.Eq <$!> go a <*!> go t <*!> go u
    Unfold uh sp unf _ -> goUnfolding unf $ goUnfold uh sp
    TraceEq a t u unf  -> goUnfolding unf $ S.Eq <$!> goFlex a <*!> goFlex t <*!> goFlex u
    UnfoldEq a t u unf -> goUnfolding unf $ S.Eq <$!> goFlex a <*!> goFlex t <*!> goFlex u
    Set                -> pure S.Set
    El a               -> S.El <$!> go a
    Pi x i a b         -> goBind a b (S.Pi x i)
    Lam sp x i a t     -> goBind a t (S.Lam sp x i)
    Sg x a b           -> goBind a b (S.Sg x)
    Pair sp t u        -> S.Pair sp <$!> go t <*!> go u
    Prop               -> pure S.Prop
    Top                -> pure S.Top
    Tt                 -> pure S.Tt
    Bot                -> pure S.Bot
    Refl a t           -> S.Refl <$!> go a <*!> go t
    Sym a x y p        -> S.Sym <$!> go a <*!> go x <*!> go y <*!> go p
    Trans a x y z p q  -> S.Trans <$!> go a <*!> go x <*!> go y <*!> go z <*!> go p <*!> go q
    Ap a b f x y p     -> S.Ap <$!> go a <*!> go b <*!> go f <*!> go x <*!> go y <*!> go p
    Magic m            -> throwIO CantUnify

psubst' :: PartialSub -> Val -> IO (S.Tm, Val)
psubst' psub t = do
  t <- psubst psub t
  let ~vt = evalInDom psub t
  pure (t, vt)


----------------------------------------------------------------------------------------------------
-- Pruning
----------------------------------------------------------------------------------------------------

-- can we replace pruned things with Top?
-- prunings: lambda, pairing, neutral, undefined

data Pr = PLam Pr | PPair Pr Pr | PKeep | PDrop

{-
prTy :: LvlArg => Pr -> Ty -> Ty
prTy p a = case (p, runIO (forceSet a)) of
  (PPair p1 p2 , Sg x a b  ) -> Sg x (prTy p1 a) $ Cl \x -> prTy p2 (b $$ fromPr p1 a x)
  (PLam p      , Pi x i a b) -> Pi x i a $ Cl \x -> prTy p (b $$ x)
  (PKeep       , a         ) -> a
  (PDrop       , a         ) -> El Top

toPr :: LvlArg => Pr -> Ty -> Val -> Val
toPr pr a t = case (pr, runIO (forceSet a)) of
  (PPair p1 p2 , Sg x a b  ) -> let t1 = proj1 t; t2 = proj2 t in
                                Pair S (toPr p1 a t1) (toPr p2 (b $$ t1) t2)
  (PLam p      , Pi x i a b) -> Lam S x i a $ Cl \x -> toPr p (b $$ x) (app t x i)
  (PKeep       , a         ) -> t
  (PDrop       , a         ) -> Tt

fromPr :: LvlArg => Pr -> Ty -> Val -> Val
fromPr pr a t = case (pr, runIO (forceSet a)) of
  (PPair p1 p2 , Sg x a b  ) -> let t1 = proj1 t; t2 = proj2 t; fst = fromPr p1 a t1 in
                                Pair S fst (fromPr p2 (b $$ fst) t2)
  (PLam p      , Pi x i a b) -> Lam S x i a $ Cl \x -> fromPr p (b $$ x) (app t x i)
  (PKeep       , a         ) -> t
  (PDrop       , a         ) -> Magic Undefined
-}

{-
prTy :: LvlArg => Pr -> Ty -> Ty
prTy p a = case (p, runIO (forceSet a)) of

  (PPair p1 p2 , Sg x a b  ) -> case prTy p1 a of
                                  El Top -> prTy p2 (b $$ fromPr p1 a Tt)
                                  a'     -> Sg x a' $ Cl \x -> prTy p2 (b $$ fromPr p1 a x)

  (PLam p      , Pi x i a b) -> Pi x i a $ Cl \x -> prTy p (b $$ x)
  (PKeep       , a         ) -> a
  (PDrop       , a         ) -> El Top

toPr :: LvlArg => Pr -> Ty -> Val -> Val
toPr pr a t = case (pr, runIO (forceSet a)) of

  (PPair p1 p2 , Sg x a b  ) -> let t1 = proj1 t; t2 = proj2 t in
                                case prTy p1 a of
                                  El Top -> toPr p2 (b $$ t1) t2
                                  _      -> Pair S (toPr p1 a t1) (toPr p2 (b $$ t1) t2)

  (PLam p      , Pi x i a b) -> Lam S x i a $ Cl \x -> toPr p (b $$ x) (app t x i)
  (PKeep       , a         ) -> t
  (PDrop       , a         ) -> Tt

fromPr :: LvlArg => Pr -> Ty -> Val -> Val
fromPr pr a t = case (pr, runIO (forceSet a)) of

  (PPair p1 p2 , Sg x a b  ) -> case prTy p1 a of
                                  El Top -> let fst = fromPr p1 a Tt in
                                            Pair S fst (fromPr p2 (b $$ fst) t)
                                  _      -> let t1 = proj1 t; t2 = proj2 t; fst = fromPr p1 a t1 in
                                            Pair S fst (fromPr p2 (b $$ fst) t2)

  (PLam p      , Pi x i a b) -> Lam S x i a $ Cl \x -> fromPr p (b $$ x) (app t x i)
  (PKeep       , a         ) -> t
  (PDrop       , a         ) -> Magic Undefined

-}


{-
data PrRes = PrRes {ty :: Ty, to :: Val -> Val, from :: Val -> Val}

pr :: LvlArg => Pr -> Ty -> PrRes
pr p a = case (p, runIO (forceSet a)) of
  (PPair p1 p2, Sg x a b) ->
    let PrRes a' toa' froma' = pr p1 a in
    PrRes
      (Sg x a' $ Cl \x -> ty (pr p2 (b $$ froma' x)))
      (\t -> let t1 = proj1 t; t2 = proj2 t in
             Pair S (toa' t1) (to (pr p2 (b $$ t1)) t2))
      (\t -> let t1 = proj1 t; t2 = proj2 t; fst = froma' t1 in
             Pair S fst (from (pr p2 (b $$ fst)) t2))

-}

str :: S.Ty -> S.Ty
str = uf

from :: LvlArg => EnvArg => Ty -> Val -> Val
from = uf

-- pr :: LvlArg => EnvArg => Ty -> S.Ty
-- pr a = case runIO (forceSet a) of
--   Sg x a b -> case pr a of
--     a'@(S.El S.Top) -> let v = Var ?lvl a' in let ?lvl = ?lvl+1; ?env = EDef ?env v
--     a'              -> _

    -- case pr a of
    -- a' -> let v = Var ?lvl a' in let ?lvl = ?lvl+1; ?env = EDef ?env v in
    --       case pr (b $$ _) of
    --         _ -> uf




-- curryTy :: Ty -> Ty
-- curryTy = \case
--   Pi x i (Sg y a b) c -> curryTy (Pi x i a $ Cl \a -> Pi nx i (b $$ a) $ Cl \b -> c $$ Pair S a b)
--   Pi x i a b          -> Pi x i a $ Cl \a -> curryTy (b $$ a)

-- curryTy :: Ty -> Ty
-- curryTy = \case
--   Pi x i a b -> case curryTy a of
--     Sg y a0 a1 -> curryTy (Pi x i a0 $ Cl \x0 -> Pi nx i (a1 $$ x0) $ Cl \x1 -> _)
--     ca         -> Pi x i ca $ Cl \x -> curryTy (b $$ (from a $$ x))
--   -- Pi x i (Sg y a b) c -> curryTy (Pi x i a $ Cl \a -> Pi nx i (b $$ a) $ Cl \b -> c $$ Pair S a b)
--   -- Pi x i a b          -> Pi x i a $ Cl \a -> curryTy (b $$ a)

-- to :: Ty -> Closure
-- to = uf

-- from :: Ty -> Closure
-- from = uf






{-
prTy :: Ty -> Ty
prTy = \case
  Sg x a b -> Sg x (prTy a) (Cl \x -> prTy (b $$ (wkVal a $$ x)))
  El Top   -> Sg NUnused (El Top) (Cl \_ -> El Top)

prVal :: Ty -> Closure
prVal = \case
  Sg x a b -> Cl \t -> Pair S (prVal a $$ proj1 t) (prVal (b $$ proj1 t) $$ proj2 t)
  El Top   -> Cl \_ -> Pair S Tt Tt

  -- t.1 : a
  -- prVal a t.1 : prTy a

  -- goal : prTy (b (wkVal a (prVal a t.1)))
  --      : prTy (b t.1)

  -- t.2 : b t.1
  -- prVal (b t.1) t.2 : prTy (b t.1)

wkVal :: Ty -> Closure
wkVal = \case
  Sg x a b -> Cl \t -> let p1 = wkVal a $$ proj1 t in Pair S p1 (wkVal (b $$ p1) $$ (proj2 t))
  El Top   -> Cl \_ -> Tt

   -- t.1 : prTy a
   -- wkVal a t.1 : a

   -- goal :  b (wkVal a t.1)


   -- t.2 : prTy (b (wkVal a (t.1)))
   -- wkVal t.2 :

-}















-- prTy :: LvlArg => EnvArg => Ty -> S.Ty
-- prTy = \case
--   Sg x a b ->
--     let a'   = prTy a in
--     let ~va' = eval a' in
--     let b'   = (let var' = Var ?lvl va' in
--                 let ?lvl = ?lvl + 1
--                     ?env = EDef ?env var' in
--                 prTy (b $$ prVal a var')) in

--     S.Sg x a' b'

--   El Top -> S.Sg NUnused (S.El S.Top) (S.El S.Top)

-- -- wkVal :: LvlArg => EnvArg => Ty -> Val -> Val
-- -- wkVal = uf

-- prVal :: LvlArg => EnvArg => Ty -> Val -> Val
-- prVal a t = case a of
--   Sg x a b -> Pair S (prVal a (proj1 t)) _

--   -- proj2 t : B (proj1 t)



-- pruneVal :: PartialSub -> Env -> PartialSub -> Ty -> Val -> IO (Ty, Closure, IOClosure)
-- pruneVal psub wk prune ty v = do

--   let (forceSetF, quoteF, appClF) = let ?lvl = prune^.cod in (forceSet, quote, ($$))
--   let (quoteP, appIOClP) = let ?lvl = prune^.dom in (quote, appIOCl)

--   v  <- forceAllWithPSub psub v
--   ty <- forceSetF ty
--   case (ty, v) of

--     (a, Rigid{}) -> do
--       a' <- snd <$!> psubst' prune a
--       pure ( a'
--            , Cl \x -> evalIn (prune^.cod) wk $ quoteP UnfoldNone x
--            , IOCl \x -> snd <$!> psubst' prune x )

--     (a, Magic Undefined) -> do
--       pure (El Top
--            , Cl \_ ->  Tt
--            , IOCl \_ -> pure $ Magic Undefined)

--     -- closure & Val strengthening is awful

--     -- (Sg x a b, Pair _ t u) -> do
--     --   (a', wkA, prA) <- pruneVal psub wk prune a t
--     --   let varF   = Var (prune^.cod) a
--     --   let varP   = Var (prune^.dom) a'
--     --   let wk'    = EDef wk varF
--     --   prAvarP <- appIOClP prA varP
--     --   let prune' = prune & dom +~ 1
--     --                      & cod +~ 1
--     --                      & domVars %~ (`EDef` varP)
--     --                      & sub %~ IM.insert (unLvl (prune^.cod)) prAvarP
--     --   (b', wkB, prB) <- pruneVal psub wk' prune' (appClF b varF) u
--     --   pure (Sg x a' (closeVal (prune^.dom) (prune^.domVars) b')
--     --       , Cl (\ab -> Pair S (wkA $$ proj1 ab) (wkB $$ proj2 ab)) -- TODO: wkB, prB strengthening?
--     --       , IOCl (\ab -> _))


-- -- ambient PSub, Env Γ Γ, Env Γ Γ*, PSub Γ* Γ, Locals Γ, Locals Γ*, SpineTy, Spine
-- pruneSp :: PartialSub -> Env -> Env -> PartialSub -> S.Locals -> S.Locals -> Ty -> Spine -> IO S.Tm
-- pruneSp psub fvars wk prune fls prls spty sp = do

--   let (quoteF, forceSetF, evalF, appClF, freshMetaF) =
--         let ?lvl = prune^.cod; ?env = fvars; ?locals = fls
--         in (quote, forceSet, eval, ($$), freshMeta)

--   let (quoteP, freshMetaP, forceSetP, appIOClP) =
--         let ?lvl = prune^.dom; ?locals = prls
--         in (quote, freshMeta, forceSet, appIOCl)

--   spty <- forceSetF spty
--   case (spty, sp) of

--     (a, SId) -> do
--       (_, a) <- psubst' prune a
--       quoteF UnfoldNone . evalIn (psub^.cod) wk <$!> freshMetaP (gjoin a)

--     (Pi x i a b, SApp t u _) -> do
--       (a', wkA, prA) <- pruneVal psub wk prune a u
--       let varF = Var (prune^.cod) a
--       let qa   = quoteF UnfoldNone a
--       forceSetP a' >>= \case
--         El Top -> do
--           sol <- pruneSp psub (EDef fvars varF) wk (prune & cod +~ 1) (S.LBind fls x qa) prls (appClF b varF) t
--           pure $ S.Lam S x i qa sol
--         a' -> do
--           let qa'    = quoteP UnfoldNone a'
--           let varP   = Var (prune^.dom) a'
--           let wk'    = EDef wk $! appClF wkA varF
--           prAvarP <- appIOClP prA varP
--           let prune' = prune & dom +~ 1
--                              & cod +~ 1
--                              & domVars %~ (`EDef` varP)
--                              & sub %~ IM.insert (unLvl (prune^.cod)) prAvarP
--           let prls' = S.LBind prls x qa'
--           let fls'  = S.LBind fls x qa
--           sol <- pruneSp psub (EDef fvars varF) wk' prune' fls' prls' (appClF b varF) t
--           pure $ S.Lam S x i qa sol

--     (El (Pi x i a b), SApp t u _) -> do
--       (a', wkA, prA) <- pruneVal psub wk prune a u
--       let varF = Var (prune^.cod) a
--       let qa   = quoteF UnfoldNone a
--       forceSetP a' >>= \case
--         El Top -> do
--           sol <- pruneSp psub (EDef fvars varF) wk (prune & cod +~ 1)
--                         (S.LBind fls x qa) prls (El (appClF b varF)) t
--           pure $ S.Lam S x i qa sol
--         a' -> do
--           let qa'    = quoteP UnfoldNone a'
--           let varP   = Var (prune^.dom) a'
--           let wk'    = EDef wk $! appClF wkA varF
--           prAvarP <- appIOClP prA varP
--           let prune' = prune & dom +~ 1
--                              & cod +~ 1
--                              & domVars %~ (`EDef` varP)
--                              & sub %~ IM.insert (unLvl (prune^.cod)) prAvarP
--           let prls' = S.LBind prls x qa'
--           let fls'  = S.LBind fls x qa
--           sol <- pruneSp psub (EDef fvars varF) wk' prune' fls' prls' (El (appClF b varF)) t
--           pure $ S.Lam P x i qa sol

--     (Sg x a b, SProj1 t) -> do
--       fst <- pruneSp psub fvars wk prune fls prls a t
--       snd <- freshMetaF (gjoin (appClF b (evalF fst)))
--       pure $ S.Pair S fst snd

--     (Sg x a b, SProj2 t) -> do
--       fst <- freshMetaF (gjoin a)
--       snd <- pruneSp psub wk fvars prune fls prls (appClF b (evalF fst)) t
--       pure $ S.Pair S fst snd

--     (El (Sg x a b), SProj1 t) -> do
--       fst <- pruneSp psub fvars wk prune fls prls (El a) t
--       snd <- freshMetaF (gjoin (El (appClF b (evalF fst))))
--       pure $ S.Pair P fst snd

--     (El (Sg x a b), SProj2 t) -> do
--       fst <- freshMetaF (gjoin (El a))
--       snd <- pruneSp psub fvars wk prune fls prls (El (appClF b (evalF fst))) t
--       pure $ S.Pair P fst snd

--     _ ->
--       impossible

prune :: PartialSub -> MetaVar -> Spine -> IO (MetaVar, Spine)
prune psub m sp = do
  uf
  -- unless (psub^.allowPruning) (throwIO CantUnify)
  -- a <- ES.unsolvedMetaType m
  -- let fvars = ENil
  --     wk     = ENil
  --     prune  = PSub ENil Nothing 0 0 mempty True
  -- sol <- pruneSp psub fvars wk prune S.LEmpty S.LEmpty a sp
  -- let ?lvl = 0
  --     ?env = ENil
  -- let vsol = eval sol
  -- ES.solve m sol vsol
  -- case spine vsol sp of
  --   Flex (FHMeta m) sp _ -> pure (m, sp)
  --   _                    -> impossible

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

merge :: LvlArg => Val -> Val -> IO S.Tm
merge topt topu = do

  let guardIrr a act = act >>= \case
        S.Magic Nonlinear -> typeRelevance a >>= \case
          RRel       -> pure $ S.Magic Nonlinear
          RIrr       -> pure $! quote UnfoldNone topt -- TODO: choose the more defined side?
          RBlockOn{} -> pure $ S.Magic Nonlinear
          RMagic{}   -> impossible
        t -> pure t

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

-- TODO: use lookupinsert
updatePSub :: Lvl -> Val -> PartialSub -> IO PartialSub
updatePSub (Lvl x) t psub = case IM.lookup x (psub^.sub) of
  Nothing -> do
    pure $! (psub & sub %~ IM.insert x t)
  Just t' -> do
    let ?lvl = psub^.dom
    merged <- evalInDom psub <$!> merge t t'
    pure $! (psub & sub %~ IM.insert x merged)

invertVal :: Lvl -> PartialSub -> Lvl -> Val -> Spine -> IO PartialSub
invertVal solvable psub param t rhsSp = do

  t <- let ?lvl = param in forceAll t
  case t of

    Pair _ t u -> do
      psub <- invertVal solvable psub param t (SProj1 rhsSp)
      invertVal solvable psub param t (SProj2 rhsSp)

    Lam sp x i a t -> do
      let var  = Var' param a True
      let ?lvl = param + 1
      invertVal solvable psub ?lvl (t $$ var) (SApp rhsSp var i)

    Rigid (RHLocalVar x xty _) sp rhsTy -> do
      unless (solvable <= x && x < psub^.cod) (throw CantUnify)
      (_, ~xty) <- psubst' psub xty
      let psub' = PSub (psub^.domVars) Nothing (psub^.dom) param mempty True
      sol <- solveNestedSp (psub^.cod) psub' xty sp (psub^.dom, rhsSp) rhsTy
      updatePSub x (evalInDom psub sol) psub

    _ ->
      throwIO CantUnify


solveTopSp :: PartialSub -> S.Locals -> Ty -> Spine -> Val -> Ty -> IO S.Tm
solveTopSp psub ls a sp rhs rhsty = do

  let go psub ls a sp = solveTopSp psub ls a sp rhs rhsty
      {-# inline go #-}

  let ?lvl    = psub^.dom
      ?env    = psub^.domVars
      ?locals = ls

  a <- forceSet a
  case (a, sp) of

    (a, SId) -> do
      () <$ psubst psub rhsty
      psubst psub rhs

    (Pi x i a b, SApp t u _) -> do
      let var   = Var' ?lvl a True
      let qa    = quote UnfoldNone a
      let ?lvl  = ?lvl + 1
      psub  <- pure (psub & domVars %~ (`EDef` var) & dom .~ ?lvl)
      ls    <- pure (S.LBind ls x qa)
      psub  <- invertVal 0 psub (psub^.cod) u SId
      S.Lam S x i qa <$!> go psub ls (b $$ var) t

    (El (Pi x i a b), SApp t u _) -> do
      let var   = Var' ?lvl a True
      let qa    = quote UnfoldNone a
      let ?lvl  = ?lvl + 1
      psub <- pure (psub & domVars %~ (`EDef` var) & dom .~ ?lvl)
      ls   <- pure (S.LBind ls x qa)
      psub <- invertVal 0 psub (psub^.cod) u SId
      S.Lam P x i qa <$!> go psub ls (El (b $$ var)) t

    (Sg x a b, SProj1 t) -> do
      fst <- go psub ls a t
      let ~vfst = eval fst
      snd <- freshMeta (gjoin (b $$ vfst))
      pure $ S.Pair S fst snd

    (Sg x a b, SProj2 t) -> do
      fst <- freshMeta (gjoin a)
      let ~vfst = eval fst
      snd <- go psub ls (b $$ vfst) t
      pure $ S.Pair S fst snd

    (El (Sg x a b), SProj1 t) -> do
      fst <- go psub ls (El a) t
      let ~vfst = eval fst
      snd <- freshMeta (gjoin (El (b $$ vfst)))
      pure $ S.Pair P fst snd

    (El (Sg x a b), SProj2 t) -> do
      fst <- freshMeta (gjoin (El a))
      let ~vfst = eval fst
      snd <- go psub ls (El (b $$ vfst)) t
      pure $ S.Pair P fst snd

    (a, SProjField t tv tty n) ->
      case n of
        0 -> go psub ls a (SProj1 t)
        n -> go psub ls a (SProj2 (SProjField t tv tty (n - 1)))

    _ -> impossible

solveNestedSp :: Lvl -> PartialSub -> Ty -> Spine -> (Lvl, Spine) -> Ty -> IO S.Tm
solveNestedSp solvable psub a sp (!rhsVar, !rhsSp) rhsty = do

  let go psub a sp = solveNestedSp solvable psub a sp (rhsVar, rhsSp) rhsty
      {-# inline go #-}

  let ?lvl = psub^.dom
      ?env = psub^.domVars

  a <- forceSet a
  case (a, sp) of

    (a, SId) -> do
      _ <- psubst psub rhsty
      psubstSp psub (S.LocalVar (lvlToIx rhsVar)) rhsSp

    (Pi x i a b, SApp t u _) -> do
      let var   = Var' ?lvl a True
      let qa    = quote UnfoldNone a
      let ?lvl  = ?lvl + 1
      psub  <- pure (psub & domVars %~ (`EDef` var) & dom .~ ?lvl)
      psub  <- invertVal solvable psub (psub^.cod) u SId
      S.Lam S x i qa <$!> go psub (b $$ var) t

    (El (Pi x i a b), SApp t u _) -> do
      let var   = Var' ?lvl a True
      let qa    = quote UnfoldNone a
      let ?lvl  = ?lvl + 1
      psub  <- pure (psub & domVars %~ (`EDef` var) & dom .~ ?lvl)
      psub  <- invertVal solvable psub (psub^.cod) u SId
      S.Lam P x i qa <$!> go psub (El (b $$ var)) t

    (Sg x a b, SProj1 t) ->
      S.Pair S <$!> go psub a t <*!> pure (S.Magic Undefined)

    (Sg x a b, SProj2 t) ->
      S.Pair S (S.Magic Undefined) <$!> go psub (b $$ Magic Undefined) t

    (El (Sg x a b), SProj1 t) ->
      S.Pair P <$!> go psub (El a) t <*!> pure (S.Magic Undefined)

    (El (Sg x a b), SProj2 t) -> do
      S.Pair P (S.Magic Undefined) <$!> go psub (El (b $$ Magic Undefined)) t

    (a, SProjField t tv tty n) ->
      case n of
        0 -> go psub a (SProj1 t)
        n -> go psub a (SProj2 (SProjField t tv tty (n - 1)))

    _ -> impossible

-- | Solve (?x sp ?= rhs : A).
solve :: LvlArg => AllowPruningArg => MetaVar -> Spine -> Val -> Ty -> IO ()
solve x sp rhs rhsty = do
  a <- ES.unsolvedMetaType x

  let goRelevant = do
        sol <- solveTopSp (PSub ENil (Just x) 0 ?lvl mempty ?allowPruning)
                          S.LEmpty a (reverseSpine sp) rhs rhsty
        ES.solve x sol (eval0 sol)

      goIrrelevant =
        (do sol <- solveTopSp (PSub ENil (Just x) 0 ?lvl mempty ?allowPruning)
                              S.LEmpty a (reverseSpine sp) rhs rhsty
            ES.solve x sol (eval0 sol))
        `catch`
        \(_ :: UnifyEx) -> pure () -- TODO: clean up unused expansion metas in this branch!

  typeRelevance rhsty >>= \case
    RRel       -> goRelevant
    RBlockOn{} -> goRelevant -- TODO: postpone
    RIrr       -> goIrrelevant
    RMagic{}   -> impossible

----------------------------------------------------------------------------------------------------
-- Unification
----------------------------------------------------------------------------------------------------


unify :: LvlArg => UnifyState -> G -> G -> IO ()
unify st t t' = uf
