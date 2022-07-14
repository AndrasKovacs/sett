
module Elaboration where

import Common
import Cxt
import Errors
import Syntax
import Values
import InCxt
import ElabState

import qualified Evaluation as E
import qualified Presyntax as P
import qualified Unification as Unif
import qualified Syntax as S
import qualified Values as V

--------------------------------------------------------------------------------

unify :: Cxt -> P.Tm -> G -> G -> IO ()
unify cxt t l r = do
  Unif.unify (_lvl cxt) USRigid l r `catch` \case
    (e :: UnifyEx) -> elabError cxt t (UnifyError (g1 l) (g1 r))

newVar :: Cxt -> V.Ty -> V.Val
newVar cxt a = V.Var (_lvl cxt) a

data Infer = Infer Tm {-# unpack #-} GTy

closeTy :: Locals -> S.Ty -> S.Ty
closeTy ls b = case ls of
  S.LEmpty           -> b
  S.LBind ls x a     -> closeTy ls (S.Pi S x Expl a b)
  S.LDefine ls x t a -> closeTy ls (Let x a t b)

freshMeta :: Cxt -> V.Ty -> IO Tm
freshMeta cxt a = do
  let ~closed = E.eval0 $ closeTy (_locals cxt) (quote cxt UnfoldNone a)
  m <- newMeta closed
  pure $ InsertedMeta m (_locals cxt)


-- Insertion
--------------------------------------------------------------------------------


-- | Insert fresh implicit applications.
insert' :: Cxt -> IO (Tm, V.Ty) -> IO (Tm, V.Ty)
insert' cxt act = go =<< act where
  go :: (Tm, V.Ty) -> IO (Tm, V.Ty)
  go (!t, !va) = forceAll cxt va >>= \case
    V.Pi _ x Impl a b -> do
      m <- freshMeta cxt a
      let mv = eval cxt m
      go (S.App t m Impl // (b $$ mv))
    va -> pure (t, va)

-- | Insert fresh implicit applications to a term which is not
--   an implicit lambda (i.e. neutral).
insert :: Cxt -> IO (Tm, V.Ty) -> IO (Tm, V.Ty)
insert cxt act = act >>= \case
  (t@(S.Lam _ _ Impl _ _), !va) -> pure (t, va)
  (t                     ,  va) -> insert' cxt (pure (t, va))

-- | Insert fresh implicit applications until we hit a Pi with
--   a particular binder name.
insertUntilName :: Cxt -> P.Tm -> P.Name -> IO (Tm, V.Ty) -> IO (Tm, V.Ty)
insertUntilName cxt pt name act = go =<< act where
  go :: (Tm, V.Ty) -> IO (Tm, V.Ty)
  go (!t, !va) = forceAll cxt va >>= \case
    va@(V.Pi _ x Impl a b) -> do
      if x == NName name then
        pure (t, va)
      else do
        m <- freshMeta cxt a
        let mv = eval cxt m
        go (S.App t m Impl // (b $$ mv))
    _ ->
      elabError cxt pt $ NoNamedImplicitArg name


--------------------------------------------------------------------------------

subtype :: Cxt -> S.Tm -> V.Ty -> V.Ty -> IO S.Tm
subtype = uf

--------------------------------------------------------------------------------

checkEl :: Cxt -> P.Tm -> GTy -> IO S.Tm
checkEl cxt topt (G topa ftopa) = do
  ftopa <- forceAll cxt ftopa
  case (topt, ftopa) of

    -- go under lambda
    (P.Lam _ x' inf ma t, V.Pi _ x i a b)
      | (case inf of P.NoName i' -> i == i'
                     P.Named x'  -> NName x' == x && i == Impl) -> do

      (a, va) <- case ma of
        Just a  -> do
          a <- check cxt a gProp
          pure (a, eval cxt a)
        Nothing -> do
          a' <- freshMeta cxt V.Prop
          let va' = eval cxt a'
          unify cxt topt (gjoin a) (gjoin va')
          pure (a', va')

      let cxt' = Cxt.bind x' (S.El a) (gjoin (V.El va)) cxt
      t <- check cxt' t $! (gjoin $! V.El (b $$ newVar cxt va))
      pure $ S.Lam P (bindToName x') i a t

    -- insert implicit lambda
    (t, V.Pi _ x Impl a b) -> do
      let qa   = quote cxt UnfoldNone a
      let cxt' = Cxt.insert qa (gjoin (V.El a)) cxt
      t <- check cxt' t $! (gjoin $! V.El (b $$ V.Var (_lvl cxt) a))
      pure $ S.Lam P x Impl qa t

    (P.Pair t u, V.Sg _ x a b) -> do
      t <- check cxt t (gjoin (V.El a))
      u <- check cxt u (gjoin $! V.El (b $$$ eval cxt t))
      pure $ S.Pair S t u

    (P.Let _ x ma t u, ftopa) -> do
      (a, va) <- case ma of
        Just a  -> do
          a <- check cxt a gSet
          pure (a, eval cxt a)
        Nothing -> do
          a' <- freshMeta cxt V.Set
          let va' = eval cxt a'
          pure (a', va')
      t <- check cxt t (gjoin va)
      let ~vt = eval cxt t
      u <- checkEl (define x a (gjoin va) t vt cxt) u (G topa ftopa)
      pure $ S.Let (NName x) a t u

    (P.Hole _, ftopa) ->
      freshMeta cxt (V.El topa)

    (topt, ftopa) -> do
      Infer t tty <- infer cxt topt
      subtype cxt t (g2 tty) (V.El ftopa)


check :: Cxt -> P.Tm -> GTy -> IO S.Tm
check cxt topt (G topa ftopa) = do
  ftopa <- forceAll cxt ftopa
  case (topt, ftopa) of

    (P.Pi _ x i a b, V.Set) -> do
      a <- check cxt a gSet
      let ~va = eval cxt a
      b <- check (bind x a (gjoin va) cxt) b gSet
      pure $ S.Pi S (bindToName x) i a b

    (P.Sg _ x a b, V.Set) -> do
      a <- check cxt a gSet
      let ~va = eval cxt a
      b <- check (bind x a (gjoin va) cxt) b gSet
      pure $ S.Sg S (bindToName x) a b

    (P.Pi _ x i a b, V.Prop) -> do
      a <- check cxt a gProp
      let ~va = eval cxt a
      b <- check (bind x a (gjoin (V.El va)) cxt) b gProp
      pure $ S.Pi P (bindToName x) i a b

    (P.Sg _ x a b, V.Prop) -> do
      a <- check cxt a gProp
      let ~va = eval cxt a
      b <- check (bind x a (gjoin (V.El va)) cxt) b gProp
      pure $ S.Sg P (bindToName x) a b

    (t, V.El a) ->
      checkEl cxt t (gjoin a)

    -- go under lambda
    (P.Lam _ x' inf ma t, V.Pi _ x i a b)
      | (case inf of P.NoName i' -> i == i'
                     P.Named x'  -> NName x' == x && i == Impl) -> do

      (a, va) <- case ma of
        Just a  -> do
          a <- check cxt a gSet
          pure (a, eval cxt a)
        Nothing -> do
          a' <- freshMeta cxt V.Set
          let va' = eval cxt a'
          unify cxt topt (gjoin a) (gjoin va')
          pure (a', va')

      let cxt' = Cxt.bind x' a (gjoin va) cxt
      t <- check cxt' t $! (gjoin $! (b $$ newVar cxt va))
      pure $ S.Lam S (bindToName x') i a t

    -- insert implicit lambda
    (t, V.Pi _ x Impl a b) -> do
      let qa   = quote cxt UnfoldNone a
      let cxt' = Cxt.insert qa (gjoin a) cxt
      t <- check cxt' t $! (gjoin $! (b $$ V.Var (_lvl cxt) a))
      pure $ S.Lam S x Impl qa t

    (P.Pair t u, V.Sg _ x a b) -> do
      t <- check cxt t (gjoin a)
      u <- check cxt u (gjoin $! (b $$$ eval cxt t))
      pure $ S.Pair S t u

    (P.Let _ x ma t u, ftopa) -> do
      (a, va) <- case ma of
        Just a  -> do
          a <- check cxt a gSet
          pure (a, eval cxt a)
        Nothing -> do
          a' <- freshMeta cxt V.Set
          let va' = eval cxt a'
          pure (a', va')
      t <- check cxt t (gjoin va)
      let ~vt = eval cxt t
      u <- check (define x a (gjoin va) t vt cxt) u (G topa ftopa)
      pure $ S.Let (NName x) a t u

    (P.Hole _, ftopa) ->
      freshMeta cxt topa

    (topt, ftopa) -> do
      Infer t tty <- infer cxt topt
      subtype cxt t (g2 tty) ftopa

infer :: Cxt -> P.Tm -> IO Infer
infer cxt pt = uf
