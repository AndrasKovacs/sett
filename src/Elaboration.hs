
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
import qualified NameTable as NT

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

freshMeta :: Cxt -> GTy -> IO Tm
freshMeta cxt (G a fa) = do
  let closed   = E.eval0 $ closeTy (_locals cxt) (quote cxt UnfoldNone a )
      ~fclosed = E.eval0 $ closeTy (_locals cxt) (quote cxt UnfoldNone fa)
  m <- newMeta (G closed fclosed)
  pure $ InsertedMeta m (_locals cxt)


-- Insertion
--------------------------------------------------------------------------------


-- | Insert fresh implicit applications.
insertApps' :: Cxt -> IO Infer -> IO Infer
insertApps' cxt act = go =<< act where
  go :: Infer -> IO Infer
  go (Infer t (G a fa)) = forceAll cxt fa >>= \case
    V.Pi _ x Impl a b -> do
      m <- freshMeta cxt (gjoin a)
      let mv = eval cxt m
      let b' = gjoin (b $$ mv)
      go $ Infer (S.App t m Impl) b'
    fa -> pure $ Infer t (G a fa)

-- | Insert fresh implicit applications to a term which is not
--   an implicit lambda (i.e. neutral).
insertApps :: Cxt -> IO Infer -> IO Infer
insertApps cxt act = act >>= \case
  inf@(Infer (S.Lam _ _ Impl _ _) _) -> pure inf
  inf                                -> insertApps' cxt (pure inf)

-- | Insert fresh implicit applications until we hit a Pi with
--   a particular binder name.
insertAppsUntilName :: Cxt -> P.Tm -> P.Name -> IO Infer -> IO Infer
insertAppsUntilName cxt pt name act = go =<< act where
  go :: Infer -> IO Infer
  go (Infer t (G a fa)) = forceAll cxt fa >>= \case
    fa@(V.Pi _ x Impl a b) -> do
      if x == NName name then
        pure (Infer t (G a fa))
      else do
        m <- freshMeta cxt (gjoin a)
        let mv = eval cxt m
        go $ Infer (S.App t m Impl) (gjoin $! (b $$ mv))
    _ ->
      elabError cxt pt $ NoNamedImplicitArg name


--------------------------------------------------------------------------------

subtype :: Cxt -> P.Tm -> S.Tm -> V.Ty -> V.Ty -> IO S.Tm
subtype cxt pt t a b = do
  fa <- forceAll cxt a
  fb <- forceAll cxt b
  case (fa, fb) of
    (V.Prop, V.Set) -> do
      pure (S.El t)
    (fa, fb) -> do
      unify cxt pt (G a fa) (G b fb)
      pure t


-- Check
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
          a' <- freshMeta cxt gProp
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
          a' <- freshMeta cxt gSet
          let va' = eval cxt a'
          pure (a', va')
      t <- check cxt t (gjoin va)
      let ~vt = eval cxt t
      u <- checkEl (define x a (gjoin va) t vt cxt) u (G topa ftopa)
      pure $ S.Let (NName x) a t u

    (P.Hole _, ftopa) ->
      freshMeta cxt (gEl (G topa ftopa))

    (topt, ftopa) -> do
      Infer t tty <- infer cxt topt
      -- there's subtyping coercion into El
      unify cxt topt tty (gEl (G topa ftopa))
      pure t

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
          a' <- freshMeta cxt gSet
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
          a' <- freshMeta cxt gSet
          let va' = eval cxt a'
          pure (a', va')
      t <- check cxt t (gjoin va)
      let ~vt = eval cxt t
      u <- check (define x a (gjoin va) t vt cxt) u (G topa ftopa)
      pure $ S.Let (NName x) a t u

    (P.Hole _, ftopa) ->
      freshMeta cxt (G topa ftopa)

    (topt, ftopa) -> do
      Infer t tty <- infer cxt topt
      subtype cxt topt t (g2 tty) ftopa

-- infer
--------------------------------------------------------------------------------

infer :: Cxt -> P.Tm -> IO Infer
infer cxt topt = case topt of

  P.Var x -> case NT.lookup x (_nameTable cxt) of
    Nothing ->
      elabError cxt topt $ NameNotInScope x
    Just (NT.Top x a ga v) ->
      pure $ Infer (S.TopDef (coerce v) x) ga
    Just (NT.Local x ga) ->
      pure $ Infer (S.LocalVar (lvlToIx (_lvl cxt) x)) ga

  P.App topt topu i -> do
    (i, t, a, fa) <- case i of
      P.NoName Impl -> do
        Infer t (G a fa) <- infer cxt topt
        pure (Impl, t, a, fa)
      P.NoName Expl -> do
        Infer t (G a fa) <- insertApps' cxt $ infer cxt topt
        pure (Expl, t, a, fa)
      P.Named x -> do
        Infer t (G a fa) <- insertAppsUntilName cxt topt x $ infer cxt topt
        pure (Impl, t, a , fa)

    forceAll cxt fa >>= \case

      V.Pi _ x _ a b -> do
        u <- check cxt topu (gjoin a)
        pure $ Infer (S.App t u i) (gjoin $! (b $$$ eval cxt u))

      V.El (V.Pi _ x i a b) -> do
        u <- check cxt topu (gjoin $ V.El a)
        pure $ Infer (S.App t u i) (gjoin $! V.El (b $$$ eval cxt u))

      fa ->
        elabError cxt topt $ ExpectedFunOrForall a

  P.Lam{} ->
    elabError cxt topt $ GenericError "can't infer type for lambda"

  P.Pair{} ->
    elabError cxt topt $ GenericError "can't infer type for pair"

  P.ProjField t x -> do
    let fieldName = NName x
    Infer t ga <- infer cxt topt
    let ~vt = eval cxt t

    let go (G a fa) ix = forceAll cxt fa >>= \case
          V.Sg _ x' a b | fieldName == x' -> do
            pure (ix, a)
          V.Sg _ x' a b -> do
            go (gjoin $! (b $$$ E.projField vt fieldName ix)) (ix + 1)
          V.El (V.Sg _ x' a b) | fieldName == x' -> do
            pure (ix, V.El a)
          V.El (V.Sg _ x' a b) -> do
            go (gjoin $! (b $$$ E.projField vt fieldName ix)) (ix + 1)
          _ ->
            elabError cxt topt $ NoSuchField x

    (ix, b) <- go ga 0
    pure $ Infer (S.ProjField t fieldName ix) (gjoin b)

  P.Let _ x ma t u -> do
    (a, va) <- case ma of
      Just a  -> do
        a <- check cxt a gSet
        pure (a, eval cxt a)
      Nothing -> do
        a' <- freshMeta cxt gSet
        let va' = eval cxt a'
        pure (a', va')
    t <- check cxt t (gjoin va)
    let ~vt = eval cxt t
    Infer u uty <- infer (define x a (gjoin va) t vt cxt) u
    pure $ Infer (S.Let (NName x) a t u) uty
