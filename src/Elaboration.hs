
module Elaboration where

import Control.Exception

import Common
import Cxt
import Errors
import Syntax
import Values
import ElabState
import Evaluation

import qualified Presyntax as P
import qualified Unification as Unif
import qualified Syntax as S
import qualified Values as V
import qualified NameTable as NT

--------------------------------------------------------------------------------

{-
TODO
 - postponings
 - pair, lambda inference
 - specialized checking cases for fully applied primitive symbols
-}

--------------------------------------------------------------------------------

elabError :: LocalsArg => P.Tm -> Error -> IO a
elabError t err = throwIO $ ErrorInCxt ?locals t err

unify :: CxtArg (P.Tm -> G -> G -> IO ())
unify t l r = do
  Unif.unify USRigid l r `catch` \case
    (e :: UnifyEx) -> elabError t (UnifyError (g1 l) (g1 r))

data Infer = Infer Tm {-# unpack #-} GTy

closeTy :: LocalsArg => S.Ty -> S.Ty
closeTy b = go ?locals b where
  go ls b = case ls of
    S.LEmpty           -> b
    S.LBind ls x a     -> go ls (S.Pi S x Expl a b)
    S.LDefine ls x t a -> go ls (Let x a t b)

freshMeta :: LvlArg => LocalsArg => GTy -> IO Tm
freshMeta (G a fa) = do
  let closed   = eval0 $ closeTy $ quote UnfoldNone a
  let ~fclosed = eval0 $ closeTy $ quote UnfoldNone fa
  m <- newMeta (G closed fclosed)
  pure $! InsertedMeta m ?locals

-- Insertion
--------------------------------------------------------------------------------

-- | Insert fresh implicit applications.
insertApps' :: LvlArg => EnvArg => LocalsArg => IO Infer -> IO Infer
insertApps' act = go =<< act where
  go :: Infer -> IO Infer
  go (Infer t (G a fa)) = forceAll fa >>= \case
    V.Pi _ x Impl a b -> do
      m <- freshMeta (gjoin a)
      let mv = eval m
      let b' = gjoin (b $$ mv)
      go $ Infer (S.App t m Impl) b'
    fa -> pure $ Infer t (G a fa)
{-# inline insertApps' #-}

-- | Insert fresh implicit applications to a term which is not
--   an implicit lambda (i.e. neutral).
insertApps :: LvlArg => EnvArg => LocalsArg => IO Infer -> IO Infer
insertApps act = act >>= \case
  inf@(Infer (S.Lam _ _ Impl _ _) _) -> pure inf
  inf                                -> insertApps' (pure inf)
{-# inline insertApps #-}

-- | Insert fresh implicit applications until we hit a Pi with
--   a particular binder name.
insertAppsUntilName :: LvlArg => EnvArg => LocalsArg => P.Tm -> P.Name -> IO Infer -> IO Infer
insertAppsUntilName pt name act = go =<< act where
  go :: Infer -> IO Infer
  go (Infer t (G a fa)) = forceAll fa >>= \case
    fa@(V.Pi _ x Impl a b) -> do
      if x == NSpan name then
        pure (Infer t (G a fa))
      else do
        m <- freshMeta (gjoin a)
        let mv = eval m
        go $! Infer (S.App t m Impl) (gjoin $! (b $$ mv))
    _ ->
      elabError pt $ NoNamedImplicitArg name
{-# inline insertAppsUntilName #-}

--------------------------------------------------------------------------------

subtype :: CxtArg (P.Tm -> S.Tm -> V.Ty -> V.Ty -> IO S.Tm)
subtype pt t a b = do
  fa <- forceAll a
  fb <- forceAll b
  case (fa, fb) of
    (V.Prop, V.Set) -> do
      pure (S.El t)
    (fa, fb) -> do
      unify pt (G a fa) (G b fb)
      pure t

-- Check
--------------------------------------------------------------------------------

checkEl :: CxtArg (P.Tm -> GTy -> IO S.Tm)
checkEl topt (G topa ftopa) = do
  ftopa <- forceAll ftopa
  case (topt, ftopa) of

    -- go under lambda
    (P.Lam _ x' inf ma t, V.Pi _ x i a b)
      | (case inf of P.NoName i' -> i == i'
                     P.Named x'  -> NSpan x' == x && i == Impl) -> do

      (a, va) <- case ma of
        Just a  -> do
          a <- check a gProp
          pure (a, eval a)
        Nothing -> do
          a' <- freshMeta gProp
          let va' = eval a'
          unify topt (gjoin a) (gjoin va')
          pure (a', va')

      bind x' (S.El a) (gjoin (V.El va)) \var ->
        S.Lam P (bindToName x') i a <$!> (check t $! gjoin $! V.El (b $$ var))

    -- insert implicit lambda
    (t, V.Pi _ x Impl a b) -> do
      let qa = quote UnfoldNone a
      insertBinder qa (gjoin (V.El a)) \var ->
        S.Lam P x Impl qa <$!> (check t $! gjoin $! V.El (b $$ var))

    (P.Pair t u, V.Sg _ x a b) -> do
      t <- check t (gjoin (V.El a))
      u <- check u (gjoin (V.El (b $$~ eval t)))
      pure $ S.Pair S t u

    (P.Let _ x ma t u, ftopa) -> do

      (a, va) <- case ma of
        Just a  -> do
          a <- check a gSet
          pure (a, eval a)
        Nothing -> do
          a' <- freshMeta gSet
          let va' = eval a'
          pure (a', va')

      t <- check t (gjoin va)

      define x a (gjoin va) t (eval t) do
        u <- checkEl u (G topa ftopa)
        pure $ S.Let (NSpan x) a t u

    (P.Hole _, ftopa) ->
      freshMeta (gEl (G topa ftopa))

    (topt, ftopa) -> do
      Infer t tty <- infer topt
      -- there's no subtyping coercion into El
      unify topt tty (gEl (G topa ftopa))
      pure t


check :: CxtArg (P.Tm -> GTy -> IO S.Tm)
check topt (G topa ftopa) = do
  ftopa <- forceAll ftopa
  case (topt, ftopa) of

    -- (P.Pi _ x i a b, V.Set) -> do
    --   a <- check a gSet
    --   bind x a (gjoin (eval a)) \_ ->
    --     S.Pi S (bindToName x) i a <$!> check b gSet

    -- (P.Sg _ x a b, V.Set) -> do
    --   a <- check a gSet
    --   bind x a (gjoin (eval a)) \_ ->
    --     S.Sg S (bindToName x) a <$!> check b gSet

    (P.Pi _ x i a b, V.Prop) -> do
      a <- check a gSet
      bind x a (gjoin (eval a)) \_ ->
        S.Pi P (bindToName x) i a <$!> check b gProp

    (P.Sg _ x a b, V.Prop) -> do
      a <- check a gProp
      bind x a (gEl (gjoin (eval a))) \_ ->
        S.Sg P (bindToName x) a <$!> check b gProp

    (t, V.El a) ->
      checkEl t (gjoin a)

    -- go under lambda
    (P.Lam _ x' inf ma t, V.Pi _ x i a b)
      | (case inf of P.NoName i' -> i == i'
                     P.Named x'  -> NSpan x' == x && i == Impl) -> do

      (a, va) <- case ma of
        Just a  -> do
          a <- check a gSet
          pure (a, eval a)
        Nothing -> do
          a' <- freshMeta gSet
          let va' = eval a'
          unify topt (gjoin a) (gjoin va')
          pure (a', va')

      bind x' a (gjoin va) \var ->
        S.Lam S (bindToName x') i a <$!> check t (gjoin $! (b $$ var))

    -- insert implicit lambda
    (t, V.Pi _ x Impl a b) -> do
      let qa = quote UnfoldNone a
      insertBinder qa (gjoin a) \var ->
        S.Lam S x Impl qa <$!> check t (gjoin $! (b $$ var))

    (P.Pair t u, V.Sg _ x a b) -> do
      t <- check t (gjoin a)
      u <- check u (gjoin (b $$~ eval t))
      pure $ S.Pair S t u

    (P.Let _ x ma t u, ftopa) -> do
      (a, va) <- case ma of
        Just a  -> do
          a <- check a gSet
          pure (a, eval a)
        Nothing -> do
          a' <- freshMeta gSet
          let va' = eval a'
          pure (a', va')
      t <- check t (gjoin va)
      define x a (gjoin va) t (eval t) do
        u <- check u (G topa ftopa)
        pure $ S.Let (NSpan x) a t u

    (P.Hole _, ftopa) ->
      freshMeta (G topa ftopa)

    (topt, ftopa) -> do
      Infer t tty <- infer topt
      subtype topt t (g2 tty) ftopa

-- infer
--------------------------------------------------------------------------------

infer :: CxtArg (P.Tm -> IO Infer)
infer topt = case topt of

  P.Var x -> case NT.lookup x ?nameTable of
    Nothing ->
      elabError topt $! NameNotInScope x
    Just (NT.Top x a ga v) ->
      pure $! Infer (S.TopDef (coerce v) x) ga
    Just (NT.Local x ga) ->
      pure $! Infer (S.LocalVar (lvlToIx x)) ga

  P.Pi _ x i topa topb -> do
    a <- check topa gSet
    bind x a (gjoin (eval a)) \_ -> do
      Infer b (G bty fbty) <- infer topb
      forceAll fbty >>= \case
        V.Set  -> pure $! Infer (S.Pi S (bindToName x) i a b) gSet
        V.Prop -> pure $! Infer (S.Pi P (bindToName x) i a b) gProp
        fbty   -> elabError topb AmbiguousUniverse

  P.Sg _ x topa topb -> do
    Infer a (G aty faty) <- infer topa
    bind x a (gjoin (eval a)) \_ -> do
      forceAll faty >>= \case
        V.Set -> do
          b <- check topb gSet
          pure $! Infer (S.Sg S (bindToName x) a b) gSet
        V.Prop -> do
          Infer b (G bty fbty) <- infer topb
          forceAll fbty >>= \case
            V.Set  -> pure $! Infer (S.Sg S (bindToName x) (S.El a) b) gSet
            V.Prop -> pure $! Infer (S.Sg P (bindToName x) a b) gProp
            _      -> elabError topb AmbiguousUniverse
        _ -> elabError topa AmbiguousUniverse

  P.Set _ ->
    pure $ Infer S.Set gSet

  P.Prop _ ->
    pure $ Infer S.Prop gSet

  P.Top _ ->
    pure $ Infer S.Top gProp

  P.Bot _ ->
    pure $ Infer S.Bot gProp

  P.Tt _ ->
    pure $! Infer S.Tt (gjoin (V.El V.Top))

  P.El _ a -> do
    a <- check a gProp
    pure $! Infer (S.El a) gSet

  topt@(P.Eq t u) -> do
    Infer t tty <- infer t
    Infer u uty <- infer u
    unify topt tty uty
    let a = quote UnfoldNone (g1 tty)
    pure $! Infer (S.Eq a t u) gProp

  P.Exfalso _ -> do
    let ty = V.PiSI na V.Set \a -> funS (V.El V.Bot) a
    pure $! Infer S.ExfalsoSym (gjoin ty)

  P.Refl _ -> do
    let ty = V.PiPI na V.Set \a -> V.PiPI nx a \x -> V.El (eq a x x)
    pure $! Infer S.ReflSym (gjoin ty)

  P.Coe _ -> do
    let ty = V.PiSI na V.Set \a -> V.PiSI nb V.Set \b ->
             funS (V.El (eqSet a b)) $ funS a b
    pure $! Infer S.CoeSym (gjoin ty)

  P.Sym _ -> do
    let ty = V.PiPI na V.Set \a -> V.PiPI ny a \x -> V.PiPI ny a \y -> V.PiPE np (V.El (eq a x y)) \p ->
             V.El (eq a y x)
    pure $! Infer S.SymSym (gjoin ty)

  P.Trans _ -> do
    let ty = V.PiPI na V.Set \a -> V.PiPI nx a \x -> V.PiPI ny a \y -> V.PiPI nz a \z ->
             V.PiPE np (eq a x y) \p -> V.PiPE nq (eq a y z) \q ->
             eq a x z
    pure $! Infer S.TransSym (gjoin ty)

  P.Ap _ -> do
    let ty = V.PiPI na V.Set \a -> V.PiPI nb V.Set \b -> V.PiPE nf (funS a b) \f -> V.PiPI nx a \x ->
             V.PiPI ny a \y -> V.PiPE np (eq a x y) \p ->
             eq b (f `appE` x) (f `appE` y)
    pure $! Infer S.ApSym (gjoin ty)

  P.Hole _ -> do
    ty <- freshMeta gSet
    let gty = gjoin (eval ty)
    tm <- freshMeta gty
    pure $! Infer tm gty

  P.App topt topu i -> do

    (i, t, a, fa) <- case i of
      P.NoName Impl -> do
        Infer t (G a fa) <- infer topt
        pure (Impl, t, a, fa)
      P.NoName Expl -> do
        Infer t (G a fa) <- insertApps' $ infer topt
        pure (Expl, t, a, fa)
      P.Named x -> do
        Infer t (G a fa) <- insertAppsUntilName topt x $ infer topt
        pure (Impl, t, a , fa)

    forceAll fa >>= \case

      V.Pi _ x _ a b -> do
        u <- check topu (gjoin a)
        pure $! Infer (S.App t u i) (gjoin (b $$~ eval u))

      V.El (V.Pi _ x i a b) -> do
        u <- check topu (gjoin a)
        pure $! Infer (S.App t u i) (gjoin (V.El (b $$~ eval u)))

      fa ->
        elabError topt $ ExpectedFunOrForall a

  -- TODO: infer, postpone if ambiguous S/P
  P.Lam{} ->
    elabError topt $ GenericError "can't infer type for lambda"

  -- TODO: infer simple product type, postpone if ambiguous S/P
  P.Pair{} ->
    elabError topt $ GenericError "can't infer type for pair"

  P.Proj1 topt _ -> do
    Infer t (G ty fty) <- infer topt
    forceAll fty >>= \case
      V.Sg _ x a b        -> pure $! Infer (Proj1 t) (gjoin a)
      V.El (V.Sg _ x a b) -> pure $! Infer (Proj1 t) (gjoin (V.El a))
      -- todo: postpone
      fty                 -> elabError topt $! ExpectedSg ty

  P.Proj2 topt _ -> do
    Infer t (G ty fty) <- infer topt
    forceAll fty >>= \case
      V.Sg _ x a b        -> pure $! Infer (Proj2 t) (gjoin (b $$~ proj1 (eval t)))
      V.El (V.Sg _ x a b) -> pure $! Infer (Proj2 t) (gjoin (V.El (b $$~ proj1 (eval t))))
      -- todo: postpone
      fty                 -> elabError topt $! ExpectedSg ty

  P.ProjField t x -> do
    let fieldName = NSpan x
    Infer t ga <- infer topt
    let ~vt = eval t

    let go a ix = forceAll a >>= \case
          V.Sg _ x' a b | fieldName == x' -> do
            pure (ix, a)
          V.Sg _ x' a b -> do
            go (b $$ projField vt ix) (ix + 1)
          V.El (V.Sg _ x' a b) | fieldName == x' -> do
            pure (ix, V.El a)
          V.El (V.Sg _ x' a b) -> do
            go (b $$ projField vt ix) (ix + 1)
          -- todo: postpone
          _ ->
            elabError topt $ NoSuchField x

    (ix, b) <- go (g2 ga) 0
    pure $! Infer (S.ProjField t ix) (gjoin b)

  P.Let _ x ma t u -> do

    (a, va) <- case ma of
      Just a  -> do
        a <- check a gSet
        pure (a, eval a)
      Nothing -> do
        a' <- freshMeta gSet
        let va' = eval a'
        pure (a', va')

    t <- check t (gjoin va)

    define x a (gjoin va) t (eval t) do
      Infer u uty <- infer u
      pure $ Infer (S.Let (NSpan x) a t u) uty
