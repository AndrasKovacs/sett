
module Elaboration where

import Control.Exception

import Common
import Cxt
import Errors
import Syntax
import Values
import ElabState
import Evaluation
-- import TopCxt

import qualified Presyntax as P
import qualified Unification as Unif
import qualified Syntax as S
import qualified Values as V
import qualified NameTable as NT

import Pretty

--------------------------------------------------------------------------------

{-
TODO
 - postponings
 - pair, lambda inference
 - specialized checking cases for fully applied primitive symbols
-}

--------------------------------------------------------------------------------


elabError :: LocalsArg => LvlArg => P.Tm -> Error -> IO a
elabError t err = do
  src <- readElabSource >>= \case
    Just src -> pure src
    Nothing  -> debug ["HOW IS THIS POSSILE"] >> impossible
  throwIO $ ErrorInCxt src ?locals ?lvl t err

unify :: LvlArg => LocalsArg => P.Tm -> G -> G -> IO ()
unify t l r = do
  let ?unifyState = USRigid conversionSpeculation
      ?names      = localNames
  Unif.unify l r `catch` \case
    (e :: UnifyEx) -> elabError t (UnifyError (g1 l) (g1 r) e)

data Infer = Infer Tm {-# unpack #-} GTy

freshMeta :: LvlArg => LocalsArg => GTy -> IO Tm
freshMeta (G a fa) = do
  let closed   = eval0 $ closeTy $ quote a
  let ~fclosed = eval0 $ closeTy $ quote fa
  m <- newMeta (G closed fclosed)
  pure $ InsertedMeta m ?locals

-- fresh meta in an extended env
freshMeta1 :: LvlArg => LocalsArg => EnvArg => S.Ty -> GTy -> IO Closure
freshMeta1 bind (G a fa) = do
  let ?lvl = ?lvl + 1; ?locals = S.LBind ?locals nx bind
  let closed   = eval0 $ closeTy $ quote a
  let ~fclosed = eval0 $ closeTy $ quote fa
  m <- newMeta (G closed fclosed)
  pure $ Cl \x -> evalIn ?lvl (EDef ?env x) (InsertedMeta m ?locals)

-- Insertion
--------------------------------------------------------------------------------

-- | Insert fresh implicit applications.
insertApps' :: LvlArg => EnvArg => LocalsArg => IO Infer -> IO Infer
insertApps' act = go =<< act where
  go :: Infer -> IO Infer
  go (Infer t (G topa topfa)) = forceAll topfa >>= \case

    V.Pi x Impl a b -> do
      m <- freshMeta (gjoin a)
      let mv = eval m
      let b' = gjoin (b $$ mv)
      go $ Infer (S.App t m Impl) b'

    V.El a -> forceAllWithTraceEq a >>= \case
      (aTrace, V.Pi x Impl a b) -> do
        m <- freshMeta (gjoin a)
        let mv = eval m
        go $ Infer (S.App t m Impl) (gjoin (V.El (b $$ mv)))
      (aTrace, _) ->
        pure $ Infer t (gjoin (V.El aTrace))
    topfa ->
      pure $ Infer t (G topa topfa)
{-# inline insertApps' #-}

-- | Insert fresh implicit applications to a term which is not
--   an implicit lambda (i.e. neutral).
insertApps :: LvlArg => EnvArg => LocalsArg => IO Infer -> IO Infer
insertApps act = act >>= \case
  inf@(Infer (S.Lam _ Impl _ _) _) -> pure inf
  inf                              -> insertApps' (pure inf)
{-# inline insertApps #-}

-- | Insert fresh implicit applications until we hit a Pi with
--   a particular binder name.
insertAppsUntilName :: LvlArg => EnvArg => LocalsArg => P.Tm -> P.Name -> IO Infer -> IO Infer
insertAppsUntilName pt name act = go =<< act where
  go :: Infer -> IO Infer
  go (Infer t (G topa topfa)) = forceAll topfa >>= \case

    topfa@(V.Pi x Impl a b) -> do
      if x == NSpan name then
        pure (Infer t (G topa topfa))
      else do
        m <- freshMeta (gjoin a)
        let mv = eval m
        go $! Infer (S.App t m Impl) (gjoin $! (b $$ mv))

    V.El a -> forceAll a >>= \case
      V.Pi x Impl a b -> do
        if x == NSpan name then
          pure (Infer t (gEl (G topa topfa)))
        else do
          m <- freshMeta (gjoin a)
          let mv = eval m
          go $! Infer (S.App t m Impl) (gjoin $! V.El (b $$ mv))
      _ -> elabError pt $ NoNamedImplicitArg name
    _ ->
      elabError pt $ NoNamedImplicitArg name
{-# inline insertAppsUntilName #-}

--------------------------------------------------------------------------------

subtype :: InCxt (P.Tm -> S.Tm -> Val -> V.GTy -> V.GTy -> IO S.Tm)
subtype pt t ~tv (G a fa) (G b fb) = do
  fa <- forceAll fa
  fb <- forceAll fb
  case (fa, fb) of
    (V.Prop, V.Set ) -> pure $ S.El t
    (V.Set , V.Prop) -> case t of
      S.El a -> pure a
      _      -> do m <- eval <$!> freshMeta gProp
                   unify pt (gjoin tv) (gjoin (V.El m))
                   pure $! quote m
    (fa, fb) -> do
      unify pt (G a fa) (G b fb)
      pure t
{-# inline subtype #-}

checkEl :: InCxt (P.Tm -> GTy -> IO S.Tm)
checkEl topt (G topa ftopa) = do
  (ftopaTrace, ftopa) <- forceAllWithTraceEq ftopa
  debug ["checkEl", P.showTm topt, show topt, showTm (quote topa), show ftopa]
  case (topt, ftopa) of

    (P.Parens _ t _, ftopa) ->
      checkEl t (G topa ftopaTrace)

    -- go under lambda
    (P.Lam _ x' inf ma t, V.Pi x i a b)
      | (case inf of P.AIExpl           -> i == Expl
                     P.AIImpl _         -> i == Impl
                     P.AINamedImpl x' _ -> NSpan x' == x && i == Impl) -> do

      (a, va) <- case ma of
        Just a' -> do
          a' <- check a' gSet
          let va' = eval a'
          unify topt (gjoin va') (gjoin a)
          pure (a', va')
        Nothing -> do
          let qa = quote a
          pure (qa, a)

      bind x' a (gjoin va) \var ->
        S.Lam (bindToName x') i a <$!> (checkEl t $! gjoin $! (b $$ var))

    -- insert implicit lambda
    (t, V.Pi x Impl a b) -> do
      let qa = quote a
      insertBinder qa (gjoin a) \var ->
        S.Lam x Impl qa <$!> (checkEl t $! gjoin $! (b $$ var))

    (P.Pair t u, V.Sg _ x a b) -> do
      t <- checkEl t (gjoin a)
      u <- checkEl u (gjoin (b $$~ eval t))
      pure $ S.Pair t u

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
      Infer t tty <- insertApps $ infer topt
      unify topt tty (gEl (G topa ftopaTrace))
      pure t


check :: InCxt (P.Tm -> GTy -> IO S.Tm)
check topt (G topa ftopa) = do

  ftopa <- forceAll ftopa

  debug ["check", P.showTm topt, showTm (quote topa)]

  case (topt, ftopa) of
    (P.Parens _ t _, ftopa) ->
      check t (G topa ftopa)

    (P.Pi _ x i a b, V.Prop) -> do
      a <- check a gSet
      bindWithTy x a \_ ->
        S.Pi (bindToName x) i a <$!> check b gProp

    (P.Sg _ x a b, V.Prop) -> do
      a <- check a gProp
      bindWithTy x a \_ ->
        S.Sg P (bindToName x) a <$!> check b gProp

    (t, V.El a) -> checkEl topt (gjoin a)

    -- go under lambda
    (P.Lam _ x' inf ma t, V.Pi x i a b)
      | (case inf of P.AIExpl           -> i == Expl
                     P.AIImpl _         -> i == Impl
                     P.AINamedImpl x' _ -> NSpan x' == x && i == Impl) -> do

      (a, va) <- case ma of
        Just a' -> do
          a' <- check a' gSet
          let va' = eval a'
          unify topt (gjoin va') (gjoin a)
          pure (a', va')
        Nothing -> do
          let qa = quote a
          pure (qa, a)

      bind x' a (gjoin va) \var ->
        S.Lam (bindToName x') i a <$!> check t (gjoin $! (b $$ var))

    -- insert implicit lambda
    (t, V.Pi x Impl a b) -> do
      let qa = quote a
      insertBinder qa (gjoin a) \var ->
        S.Lam x Impl qa <$!> check t (gjoin $! (b $$ var))

    (P.Pair t u, V.Sg sp x a b) -> do
      t <- check t (gjoin a)
      u <- check u (gjoin (b $$~ eval t))
      pure $ S.Pair t u

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
      Infer t tty <- insertApps $ infer topt
      debug ["subtype", showTm (quote (g1 tty)), showTm (quote (g2 tty)), showTm (quote topa), showTm (quote ftopa)]
      subtype topt t (eval t) tty (G topa ftopa)


-- infer
--------------------------------------------------------------------------------

-- | Ensure that a type is Set or Prop.
ensureSP :: InCxt (P.Tm -> V.Ty -> IO SP)
ensureSP topt a = forceAll a >>= \case
  V.Set  -> pure S
  V.Prop -> pure P
  Flex{} -> elabError topt AmbiguousUniverse
  _      -> elabError topt ExpectedSetProp

-- TODO: infer with SetProp arg, only for going under lambdas without ambiguity

infer :: InCxt (P.Tm -> IO Infer)
infer topt = do

  debug ["infer", P.showTm topt]

  Infer t ty <- case topt of

    P.Parens _ t _ ->
      infer t

    P.Var x -> case NT.lookup x ?nameTable of
      Nothing ->
        elabError topt $ NameNotInScope x
      Just (NT.Top x a ga v) ->
        pure $! Infer (S.TopDef x v (g2 ga)) ga
      Just (NT.Local x ga) ->
        pure $! Infer (S.LocalVar (lvlToIx x)) ga

    P.Pi _ x i topa topb -> do
      a <- check topa gSet
      bindWithTy x a \_ -> do
        Infer b (G bty fbty) <- infer topb
        sp <- ensureSP topb fbty
        pure $! Infer (S.Pi (bindToName x) i a b) (gU sp)

    P.Sg _ x topa topb -> do
      Infer a (G aty faty) <- infer topa
      let xn = bindToName x
      bindWithTy x a \_ -> do
        ensureSP topa faty >>= \case
          S -> do
            b <- check topb gSet
            pure $! Infer (S.Sg S xn a b) gSet
          P -> do
            Infer b (G bty fbty) <- infer topb
            ensureSP topb fbty >>= \case
              S -> pure $! Infer (S.Sg S xn (S.El a) b) gSet
              P -> pure $! Infer (S.Sg P xn a        b) gProp

    P.El _ -> do
      pure $! Infer S.ElSym (gjoin (V.Prop ==> V.Set))

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

    topt@(P.Eq t Nothing u) -> do
      Infer t tty <- infer t
      Infer u uty <- infer u
      unify topt tty uty
      let a = quote (g1 tty)
      pure $! Infer (S.Eq a t u) gProp

    topt@(P.Eq t (Just a) u) -> do
      a <- check a gSet
      let ga = gjoin (eval a)
      t <- check t ga
      u <- check u ga
      pure $! Infer (S.Eq a t u) gProp

    P.Hole _ -> do
      ty <- freshMeta gSet
      let gty = gjoin (eval ty)
      tm <- freshMeta gty
      pure $! Infer tm gty

    P.App topt topu i -> do

      (i, t, a, fa) <- case i of
        P.AIImpl _ -> do
          Infer t (G a fa) <- infer topt
          pure (Impl, t, a, fa)
        P.AIExpl -> do
          Infer t (G a fa) <- insertApps' $ infer topt
          pure (Expl, t, a, fa)
        P.AINamedImpl x _ -> do
          Infer t (G a fa) <- insertAppsUntilName topt x $ infer topt
          pure (Impl, t, a, fa)

      forceSet fa >>= \case

        V.Pi x _ a b -> do
          u <- check topu (gjoin a)
          pure $! Infer (S.App t u i) (gjoin (b $$~ eval u))

        V.El (V.Pi x _ a b) -> do
          u <- check topu (gjoin a)
          pure $! Infer (S.App t u i) (gjoin (V.El (b $$~ eval u)))

        fa ->
          elabError topt $ ExpectedFun a     -- TODO: postpone

    -- TODO: infer, postpone if ambiguous S/P
    P.Lam _ x inf ma t -> do
      i <- case inf of
        P.AIImpl _        -> pure Impl
        P.AIExpl          -> pure Expl
        P.AINamedImpl _ _ ->
          elabError topt $ GenericError "Can't infer type for lambda with named argument"
      a <- case ma of
        Nothing -> freshMeta gSet
        Just a  -> check a gSet
      let ~va = eval a
      Infer t b <- bind x a (gjoin va) \_ -> infer t
      let bcl = closeVal (g1 b)
      let name = bindToName x
      pure $ Infer (S.Lam name i a t) (gjoin (V.Pi name i va bcl))


    -- TODO: infer simple product type, postpone if ambiguous S/P
    P.Pair{} ->
      elabError topt $ GenericError "can't infer type for pair"

    P.Proj1 topt _ -> do
      Infer t (G ty fty) <- infer topt
      forceSet fty >>= \case
        V.Sg _ x a b        -> pure $! Infer (Proj1 t) (gjoin a)
        V.El (V.Sg _ x a b) -> pure $! Infer (Proj1 t) (gjoin (V.El a))

        -- fty@Flex{} -> do                       -- universe ambiguity! TODO: postpone
        --   a <- freshMeta gSet
        --   let va = eval a
        --   b <- freshMeta1 a gSet
        --   let sg = uf -- V.SgPrim nx va b
        --   unify topt (G ty fty) (gjoin sg)
        --   pure $! Infer (Proj1 t) (gjoin va)

        _ -> do
          elabError topt $! ExpectedSg ty

    P.Proj2 topt _ -> do
      Infer t (G ty fty) <- infer topt
      forceSet fty >>= \case
        V.Sg _ x a b        -> pure $! Infer (Proj2 t) (gjoin (b $$~ proj1 (eval t)))
        V.El (V.Sg _ x a b) -> pure $! Infer (Proj2 t) (gjoin (V.El (b $$~ proj1 (eval t))))

        -- fty@Flex{} -> do                      -- universe ambiguity! TODO: postpone
        --   a <- freshMeta gSet
        --   let va = eval a
        --   b <- freshMeta1 a gSet
        --   let sg = uf -- V.SgPrim nx va b
        --   unify topt (G ty fty) (gjoin sg)
        --   pure $! Infer (Proj2 t) (gjoin (b $$ proj1 (eval t)))

        _ -> do
          elabError topt $! ExpectedSg ty

    P.ProjField topt x -> do
      let fieldName = NSpan x
      Infer t ga <- infer topt
      let ~vt = eval t

      let go a ix = forceSet a >>= \case
            V.Sg _ x' a b | fieldName == x' -> do
              pure (ix, a)
            V.Sg _ x' a b -> do
              go (b $$~ projField vt ix) (ix + 1)
            V.El (V.Sg _ x' a b) | fieldName == x' -> do
              pure (ix, V.El a)
            V.El (V.Sg _ x' a b) -> do
              go (V.El (b $$~ projField vt ix)) (ix + 1)
            _ ->
              elabError topt $ NoSuchField x  -- TODO: postpone

      (ix, b) <- go (g2 ga) 0
      pure $! Infer (S.ProjField t fieldName ix) (gjoin b)

    P.Let _ x ma t u -> do

      (a, va) <- case ma of
        Just a -> do
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

    P.Exfalso _ -> do
      let ty = V.PiI na V.Set \a -> V.El V.Bot ==> a
      pure $! Infer S.ExfalsoSym (gjoin ty)

    P.Coe _ -> do
      let ty = V.PiI na V.Set \a -> V.PiI nb V.Set \b -> V.El (eqSet a b) ==> a ==> b
      pure $! Infer S.CoeSym (gjoin ty)

    P.Refl _ -> do
      let ty = V.El $ V.PiI na V.Set \a -> V.PiI nx a \x -> eq a x x
      pure $! Infer S.ReflSym (gjoin ty)

    P.Sym _ -> do
      let ty = V.El $ V.PiI na V.Set \a -> V.PiI ny a \x -> V.PiI ny a \y -> V.PiE np (V.El (eq a x y)) \p -> eq a y x
      pure $! Infer S.SymSym (gjoin ty)

    P.Trans _ -> do
      let ty = V.El $
               V.PiI na V.Set \a -> V.PiI nx a \x -> V.PiI ny a \y -> V.PiI nz a \z ->
               V.PiE np (V.El (eq a x y)) \p -> V.PiE nq (V.El (eq a y z)) \q ->
               eq a x z
      pure $! Infer S.TransSym (gjoin ty)

    P.Ap _ -> do
      let ty = V.El $
               V.PiI na V.Set \a -> V.PiI nb V.Set \b -> V.PiE nf (a ==> b) \f -> V.PiI nx a \x ->
               V.PiI ny a \y -> V.PiE np (V.El (eq a x y)) \p ->
               eq b (f `appE` x) (f `appE` y)
      pure $! Infer S.ApSym (gjoin ty)

  debug ["inferred", showTm t, showTm (quote (g1 ty)), showTm (quote (g2 ty))]
  pure (Infer t ty)


-- top-level
--------------------------------------------------------------------------------

inferTop :: NT.NameTableArg => TopLvlArg => P.TopLevel -> IO NT.NameTable
inferTop = \case

  P.Nil -> pure ?nameTable

  P.Define x ma t top -> initializeCxt do
    (a, va) <- case ma of

      Nothing -> do
        a' <- freshMeta gSet
        let va' = eval a'
        pure (a', va')
      Just a -> do
        a <- check a gSet
        pure (a, eval a)

    t <- check t (gjoin va)

    frz <- freezeMetas
    pushTop (TEDef x a t frz)
    let ?nameTable = NT.insert (Bind x) (NT.Top ?topLvl a (gjoin va) (eval t)) ?nameTable
        ?topLvl    = ?topLvl + 1

    inferTop top

  P.Postulate x a top -> initializeCxt do
    a <- check a gSet
    let ~va = eval a
        v   = Rigid (RHPostulate ?topLvl va) SId va

    frz <- freezeMetas
    pushTop (TEPostulate x a (gjoin va) frz)

    let ?nameTable = NT.insert (Bind x) (NT.Top ?topLvl a (gjoin va) v) ?nameTable
        ?topLvl    = ?topLvl + 1

    inferTop top

-- | Elaborate top-level presyntax, fill up `topInfo`.
--   Precondition: ElabState is in reset state.
elab :: P.TopLevel -> IO NT.NameTable
elab top = do
  let ?nameTable = mempty
      ?topLvl    = 0
  inferTop top
