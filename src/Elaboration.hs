
module Elaboration where

import Control.Exception
import Data.ByteString()

import Common
import Configuration
import Cxt
import ElabState
import Errors
import Evaluation
import Pretty
import Syntax
import Unification (freshMeta, UnifyEx(..))
import Values
import Optimize

import qualified NameTable as NT
import qualified Presyntax as P
import qualified Syntax as S
import qualified Unification as Unif
import qualified Values as V

--------------------------------------------------------------------------------

elabError :: LocalsArg => LvlArg => P.Tm -> Error -> IO a
elabError t err = do
  src <- readElabSource >>= \case
    Just src -> pure src
    Nothing  -> impossible
  throwIO $ ErrorInCxt src ?locals ?lvl t err

unify :: LvlArg => LocalsArg => P.Tm -> Val -> Val -> IO ()
unify t l r = do
  let ?unifyState = USRigid conversionSpeculation
      ?names      = localNames
  Unif.unify (G l l) (G r r) `catch` \case
    (e :: UnifyEx) -> elabError t (UnifyError l r e)

data Infer = Infer Tm V.Ty

-- Insertion
--------------------------------------------------------------------------------

-- | Insert fresh implicit applications.
insertApps' :: LvlArg => EnvArg => LocalsArg => IO Infer -> IO Infer
insertApps' act = go =<< act where

  go :: Infer -> IO Infer
  go (Infer t topa) = forceAll topa >>= \case

    V.Pi x Impl a b -> do
      m <- freshMeta a
      go $! Infer (S.App t m Impl) (b $$ eval m)

    V.El a -> forceAll a >>= \case
      V.Pi x Impl a b -> do
        m <- freshMeta a
        let mv = eval m
        go $! Infer (S.App t m Impl) (V.El (b $$ mv))
      _ ->
        pure $ Infer t topa
    _ ->
      pure $ Infer t topa
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
  go (Infer t topa) = forceAll topa >>= \case

    ftopa@(V.Pi x Impl a b) -> do
      if x == NSpan name then
        pure (Infer t topa)
      else do
        m <- freshMeta a
        let mv = eval m
        go $! Infer (S.App t m Impl) (b $$ mv)

    V.El topa -> forceAll topa >>= \case
      V.Pi x Impl a b -> do
        if x == NSpan name then
          pure (Infer t (V.El topa))
        else do
          m <- freshMeta a
          let mv = eval m
          go $! Infer (S.App t m Impl) (V.El (b $$ mv))
      _ -> elabError pt $ NoNamedImplicitArg name
    _ ->
      elabError pt $ NoNamedImplicitArg name
{-# inline insertAppsUntilName #-}

--------------------------------------------------------------------------------

subtype :: InCxt (P.Tm -> S.Tm -> Val -> V.Ty -> V.Ty -> IO S.Tm)
subtype pt t ~tv a b = do
  fa <- forceAll a
  fb <- forceAll b
  debug ["subtype", showTm (quote a), showTm (quote fa), showTm (quote b), showTm (quote fb)]
  case (fa, fb) of
    (V.Prop, V.Set ) -> pure $ S.El t
    (V.Set , V.Prop) -> case t of
      S.El a -> pure a
      _      -> do m <- eval <$!> freshMeta V.Prop
                   unify pt tv (V.El m)
                   pure $! quote m
    _ -> do
      unify pt a b
      pure t
{-# inline subtype #-}

checkEl :: InCxt (P.Tm -> V.Ty -> IO S.Tm)
checkEl topt topa = case topt of

  P.Parens _ t _ ->
    checkEl t topa

  P.Let _ x ma t u -> do
    (a, va) <- checkSetAnnot ma
    t       <- check t va
    define x a va t (eval t) do
      u <- checkEl u topa
      pure $ S.Let (NSpan x) a t u

  P.Hole _ ->
    freshMeta topa

  _ -> do
    ftopa <- forceAll topa
    debug ["checkEl" , P.showTm topt , showTm (quote topa), showTm (quote ftopa)]
    case (topt, ftopa) of

      -- go under lambda
      (P.Lam _ x' inf ma t, V.Pi x i a b)
        | (case inf of P.AIExpl           -> i == Expl
                       P.AIImpl _         -> i == Impl
                       P.AINamedImpl x' _ -> NSpan x' == x && i == Impl) -> do
        (a, va) <- case ma of
          Just a' -> do
            a' <- check a' V.Set
            let va' = eval a'
            unify topt va' a
            pure (a', va')
          Nothing -> do
            let qa = quote a
            pure (qa, a)
        bind x' a va \var ->
          S.Lam (bindToName x') i a <$!> (checkEl t $! (b $$ var))

      -- insert implicit lambda
      (t, V.Pi x Impl a b) -> do
        let qa = quote a
        insertBinder x qa a \var ->
          S.Lam x Impl qa <$!> (checkEl t $! (b $$ var))

      (P.Pair t u, V.Sg _ x a b) -> do
        t <- checkEl t a
        u <- checkEl u (b $$~ eval t)
        pure $ S.Pair t u

      (topt, _) -> do
        Infer t tty <- insertApps $ infer topt
        unify topt tty (V.El topa)
        pure t

checkSetAnnot :: InCxt (Maybe P.Tm -> IO (S.Tm, V.Ty))
checkSetAnnot ma = case ma of
  Just a  -> do
    a <- check a V.Set
    let va = eval a
    pure (a, va)
  Nothing -> do
    a <- freshMeta V.Set
    let va = eval a
    pure (a, va)
{-# inline checkSetAnnot #-}

check :: InCxt (P.Tm -> V.Ty -> IO S.Tm)
check topt topa = do

  case topt of
    P.Parens _ t _ ->
      check t topa

    P.Let _ x ma t u -> do
      (a, va) <- checkSetAnnot ma
      t       <- check t va
      define x a va t (eval t) do
        u <- check u topa
        pure $ S.Let (NSpan x) a t u

    P.Hole _ ->
      freshMeta topa

    _ -> do
      ftopa <- forceAll topa
      debug ["check", P.showTm topt, showTm (quote topa)]

      case (topt, ftopa) of

        (P.Pi _ x i a b, V.Prop) -> do
          a <- check a V.Set
          bindWithTy x a \_ ->
            S.Pi (bindToName x) i a <$!> check b V.Prop

        (P.Sg _ x a b, V.Prop) -> do
          a <- check a V.Prop
          bindWithTy x a \_ ->
            S.Sg P (bindToName x) a <$!> check b V.Prop

        (t, V.El a) -> checkEl topt a

        -- go under lambda
        (P.Lam _ x' inf ma t, V.Pi x i a b)
          | (case inf of P.AIExpl           -> i == Expl
                         P.AIImpl _         -> i == Impl
                         P.AINamedImpl x' _ -> NSpan x' == x && i == Impl) -> do

          (a, va) <- case ma of
            Just a' -> do
              a' <- check a' V.Set
              let va' = eval a'
              unify topt va' a
              pure (a', va')
            Nothing -> do
              let qa = quote a
              pure (qa, a)

          bind x' a va \var ->
            S.Lam (bindToName x') i a <$!> check t (b $$ var)

        -- insert implicit lambda
        (t, V.Pi x Impl a b) -> do
          let qa = quote a
          insertBinder x qa a \var ->
            S.Lam x Impl qa <$!> check t (b $$ var)

        (P.Pair t u, V.Sg sp x a b) -> do
          t <- check t a
          u <- check u (b $$~ eval t)
          pure $ S.Pair t u

        (P.Pack _ t, V.Newtype a b x bx) -> do
          S.Pack <$!> check t bx

        (P.Pair t u, V.Newtype a b x bx) -> do
          S.Pack <$!> check topt bx

        (topt, _) -> do
          Infer t tty <- insertApps $ infer topt
          subtype topt t (eval t) tty topa


-- infer
--------------------------------------------------------------------------------

-- | Ensure that a type is Set or Prop.
ensureSP :: InCxt (P.Tm -> V.Ty -> IO SP)
ensureSP topt a = forceAll a >>= \case
  V.Set  -> pure S
  V.Prop -> pure P
  Flex{} -> elabError topt AmbiguousUniverse -- TODO: postpone
  _      -> elabError topt ExpectedSetProp

infer :: InCxt (P.Tm -> IO Infer)
infer topt = do

  debug ["infer", P.showTm topt]

  Infer t ty <- case topt of

    P.Parens _ t _ ->
      infer t

    P.Var x -> case NT.lookup x ?nameTable of
      Nothing ->
        elabError topt $ NameNotInScope x
      Just (NT.Top x a va v) ->
        pure $! Infer (S.TopDef x v va) va
      Just (NT.Local x ga) ->
        pure $! Infer (S.LocalVar (lvlToIx x)) ga

    P.Pi _ x i topa topb -> do
      a <- check topa V.Set
      bindWithTy x a \_ -> do
        Infer b bty <- infer topb
        sp <- ensureSP topb bty
        pure $! Infer (S.Pi (bindToName x) i a b) (uSP sp)

    P.Sg _ x topa topb -> do
      Infer a aty <- infer topa
      let xn = bindToName x
      bindWithTy x a \_ -> do
        ensureSP topa aty >>= \case
          S -> do
            b <- check topb V.Set
            pure $! Infer (S.Sg S xn a b) V.Set
          P -> do
            Infer b bty <- infer topb
            ensureSP topb bty >>= \case
              S -> pure $! Infer (S.Sg S xn (S.El a) b) V.Set
              P -> pure $! Infer (S.Sg P xn a        b) V.Prop

    P.El _ -> do
      pure $! Infer S.ElSym (V.Prop ==> V.Set)

    P.Set _ ->
      pure $ Infer S.Set V.Set

    P.Prop _ ->
      pure $ Infer S.Prop V.Set

    P.Top _ ->
      pure $ Infer S.Top V.Prop

    P.Bot _ ->
      pure $ Infer S.Bot V.Prop

    P.Tt _ ->
      pure $ Infer S.Tt (V.El V.Top)

    P.Eq t Nothing u -> do
      Infer t tty <- insertApps $ infer t
      u <- check u tty
      let a = quote tty
      pure $ Infer (S.Eq a t u) V.Prop

    P.Eq t (Just a) u -> do
      a <- check a V.Set
      let va = eval a
      t <- check t va
      u <- check u va
      pure $ Infer (S.Eq a t u) V.Prop

    P.Hole _ -> do
      ty <- freshMeta V.Set
      let vty = eval ty
      tm <- freshMeta vty
      pure $ Infer tm vty

    P.App topt topu i -> do

      (i, t, a) <- case i of
        P.AIImpl _ -> do
          Infer t a <- infer topt
          pure (Impl, t, a)
        P.AIExpl -> do
          Infer t a <- insertApps' $ infer topt
          pure (Expl, t, a)
        P.AINamedImpl x _ -> do
          Infer t a <- insertAppsUntilName topt x $ infer topt
          pure (Impl, t, a)

      forceSet a >>= \case

        V.Pi x _ a b -> do
          u <- check topu a
          pure $! Infer (S.App t u i) (b $$~ eval u)

        V.El (V.Pi x _ a b) -> do
          u <- check topu a
          pure $! Infer (S.App t u i) (V.El (b $$~ eval u))

        fa ->
          elabError topt $ ExpectedFun a     -- TODO: postpone

    P.Lam _ x inf ma t -> do
      i <- case inf of
        P.AIImpl _        -> pure Impl
        P.AIExpl          -> pure Expl
        P.AINamedImpl _ _ -> elabError topt $ GenericError "Can't infer type for lambda with named argument"
      a <- case ma of
        Nothing -> freshMeta V.Set
        Just a  -> check a V.Set
      let ~va = eval a
      Infer t b <- bind x a va \_ -> infer t
      let name = bindToName x
      forceAll b >>= \case
        V.Flex{} ->
          elabError topt AmbiguousUniverse -- TODO: postpone
        V.El b   -> do
          let bcl = closeVal b
          pure $ Infer (S.Lam name i a t) (V.El (V.Pi name i va bcl))
        _ -> do
          let bcl = closeVal b
          pure $ Infer (S.Lam name i a t) (V.Pi name i va bcl)

    -- Infer simple product type
    P.Pair t u -> do
      Infer t a <- insertApps $ infer t
      Infer u b <- insertApps $ infer u
      fa        <- forceAll a
      fb        <- forceAll b
      -- debug ["INFERPAIR", P.showTm topt, showTm (quote a), showTm (quote b),
      --                     showTm (quote fa), showTm (quote fb)]
      case (fa, fb) of
        (Flex{}  , _       ) ->
          elabError topt AmbiguousUniverse

        (_       , Flex{}  ) ->
          elabError topt AmbiguousUniverse

        -- intentionally creating extra metas to get more solution sharing
        (V.El a' , V.El b' ) -> do
          ma <- eval <$!> freshMeta V.Prop  -- TODO: optimize
          mb <- eval <$!> freshMeta V.Prop
          unify topt ma a'
          unify topt mb b'
          pure $! Infer (S.Pair t u) (V.El (andP ma mb))
        _ ->
          pure $! Infer (S.Pair t u) (prod a b)


    P.Proj1 topt _ -> do
      Infer t tty <- infer topt
      forceSet tty >>= \case
        V.Sg _ x a b        -> pure $! Infer (Proj1 t) a
        V.El (V.Sg _ x a b) -> pure $! Infer (Proj1 t) (V.El a)
        V.Newtype _ _ _ bx  -> do
          forceSet bx >>= \case
            V.Sg _ x a b        -> pure $! Infer (Proj1 (Unpack t)) a
            V.El (V.Sg _ x a b) -> pure $! Infer (Proj1 (Unpack t)) (V.El a)
            _                   -> elabError topt $! ExpectedSg tty

        -- fty@Flex{} -> do                       -- universe ambiguity! TODO: postpone
        --   a <- freshMeta V.Set
        --   let va = eval a
        --   b <- freshMeta1 a V.Set
        --   let sg = uf -- V.SgPrim nx va b
        --   unify topt (G ty fty) (gjoin sg)
        --   pure $! Infer (Proj1 t) (gjoin va)

        _ -> do
          elabError topt $! ExpectedSg tty

    P.Proj2 topt _ -> do
      Infer t tty <- infer topt
      forceSet tty >>= \case
        V.Sg _ x a b        -> pure $! Infer (Proj2 t) (b $$~ proj1 (eval t))
        V.El (V.Sg _ x a b) -> pure $! Infer (Proj2 t) (V.El (b $$~ proj1 (eval t)))
        V.Newtype _ _ _ bx  -> do
          forceSet bx >>= \case
            V.Sg _ x a b        -> pure $! Infer (Proj2 (Unpack t)) (b $$~ proj1 (eval t))
            V.El (V.Sg _ x a b) -> pure $! Infer (Proj2 (Unpack t)) (V.El (b $$~ proj1 (eval t)))
            _                   -> elabError topt $! ExpectedSg tty

        -- fty@Flex{} -> do                      -- universe ambiguity! TODO: postpone
        --   a <- freshMeta V.Set
        --   let va = eval a
        --   b <- freshMeta1 a V.Set
        --   let sg = uf -- V.SgPrim nx va b
        --   unify topt (G ty fty) (gjoin sg)
        --   pure $! Infer (Proj2 t) (gjoin (b $$ proj1 (eval t)))

        _ -> do
          elabError topt $! ExpectedSg tty

    P.ProjField topt fieldSpan -> do
      let fieldName = NSpan fieldSpan
      Infer t tty <- infer topt

      let go ~vt a ix = forceSet a >>= \case
            V.Sg _ x' a b | fieldName == x' -> do
              pure (ix, a)
            V.Sg _ x' a b -> do
              go vt (b $$~ projField vt ix) (ix + 1)
            V.El (V.Sg _ x' a b) | fieldName == x' -> do
              pure (ix, V.El a)
            V.El (V.Sg _ x' a b) -> do
              go vt (V.El (b $$~ projField vt ix)) (ix + 1)
            _ ->
              elabError topt $ NoSuchField fieldSpan  -- TODO: postpone

      forceSet tty >>= \case
        V.Newtype _ _ _ bx -> do
          let ~vt = unpack (eval t)
          (ix, b) <- go vt bx 0
          pure $! Infer (S.ProjField (S.Unpack t) fieldName ix) b
        tty -> do
          let ~vt = eval t
          (ix, b) <- go vt tty 0
          pure $! Infer (S.ProjField t fieldName ix) b

    P.Let _ x ma t u -> do

      (a, va) <- case ma of
        Just a -> do
          a <- check a V.Set
          let va = eval a
          pure (a, va)
        Nothing -> do
          a <- freshMeta V.Set
          let va = eval a
          pure (a, va)

      t <- check t va

      define x a va t (eval t) do
        Infer u uty <- infer u
        pure $ Infer (S.Let (NSpan x) a t u) uty

    P.Newtype _ -> do
      let ty = V.PiI na V.Set \a -> V.PiE nb (a ==> V.Set) \b -> V.PiE nx a \x -> V.Set
      pure $! Infer S.NewtypeSym ty

    P.Pack _ t -> do
      elabError topt $ GenericError "Can't infer type for packed value"

    P.Unpack t _ -> do
      Infer t a <- infer t
      forceAll a >>= \case
        V.Newtype _ _ _ bx -> pure $! Infer (S.Unpack t) bx
        _                  -> elabError topt $ GenericError "Can't infer type for packed value" -- TODO:postpone

    P.Exfalso _ -> do
      let ty = V.PiI na V.Set \a -> V.El V.Bot ==> a
      pure $! Infer S.ExfalsoSym ty

    P.Coe _ -> do
      let ty = V.PiI na V.Set \a -> V.PiI nb V.Set \b -> V.El (eqSet a b) ==> a ==> b
      pure $! Infer S.CoeSym ty

    P.Refl _ -> do
      let ty = V.El $ V.PiI na V.Set \a -> V.PiI nx a \x -> eq a x x
      pure $! Infer S.ReflSym ty

    P.Sym _ -> do
      let ty = V.El $ V.PiI na V.Set \a -> V.PiI ny a \x -> V.PiI ny a \y -> V.PiE np (V.El (eq a x y)) \p -> eq a y x
      pure $! Infer S.SymSym ty

    P.Trans _ -> do
      let ty = V.El $
               V.PiI na V.Set \a -> V.PiI nx a \x -> V.PiI ny a \y -> V.PiI nz a \z ->
               V.PiE np (V.El (eq a x y)) \p -> V.PiE nq (V.El (eq a y z)) \q ->
               eq a x z
      pure $! Infer S.TransSym ty

    P.Ap _ -> do
      let ty = V.El $
               V.PiI na V.Set \a -> V.PiI nb V.Set \b -> V.PiE nf (a ==> b) \f -> V.PiI nx a \x ->
               V.PiI ny a \y -> V.PiE np (V.El (eq a x y)) \p ->
               eq b (f `appE` x) (f `appE` y)
      pure $! Infer S.ApSym ty

  debug ["inferred", showTm t, showTm (quote ty)]
  pure (Infer t ty)


-- top-level
--------------------------------------------------------------------------------

inferTop :: NT.NameTableArg => TopLvlArg => P.TopLevel -> IO NT.NameTable
inferTop = \case

  P.Nil -> pure ?nameTable

  P.Define x ma t top -> initializeCxt do
    a <- case ma of
      Nothing -> freshMeta V.Set
      Just a  -> check a V.Set

    t      <- check t (eval a)
    (t, a) <- simplifyTopBlock (t, a)
    ~va    <- pure (eval a)

    frz <- freezeMetas
    pushTop (TEDef x a t frz)

    case NT.lookup x ?nameTable of
      Nothing -> pure ()
      Just _  -> elabError (P.Var x) TopLevelShadowing

    let ?nameTable = NT.insert (Bind x) (NT.Top ?topLvl a va (eval t)) ?nameTable
        ?topLvl    = ?topLvl + 1

    inferTop top

  P.Postulate x a top -> initializeCxt do
    a <- check a V.Set

    (a, _) <- simplifyTopBlock (a, S.Set)

    let ~va = eval a
        v   = Rigid (RHPostulate ?topLvl va) SId va

    frz <- freezeMetas
    pushTop (TEPostulate x a va frz)

    let ?nameTable = NT.insert (Bind x) (NT.Top ?topLvl a va v) ?nameTable
        ?topLvl    = ?topLvl + 1

    inferTop top

-- | Elaborate top-level presyntax, fill up `topInfo`.
--   Precondition: ElabState is in reset state.
elab :: P.TopLevel -> IO NT.NameTable
elab top = do
  let ?nameTable = mempty
      ?topLvl    = 0
  inferTop top
