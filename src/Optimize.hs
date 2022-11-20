
module Optimize (isInlinable, simplifyTopBlock) where

{-|
Inlining metas into elaboration output.
-}

import GHC.Exts hiding (inline)
import IO
import qualified Data.Array.FM as AFM
import qualified Data.Ref.F    as RF

import Common
import Syntax
import qualified ElabState as ES
import qualified Evaluation as E
import qualified Values as V

import Pretty

-- Config
--------------------------------------------------------------------------------

inlineMaxSize :: Int
inlineMaxSize = 100

simplificationPasses :: Int
simplificationPasses = 0


-- Compute term sizes
--------------------------------------------------------------------------------

data TmInfo = TmInfo Int Int -- size, number of unsolved metas

incr :: TmInfo -> TmInfo
incr (TmInfo s ms) = TmInfo (s + 1) ms

addMeta :: TmInfo -> TmInfo
addMeta (TmInfo s ms) = TmInfo s (ms + 1)

tmInfo :: Tm -> TmInfo
tmInfo t = go t (TmInfo 0 0) where
  go t s = case t of
    LocalVar x       -> incr s
    TopDef _ _ _     -> incr s
    Lam _ _ _ t      -> incr s
    App t u _        -> go t $ go u $ incr s
    Pair t u         -> go t $ go u $ incr s
    ProjField t _ _  -> go t $ incr s
    Proj1 t          -> go t $ incr s
    Proj2 t          -> go t $ incr s
    Pi _ _ t u       -> go t $ go u $ incr s
    Sg _ _ t u       -> go t $ go u $ incr s
    NewtypeSym       -> incr s
    Pack t           -> go t $ incr s
    Unpack t         -> go t $ incr s
    Postulate _ _    -> incr s
    InsertedMeta x _ -> addMeta $ incr s
    Meta x           -> addMeta $ incr s
    Let _ t u v      -> go t $ go u $ go v $ incr s
    Set              -> incr s
    Prop             -> incr s
    Top              -> incr s
    Tt               -> incr s
    Bot              -> incr s
    EqSym            -> incr s
    CoeSym           -> incr s
    ReflSym          -> incr s
    SymSym           -> incr s
    TransSym         -> incr s
    ApSym            -> incr s
    ExfalsoSym       -> incr s
    ElSym            -> incr s
    Magic _          -> impossible

dropClosingLams :: LocalsArg => Tm -> Tm
dropClosingLams = go ?locals where
  go LEmpty             t             = t
  go (LDefine ls _ _ _) t             = go ls t
  go (LBind ls _ _)     (Lam _ _ _ t) = go ls t
  go _                  _             = impossible

isInlinable :: LocalsArg => Tm -> Bool
isInlinable t = case tmInfo (dropClosingLams t) of
  TmInfo s ms -> s <= inlineMaxSize -- && ms <= 1


-- Inline the inlinable metavars.
--------------------------------------------------------------------------------

data VT = VT# Int Any

pattern VTV :: V.Val -> VT
pattern VTV v <- VT# 0 (unsafeCoerce# -> v) where
  VTV v = VT# 0 (unsafeCoerce# v)

pattern VTT :: Tm -> VT
pattern VTT t <- VT# 1 (unsafeCoerce# -> t) where
  VTT t = VT# 1 (unsafeCoerce# t)
{-# complete VTV, VTT #-}

vtcase :: VT -> (V.Val -> a) -> (Tm -> a) -> a
vtcase (VT# tag x) f g = case tag of
  0 -> f (unsafeCoerce# x)
  _ -> g (unsafeCoerce# x)
{-# inline vtcase #-}

vtmap :: VT -> (V.Val -> V.Val) -> (Tm -> Tm) -> VT
vtmap t f g = vtcase t (VTV . f) (VTT . g)
{-# inline vtmap #-}

app :: LvlArg => VT -> V.Val -> Icit -> VT
app t ~u i = vtmap t
  (\t -> E.app t u i)
  (\t -> App t (E.quote u) i)
{-# inline app #-}

proj1 :: LvlArg => VT -> VT
proj1 t = vtmap t E.proj1 Proj1
{-# inline proj1 #-}

proj2 :: LvlArg => VT -> VT
proj2 t = vtmap t E.proj2 Proj2
{-# inline proj2 #-}

projField :: LvlArg => VT -> Name -> Int -> VT
projField t x n = vtmap t (\t -> E.projField t n) (\t -> ProjField t x n)
{-# inline projField #-}

quote :: LvlArg => VT -> Tm
quote t = vtcase t E.quote id
{-# inline quote #-}

insertedMeta :: LvlArg => V.EnvArg => MetaVar -> Locals -> VT
insertedMeta x ls = case runIO (ES.readMeta x) of
  ES.MESolved s | s^.ES.isInlinable ->
    VTV $ E.spine (s^.ES.solutionVal) $! E.maskEnv' ?env ls (s^.ES.ty)
  _ ->
    VTT $ InsertedMeta x ls
{-# inline insertedMeta #-}

meta :: LvlArg => V.EnvArg => MetaVar -> VT
meta x = case runIO (ES.readMeta x) of
  ES.MESolved s | s^.ES.isInlinable -> VTV (s^.ES.solutionVal)
  _                                 -> VTT $ Meta x
{-# inline meta #-}

inlineSp :: LvlArg => V.EnvArg => Tm -> VT
inlineSp t = case t of
  InsertedMeta x ls -> insertedMeta x ls
  Meta x            -> meta x
  App t u i         -> app (inlineSp t) (E.eval u) i
  Proj1 t           -> proj1 (inlineSp t)
  Proj2 t           -> proj2 (inlineSp t)
  ProjField t x n   -> projField (inlineSp t) x n
  t                 -> VTT t

inline :: LvlArg => V.EnvArg => Tm -> Tm
inline t = let
  go = inline; {-# inline go #-}

  goBind a t =
    let v = V.Var ?lvl ((E.eval a)) in
    let ?lvl = ?lvl + 1 in
    let ?env = V.EDef ?env v in
    inline t

  in case t of
    LocalVar x        -> t
    TopDef x v a      -> t
    Lam x i a t       -> Lam x i (go a) (goBind a t)
    App t u i         -> quote (app (inlineSp t) (E.eval u) i)
    Pair t u          -> Pair (go t) (go u)
    ProjField t x n   -> quote (projField (inlineSp t) x n)
    Proj1 t           -> quote (proj1 (inlineSp t))
    Proj2 t           -> quote (proj2 (inlineSp t))
    Pi x i a b        -> Pi x i (go a) (goBind a b)
    Sg sp x a b       -> Sg sp x (go a) (goBind a b)
    NewtypeSym        -> t
    Pack t            -> case t of Unpack t -> go t; t -> Pack (go t)
    Unpack t          -> Unpack (go t)
    Postulate _ _     -> t
    InsertedMeta x ls -> quote (insertedMeta x ls)
    Meta x            -> quote (meta x)
    Let x a t u       -> Let x (go a) (go t) (goBind a u)
    Set               -> t
    Prop              -> t
    Top               -> t
    Tt                -> t
    Bot               -> t
    EqSym             -> t
    CoeSym            -> t
    ReflSym           -> t
    SymSym            -> t
    TransSym          -> t
    ApSym             -> t
    ExfalsoSym        -> t
    ElSym             -> t
    Magic _           -> impossible


inline0 :: Tm -> Tm
inline0 t = let ?lvl = 0; ?env = V.ENil in inline t


-- Count occurrences
--------------------------------------------------------------------------------

type Start  = (?start :: MetaVar)
type End    = (?end   :: MetaVar)
type Occurs = (?occurrences :: AFM.Array Int)

lookupCount :: Start => Occurs => MetaVar -> IO Int
lookupCount x = do
  let i = coerce x - coerce ?start :: Int
  if 0 <= i && i < AFM.size ?occurrences
    then AFM.read ?occurrences i            -- TODO: safeRead in primData
    else impossible

bump :: Start => Occurs => MetaVar -> IO ()
bump x = do
  let i = coerce x - coerce ?start :: Int
  if 0 <= i && i < AFM.size ?occurrences
    then AFM.modify ?occurrences i (+1)     -- TODO: safeModify in primdata
    else pure ()

count :: Start => Occurs => Tm -> IO ()
count = \case
  LocalVar x        -> pure ()
  TopDef x v a      -> pure ()
  Lam x i a t       -> count a >> count t
  App t u i         -> count t >> count u
  Pair t u          -> count t >> count u
  ProjField t x n   -> count t
  Proj1 t           -> count t
  Proj2 t           -> count t
  Pi x i a b        -> count a >> count b
  Sg sp x a b       -> count a >> count b
  NewtypeSym        -> pure ()
  Pack t            -> count t
  Unpack t          -> count t
  Postulate _ _     -> pure ()
  InsertedMeta x ls -> bump x
  Meta x            -> bump x
  Let x a t u       -> count a >> count t >> count u
  Set               -> pure ()
  Prop              -> pure ()
  Top               -> pure ()
  Tt                -> pure ()
  Bot               -> pure ()
  EqSym             -> pure ()
  CoeSym            -> pure ()
  ReflSym           -> pure ()
  SymSym            -> pure ()
  TransSym          -> pure ()
  ApSym             -> pure ()
  ExfalsoSym        -> pure ()
  ElSym             -> pure ()
  Magic _           -> impossible


-- Simplification
--------------------------------------------------------------------------------

countAllOccurs :: Start => End => Occurs => Tm -> Ty -> IO ()
countAllOccurs t a = do

  let go :: Start => End => Occurs => MetaVar -> IO ()
      go x | x < ?end = do
        ES.readMeta x >>= \case
          ES.MESolved s | not (s^.ES.isInlinable) -> count (s^.ES.solution)
          _                                       -> pure ()
        go (x + 1)
      go x = pure ()

  go ?start
  count a
  count t

updateInlines :: Start => End => Occurs => IO ()
updateInlines = do

  let go :: Start => End => Occurs => MetaVar -> IO ()
      go x | x < ?end = do

        ES.readMeta x >>= \case
          ES.MESolved s | not (s^.ES.isInlinable) -> do
            let ?locals = s^.ES.locals
            occCount <- lookupCount x
            let inl = isInlinable (s^.ES.solution)
            -- debug ["UPD INLINE", show x, showTm0 (s^.ES.solution), show occCount, show inl]
            when (inl || occCount <= 1) $
              ES.writeMeta x $
                ES.MESolved (s & ES.isInlinable      .~ True
                               & ES.inlinableChanged .~ True)
          _ -> pure ()

        go (x + 1)
      go x = pure ()
  go ?start

inlineAll :: Start => End => Occurs => Tm -> Ty -> IO (Tm, Ty)
inlineAll t a = do

  let go :: Start => End => Occurs => MetaVar -> IO ()
      go x | x < ?end = do
        ES.readMeta x >>= \case
          ES.MESolved s | s^.ES.inlinableChanged || not (s^.ES.isInlinable) -> do
            ES.writeMeta x $ ES.MESolved (s & ES.inlinableChanged .~ False
                                            & ES.solution %~ inline0)
          _ -> pure ()
        go (x + 1)
      go x = pure ()

  go ?start
  a <- pure $! inline0 a
  t <- pure $! inline0 t
  pure (t, a)

-- | Simplify current meta block.
--     1. Count occurrences of metas.
--     2. Mark linear and small metas as inline.
--     3. Do inlining on everything in the block.
simplificationPass :: Start => End => Occurs => (Tm, Ty) -> IO (Tm, Ty)
simplificationPass (t, a) = do
  AFM.set ?occurrences 0
  countAllOccurs t a
  updateInlines
  inlineAll t a

simplifyTopBlock :: (Tm, Ty) -> IO (Tm, Ty)
simplifyTopBlock (!t, !a) = do
  start <- RF.read ES.frozen
  end   <- ES.nextMeta

  let blockSize :: Int
      blockSize = coerce end - coerce start

  if blockSize == 0 then
    pure (t, a)

  else do
    occurrences <- AFM.new @Int blockSize

    let ?start       = start
        ?end         = end
        ?occurrences = occurrences

    let go :: Int -> (Tm, Ty) -> IO (Tm, Ty)
        go 0 ta = pure ta
        go n ta = do
          -- debug ["OPTPASS"]
          ta <- simplificationPass ta
          go (n - 1) ta

    go simplificationPasses (t, a)
