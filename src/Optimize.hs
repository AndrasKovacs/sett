
module Optimize (isInlinable, inlineMetaBlock) where

{-|
Inlining metas into elaboration output.
-}

import Common
import Syntax
import Pretty

import qualified ElabState as ES
import qualified Evaluation as E
import qualified Values as V

import GHC.Exts hiding (inline)
import IO
import qualified Data.Array.FM as AFM
import qualified Data.Array.FI as AFI
import qualified Data.Ref.F    as RF

import Debug.Trace

--------------------------------------------------------------------------------

inlineMaxSize :: Int
inlineMaxSize = 0

tmSize :: Tm -> Int
tmSize t = go t 0 where
  go t s = case t of
    LocalVar x      -> s + 1
    TopDef _ _ _    -> s + 1
    Lam _ _ _ t     -> s + 1
    App t u _       -> go t $ go u $ s + 1
    Pair t u        -> go t $ go u $ s + 1
    ProjField t _ _ -> go t $ s + 1
    Proj1 t         -> go t $ s + 1
    Proj2 t         -> go t $ s + 1
    Pi _ _ t u      -> go t $ go u $ s + 1
    Sg _ _ t u      -> go t $ go u $ s + 1
    NewtypeSym      -> s + 1
    Pack t          -> go t $ s + 1
    Unpack t        -> go t $ s + 1
    Postulate _ _   -> s + 1
    InsertedMeta{}  -> s + 1
    Meta{}          -> s + 1
    Let _ t u v     -> go t $ go u $ go v $ s + 1
    Set             -> s + 1
    Prop            -> s + 1
    Top             -> s + 1
    Tt              -> s + 1
    Bot             -> s + 1
    EqSym           -> s + 1
    CoeSym          -> s + 1
    ReflSym         -> s + 1
    SymSym          -> s + 1
    TransSym        -> s + 1
    ApSym           -> s + 1
    ExfalsoSym      -> s + 1
    ElSym           -> s + 1
    Magic _         -> impossible

dropClosingLams :: LocalsArg => Tm -> Tm
dropClosingLams = go ?locals where
  go LEmpty             t             = t
  go (LDefine ls _ _ _) t             = go ls t
  go (LBind ls _ _)     (Lam _ _ _ t) = go ls t
  go _                  _             = impossible

metaSolutionSize :: LocalsArg => Tm -> Int
metaSolutionSize t = tmSize (dropClosingLams t)

isInlinable :: LocalsArg => Tm -> Bool
isInlinable t = metaSolutionSize t <= inlineMaxSize

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
  ES.MESolved _ t v a True -> VTV $ E.spine v $! E.maskEnv' ?env ls a
  _                        -> VTT $ InsertedMeta x ls
{-# inline insertedMeta #-}

meta :: LvlArg => V.EnvArg => MetaVar -> VT
meta x = case runIO (ES.readMeta x) of
  ES.MESolved _ t v a True -> VTV v
  _                        -> VTT $ Meta x
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

-- inline0 :: Tm -> Tm
-- inline0 t = runIO do
--   debug ["INLINE0-PRE", showTm0 t]
--   let ?lvl = 0; ?env = V.ENil
--   let res = inline t
--   debug ["INLINE0-POST", showTm0 res]
--   pure res

inline0 :: Tm -> Tm
inline0 t = let ?lvl = 0; ?env = V.ENil in inline t

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
    else impossible

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

countAllOccurs :: Start => End => Occurs => Tm -> Ty -> IO ()
countAllOccurs t a = do
  let go :: Start => End => Occurs => MetaVar -> IO ()
      go x | x < ?end = ES.readMeta x >>= \case
        ES.MEUnsolved _ _     -> go (x + 1)
        ES.MESolved _ t _ _ _ -> count t >> go (x + 1)
      go x = pure ()

  go ?start
  count a
  count t

markInlines :: Start => End => Occurs => IO ()
markInlines = do
  let go :: Start => End => Occurs => MetaVar -> IO ()
      go x | x < ?end = do
        debug ["MARK", show x, show ?start, show ?end]
        ES.readMeta x >>= \case
          ES.MESolved c t a va _ -> do
            lookupCount x >>= \case
              n | n <= 1 -> ES.writeMeta x (ES.MESolved c t a va True)
              _          -> pure ()
          _ -> pure ()
        go (x + 1)

      go x = pure ()
  go ?start

inlineAll :: Start => End => Occurs => Tm -> Ty -> IO (Tm, Ty)
inlineAll t a = do

  let go :: Start => End => Occurs => MetaVar -> IO ()
      go x | x < ?end = do
        ES.readMeta x >>= \case
          ES.MEUnsolved{} -> pure ()
          ES.MESolved c t v a inl -> do
           ES.writeMeta x $ ES.MESolved c (inline0 t) v a inl
        go (x + 1)
      go x = pure ()

  go ?start
  a <- pure $! inline0 a
  t <- pure $! inline0 t
  pure (t, a)


-- | Simplify current meta block.
--     1. Count occurrences of metas.
--     2. Mark linear metas as inline.
--     3. Perform inlining on everything in the block.
inlineMetaBlock :: Tm -> Ty -> IO (Tm, Ty)
inlineMetaBlock t a = do
  -- get extent of block
  start <- RF.read ES.frozen
  end   <- ES.nextMeta

  let blockSize :: Int
      blockSize = coerce end - coerce start

  if blockSize == 0 then
    pure (t, a)
  else do
    occurrences <- AFM.new @Int blockSize
    AFM.set occurrences 0

    let ?start       = start
        ?end         = end
        ?occurrences = occurrences

    occs <- AFI.foldr (:) [] <$> AFM.unsafeFreeze occurrences
    debug ["PRE-OCCS", show $ zip [coerce ?start .. coerce ?end :: Int] occs]

    countAllOccurs t a

    occs <- AFI.foldr (:) [] <$> AFM.unsafeFreeze occurrences
    debug ["POST-OCCS", show $ zip [coerce ?start .. coerce ?end :: Int] occs]

    markInlines
    inlineAll t a
