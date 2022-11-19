
module Optimize (inline, isInlinable) where

{-|
Inlining metas into elaboration output.
-}

import GHC.Exts hiding (inline)

import IO
import Common
import Syntax
import qualified Evaluation as E
import qualified Values as V
import qualified ElabState as ES

--------------------------------------------------------------------------------

inlineMaxSize :: Int
inlineMaxSize = 15

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
  VTT t = VT# 0 (unsafeCoerce# t)
{-# complete VTV, VTT #-}

vtmap :: VT -> (V.Val -> V.Val) -> (Tm -> Tm) -> VT
vtmap (VTV v) f g = VTV (f v)
vtmap (VTT t) f g = VTT (g t)
{-# inline vtmap #-}

app :: LvlArg => VT -> V.Val -> Icit -> VT
app t u i = vtmap t
  (\t -> E.app t u i)
  (\t -> App t (E.quote u) i)

proj1 :: LvlArg => VT -> VT
proj1 t = vtmap t E.proj1 Proj1

proj2 :: LvlArg => VT -> VT
proj2 t = vtmap t E.proj2 Proj2

projField :: LvlArg => VT -> Name -> Int -> VT
projField t x n = vtmap t (\t -> E.projField t n) (\t -> ProjField t x n)

quote :: LvlArg => VT -> Tm
quote (VTV v) = E.quote v
quote (VTT t) = t

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
inlineSp = \case
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
    let v = V.Var ?lvl (E.eval a) in
    let ?lvl = ?lvl + 1 in
    let ?env = V.EDef ?env v in
    go t

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
