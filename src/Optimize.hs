
module Optimize where

{-|
Inlining metas into elaboration output.
-}

import qualified Data.IntSet as IS

import Common
import Syntax

{-
First approximation of inlining metas:
  - meta is inlinable if it is size X at most and only contains
    app, proj, Set, Prop, topvar, linear localvars
-}

data TmInfo = TmInfo {
    size     :: Int
  , localSet :: IS.IntSet
  , linear   :: Bool
  }

inlineMaxSize :: Int
inlineMaxSize = 10

tmInfo :: Tm -> TmInfo
tmInfo = goLams where

  goLams :: Tm -> TmInfo
  goLams = \case
    Lam _ _ _ t -> goLams t
    t           -> go t (TmInfo 0 mempty True)

  incr (TmInfo s xs lin) =
    TmInfo (s + 1) xs lin

  addVar (Ix x) (TmInfo s xs lin) =
    TmInfo (s + 1) (IS.insert x xs) (IS.notMember x xs)

  go :: Tm -> TmInfo -> TmInfo
  go t inf = case t of
    LocalVar x      -> addVar x inf
    TopDef _ _ _    -> incr inf
    Lam _ _ _ t     -> incr inf
    App t u _       -> go t $ go u $ incr inf
    Pair t u        -> go t $ go u $ incr inf
    ProjField t _ _ -> go t $ incr inf
    Proj1 t         -> go t $ incr inf
    Proj2 t         -> go t $ incr inf
    Pi _ _ t u      -> go t $ go u $ incr inf
    Sg _ _ t u      -> go t $ go u $ incr inf
    NewtypeSym      -> incr inf
    Pack t          -> go t $ incr inf
    Unpack t        -> go t $ incr inf
    Postulate _ _   -> incr inf
    InsertedMeta{}  -> incr inf
    Meta{}          -> incr inf
    Let _ t u v     -> go t $ go u $ go v $ incr inf
    Set             -> incr inf
    Prop            -> incr inf
    Top             -> incr inf
    Tt              -> incr inf
    Bot             -> incr inf
    EqSym           -> incr inf
    CoeSym          -> incr inf
    ReflSym         -> incr inf
    SymSym          -> incr inf
    TransSym        -> incr inf
    ApSym           -> incr inf
    ExfalsoSym      -> incr inf
    ElSym           -> incr inf
    Magic _         -> impossible

isInlinable :: Tm -> Bool
isInlinable t = case tmInfo t of
  TmInfo size _ lin -> lin && size <= inlineMaxSize
