
module Cxt.Extension where

import Common
import Cxt.Types
import Evaluation
import Values

import qualified NameTable as N
import qualified Syntax as S
import qualified Values as V

-- | Add a bound variable to the context. We bring the new variable into scope.
bind :: InCxt (Bind -> S.Ty -> V.Ty -> InCxt (Val -> a) -> a)
bind x a va k =
  let v          = V.Var ?lvl va
  in
  let ?lvl       = ?lvl + 1
      ?env       = V.EDef ?env v
      ?locals    = S.LBind ?locals (bindToName x) a
      ?nameTable = N.insert x (N.Local ?lvl va) ?nameTable
  in forceCxt (k v)
{-# inline bind #-}

-- | Add a bound variable to the context, where we only have a syntactic
--   representation of the binder type.
bindWithTy :: InCxt (Bind -> S.Ty -> InCxt (Val -> a) -> a)
bindWithTy x a k = bind x a (eval a) k
{-# inline bindWithTy #-}

-- | Add a definition to the context.
define :: InCxt (Span -> S.Ty -> V.Ty -> S.Tm -> V.Val -> InCxt a -> a)
define x a ga t ~vt k =
  let ?lvl       = ?lvl + 1
      ?env       = V.EDef ?env vt
      ?locals    = S.LDefine ?locals (NSpan x) a t
      ?nameTable = N.insert (Bind x) (N.Local ?lvl ga) ?nameTable
  in forceCxt k
{-# inline define #-}

-- | Add a bound variable which does not exist in the source.
insertBinder :: InCxt (Name -> S.Ty -> V.Ty -> InCxt (Val -> a) -> a)
insertBinder x a va k =
  let v          = V.Var ?lvl va
  in
  let ?lvl       = ?lvl + 1
      ?env       = V.EDef ?env v
      ?locals    = S.LBind ?locals x a
  in forceCxt (k v)
{-# inline insertBinder #-}

initializeCxt :: N.NameTableArg => InCxt a -> a
initializeCxt k =
  let ?lvl       = 0 :: Lvl
      ?env       = ENil
      ?locals    = S.LEmpty
  in k
{-# inline initializeCxt #-}
