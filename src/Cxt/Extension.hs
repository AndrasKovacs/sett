
module Cxt.Extension where

import Common
import Cxt.Types
import Values

import qualified NameTable as N
import qualified Syntax as S
import qualified Values as V

-- | Add a bound variable to the context. We bring the new variable into scope.
bind :: CxtArg => Bind -> S.Ty -> V.GTy -> (CxtArg => Val -> a) -> a
bind x a ga k =
  let v          = V.Var ?lvl (g2 ga)
  in
  let ?lvl       = ?lvl + 1
      ?env       = V.EDef ?env v
      ?locals    = S.LBind ?locals (bindToName x) a
      ?nameTable = N.insert x (N.Local ?lvl ga) ?nameTable
  in cxt $ k v
{-# inline bind #-}

-- | Add a definition to the context.
define :: CxtArg => Span -> S.Ty -> V.GTy -> S.Tm -> V.Val -> (CxtArg => a) -> a
define x a ga t ~vt k =
  let ?lvl = ?lvl + 1
      ?env = V.EDef ?env vt
      ?locals = S.LDefine ?locals (NSpan x) a t
      ?nameTable = N.insert (Bind x) (N.Local ?lvl ga) ?nameTable
  in cxt k
{-# inline define #-}

-- | Add a bound variable which does not exist in the source.
insertBinder :: CxtArg => S.Ty -> V.GTy -> (CxtArg => Val -> a) -> a
insertBinder a ga k =
  let v          = V.Var ?lvl (g2 ga)
  in
  let ?lvl       = ?lvl + 1
      ?env       = V.EDef ?env v
      ?locals    = S.LBind ?locals NUnused a
  in cxt $ k v
{-# inline insertBinder #-}

-- | Run starting with the empty context.
withEmptyCxt :: (CxtArg => a) -> a
withEmptyCxt k =
  let ?lvl       = 0 :: Lvl
      ?env       = ENil
      ?locals    = S.LEmpty
      ?nameTable = mempty :: N.NameTable
  in k
{-# inline withEmptyCxt #-}
