
module Cxt.Extension where

import Common
import Cxt.Types
import Values

import qualified NameTable as N
import qualified Syntax as S
import qualified Values as V

empty :: Cxt
empty = Cxt V.ENil 0 S.LEmpty mempty

-- | Insert a bound variable.
bind :: Bind -> S.Ty -> V.GTy -> Cxt -> Cxt
bind x a ga (Cxt e l ls tbl) =
  Cxt (V.EDef e (V.Var l (g2 ga)))
      (l + 1)
      (S.LBind ls (bindToName x) a)
      (N.insert x (N.Local l ga) tbl)

-- | Insert a definition.
define :: Span -> S.Ty -> V.GTy -> S.Tm -> V.Val -> Cxt -> Cxt
define x a ga t vt (Cxt e l ls tbl) =
  Cxt (V.EDef e vt)
      (l + 1)
      (S.LDefine ls (NName x) a t)
      (N.insert (Bind x) (N.Local l ga) tbl)

-- | Insert a bound variable which does not exist in the source.
insert :: S.Ty -> V.GTy -> Cxt -> Cxt
insert a ga (Cxt e l ls tbl) =
  Cxt (V.EDef e (V.Var l (g2 ga)))
      (l + 1)
      (S.LBind ls NUnused a)
      tbl
